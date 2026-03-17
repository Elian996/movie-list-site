import json
import os
import re
import ssl
import sqlite3
import subprocess
import sys
import time
from datetime import datetime
from functools import wraps
from html import unescape
from html.parser import HTMLParser
from http.cookiejar import CookieJar
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin, urlparse
from urllib.request import HTTPCookieProcessor, Request, build_opener, urlopen

from flask import (
    Flask,
    jsonify,
    redirect,
    render_template,
    request,
    session,
    url_for,
)
from itsdangerous import BadSignature, BadTimeSignature, URLSafeTimedSerializer
from werkzeug.security import check_password_hash, generate_password_hash

try:
    from bs4 import BeautifulSoup
except ImportError:  # pragma: no cover - optional dependency
    BeautifulSoup = None


BASE_DIR = os.path.dirname(os.path.abspath(__file__))


def load_local_env():
    env_path = os.path.join(BASE_DIR, ".env")
    if not os.path.exists(env_path):
        return

    with open(env_path, "r", encoding="utf-8") as env_file:
        for raw_line in env_file:
            line = raw_line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue

            key, value = line.split("=", 1)
            key = key.strip()
            if not key or key in os.environ:
                continue

            value = value.strip()
            if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
                value = value[1:-1]
            os.environ[key] = value


load_local_env()

DATABASE_PATH = os.path.join(BASE_DIR, "movies.db")
MAX_IMPORT_RECORDS = 1000
USERNAME_PATTERN = re.compile(r"^[A-Za-z0-9]{4}$")
PASSWORD_PATTERN = re.compile(r"^[A-Za-z0-9]{8}$")
DOUBAN_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/122.0.0.0 Safari/537.36"
    ),
    "Accept": (
        "text/html,application/xhtml+xml,application/xml;q=0.9,"
        "image/avif,image/webp,image/apng,*/*;q=0.8"
    ),
    "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
    "Referer": "https://movie.douban.com/",
    "Cache-Control": "no-cache",
    "Pragma": "no-cache",
    "Upgrade-Insecure-Requests": "1",
}

DOUBAN_WARMUP_URLS = (
    "https://www.douban.com/",
    "https://movie.douban.com/",
)

DOUBAN_BROWSER_PAGE_SCRIPT = r"""
(() => {
  const nextLink =
    document.querySelector('.paginator .next a[href]') ||
    document.querySelector('link[rel="next"][href]') ||
    Array.from(document.querySelectorAll('a[href]')).find((node) => {
      const text = (node.textContent || '').trim();
      return text === '后页' || text === '后页>';
    });

  return JSON.stringify({
    url: location.href,
    title: document.title,
    nextHref: nextLink ? (nextLink.href || nextLink.getAttribute('href') || '') : '',
    html: document.documentElement.outerHTML
  });
})()
""".strip()

BROWSER_LABELS = {
    "auto": "自动检测",
    "chrome": "Google Chrome",
    "safari": "Safari",
}

BROWSER_APP_NAMES = {
    "chrome": "Google Chrome",
    "safari": "Safari",
}

DEEPSEEK_API_URL = "https://api.deepseek.com/chat/completions"
DEEPSEEK_MODEL = os.environ.get("DEEPSEEK_MODEL", "deepseek-chat").strip() or "deepseek-chat"
DEEPSEEK_REQUEST_TIMEOUT = 45
AI_CHAT_HISTORY_LIMIT = 12
AI_MOVIE_CONTEXT_LIMIT = 1000


class DoubanCollectionHTMLParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.stack = []
        self.item_depth = 0
        self.current_item = None
        self.capture_title_depth = None
        self.capture_intro_depth = None
        self.capture_subject_link_depth = None
        self.current_subject_link = []
        self.pairs = []

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        class_names = set((attributes.get("class") or "").split())
        href = attributes.get("href") or ""

        self.stack.append({"tag": tag, "classes": class_names, "href": href})
        depth = len(self.stack)

        if "item" in class_names:
            self.item_depth += 1
            if self.item_depth == 1:
                self.current_item = {"title": [], "intro": [], "subject_titles": []}

        if not self.current_item:
            return

        if "title" in class_names and self.capture_title_depth is None:
            self.capture_title_depth = depth

        if "intro" in class_names and self.capture_intro_depth is None:
            self.capture_intro_depth = depth

        if self.capture_subject_link_depth is None and is_movie_subject_url(href):
            self.capture_subject_link_depth = depth
            self.current_subject_link = []

    def handle_endtag(self, tag):
        if not self.stack:
            return

        depth = len(self.stack)
        node = self.stack.pop()

        if self.capture_subject_link_depth == depth:
            text = normalize_text("".join(self.current_subject_link))
            if text and self.current_item is not None:
                self.current_item["subject_titles"].append(text)
            self.capture_subject_link_depth = None
            self.current_subject_link = []

        if self.capture_title_depth == depth:
            self.capture_title_depth = None

        if self.capture_intro_depth == depth:
            self.capture_intro_depth = None

        if "item" in node["classes"]:
            if self.item_depth == 1 and self.current_item is not None:
                pair = finalize_extracted_item(
                    title="".join(self.current_item["title"]),
                    intro="".join(self.current_item["intro"]),
                    subject_titles=self.current_item["subject_titles"],
                )
                if pair:
                    self.pairs.append(pair)
                self.current_item = None
            self.item_depth = max(self.item_depth - 1, 0)

    def handle_data(self, data):
        if not self.current_item:
            return

        if self.capture_title_depth is not None:
            self.current_item["title"].append(data)

        if self.capture_intro_depth is not None:
            self.current_item["intro"].append(data)

        if self.capture_subject_link_depth is not None:
            self.current_subject_link.append(data)


class AIConfigurationError(ValueError):
    """Raised when the AI feature is not fully configured."""


app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "dev-secret-change-me")
app.config["MAX_FORM_MEMORY_SIZE"] = 4 * 1024 * 1024


def get_token_serializer():
    return URLSafeTimedSerializer(app.secret_key, salt="douban-import")


def get_connection():
    connection = sqlite3.connect(DATABASE_PATH)
    connection.row_factory = sqlite3.Row
    return connection


def utc_now():
    return datetime.utcnow().isoformat(timespec="seconds")


def column_exists(connection, table_name, column_name):
    columns = connection.execute(f"PRAGMA table_info({table_name})").fetchall()
    return any(column["name"] == column_name for column in columns)


def init_db():
    connection = get_connection()

    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT NOT NULL UNIQUE,
            password_hash TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """
    )

    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS movies (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            director TEXT NOT NULL,
            title TEXT NOT NULL,
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users (id)
        )
        """
    )

    if not column_exists(connection, "movies", "user_id"):
        connection.execute("ALTER TABLE movies ADD COLUMN user_id INTEGER")

    connection.execute(
        """
        CREATE INDEX IF NOT EXISTS idx_movies_user_title
        ON movies (user_id, title, director)
        """
    )
    connection.commit()
    connection.close()


def validate_username(username):
    if not USERNAME_PATTERN.fullmatch(username or ""):
        raise ValueError("用户名必须是 4 位字母或数字。")


def validate_password(password):
    if not PASSWORD_PATTERN.fullmatch(password or ""):
        raise ValueError("密码必须是 8 位字母或数字。")


def get_user_by_username(username):
    connection = get_connection()
    user = connection.execute(
        "SELECT id, username, password_hash, created_at FROM users WHERE username = ?",
        (username,),
    ).fetchone()
    connection.close()
    return dict(user) if user else None


def get_user_by_id(user_id):
    connection = get_connection()
    user = connection.execute(
        "SELECT id, username, created_at FROM users WHERE id = ?",
        (user_id,),
    ).fetchone()
    connection.close()
    return dict(user) if user else None


def create_user(username, password):
    validate_username(username)
    validate_password(password)

    existing_user = get_user_by_username(username)
    if existing_user:
        raise ValueError("用户名已存在，请换一个。")

    connection = get_connection()
    user_count = connection.execute("SELECT COUNT(*) AS count FROM users").fetchone()["count"]
    now = utc_now()

    try:
        cursor = connection.execute(
            """
            INSERT INTO users (username, password_hash, created_at)
            VALUES (?, ?, ?)
            """,
            (username, generate_password_hash(password), now),
        )
        user_id = cursor.lastrowid

        # Preserve the pre-login single-user data by assigning orphan rows
        # to the very first registered account.
        if user_count == 0:
            connection.execute(
                "UPDATE movies SET user_id = ? WHERE user_id IS NULL",
                (user_id,),
            )

        connection.commit()
    finally:
        connection.close()

    return get_user_by_id(user_id)


def authenticate_user(username, password):
    validate_username(username)
    validate_password(password)

    user = get_user_by_username(username)
    if not user or not check_password_hash(user["password_hash"], password):
        raise ValueError("用户名或密码错误。")

    return get_user_by_id(user["id"])


def get_current_user():
    user_id = session.get("user_id")
    if not user_id:
        return None
    return get_user_by_id(user_id)


def create_bookmarklet_token(user_id):
    return get_token_serializer().dumps({"user_id": user_id})


def parse_bookmarklet_token(token, max_age=7 * 24 * 60 * 60):
    try:
        payload = get_token_serializer().loads(token, max_age=max_age)
    except (BadSignature, BadTimeSignature) as error:
        raise ValueError("导入链接已失效，请回到电影清单页面重新生成后再试。") from error

    user_id = payload.get("user_id")
    if not user_id or not get_user_by_id(user_id):
        raise ValueError("导入链接对应的用户不存在，请重新登录后再试。")

    return user_id


def login_required(route_function):
    @wraps(route_function)
    def wrapper(*args, **kwargs):
        if not get_current_user():
            return redirect(url_for("login_page"))
        return route_function(*args, **kwargs)

    return wrapper


def api_login_required(route_function):
    @wraps(route_function)
    def wrapper(*args, **kwargs):
        user = get_current_user()
        if not user:
            return jsonify({"error": "请先登录。"}), 401
        return route_function(user, *args, **kwargs)

    return wrapper


def list_movies(user_id):
    connection = get_connection()
    rows = connection.execute(
        """
        SELECT id, director, title, created_at, updated_at
        FROM movies
        WHERE user_id = ?
        ORDER BY LOWER(title) ASC, LOWER(director) ASC, id ASC
        """,
        (user_id,),
    ).fetchall()
    connection.close()
    return [dict(row) for row in rows]


def is_deepseek_configured():
    return bool((os.environ.get("DEEPSEEK_API_KEY") or "").strip())


def normalize_ai_messages(raw_messages):
    if not isinstance(raw_messages, list):
        raise ValueError("AI 对话格式不正确，请刷新页面后重试。")

    cleaned_messages = []
    allowed_roles = {"user", "assistant"}

    for item in raw_messages[-AI_CHAT_HISTORY_LIMIT:]:
        if not isinstance(item, dict):
            continue

        role = (item.get("role") or "").strip()
        content = (item.get("content") or "").strip()

        if role not in allowed_roles or not content:
            continue

        cleaned_messages.append(
            {
                "role": role,
                "content": content[:4000],
            }
        )

    if not cleaned_messages:
        raise ValueError("请先输入你想让 AI 分析的问题。")

    if cleaned_messages[-1]["role"] != "user":
        raise ValueError("最后一条消息需要是你的提问。")

    return cleaned_messages


def build_movie_context_for_ai(user_id):
    movies = list_movies(user_id)[:AI_MOVIE_CONTEXT_LIMIT]
    total_movies = len(movies)

    if not movies:
        return (
            "当前用户还没有保存电影记录。"
            "如果用户请求分析口味，请先说明样本不足，再给出可执行的补充建议。"
        )

    movie_lines = [
        f"{index + 1}. {movie['title']} / {movie['director']}"
        for index, movie in enumerate(movies)
    ]

    return (
        f"当前用户已保存 {total_movies} 部电影。"
        "以下是当前已保存片单，格式为“影名 / 导演”：\n"
        + "\n".join(movie_lines)
    )


def build_ai_system_prompt():
    return (
        "你是网站里的电影分析助手，负责根据用户当前片单做口味分析、观影总结和电影推荐。"
        "请始终使用简体中文回复，语气自然、具体、克制，适合放在网页右下角的小型聊天窗口里。"
        "如果用户要求推荐电影，优先推荐不在用户当前片单中的影片，每次给 3 到 5 部即可，"
        "并为每一部写清楚为什么适合他。"
        "如果用户要求分析片单，请总结题材偏好、导演倾向、地区风格、观影气质或明显缺口。"
        "如果用户片单样本不够、信息不足，先明确说明判断依据有限，再继续给建议。"
        "不要假装知道你不确定的剧情、年份或主创信息；拿不准时请直接说明。"
        "除非用户明确要求，不要输出过长答案，也不要重复整份片单。"
    )


def parse_deepseek_error(error):
    try:
        body = error.read().decode("utf-8", errors="ignore")
    except Exception:
        body = ""

    try:
        payload = json.loads(body) if body else {}
    except json.JSONDecodeError:
        payload = {}

    error_message = (
        payload.get("error", {}).get("message")
        or payload.get("message")
        or body.strip()
    )

    if error.code == 401:
        return "DeepSeek API Key 无效或已失效，请更新后重试。"
    if error.code == 402:
        return "DeepSeek 账户余额不足，请先充值后再试。"
    if error.code == 429:
        return "DeepSeek 当前请求过多，请稍后再试。"
    if error_message:
        return f"DeepSeek 请求失败：{error_message}"
    return f"DeepSeek 请求失败（HTTP {error.code}）。"


def request_deepseek_chat(messages):
    api_key = (os.environ.get("DEEPSEEK_API_KEY") or "").strip()
    if not api_key:
        raise AIConfigurationError(
            "AI 功能已经接好，但服务器还没有配置 DeepSeek API Key。"
            "把 `DEEPSEEK_API_KEY` 配好后，这个聊天窗就能直接使用。"
        )

    payload = {
        "model": DEEPSEEK_MODEL,
        "messages": messages,
        "temperature": 0.8,
        "max_tokens": 900,
    }
    request_object = Request(
        DEEPSEEK_API_URL,
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
        method="POST",
    )

    try:
        with urlopen(request_object, timeout=DEEPSEEK_REQUEST_TIMEOUT) as response:
            raw_body = response.read().decode("utf-8", errors="ignore")
    except HTTPError as error:
        raise ValueError(parse_deepseek_error(error)) from error
    except URLError as error:
        if isinstance(error.reason, ssl.SSLCertVerificationError):
            insecure_context = ssl._create_unverified_context()
            try:
                with urlopen(
                    request_object,
                    timeout=DEEPSEEK_REQUEST_TIMEOUT,
                    context=insecure_context,
                ) as response:
                    raw_body = response.read().decode("utf-8", errors="ignore")
            except HTTPError as nested_error:
                raise ValueError(parse_deepseek_error(nested_error)) from nested_error
            except URLError as nested_error:
                raise ValueError("暂时无法连接 DeepSeek 服务，请稍后再试。") from nested_error
        else:
            raise ValueError("暂时无法连接 DeepSeek 服务，请稍后再试。") from error

    try:
        response_payload = json.loads(raw_body)
    except json.JSONDecodeError as error:
        raise ValueError("DeepSeek 返回的数据无法解析，请稍后再试。") from error

    assistant_message = (
        response_payload.get("choices", [{}])[0]
        .get("message", {})
        .get("content", "")
        .strip()
    )
    if not assistant_message:
        raise ValueError("DeepSeek 没有返回可用内容，请稍后再试。")

    return assistant_message


def chat_with_movie_ai(user_id, conversation_messages):
    messages = [
        {"role": "system", "content": build_ai_system_prompt()},
        {"role": "system", "content": build_movie_context_for_ai(user_id)},
        *conversation_messages,
    ]
    return request_deepseek_chat(messages)


def replace_movies(rows, user_id):
    now = utc_now()
    cleaned_rows = []

    for row in rows:
        director = (row.get("director") or "").strip()
        title = (row.get("title") or "").strip()

        if not director and not title:
            continue

        if not director or not title:
            raise ValueError("每一条电影记录都需要同时填写导演和影名。")

        cleaned_rows.append(
            {
                "id": row.get("id"),
                "director": director,
                "title": title,
            }
        )

    connection = get_connection()

    try:
        existing_rows = connection.execute(
            "SELECT id, created_at FROM movies WHERE user_id = ?",
            (user_id,),
        ).fetchall()
        created_at_by_id = {row["id"]: row["created_at"] for row in existing_rows}

        connection.execute("DELETE FROM movies WHERE user_id = ?", (user_id,))
        for row in cleaned_rows:
            existing_id = row.get("id")
            created_at = created_at_by_id.get(existing_id, now)
            connection.execute(
                """
                INSERT INTO movies (user_id, director, title, created_at, updated_at)
                VALUES (?, ?, ?, ?, ?)
                """,
                (user_id, row["director"], row["title"], created_at, now),
            )
        connection.commit()
    finally:
        connection.close()


def normalize_text(value):
    return re.sub(r"\s+", " ", unescape(value or "")).strip()


def clean_title_text(value):
    title = normalize_text(strip_tags(value))
    title = re.split(r"\s*/\s*", title, maxsplit=1)[0].strip()
    return re.sub(r"\s+", " ", title)


def is_movie_subject_url(url):
    return bool(
        re.search(
            r"^(?:https?://movie\.douban\.com)?/subject/\d+/?",
            (url or "").strip(),
            flags=re.IGNORECASE,
        )
    )


def finalize_extracted_item(title="", intro="", subject_titles=None):
    resolved_title = clean_title_text(title)
    if not resolved_title:
        for candidate in subject_titles or []:
            resolved_title = clean_title_text(candidate)
            if resolved_title:
                break

    director = parse_director_from_text(intro, title=resolved_title)
    if resolved_title and director:
        return (resolved_title, director)
    return None


def extract_title_and_director_pairs(html):
    pairs = []

    if BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")
        item_candidates = soup.select(".item")

        for item in item_candidates:
            title = ""
            director = ""

            title_node = item.select_one(".title")
            if title_node:
                title = title_node.get_text(" ", strip=True).split("/")[0].strip()

            intro_node = item.select_one(".intro")
            if intro_node:
                director = parse_director_from_text(
                    intro_node.get_text(" ", strip=True), title=title
                )

            if title and director:
                pairs.append((title, director))

        if pairs:
            return pairs

    parser = DoubanCollectionHTMLParser()
    try:
        parser.feed(html)
        parser.close()
    except Exception:
        parser = None

    if parser and parser.pairs:
        return parser.pairs

    item_matches = re.findall(
        r'<div[^>]*class="[^"]*\bitem\b[^"]*"[^>]*>(.*?)</div>\s*</div>',
        html,
        flags=re.IGNORECASE | re.DOTALL,
    )

    if item_matches:
        for item_html in item_matches:
            title_match = re.search(
                r'<li[^>]*class="[^"]*\btitle\b[^"]*"[^>]*>(.*?)</li>',
                item_html,
                flags=re.IGNORECASE | re.DOTALL,
            )
            intro_match = re.search(
                r'<li[^>]*class="[^"]*\bintro\b[^"]*"[^>]*>(.*?)</li>',
                item_html,
                flags=re.IGNORECASE | re.DOTALL,
            )

            if not title_match or not intro_match:
                continue

            pair = finalize_extracted_item(
                title=title_match.group(1),
                intro=strip_tags(intro_match.group(1)),
            )
            if pair:
                pairs.append(pair)
    else:
        title_matches = re.findall(
            r'<(?:span|li)[^>]*class="[^"]*\btitle\b[^"]*"[^>]*>(.*?)</(?:span|li)>',
            html,
            flags=re.IGNORECASE | re.DOTALL,
        )
        intro_matches = re.findall(
            r'<(?:span|li)[^>]*class="[^"]*\bintro\b[^"]*"[^>]*>(.*?)</(?:span|li)>',
            html,
            flags=re.IGNORECASE | re.DOTALL,
        )

        for raw_title, raw_intro in zip(title_matches, intro_matches):
            pair = finalize_extracted_item(title=raw_title, intro=strip_tags(raw_intro))
            if pair:
                pairs.append(pair)

    return pairs


def strip_tags(value):
    return re.sub(r"<[^>]+>", "", value or "").strip()


def parse_director_from_text(text, title=""):
    normalized = re.sub(r"\s+", " ", text or "").strip()
    normalized = re.sub(r"https?://\S+|www\.\S+", "", normalized, flags=re.IGNORECASE)
    match = re.search(r"导演[:：]?\s*([^/]+)", normalized)
    if match:
        return match.group(1).strip()

    parts = [part.strip() for part in normalized.split("/") if part.strip()]
    for part in parts:
        if is_year_segment(part) or is_metadata_segment(part):
            continue
        if is_director_segment(part, title):
            return part

    duration_index = find_duration_index(parts)
    if duration_index is not None:
        directors = collect_directors_before_duration(parts, duration_index, title)
        if directors:
            return " / ".join(directors)

    if parts:
        return next(
            (part for part in parts if not is_year_segment(part) and not is_metadata_segment(part)),
            parts[0],
        )
    return ""


def is_year_segment(part):
    return bool(re.fullmatch(r"\d{4}(?:[-.]\d{1,2}[-.]\d{1,2})?", part or ""))


def is_metadata_segment(part):
    metadata_keywords = (
        "分钟",
        "集",
        "中国",
        "美国",
        "英国",
        "日本",
        "韩国",
        "法国",
        "德国",
        "意大利",
        "西班牙",
        "中国大陆",
        "中国香港",
        "中国台湾",
        "纪录片",
        "剧情",
        "喜剧",
        "动作",
        "动画",
        "爱情",
        "惊悚",
        "恐怖",
        "战争",
        "冒险",
        "奇幻",
        "科幻",
        "犯罪",
        "悬疑",
        "音乐",
        "歌舞",
        "家庭",
        "传记",
        "历史",
        "武侠",
        "古装",
        "脱口秀",
        "真人秀",
        "短片",
        "韩语",
        "英语",
        "日语",
        "法语",
        "粤语",
        "汉语",
        "普通话",
    )
    return any(keyword in (part or "") for keyword in metadata_keywords)


def find_duration_index(parts):
    duration_pattern = re.compile(
        r"^\d+\s*(分钟|min|分钟\(.+\)|集|集\(.+\)|小时|季|集全)$",
        flags=re.IGNORECASE,
    )
    for index, part in enumerate(parts):
        if duration_pattern.search(part) or "分钟" in part:
            return index
    return None


def collect_directors_before_duration(parts, duration_index, title=""):
    directors = []

    for index in range(duration_index - 1, -1, -1):
        part = parts[index].strip()
        if not part:
            continue

        if is_director_segment(part, title):
            directors.insert(0, part)
            continue

        if directors:
            break

    return directors


def is_director_segment(part, title=""):
    if len(part) > 40:
        return False

    lowered = part.lower()
    if lowered.startswith(("http://", "https://", "www.")):
        return False

    if is_metadata_segment(part):
        return False

    if re.search(r"\d{4}", part):
        return False

    if re.search(r"[()（）]", part):
        return False

    cleaned_title = (title or "").strip()
    if cleaned_title and part == cleaned_title:
        return False

    return bool(re.search(r"[\u4e00-\u9fffA-Za-z]", part))


def looks_like_douban_login_page(html):
    normalized = normalize_text(strip_tags(html))
    login_markers = (
        "登录豆瓣",
        "扫码登录",
        "密码登录",
        "豆瓣账号登录",
        "accounts.douban.com/passport/login",
    )
    return any(marker in normalized or marker in html for marker in login_markers)


def looks_like_douban_block_page(html):
    normalized = normalize_text(strip_tags(html))
    block_markers = (
        "检测到有异常请求",
        "sec.douban.com",
        "访问受限",
        "安全验证",
        "验证码",
        "403 Forbidden",
    )
    return any(marker in normalized or marker in html for marker in block_markers)


def apple_script_quote(value):
    return (
        (value or "")
        .replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
    )


def run_applescript(script, browser_label="浏览器"):
    try:
        completed = subprocess.run(
            ["/usr/bin/osascript"],
            input=script,
            text=True,
            capture_output=True,
            check=True,
        )
    except FileNotFoundError as error:
        raise ValueError("当前系统不支持通过浏览器会话导入。") from error
    except subprocess.CalledProcessError as error:
        detail = (error.stderr or error.stdout or "").strip()
        if "Not authorized" in detail or "1743" in detail:
            raise ValueError(
                f"浏览器导入需要系统授权控制 {browser_label}。请在弹窗中允许，"
                "或到“系统设置 -> 隐私与安全性 -> 自动化”里开启权限后重试。"
            ) from error
        raise ValueError(f"通过 {browser_label} 导入失败：{detail or '未知错误'}") from error

    return completed.stdout.strip()


def run_command(command, input_text=None):
    completed = subprocess.run(
        command,
        input=input_text,
        text=True,
        capture_output=True,
        check=True,
    )
    return completed.stdout


def get_clipboard_text():
    return run_command(["/usr/bin/pbpaste"])


def set_clipboard_text(value):
    run_command(["/usr/bin/pbcopy"], input_text=value)


def get_frontmost_supported_browser():
    script = '''
tell application "System Events"
    set frontApp to name of first application process whose frontmost is true
end tell
return frontApp
'''.strip()
    try:
        app_name = run_applescript(script).strip()
    except ValueError:
        return ""

    for browser_name, known_app_name in BROWSER_APP_NAMES.items():
        if app_name == known_app_name:
            return browser_name
    return ""


def open_chrome_window(url):
    quoted_url = apple_script_quote(url)
    script = f'''
tell application "Google Chrome"
    activate
    set newWindow to make new window
    set URL of active tab of newWindow to "{quoted_url}"
    repeat 120 times
        if loading of active tab of newWindow is false then exit repeat
        delay 0.25
    end repeat
    delay 0.3
    return id of newWindow
end tell
'''.strip()
    return int(run_applescript(script, browser_label=BROWSER_LABELS["chrome"]))


def read_chrome_window_snapshot(window_id, current_url):
    original_clipboard = ""
    clipboard_backed_up = False
    source_url = current_url if current_url.startswith("view-source:") else f"view-source:{current_url}"
    quoted_url = apple_script_quote(source_url)
    script = f'''
tell application "Google Chrome"
    set targetWindow to first window whose id is {int(window_id)}
    activate
    set URL of active tab of targetWindow to "{quoted_url}"
    repeat 120 times
        if loading of active tab of targetWindow is false then exit repeat
        delay 0.25
    end repeat
end tell
tell application "System Events"
    tell process "Google Chrome"
        keystroke "a" using {{command down}}
        delay 0.15
        keystroke "c" using {{command down}}
    end tell
end tell
'''.strip()
    try:
        original_clipboard = get_clipboard_text()
        clipboard_backed_up = True
    except Exception:
        original_clipboard = ""

    try:
        run_applescript(script, browser_label=BROWSER_LABELS["chrome"])
        time.sleep(0.2)
        html = get_clipboard_text()
    except ValueError as error:
        message = str(error)
        if "System Events" in message:
            raise ValueError(
                "通过 Google Chrome 导入失败：需要允许本应用控制系统键盘与辅助功能，"
                "以便自动复制页面源码。请在“系统设置 -> 隐私与安全性 -> 辅助功能 / 自动化”中授权后重试。"
            ) from error
        raise
    finally:
        if clipboard_backed_up:
            try:
                set_clipboard_text(original_clipboard)
            except Exception:
                pass

    if not html.strip():
        raise ValueError("Chrome 没有复制到页面源码，请确认豆瓣页面已经完全加载。")

    return json.dumps(
        {
            "url": current_url,
            "nextHref": find_next_page_url(html, current_url) or "",
            "html": html,
        }
    )


def navigate_chrome_window(window_id, url):
    quoted_url = apple_script_quote(url)
    script = f'''
tell application "Google Chrome"
    set targetWindow to first window whose id is {int(window_id)}
    set URL of active tab of targetWindow to "{quoted_url}"
    repeat 120 times
        if loading of active tab of targetWindow is false then exit repeat
        delay 0.25
    end repeat
    delay 0.3
    return URL of active tab of targetWindow
end tell
'''.strip()
    return run_applescript(script, browser_label=BROWSER_LABELS["chrome"])


def close_chrome_window(window_id):
    script = f'''
tell application "Google Chrome"
    if (count of (every window whose id is {int(window_id)})) > 0 then
        close (first window whose id is {int(window_id)})
    end if
end tell
'''.strip()
    try:
        run_applescript(script, browser_label=BROWSER_LABELS["chrome"])
    except ValueError:
        pass


def open_safari_window(url):
    quoted_url = apple_script_quote(url)
    script = f'''
tell application "Safari"
    activate
    make new document with properties {{URL:"{quoted_url}"}}
    set targetWindow to front window
    repeat 120 times
        try
            if (do JavaScript "document.readyState" in current tab of targetWindow) is "complete" then exit repeat
        end try
        delay 0.25
    end repeat
    delay 0.3
    return id of targetWindow
end tell
'''.strip()
    return int(run_applescript(script, browser_label=BROWSER_LABELS["safari"]))


def read_safari_window_snapshot(window_id):
    quoted_js = apple_script_quote(DOUBAN_BROWSER_PAGE_SCRIPT)
    script = f'''
tell application "Safari"
    set targetWindow to first window whose id is {int(window_id)}
    repeat 120 times
        try
            if (do JavaScript "document.readyState" in current tab of targetWindow) is "complete" then exit repeat
        end try
        delay 0.25
    end repeat
    delay 0.2
    return do JavaScript "{quoted_js}" in current tab of targetWindow
end tell
'''.strip()
    raw_output = run_applescript(script, browser_label=BROWSER_LABELS["safari"])
    if not raw_output:
        raise ValueError("Safari 没有返回页面内容，请确认豆瓣标签页已经完全加载。")
    return raw_output


def navigate_safari_window(window_id, url):
    quoted_url = apple_script_quote(url)
    script = f'''
tell application "Safari"
    set targetWindow to first window whose id is {int(window_id)}
    set URL of current tab of targetWindow to "{quoted_url}"
    repeat 120 times
        try
            if (do JavaScript "document.readyState" in current tab of targetWindow) is "complete" then exit repeat
        end try
        delay 0.25
    end repeat
    delay 0.3
    return URL of current tab of targetWindow
end tell
'''.strip()
    return run_applescript(script, browser_label=BROWSER_LABELS["safari"])


def close_safari_window(window_id):
    script = f'''
tell application "Safari"
    if (count of (every window whose id is {int(window_id)})) > 0 then
        close (first window whose id is {int(window_id)})
    end if
end tell
'''.strip()
    try:
        run_applescript(script, browser_label=BROWSER_LABELS["safari"])
    except ValueError:
        pass


def get_browser_candidates(preferred_browser):
    if preferred_browser == "chrome":
        return ["chrome"]
    if preferred_browser == "safari":
        return ["safari"]

    frontmost_browser = get_frontmost_supported_browser()
    ordered_browsers = []

    if frontmost_browser:
        ordered_browsers.append(frontmost_browser)

    for browser_name in ("chrome", "safari"):
        if browser_name not in ordered_browsers:
            ordered_browsers.append(browser_name)

    return ordered_browsers


def open_browser_window(browser_name, url):
    if browser_name == "chrome":
        return open_chrome_window(url)
    if browser_name == "safari":
        return open_safari_window(url)
    raise ValueError(f"不支持的浏览器：{browser_name}")


def read_browser_window_snapshot(browser_name, window_id, current_url):
    if browser_name == "chrome":
        return read_chrome_window_snapshot(window_id, current_url)
    if browser_name == "safari":
        return read_safari_window_snapshot(window_id)
    raise ValueError(f"不支持的浏览器：{browser_name}")


def navigate_browser_window(browser_name, window_id, url):
    if browser_name == "chrome":
        return navigate_chrome_window(window_id, url)
    if browser_name == "safari":
        return navigate_safari_window(window_id, url)
    raise ValueError(f"不支持的浏览器：{browser_name}")


def close_browser_window(browser_name, window_id):
    if browser_name == "chrome":
        close_chrome_window(window_id)
        return
    if browser_name == "safari":
        close_safari_window(window_id)
        return
    raise ValueError(f"不支持的浏览器：{browser_name}")


def collect_pairs_via_browser(start_url, preferred_browser="auto"):
    if sys.platform != "darwin":
        raise ValueError("浏览器导入目前只支持 macOS。")

    browser_errors = []

    for browser_name in get_browser_candidates(preferred_browser):
        window_id = None
        visited_urls = set()
        all_pairs = []
        page_count = 0

        try:
            window_id = open_browser_window(browser_name, start_url)
            current_url = start_url

            while (
                current_url
                and current_url not in visited_urls
                and len(all_pairs) < MAX_IMPORT_RECORDS
            ):
                visited_urls.add(current_url)
                snapshot_json = read_browser_window_snapshot(
                    browser_name,
                    window_id,
                    current_url,
                )
                try:
                    snapshot = json.loads(snapshot_json)
                except json.JSONDecodeError as error:
                    raise ValueError(
                        f"{BROWSER_LABELS[browser_name]} 返回的页面数据无法解析。"
                    ) from error

                html = snapshot.get("html", "")
                current_url = (snapshot.get("url", current_url) or current_url).strip()
                next_url = (snapshot.get("nextHref", "") or "").strip()

                page_count += 1
                validate_douban_collection_page(html, via_browser=True)

                page_pairs = extract_title_and_director_pairs(html)
                all_pairs.extend(page_pairs)

                if len(page_pairs) == 0:
                    break

                if next_url and next_url not in visited_urls:
                    if browser_name != "chrome":
                        navigate_browser_window(browser_name, window_id, next_url)
                    current_url = next_url
                else:
                    current_url = None

            if all_pairs:
                return all_pairs[:MAX_IMPORT_RECORDS], page_count, browser_name

            browser_errors.append(
                f"{BROWSER_LABELS[browser_name]} 已打开页面，但没有识别到电影数据。"
            )
        except ValueError as error:
            browser_errors.append(str(error))
        finally:
            if window_id is not None:
                close_browser_window(browser_name, window_id)

    detail = "；".join(dict.fromkeys(browser_errors))
    raise ValueError(
        "浏览器导入失败。没有在可用浏览器里拿到有效的豆瓣“看过”列表。"
        + (f" 详情：{detail}" if detail else "")
    )


def build_douban_opener():
    return build_opener(HTTPCookieProcessor(CookieJar()))


def fetch_html_once(url, headers, opener=None, context=None):
    request_object = Request(url, headers=headers)
    try:
        if opener is not None:
            with opener.open(request_object, timeout=15) as response:
                return response.read().decode("utf-8", errors="ignore")
        with urlopen(request_object, timeout=15, context=context) as response:
            return response.read().decode("utf-8", errors="ignore")
    except URLError as error:
        # Some local environments inject a custom certificate chain and break
        # Python's default HTTPS verification for otherwise valid pages.
        if isinstance(error.reason, ssl.SSLCertVerificationError):
            insecure_context = ssl._create_unverified_context()
            with urlopen(request_object, timeout=15, context=insecure_context) as response:
                return response.read().decode("utf-8", errors="ignore")
        raise


def warm_up_douban_session(opener, headers, target_url, force=False):
    if getattr(opener, "_douban_warmed", False) and not force:
        return

    warmup_urls = list(DOUBAN_WARMUP_URLS)

    parsed_target = urlparse(target_url)
    if parsed_target.scheme and parsed_target.netloc:
        warmup_urls.append(f"{parsed_target.scheme}://{parsed_target.netloc}/")

    for warmup_url in warmup_urls:
        try:
            fetch_html_once(warmup_url, headers=headers, opener=opener)
        except Exception:
            continue

    opener._douban_warmed = True


def fetch_html(url, headers, opener=None):
    active_opener = opener or build_douban_opener()
    warm_up_douban_session(active_opener, headers, url)

    try:
        return fetch_html_once(url, headers=headers, opener=active_opener)
    except HTTPError as error:
        if error.code != 403:
            raise

        warm_up_douban_session(active_opener, headers, url, force=True)
        return fetch_html_once(url, headers=headers, opener=active_opener)


def find_next_page_url(html, current_url):
    if BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")
        next_link = soup.select_one('.paginator .next a[href], link[rel="next"]')
        if next_link and next_link.get("href"):
            return urljoin(current_url, next_link["href"])

    paginator_match = re.search(
        r'<span[^>]*class="[^"]*\bnext\b[^"]*"[^>]*>.*?<a[^>]*href="([^"]+)"',
        html,
        flags=re.IGNORECASE,
    )
    if paginator_match:
        return urljoin(current_url, paginator_match.group(1))

    link_match = re.search(
        r'<link[^>]*rel="next"[^>]*href="([^"]+)"',
        html,
        flags=re.IGNORECASE,
    )
    if link_match:
        return urljoin(current_url, link_match.group(1))

    text_match = re.search(
        r'<a[^>]*href="([^"]+)"[^>]*>\s*后页',
        html,
        flags=re.IGNORECASE,
    )
    if text_match:
        return urljoin(current_url, text_match.group(1))

    return None


def validate_douban_collection_page(html, cookie_provided=False, via_browser=False):
    if looks_like_douban_block_page(html):
        if via_browser:
            raise ValueError(
                "当前浏览器打开的是豆瓣安全验证页或风控页。请先在浏览器里完成验证，"
                "确认页面能正常看到“我看过的影视”列表后再重试。"
            )
        raise ValueError(
            "豆瓣暂时拦截了这次抓取请求。请稍后重试，或改为粘贴页面 HTML 导入。"
        )

    if looks_like_douban_login_page(html):
        if via_browser:
            raise ValueError(
                "当前所选浏览器里没有可用的豆瓣登录态。请先在这个浏览器中登录豆瓣，"
                "或者切换到另一个已登录的浏览器后重试。"
            )
        if cookie_provided:
            raise ValueError(
                "豆瓣返回了登录页，当前 Cookie 可能已失效。请更新浏览器 Cookie 后重试。"
            )
        raise ValueError(
            "这个页面需要登录后才能访问。请补充浏览器 Cookie，或直接粘贴页面 HTML 导入。"
        )


def collect_paginated_pairs(start_url, headers, opener, cookie_provided=False):
    current_url = start_url
    visited_urls = set()
    all_pairs = []
    page_count = 0

    while (
        current_url
        and current_url not in visited_urls
        and len(all_pairs) < MAX_IMPORT_RECORDS
    ):
        visited_urls.add(current_url)
        html = fetch_html(current_url, headers, opener=opener)
        page_count += 1
        validate_douban_collection_page(html, cookie_provided=cookie_provided)

        page_pairs = extract_title_and_director_pairs(html)
        all_pairs.extend(page_pairs)

        if len(page_pairs) == 0:
            break

        current_url = find_next_page_url(html, current_url)

    return all_pairs[:MAX_IMPORT_RECORDS], page_count


def normalize_import_pairs(extracted_pairs):
    if not extracted_pairs:
        raise ValueError(
            "没有从页面中识别出电影数据。请确认页面内容确实是豆瓣“看过”列表，"
            "而不是登录页、验证码页或其他页面。"
        )

    normalized_pairs = []
    seen_pairs = set()

    for title, director in extracted_pairs:
        pair_key = ((title or "").strip(), (director or "").strip())
        if pair_key[0] and pair_key[1] and pair_key not in seen_pairs:
            normalized_pairs.append(pair_key)
            seen_pairs.add(pair_key)

    if not normalized_pairs:
        raise ValueError("没有可导入的有效电影数据。")

    return normalized_pairs


def persist_import_pairs(
    extracted_pairs,
    user_id,
    page_count_hint=1,
    browser_used="",
):
    normalized_pairs = normalize_import_pairs(extracted_pairs)

    connection = get_connection()
    inserted_count = 0

    try:
        existing_pairs = {
            (row["title"], row["director"])
            for row in connection.execute(
                "SELECT title, director FROM movies WHERE user_id = ?",
                (user_id,),
            ).fetchall()
        }
        now = utc_now()

        for title, director in normalized_pairs:
            if (title, director) in existing_pairs:
                continue

            connection.execute(
                """
                INSERT INTO movies (user_id, director, title, created_at, updated_at)
                VALUES (?, ?, ?, ?, ?)
                """,
                (user_id, director, title, now, now),
            )
            existing_pairs.add((title, director))
            inserted_count += 1

        connection.commit()
    finally:
        connection.close()

    return {
        "imported_count": inserted_count,
        "parsed_count": len(normalized_pairs),
        "page_count": page_count_hint or 1,
        "capped": len(normalized_pairs) >= MAX_IMPORT_RECORDS,
        "browser_used": browser_used,
    }


def import_from_douban(
    url="",
    html="",
    cookie="",
    user_id=None,
    prefer_browser=False,
    browser="auto",
    page_count_hint=None,
):
    normalized_url = unescape((url or "").strip())
    payload_html = html.strip()
    page_count = 1
    cookie_value = cookie.strip()
    browser_used = ""

    if not payload_html:
        if not normalized_url:
            raise ValueError("请提供豆瓣页面 URL 或页面 HTML。")

        parsed = urlparse(normalized_url)
        if "douban.com" not in parsed.netloc:
            raise ValueError("目前只支持导入 douban.com 页面。")

        if prefer_browser:
            extracted_pairs, page_count, browser_used = collect_pairs_via_browser(
                normalized_url,
                preferred_browser=browser,
            )
        else:
            headers = dict(DOUBAN_HEADERS)
            if cookie_value:
                headers["Cookie"] = cookie_value

            opener = build_douban_opener()
            try:
                extracted_pairs, page_count = collect_paginated_pairs(
                    normalized_url,
                    headers,
                    opener=opener,
                    cookie_provided=bool(cookie_value),
                )
            except HTTPError as error:
                if error.code == 403:
                    raise ValueError(
                        "豆瓣拒绝了这次抓取请求（403）。请优先使用页面里的“无权限一键导入”书签，"
                        "或更新 Cookie，或者直接粘贴页面 HTML 导入。"
                    ) from error
                raise
    else:
        validate_douban_collection_page(payload_html, cookie_provided=bool(cookie_value))
        extracted_pairs = extract_title_and_director_pairs(payload_html)

    return persist_import_pairs(
        extracted_pairs,
        user_id=user_id,
        page_count_hint=page_count_hint or page_count,
        browser_used=browser_used,
    )


def build_import_message(result):
    return (
        f"{f'已通过 {BROWSER_LABELS.get(result['browser_used'], result['browser_used'])} 导入。' if result['browser_used'] else ''}"
        f"共抓取 {result['page_count']} 页，解析到 {result['parsed_count']} 条电影，"
        f"成功导入 {result['imported_count']} 条新记录。"
        f"{' 已达到 1000 条导入上限。' if result['capped'] else ''}"
    )


@app.route("/")
@login_required
def home():
    current_user = get_current_user()
    return render_template(
        "index.html",
        movies=list_movies(current_user["id"]),
        current_user=current_user,
        ai_available=is_deepseek_configured(),
        bookmarklet_token=create_bookmarklet_token(current_user["id"]),
        initial_message=request.args.get("import_message", ""),
        initial_message_type=request.args.get("import_type", "info"),
    )


@app.route("/login")
def login_page():
    if get_current_user():
        return redirect(url_for("home"))
    return render_template(
        "auth.html",
        mode="login",
        error=request.args.get("error", ""),
        success=request.args.get("success", ""),
        username=request.args.get("username", ""),
    )


@app.route("/register")
def register_page():
    if get_current_user():
        return redirect(url_for("home"))
    return render_template(
        "auth.html",
        mode="register",
        error=request.args.get("error", ""),
        success=request.args.get("success", ""),
        username=request.args.get("username", ""),
    )


@app.post("/login")
def login_submit():
    username = (request.form.get("username") or "").strip()
    password = (request.form.get("password") or "").strip()

    try:
        user = authenticate_user(username, password)
    except ValueError as error:
        return redirect(
            url_for("login_page", error=str(error), username=username)
        )

    session["user_id"] = user["id"]
    return redirect(url_for("home"))


@app.post("/register")
def register_submit():
    username = (request.form.get("username") or "").strip()
    password = (request.form.get("password") or "").strip()
    confirm_password = (request.form.get("confirm_password") or "").strip()

    if password != confirm_password:
        return redirect(
            url_for("register_page", error="两次输入的密码不一致。", username=username)
        )

    try:
        user = create_user(username, password)
    except ValueError as error:
        return redirect(
            url_for("register_page", error=str(error), username=username)
        )

    session["user_id"] = user["id"]
    return redirect(url_for("home"))


@app.post("/logout")
def logout():
    session.clear()
    return redirect(url_for("login_page", success="已退出登录。"))


@app.route("/api/movies")
@api_login_required
def movies_api(current_user):
    return jsonify({"movies": list_movies(current_user["id"])})


@app.post("/api/ai/chat")
@api_login_required
def ai_chat(current_user):
    payload = request.get_json(silent=True) or {}

    try:
        conversation_messages = normalize_ai_messages(payload.get("messages", []))
        message = chat_with_movie_ai(current_user["id"], conversation_messages)
    except AIConfigurationError as error:
        return jsonify({"error": str(error)}), 503
    except ValueError as error:
        return jsonify({"error": str(error)}), 400

    return jsonify({"message": message})


@app.post("/api/movies/save")
@api_login_required
def save_movies(current_user):
    payload = request.get_json(silent=True) or {}
    rows = payload.get("movies", [])

    try:
        replace_movies(rows, current_user["id"])
    except ValueError as error:
        return jsonify({"error": str(error)}), 400

    return jsonify(
        {
            "movies": list_movies(current_user["id"]),
            "message": "保存成功。",
        }
    )


@app.post("/api/import")
@api_login_required
def import_movies(current_user):
    payload = request.get_json(silent=True) or {}

    try:
        result = import_from_douban(
            url=payload.get("url", ""),
            html=payload.get("html", ""),
            cookie=payload.get("cookie", ""),
            prefer_browser=bool(payload.get("preferBrowser")),
            browser=(payload.get("browser") or "auto").strip().lower(),
            user_id=current_user["id"],
        )
    except (HTTPError, URLError) as error:
        return jsonify({"error": f"导入失败：{error}"}), 400
    except ValueError as error:
        return jsonify({"error": str(error)}), 400

    return jsonify(
        {
            "movies": list_movies(current_user["id"]),
            "message": build_import_message(result),
        }
    )


@app.post("/import/bookmarklet")
def import_movies_from_bookmarklet():
    token = (request.form.get("token") or "").strip()
    pairs_json = request.form.get("pairs_json", "")
    payload_html = request.form.get("html", "")
    page_count_raw = (request.form.get("page_count") or "").strip()
    source_url = (request.form.get("url") or "").strip()

    try:
        user_id = parse_bookmarklet_token(token)
        page_count_hint = int(page_count_raw) if page_count_raw.isdigit() else None
        if pairs_json.strip():
            parsed_pairs = json.loads(pairs_json)
            extracted_pairs = []

            for item in parsed_pairs:
                if not isinstance(item, dict):
                    continue
                extracted_pairs.append(
                    ((item.get("title") or "").strip(), (item.get("director") or "").strip())
                )

            result = persist_import_pairs(
                extracted_pairs,
                user_id=user_id,
                page_count_hint=page_count_hint,
            )
        else:
            result = import_from_douban(
                url=source_url,
                html=payload_html,
                user_id=user_id,
                page_count_hint=page_count_hint,
            )
        return redirect(
            url_for(
                "home",
                import_message=build_import_message(result),
                import_type="success",
            )
        )
    except (ValueError, json.JSONDecodeError) as error:
        return redirect(
            url_for(
                "home",
                import_message=str(error),
                import_type="error",
            )
        )


init_db()


if __name__ == "__main__":
    app.run(debug=True)
