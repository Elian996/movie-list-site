import os
import re
import ssl
import sqlite3
from datetime import datetime
from functools import wraps
from html import unescape
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin, urlparse
from urllib.request import Request, urlopen

from flask import (
    Flask,
    jsonify,
    redirect,
    render_template,
    request,
    session,
    url_for,
)
from werkzeug.security import check_password_hash, generate_password_hash

try:
    from bs4 import BeautifulSoup
except ImportError:  # pragma: no cover - optional dependency
    BeautifulSoup = None


BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATABASE_PATH = os.path.join(BASE_DIR, "movies.db")
MAX_IMPORT_RECORDS = 1000
USERNAME_PATTERN = re.compile(r"^[A-Za-z0-9]{4}$")
PASSWORD_PATTERN = re.compile(r"^[A-Za-z0-9]{8}$")
DOUBAN_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/122.0.0.0 Safari/537.36"
    )
}

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "dev-secret-change-me")


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

            title = strip_tags(title_match.group(1)).split("/")[0].strip()
            director = parse_director_from_text(
                strip_tags(intro_match.group(1)), title=title
            )
            if title and director:
                pairs.append((title, director))
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
            title = strip_tags(raw_title).split("/")[0].strip()
            director = parse_director_from_text(strip_tags(raw_intro), title=title)
            if title and director:
                pairs.append((title, director))

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
    duration_index = find_duration_index(parts)
    if duration_index is not None:
        directors = collect_directors_before_duration(parts, duration_index, title)
        if directors:
            return " / ".join(directors)

    if len(parts) >= 2:
        return parts[-1]
    if parts:
        return parts[0]
    return ""


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

    blocked_keywords = (
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
    if any(keyword in part for keyword in blocked_keywords):
        return False

    if re.search(r"\d{4}", part):
        return False

    if re.search(r"[()（）]", part):
        return False

    cleaned_title = (title or "").strip()
    if cleaned_title and part == cleaned_title:
        return False

    return bool(re.search(r"[\u4e00-\u9fffA-Za-z]", part))


def fetch_html(url, headers):
    request_object = Request(url, headers=headers)
    try:
        with urlopen(request_object, timeout=15) as response:
            return response.read().decode("utf-8", errors="ignore")
    except URLError as error:
        # Some local environments inject a custom certificate chain and break
        # Python's default HTTPS verification for otherwise valid pages.
        if isinstance(error.reason, ssl.SSLCertVerificationError):
            insecure_context = ssl._create_unverified_context()
            with urlopen(
                request_object, timeout=15, context=insecure_context
            ) as response:
                return response.read().decode("utf-8", errors="ignore")
        raise


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


def collect_paginated_pairs(start_url, headers):
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
        html = fetch_html(current_url, headers)
        page_count += 1

        page_pairs = extract_title_and_director_pairs(html)
        all_pairs.extend(page_pairs)

        if len(page_pairs) == 0:
            break

        current_url = find_next_page_url(html, current_url)

    return all_pairs[:MAX_IMPORT_RECORDS], page_count


def import_from_douban(url="", html="", cookie="", user_id=None):
    normalized_url = unescape((url or "").strip())
    payload_html = html.strip()
    page_count = 1

    if not payload_html:
        if not normalized_url:
            raise ValueError("请提供豆瓣页面 URL 或页面 HTML。")

        parsed = urlparse(normalized_url)
        if "douban.com" not in parsed.netloc:
            raise ValueError("目前只支持导入 douban.com 页面。")

        headers = dict(DOUBAN_HEADERS)
        if cookie.strip():
            headers["Cookie"] = cookie.strip()

        extracted_pairs, page_count = collect_paginated_pairs(normalized_url, headers)
    else:
        extracted_pairs = extract_title_and_director_pairs(payload_html)

    if not extracted_pairs:
        raise ValueError("没有从页面中识别出电影数据，请确认页面内容是否为豆瓣“看过”列表。")

    normalized_pairs = []
    seen_pairs = set()

    for title, director in extracted_pairs:
        pair_key = (title.strip(), director.strip())
        if pair_key[0] and pair_key[1] and pair_key not in seen_pairs:
            normalized_pairs.append(pair_key)
            seen_pairs.add(pair_key)

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
        "page_count": page_count,
        "capped": len(normalized_pairs) >= MAX_IMPORT_RECORDS,
    }


@app.route("/")
@login_required
def home():
    current_user = get_current_user()
    return render_template(
        "index.html",
        movies=list_movies(current_user["id"]),
        current_user=current_user,
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
            user_id=current_user["id"],
        )
    except (HTTPError, URLError) as error:
        return jsonify({"error": f"导入失败：{error}"}), 400
    except ValueError as error:
        return jsonify({"error": str(error)}), 400

    return jsonify(
        {
            "movies": list_movies(current_user["id"]),
            "message": (
                f"共抓取 {result['page_count']} 页，解析到 {result['parsed_count']} 条电影，"
                f"成功导入 {result['imported_count']} 条新记录。"
                f"{' 已达到 1000 条导入上限。' if result['capped'] else ''}"
            ),
        }
    )


init_db()


if __name__ == "__main__":
    app.run(debug=True)
