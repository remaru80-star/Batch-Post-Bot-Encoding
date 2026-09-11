# ==================== IMPORTS & CONFIG ====================
import asyncio
import sys

if sys.version_info >= (3, 10):
    try:
        asyncio.get_running_loop()
    except RuntimeError:
        asyncio.set_event_loop(asyncio.new_event_loop())

import os
import re
import json
import time
import glob
import uuid
import logging
import subprocess
import shutil
import inspect
import warnings
from urllib.parse import unquote_plus
from datetime import datetime, timedelta
from typing import Dict, List, Tuple, Optional, Any
from dotenv import load_dotenv
from PIL import Image
import motor.motor_asyncio
from bson import ObjectId
from bson.errors import InvalidId
from pyrogram import Client, filters, __version__, idle, StopPropagation
from pyrogram.types import Message, InlineKeyboardButton, InlineKeyboardMarkup

try:
    import tgcrypto
    print("✅ TgCrypto loaded — accelerated encryption enabled")
except ImportError:
    tgcrypto = None
    print("⚠️ TgCrypto NOT installed — falling back to slower pure-Python encryption. Run: pip install tgcrypto")

# Optional torrent backend #1 — python-libtorrent. Preferred when available: it can fetch a
# torrent's metadata WITHOUT downloading its content (so Season/Episode can be validated
# before wasting bandwidth), download only the one video file we actually want, and stop
# seeding the moment it's done. Falls back to aria2c (see find_aria2()) when missing.
try:
    import libtorrent as lt
except ImportError:
    lt = None

load_dotenv()


def _parse_ids(raw: str) -> List[int]:
    """Parses a comma/space separated list of Telegram user IDs.

    Non-numeric junk and 0 are dropped rather than accepted. That 0 matters: the old default
    here was the string "0", so an unset ADMIN produced [0] — a truthy list containing a user
    ID no real account has. staff_filter then matched nobody while `if not Config.STAFF`
    stayed False, so the bot started up clean, printed no warning, and silently ignored every
    message. Anything that isn't a usable ID has to disappear completely, so STAFF really is
    empty when nothing was configured.
    """
    out: List[int] = []
    for part in re.split(r"[,\s]+", raw or ""):
        part = part.strip()
        if not part:
            continue
        try:
            val = int(part)
        except ValueError:
            print(f"⚠️ Ignoring invalid ID in ADMIN/MODERATOR: {part!r} — must be a numeric Telegram user ID.")
            continue
        if val and val not in out:
            out.append(val)
    return out


class Config:
    API_ID = int(os.getenv("API_ID", "0"))
    API_HASH = os.getenv("API_HASH", "")
    BOT_TOKEN = os.getenv("BOT_TOKEN", "")
    ADMIN = _parse_ids(os.getenv("ADMIN", ""))
    MODERATOR = _parse_ids(os.getenv("MODERATOR", ""))
    # STAFF = anyone allowed to talk to the bot at all. Everyone else gets NO response
    # (see staff_filter below). ADMIN additionally unlocks bot-wide settings (/bot_settings).
    STAFF = sorted(set(ADMIN) | set(MODERATOR))
    DB_URL = os.getenv("DB_URL", "")
    DB_NAME = os.getenv("DB_NAME", "BatchAutoRenameBot")
    BOT_UPTIME = time.time()
    MAX_FILE_SIZE = 2 * 1024 * 1024 * 1024
    MAX_COVER_SIZE = 10 * 1024 * 1024  # Telegram's photo-style upload cap for `cover`
    # ---- Torrent limits ----
    # Hard ceiling on what a single torrent is allowed to be, so one bad magnet can't fill
    # the server's disk. Checked as soon as the torrent's metadata is known (before any
    # content is downloaded), then again against actual free disk space.
    MAX_TORRENT_SIZE = int(os.getenv("MAX_TORRENT_SIZE_GB", "20")) * 1024 * 1024 * 1024
    # The encode chain holds at most 2 files at once (previous rung + the rung being written),
    # so require the torrent's size times this factor in free space before starting.
    DISK_HEADROOM_FACTOR = float(os.getenv("DISK_HEADROOM_FACTOR", "2.5"))
    TORRENT_METADATA_TIMEOUT = int(os.getenv("TORRENT_METADATA_TIMEOUT", "300"))  # seconds
    TORRENT_STALL_TIMEOUT = int(os.getenv("TORRENT_STALL_TIMEOUT", "1800"))       # 0 bytes for this long -> abort
    ENCODE_TIMEOUT = int(os.getenv("ENCODE_TIMEOUT", "43200"))                    # 12h per rung


os.makedirs("downloads", exist_ok=True)
os.makedirs("temp", exist_ok=True)
os.makedirs("torrents", exist_ok=True)

app = Client(
    "batch_autorename_bot",
    api_id=Config.API_ID,
    api_hash=Config.API_HASH,
    bot_token=Config.BOT_TOKEN,
    workers=10,
    sleep_threshold=10,
    # NOT in_memory: private channels can only be reached by numeric chat_id once Pyrogram has
    # resolved their "peer" at least once. in_memory=True throws that cache away on every
    # restart, which causes CHANNEL_INVALID for any private channel the bot hasn't freshly
    # seen a message from since the last restart. A persistent session file (batch_autorename_bot.session)
    # keeps that cache across restarts instead.
)

# Feature-detect whether the installed Pyrogram build supports the `cover` kwarg on
# send_video (Bot API 8.3+ — Telegram's native full-quality video poster). Stock Pyrogram
# does not have this yet — forks like Pyrofork do. Checked once at import time instead of
# guessing, so the bot degrades gracefully (falls back to ffmpeg-embedded cover only,
# no crash) if it isn't available.
SEND_VIDEO_SUPPORTS_COVER = "cover" in inspect.signature(app.send_video).parameters
if not SEND_VIDEO_SUPPORTS_COVER:
    print(
        "⚠️ Installed Pyrogram build has no `cover` parameter on send_video(). Cover images "
        "will still be embedded into the file itself via ffmpeg, but won't show as Telegram's "
        "native high-quality video poster until you install a fork that supports it "
        "(e.g. pip install pyrofork)."
    )


# ==================== ACCESS CONTROL ====================
# Nobody outside Config.STAFF (ADMIN + MODERATOR) gets ANY reply from the bot — private
# commands, file uploads, and callback buttons are all gated. If Config.STAFF is empty
# (nothing set in .env), the bot will not respond to anyone — set ADMIN in .env first.
staff_filter = filters.user(Config.STAFF) if Config.STAFF else filters.create(lambda _, __, ___: False)


def is_staff(user_id: Optional[int]) -> bool:
    return bool(user_id) and user_id in Config.STAFF


def is_admin(user_id: Optional[int]) -> bool:
    return bool(user_id) and user_id in Config.ADMIN


# ==================== IN-MEMORY STATE ====================
conversation_state: Dict[int, dict] = {}
sequence_sessions: Dict[int, dict] = {}
auto_post_sessions: Dict[int, dict] = {}   # uid -> {"batch_id": str}  — see /auto_post
DEFAULT_SEQ_MODE = 1

# Single global FIFO queue. Jobs are processed one at a time, in order,
# by queue_worker(). A "job" is either one file (normal send), a whole
# sorted sequence (list of files added together via /esequence), or a
# torrent job (download -> 1080p/720p/480p encode ladder -> post).
file_queue: "asyncio.Queue" = asyncio.Queue()

# Every torrent job gets an entry here from the moment it's queued until it finishes, so
# /cancel_job (and the 🛑 button on the live progress message) can abort it mid-download or
# mid-encode. The cancel Event is polled by the torrent download loop and kills the running
# ffmpeg process, which is why a cancel takes effect within a second or two instead of
# waiting for a multi-hour encode to finish.
active_jobs: Dict[str, dict] = {}   # job_id -> {"cancel": asyncio.Event, "user": int, "desc": str, "running": bool}


def new_job_id() -> str:
    return uuid.uuid4().hex[:10]


def register_job(job_id: str, user_id: int, desc: str) -> asyncio.Event:
    ev = asyncio.Event()
    active_jobs[job_id] = {"cancel": ev, "user": user_id, "desc": desc, "running": False}
    return ev


def cancel_jobs_for_user(user_id: int) -> int:
    n = 0
    for info in active_jobs.values():
        if info["user"] == user_id and not info["cancel"].is_set():
            info["cancel"].set()
            n += 1
    return n


# ==================== QUALITY / FILENAME PARSING ====================
# NOTE ON THIS SECTION: the season/episode/quality detection below is ported from a
# sibling bot whose pattern list turned out to catch far more real-world filename
# shapes than a "normalize separators then regex" approach does. The key difference:
# these patterns run against the RAW filename, never a normalized copy — because
# separator characters ('-', '.', '_', brackets) are often part of what the pattern
# is matching (e.g. "[04 - Title]" needs that literal " - " to distinguish the episode
# number from the title that follows it). normalize_for_match() below is kept, but is
# used ONLY for anime-name batch matching, never for season/episode/quality extraction.

QUALITY_ORDER = ["144p", "240p", "360p", "480p", "576p", "720p", "1080p", "2K", "4K"]
QUALITY_INDEX = {q: i for i, q in enumerate(QUALITY_ORDER)}

# Pixel height each quality label means when ENCODING to it (see the encode ladder). Only
# labels listed here can be used as an encode rung — everything else is a detection-only
# label.
QUALITY_HEIGHT = {
    "144p": 144, "240p": 240, "360p": 360, "480p": 480,
    "576p": 576, "720p": 720, "1080p": 1080, "2K": 1440, "4K": 2160,
}

# Ordered, most-specific-first. First pattern that matches a given field wins;
# later patterns are only tried if that field is still missing.
SEASON_EPISODE_PATTERNS = [
    (re.compile(r'S(\d+)\s*-\s*(\d+)', re.IGNORECASE), ('season', 'episode')),               # S1 - 01
    (re.compile(r'\[(\d+)\s*-', re.IGNORECASE), (None, 'episode')),                           # [04 - Title]
    (re.compile(r'\[E(\d+)\s*-', re.IGNORECASE), (None, 'episode')),                          # [E04 - Title]
    (re.compile(r'\[S(\d+)[\s-]+(\d+)\]', re.IGNORECASE), ('season', 'episode')),             # [S02-12] / [S02 12]
    (re.compile(r'S(\d+)(?:E|EP)(\d+)', re.IGNORECASE), ('season', 'episode')),               # S01E01 / S01EP01
    (re.compile(r'S(\d+)[\s-]*(?:E|EP)(\d+)', re.IGNORECASE), ('season', 'episode')),         # S01 - E01
    (re.compile(r'Season\s*(\d+)\s*Episode\s*(\d+)', re.IGNORECASE), ('season', 'episode')),
    (re.compile(r'Season\s*(\d+)', re.IGNORECASE), ('season', None)),                         # Season 2 (standalone)
    (re.compile(r'\[S(\d+)\]\s*\[?E(\d+)\]?', re.IGNORECASE), ('season', 'episode')),
    (re.compile(r'\[S(\d+)\]', re.IGNORECASE), ('season', None)),
    (re.compile(r'\bS(\d+)\b', re.IGNORECASE), ('season', None)),
    (re.compile(r'(?:^|[\s\[\-_])(?:E|EP)(\d+)(?:$|[\s\]\-_])', re.IGNORECASE), (None, 'episode')),
    (re.compile(r'Episode\s*(\d+)', re.IGNORECASE), (None, 'episode')),
]

QUALITY_PATTERNS = [
    (re.compile(r'\b(4k|2160p)\b', re.IGNORECASE), lambda m: "4K"),
    (re.compile(r'\b(2k|1440p)\b', re.IGNORECASE), lambda m: "2K"),
    (re.compile(r'\b(1080p)\b', re.IGNORECASE), lambda m: "1080p"),
    (re.compile(r'\b(720p)\b', re.IGNORECASE), lambda m: "720p"),
    (re.compile(r'\b(576p)\b', re.IGNORECASE), lambda m: "576p"),
    (re.compile(r'\b(480p)\b', re.IGNORECASE), lambda m: "480p"),
    (re.compile(r'\b(HDRip|HDTV)\b', re.IGNORECASE), lambda m: "720p"),  # no exact resolution — bucket as 720p
    (re.compile(r'\[(4k|2160p|2k|1440p|1080p|720p|576p|480p)\]', re.IGNORECASE),
     lambda m: {"4k": "4K", "2160p": "4K", "2k": "2K", "1440p": "2K"}.get(m.group(1).lower(), m.group(1))),
]

# ---- FALLBACK PATTERNS ----------------------------------------------------------------
# The primary lists above rely on \b (regex word boundary). Underscore "_" counts as a
# "word" character in regex, so \b finds NO boundary between "S01" and "_07", or around
# "_480p_" — meaning a filename like:
#   S01_07_Smoking_Behind_the_Supermarket_With_You_480p_Dual_@GenDubs.mkv
# fails Season, Episode AND Quality detection under the primary patterns above, even
# though a human reads it as S01 / E07 / 480p instantly.
#
# These fallback patterns are NOT merged into the primary lists and do not change any
# existing behavior. They only run afterward, and only for whichever field(s) the
# primary pass still couldn't find. They use a manual alnum lookaround instead of \b,
# so "_", "-", spaces, and string edges all count as valid separators.
FALLBACK_SEASON_EPISODE_PATTERNS = [
    # S01_07 / S01-07 / S01 07 — season + episode joined with no E/EP letter at all.
    (re.compile(r'(?<![A-Za-z0-9])S(\d{1,2})[_\-\s](\d{1,3})(?![A-Za-z0-9])', re.IGNORECASE), ('season', 'episode')),
    # Standalone "S01" as its own underscore/dash/space-delimited token.
    (re.compile(r'(?<![A-Za-z0-9])S(\d+)(?![A-Za-z0-9])', re.IGNORECASE), ('season', None)),
    # Standalone "E07" / "EP07" as its own underscore/dash/space-delimited token.
    (re.compile(r'(?<![A-Za-z0-9])(?:E|EP)(\d+)(?![A-Za-z0-9])', re.IGNORECASE), (None, 'episode')),
]

FALLBACK_QUALITY_PATTERNS = [
    (re.compile(r'(?<![A-Za-z0-9])(4k|2160p)(?![A-Za-z0-9])', re.IGNORECASE), lambda m: "4K"),
    (re.compile(r'(?<![A-Za-z0-9])(2k|1440p)(?![A-Za-z0-9])', re.IGNORECASE), lambda m: "2K"),
    (re.compile(r'(?<![A-Za-z0-9])(1080p)(?![A-Za-z0-9])', re.IGNORECASE), lambda m: "1080p"),
    (re.compile(r'(?<![A-Za-z0-9])(720p)(?![A-Za-z0-9])', re.IGNORECASE), lambda m: "720p"),
    (re.compile(r'(?<![A-Za-z0-9])(576p)(?![A-Za-z0-9])', re.IGNORECASE), lambda m: "576p"),
    (re.compile(r'(?<![A-Za-z0-9])(480p)(?![A-Za-z0-9])', re.IGNORECASE), lambda m: "480p"),
    (re.compile(r'(?<![A-Za-z0-9])(HDRip|HDTV)(?![A-Za-z0-9])', re.IGNORECASE), lambda m: "720p"),
]
# -----------------------------------------------------------------------------------------


def quality_label(q_int: int) -> str:
    if 0 <= q_int < len(QUALITY_ORDER):
        return QUALITY_ORDER[q_int]
    return "HD"


def normalize_for_match(s: str) -> str:
    """Normalizes separators so 'Black Torch' matches 'Black.Torch' / 'Black_Torch' / 'Black-Torch'.
    Used ONLY for anime-name batch matching — never for season/episode/quality extraction,
    since those regexes rely on the raw separator characters to disambiguate."""
    s = s.lower()
    s = re.sub(r'[._\-]+', ' ', s)
    s = re.sub(r'\s+', ' ', s)
    return s.strip()


def as_channel_ref(value: Any) -> Optional[dict]:
    """Batches created with an older version of this bot stored Thumbnail/Cover Image as a
    plain file_id string. The current version stores them as {"chat_id":.., "message_id":..}
    pointing into the Thumb/Cover Channel instead. This guards every read site against that
    old format so it's skipped cleanly (instead of crashing with 'str' object has no attribute
    'get') — the batch just needs its Thumbnail/Cover Image re-set once via the bot's menu."""
    if isinstance(value, dict) and value.get("chat_id") and value.get("message_id"):
        return value
    return None


def get_main_channels(batch: dict) -> List[dict]:
    """Returns this batch's Main Channels as a list of {"id":.., "title":..} dicts.

    Batches created before multi-Main-Channel support stored a single Main Channel under
    the old "main_channel" key. This transparently migrates that old shape into the new
    "main_channels" list ON READ ONLY — no DB migration script needed, and old batches
    keep working exactly as before (just as a one-item list now)."""
    channels = batch.get("main_channels")
    if channels:
        return channels
    old = batch.get("main_channel")
    if old and old.get("id"):
        return [old]
    return []



def _extract_season_episode_str(text: str) -> Tuple[Optional[str], Optional[str]]:
    """Runs the ordered PRIMARY pattern list against the raw filename first. Returns
    (season, episode) as strings (or None), stopping early once both are found.

    FALLBACK: if, after the primary pass, season and/or episode is STILL missing, a
    second pass runs FALLBACK_SEASON_EPISODE_PATTERNS (underscore-aware) — but only to
    fill in whatever field is still empty. A field the primary patterns already found is
    never touched or overwritten by the fallback pass. This means existing filenames that
    already worked behave identically; only filenames that previously failed get a second
    chance."""
    if not text:
        return None, None
    season_found = None
    episode_found = None

    # ---- PRIMARY PASS ----
    for pattern, (season_group, episode_group) in SEASON_EPISODE_PATTERNS:
        if season_found and episode_found:
            break
        match = pattern.search(text)
        if not match:
            continue
        if season_group and not season_found:
            try:
                season_found = match.group(1)
            except Exception:
                pass
        if episode_group and not episode_found:
            try:
                ep_idx = 2 if season_group else 1
                episode_found = match.group(ep_idx)
            except Exception:
                try:
                    episode_found = match.group(1)
                except Exception:
                    pass

    # ---- FALLBACK PASS — only runs if something is still missing ----
    if not season_found or not episode_found:
        for pattern, (season_group, episode_group) in FALLBACK_SEASON_EPISODE_PATTERNS:
            if season_found and episode_found:
                break
            match = pattern.search(text)
            if not match:
                continue
            if season_group and not season_found:
                try:
                    season_found = match.group(1)
                except Exception:
                    pass
            if episode_group and not episode_found:
                try:
                    ep_idx = 2 if season_group else 1
                    episode_found = match.group(ep_idx)
                except Exception:
                    try:
                        episode_found = match.group(1)
                    except Exception:
                        pass

    return season_found, episode_found



def _extract_quality_str(text: str) -> Optional[str]:
    if not text:
        return None
    # ---- PRIMARY PASS ----
    for pattern, extractor in QUALITY_PATTERNS:
        match = pattern.search(text)
        if match:
            return extractor(match)
    # ---- FALLBACK PASS — only runs if the primary pass found nothing ----
    for pattern, extractor in FALLBACK_QUALITY_PATTERNS:
        match = pattern.search(text)
        if match:
            return extractor(match)
    return None


def extract_file_info(file_name: str) -> Tuple[int, int, int]:
    """
    Returns (season, episode, quality_index).
    season == 0   -> season not found
    episode == 0  -> episode not found
    quality == -1 -> quality not found

    Matches against the RAW filename (not normalized) — see the note at the top of
    this section for why. Primary patterns are tried first; underscore-aware fallback
    patterns only run for whatever field the primary pass couldn't find.
    """
    season_s, episode_s = _extract_season_episode_str(file_name)

    # [SO] tag with no season detected -> default to season 1.
    if not season_s and re.search(r'\[SO\]', file_name, re.IGNORECASE):
        season_s = "1"

    quality_s = _extract_quality_str(file_name)

    season = int(season_s) if season_s and season_s.isdigit() else 0
    episode = int(episode_s) if episode_s and episode_s.isdigit() else 0
    quality = QUALITY_INDEX.get(quality_s, -1) if quality_s else -1

    return season, episode, quality


def extract_season_episode_from_sources(*sources: Optional[str]) -> Tuple[int, int]:
    """Season/Episode detection for the TORRENT pipeline, which has several candidate
    strings to work from instead of one filename: the text the user typed alongside the
    magnet, the torrent's own name, and the video file's name inside the torrent.

    Each source is tried in the order given, and the FIRST source that yields a value
    wins for that field — so a user can override bad torrent naming just by typing
    `S02E07` in the same message as the magnet link. Quality is deliberately NOT detected
    here: for torrents the output quality is dictated by the encode ladder (1080p → 720p →
    480p), not by whatever the source happened to be labelled."""
    season = 0
    episode = 0
    for src in sources:
        if not src:
            continue
        if season and episode:
            break
        s_str, e_str = _extract_season_episode_str(src)
        if not season and s_str and s_str.isdigit():
            season = int(s_str)
        if not episode and e_str and e_str.isdigit():
            episode = int(e_str)
    if not season:
        for src in sources:
            if src and re.search(r'\[SO\]', src, re.IGNORECASE):
                season = 1
                break
    return season, episode



def find_missing_field(season: int, episode: int, quality: int) -> Optional[str]:
    """Checks Season -> Episode -> Quality in that order and returns the name of the
    FIRST one that's missing, so the caller can stop immediately and report just that
    one field instead of piling up every problem at once."""
    if season == 0:
        return "Season"
    if episode == 0:
        return "Episode"
    if quality == -1:
        return "Quality"
    return None


def missing_field_message(file_name: str, missing_field: str, season: int, episode: int,
                           quality: int, batch_name: Optional[str] = None,
                           extra_context: str = "") -> str:
    """Builds the standard 'stopped here' notice shown whenever a required field
    can't be detected from a filename."""
    lines = [
        f"🛑 **{missing_field} not found** — stopped here.",
        "",
        f"`{file_name[:80]}`",
    ]
    if batch_name:
        lines.append(f"Identified batch: `{batch_name}`")
    lines.append("")
    lines.append(
        f"I couldn't detect the {missing_field.lower()} from this filename, so "
        f"{extra_context or 'processing did not continue'}. Rename the file so it includes a "
        f"detectable {missing_field.lower()} and send it again."
    )
    lines.append("")
    lines.append("_Detected so far:_")
    lines.append(f"• Season: {season if season else '❌ not found'}")
    lines.append(f"• Episode: {episode if episode else '❌ not found'}")
    lines.append(f"• Quality: {quality_label(quality) if quality >= 0 else '❌ not found'}")
    return "\n".join(lines)


def humanbytes(size):
    if not size:
        return "0 B"
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if size < 1024.0:
            return f"{size:.2f} {unit}"
        size /= 1024.0
    return f"{size:.2f} PB"


def TimeFormatter(milliseconds: int) -> str:
    seconds, milliseconds = divmod(int(milliseconds), 1000)
    minutes, seconds = divmod(seconds, 60)
    hours, minutes = divmod(minutes, 60)
    days, hours = divmod(hours, 24)
    tmp = ((str(days) + "d, ") if days else "") + \
          ((str(hours) + "h, ") if hours else "") + \
          ((str(minutes) + "m, ") if minutes else "") + \
          ((str(seconds) + "s, ") if seconds else "")
    return tmp[:-2] or "0s"


def progress_bar(pct: float, width: int = 20) -> str:
    pct = max(0.0, min(100.0, pct))
    filled = int(pct / 100 * width)
    return "█" * filled + "░" * (width - filled)


def get_msg_fname(msg: Message) -> str:
    if msg.document:
        return msg.document.file_name or "file"
    if msg.video:
        return msg.video.file_name or "video.mp4"
    if msg.audio:
        return msg.audio.file_name or "audio.mp3"
    return "file"



# ==================== ENCODE SETTINGS (bot-wide, stored in the settings doc) ====================
# The torrent pipeline's output ladder and encoder knobs. Kept bot-wide (not per batch) because
# they describe *how* this server encodes, not what a particular anime looks like. Editable
# from /encode_settings.
DEFAULT_ENCODE = {
    # Rungs are always processed high -> low, and each rung is encoded FROM the previous
    # rung's output (1080p from the torrent, 720p from the 1080p, 480p from the 720p), which
    # is dramatically faster than re-encoding the huge source three times.
    "ladder": ["1080p", "720p", "480p"],
    "codec": "x264",          # x264 | x265 | hw   (hw = the auto-detected hardware encoder)
    "crf": 23,                # quality floor: lower = bigger/better. 20-26 is the sane range.
    "preset": "veryfast",     # measured as the best speed/quality point once -maxrate caps the
                              # bitrate — slower presets cost 1.5-2.7x the time for no measurable
                              # SSIM/PSNR gain at a fixed rate. Raise it if you have spare cores.
    "tune": "animation",      # animation | film | grain | none — animation is a big win on anime.
    "bit_depth": 8,           # 8 is universally playable; 10 is ~8% smaller but many phones can't decode it.
    "audio": "auto",          # auto = copy unless it would eat the size budget, then re-encode.
    "container": "mkv",       # mkv keeps multi-audio + soft subs + font attachments; mp4 is more compatible.
    "skip_upscale": True,     # don't encode a 1080p rung out of a 720p source.
    "keep_subs": True,        # copy subtitle streams into the output.
    "scaler": "lanczos",      # downscale filter: lanczos (sharpest) | bicubic (cheaper) | spline
    # Hard size ceilings per rung, in MB. Enforced with capped CRF (-maxrate/-bufsize derived
    # from the file's duration) plus one automatic higher-CRF retry if a rung still overshoots.
    # 0 disables the cap for that rung and lets CRF alone decide.
    "targets": {"1080p": 250, "720p": 150, "480p": 90},
}
ENCODE_PRESETS = ["ultrafast", "superfast", "veryfast", "faster", "fast", "medium", "slow", "slower"]
ENCODE_TUNES = ["animation", "film", "grain", "none"]
ENCODE_CODECS = ["x264", "x265", "hw"]
# Lower resolutions tolerate a slightly higher CRF for the same perceived quality, because the
# downscale has already removed the fine detail that a low CRF would be protecting.
RUNG_CRF_OFFSET = {"1080p": 0, "720p": 1, "480p": 2, "360p": 3, "2160p": -1, "1440p": 0}
DEFAULT_TARGET_MB = {"2160p": 900, "1440p": 500, "1080p": 250, "720p": 150, "480p": 90, "360p": 60}


def get_encode_settings(settings: dict) -> dict:
    """Merges the stored encode settings over the defaults, so a settings doc written by an
    older version of the bot (missing newer keys) still produces a complete config."""
    enc = dict(DEFAULT_ENCODE)
    enc["targets"] = dict(DEFAULT_ENCODE["targets"])
    stored = settings.get("encode") or {}
    for k, v in stored.items():
        if k in enc and v is not None:
            enc[k] = v
    ladder = [q for q in enc.get("ladder", []) if q in QUALITY_HEIGHT]
    # Always high -> low; the chain depends on it.
    ladder.sort(key=lambda q: QUALITY_HEIGHT[q], reverse=True)
    enc["ladder"] = ladder or list(DEFAULT_ENCODE["ladder"])
    try:
        enc["crf"] = max(14, min(35, int(enc["crf"])))
    except Exception:
        enc["crf"] = DEFAULT_ENCODE["crf"]
    if enc.get("preset") not in ENCODE_PRESETS:
        enc["preset"] = DEFAULT_ENCODE["preset"]
    if enc.get("tune") not in ENCODE_TUNES:
        enc["tune"] = DEFAULT_ENCODE["tune"]
    if enc.get("codec") not in ENCODE_CODECS:
        enc["codec"] = DEFAULT_ENCODE["codec"]
    if enc.get("audio") not in ("auto", "copy", "aac"):
        enc["audio"] = DEFAULT_ENCODE["audio"]
    if enc.get("container") not in ("mkv", "mp4"):
        enc["container"] = "mkv"
    if enc.get("scaler") not in ("lanczos", "bicubic", "spline"):
        enc["scaler"] = DEFAULT_ENCODE["scaler"]
    try:
        enc["bit_depth"] = 10 if int(enc["bit_depth"]) == 10 else 8
    except Exception:
        enc["bit_depth"] = 8
    # Normalise the per-rung size ceilings, filling in a sane default for any rung the stored
    # doc doesn't mention (e.g. a rung added to the ladder after the targets were last saved).
    targets = {}
    stored_targets = enc.get("targets") or {}
    for q in enc["ladder"]:
        raw = stored_targets.get(q, DEFAULT_TARGET_MB.get(q, 0))
        try:
            targets[q] = max(0, int(raw))
        except Exception:
            targets[q] = DEFAULT_TARGET_MB.get(q, 0)
    enc["targets"] = targets
    return enc


def resolve_codec(enc: dict) -> Tuple[str, str]:
    """Turns the `codec` setting into (ffmpeg encoder name, human label), falling back when the
    requested one isn't usable on this machine. `hw` only resolves to a hardware encoder that
    passed the startup smoke test, so picking it on a box with no GPU degrades to x264 instead
    of failing every single encode."""
    probe_encoder_caps()
    want = enc.get("codec", "x264")
    if want == "hw":
        hw = ENCODER_CAPS.get("hw_hevc") if enc.get("container") == "mkv" else None
        hw = ENCODER_CAPS.get("hw") or hw
        if hw:
            return hw, f"hardware ({hw})"
        return "libx264", "x264 (no working hardware encoder found)"
    if want == "x265":
        if ENCODER_CAPS.get("x265"):
            return "libx265", "x265 / HEVC"
        return "libx264", "x264 (libx265 not in this ffmpeg build)"
    return "libx264", "x264"





# ==================== DATABASE ====================
class Database:
    def __init__(self):
        self.client = motor.motor_asyncio.AsyncIOMotorClient(Config.DB_URL)
        self.db = self.client[Config.DB_NAME]
        self.batches = self.db.batches
        self.users = self.db.users
        self.channels = self.db.channels
        self.settings = self.db.settings  # single doc {_id:"global", backup_channel:.., thumb_channel:.., encode:{..}}

    async def init_db(self):
        pass

    # ---------- Users ----------
    async def add_user(self, user_id: int):
        await self.users.update_one(
            {"_id": int(user_id)},
            {"$setOnInsert": {"_id": int(user_id), "sequence_mode": DEFAULT_SEQ_MODE,
                               "join_date": datetime.now().isoformat()}},
            upsert=True,
        )

    async def get_sequence_mode(self, user_id: int) -> int:
        doc = await self.users.find_one({"_id": int(user_id)})
        return doc.get("sequence_mode", DEFAULT_SEQ_MODE) if doc else DEFAULT_SEQ_MODE

    async def set_sequence_mode(self, user_id: int, mode: int):
        await self.users.update_one({"_id": int(user_id)}, {"$set": {"sequence_mode": mode}}, upsert=True)

    # ---------- Channel Registry ----------
    async def register_channel(self, chat_id: int, title: str):
        await self.channels.update_one(
            {"_id": int(chat_id)},
            {"$set": {"title": title, "registered_at": datetime.now().isoformat()}},
            upsert=True,
        )

    async def unregister_channel(self, chat_id: int):
        await self.channels.delete_one({"_id": int(chat_id)})

    async def list_channels(self) -> List[dict]:
        return await self.channels.find({}).to_list(length=200)

    async def get_channel(self, chat_id: int) -> Optional[dict]:
        return await self.channels.find_one({"_id": int(chat_id)})

    async def get_channel_invite_link(self, chat_id: int) -> Optional[str]:
        """Cached private, non-expiring invite link for a registered channel (see
        get_channel_join_link() below for why this is cached instead of regenerated
        on every post)."""
        doc = await self.get_channel(chat_id)
        return doc.get("invite_link") if doc else None

    async def set_channel_invite_link(self, chat_id: int, link: str):
        await self.channels.update_one({"_id": int(chat_id)}, {"$set": {"invite_link": link}}, upsert=True)


    async def remove_channel_references(self, chat_id: int):
        """When a channel is deleted from the registry (/delete_channel), scrub it from
        anything that might still point at it — every batch's Sub Channel / Main Channel(s),
        and the bot-wide Backup Channel / Thumb-Cover Channel — so nothing silently keeps
        trying to post to or fetch images from a channel that's no longer registered."""
        cid = int(chat_id)
        await self.batches.update_many({"sub_channel.id": cid}, {"$set": {"sub_channel": None}})
        # Old single-value Main Channel field (pre multi-channel support).
        await self.batches.update_many({"main_channel.id": cid}, {"$set": {"main_channel": None}})
        # New multi-value Main Channels list — pull just the matching entry, keep the rest.
        await self.batches.update_many({}, {"$pull": {"main_channels": {"id": cid}}})
        settings = await self.get_settings()
        backup_ch = settings.get("backup_channel")
        if backup_ch and backup_ch.get("id") == cid:
            await self.set_setting("backup_channel", None)
        thumb_ch = settings.get("thumb_channel")
        if thumb_ch and thumb_ch.get("id") == cid:
            await self.set_setting("thumb_channel", None)

    # ---------- Bot-wide Settings (Backup / Thumb Channel / Encode) ----------
    async def get_settings(self) -> dict:
        doc = await self.settings.find_one({"_id": "global"})
        return doc or {}

    async def set_setting(self, field: str, value: Any):
        await self.settings.update_one({"_id": "global"}, {"$set": {field: value}}, upsert=True)

    async def get_encode(self) -> dict:
        return get_encode_settings(await self.get_settings())

    async def set_encode_field(self, field: str, value: Any):
        await self.set_setting(f"encode.{field}", value)

    # ---------- Batches ----------
    def _default_batch(self, name: str) -> dict:
        return {
            "name": name,
            "thumbnail": None,      # {"chat_id": int, "message_id": int} — lives in the Thumb/Cover Channel
            "cover_image": None,    # {"chat_id": int, "message_id": int} — lives in the Thumb/Cover Channel
            "metadata": {
                "enabled": True,
                "title": "Encoded by @AnimeMultiDub",
                "author": "@AnimeMultiDub",
                "artist": "@AnimeMultiDub",
                "audio": "By @AnimeMultiDub",
                "subtitle": "By @AnimeMultiDub",
                "video": "Encoded By @AnimeMultiDub",
            },
            "autorename_format": None,
            "autocaption_format": None,
            "mediatype": "document",
            "anime_names": [],
            "sub_channel": None,
            "main_channels": [],   # list of {"id": int, "title": str} — a batch can have 1+ Main Channels
            "top_post_format": None,
            "bottom_post": None,
            "created_at": datetime.now().isoformat(),
        }


    async def create_batch(self, name: str) -> str:
        doc = self._default_batch(name)
        result = await self.batches.insert_one(doc)
        return str(result.inserted_id)

    async def get_batch(self, batch_id: str) -> Optional[dict]:
        try:
            oid = ObjectId(batch_id)
        except (InvalidId, TypeError):
            return None
        return await self.batches.find_one({"_id": oid})

    async def list_batches(self) -> List[dict]:
        return await self.batches.find({}).to_list(length=200)

    async def delete_batch(self, batch_id: str):
        try:
            oid = ObjectId(batch_id)
        except (InvalidId, TypeError):
            return
        await self.batches.delete_one({"_id": oid})

    async def update_batch_field(self, batch_id: str, field: str, value: Any):
        try:
            oid = ObjectId(batch_id)
        except (InvalidId, TypeError):
            return
        await self.batches.update_one({"_id": oid}, {"$set": {field: value}})

    async def name_exists(self, name: str) -> bool:
        doc = await self.batches.find_one({"name": {"$regex": f"^{re.escape(name)}$", "$options": "i"}})
        return bool(doc)

    async def find_batch_for_filename(self, file_name: str) -> Optional[dict]:
        """Matches a file to a batch by checking whether any of the batch's Anime Names
        appears inside the filename (normalized, so separators don't matter). Longest
        matching name wins when multiple batches could match."""
        batches = await self.list_batches()
        fname_norm = normalize_for_match(file_name)
        best = None
        best_len = -1
        for b in batches:
            for name in b.get("anime_names", []):
                name_norm = normalize_for_match(name)
                if name_norm and name_norm in fname_norm and len(name_norm) > best_len:
                    best = b
                    best_len = len(name_norm)
        return best


db = Database()



# ==================== FORMAT HELPERS ====================

# Telegram rejects any messages.SendMessage whose text is longer than 4096 characters with
# [400 MESSAGE_TOO_LONG]. That error is raised inside the handler, so from the user's side the
# bot looks completely dead — it connects fine, the handler fires, and then nothing arrives in
# the chat. The long informational replies (/start, /help) sit right at that boundary, so they
# go through reply_long() instead of reply_text(): it splits on paragraph/line boundaries so a
# future edit to the help text can never silently break the command again.
TG_TEXT_LIMIT = 4096
_SPLIT_MARGIN = 96  # leaves room for the "(1/2)" style continuation hint


def split_for_telegram(text: str, limit: int = TG_TEXT_LIMIT - _SPLIT_MARGIN) -> List[str]:
    """Breaks text into <=limit-character chunks, preferring blank-line boundaries, then single
    newlines, then a hard cut. Paragraph-aware so markdown (** pairs, bullet blocks) isn't split
    down the middle of a line."""
    if len(text) <= limit:
        return [text]
    chunks: List[str] = []
    remaining = text
    while len(remaining) > limit:
        window = remaining[:limit]
        cut = window.rfind("\n\n")
        if cut < limit // 2:
            cut = window.rfind("\n")
        if cut < limit // 2:
            cut = window.rfind(" ")
        if cut <= 0:
            cut = limit
        chunks.append(remaining[:cut].rstrip())
        remaining = remaining[cut:].lstrip("\n")
    if remaining.strip():
        chunks.append(remaining)
    return chunks


def clip_for_display(value: Optional[str], limit: int = 220) -> str:
    """Shortens a user-supplied field (a Top Post template, an Anime Names list, ...) for the
    settings/info screens. Those are edit_text calls carrying an inline keyboard, so they can't
    be split across messages — one 3000-character Top Post Format would otherwise make the whole
    batch-info screen unsendable. Newlines are folded so the value stays on one line."""
    if not value:
        return ""
    flat = " ".join(str(value).split())
    return flat if len(flat) <= limit else flat[:limit - 1].rstrip() + "…"


async def reply_long(message: Message, text: str, **kwargs):
    parts = split_for_telegram(text)
    markup = kwargs.pop("reply_markup", None)
    sent = None
    for i, part in enumerate(parts):
        last = (i == len(parts) - 1)
        if len(parts) > 1 and not last:
            part = f"{part}\n\n__…continued ({i + 1}/{len(parts)})__"
        sent = await message.reply_text(part, **({"reply_markup": markup} if (last and markup) else {}), **kwargs)
    return sent


# Any text wrapped like <this> inside an Autocaption Format, Top Post Format, or Bottom
# Post caption gets rendered **bold** on Telegram once the template is filled in — e.g.
# "<Attack on Titan> S{season}" sends "Attack on Titan" in bold, followed by the season.
# NOT applied to the Autorename Format: filenames can't render markdown, so bold tags
# there are just stripped down to their plain text by sanitize_filename() instead (see
# its docstring below).
BOLD_TAG_PATTERN = re.compile(r'<([^<>\n]+)>')


def apply_bold_tags(text: Optional[str]) -> Optional[str]:
    """Converts every <text> segment into Telegram markdown bold (**text**). Meant to be
    called AFTER all {placeholder} substitution is done, so users can freely wrap
    placeholders too, e.g. autocaption `<{filename}>` -> **whatever the filename is**."""
    if not text:
        return text
    return BOLD_TAG_PATTERN.sub(lambda m: f"**{m.group(1)}**", text)


def apply_per_file_format(template: str, base_name: str, season: int, episode: int,
                           quality_idx: int, file_size: int, duration: int) -> str:
    replacements = {
        "{season}": f"{season:02d}" if season else "00",
        "{episode}": f"{episode:02d}" if episode else "00",
        "{quality}": quality_label(quality_idx) if quality_idx >= 0 else "HD",
        "{filename}": base_name,
        "{filesize}": humanbytes(file_size),
        "{duration}": str(timedelta(seconds=duration)) if duration else "00:00:00",
    }
    out = template
    for k, v in replacements.items():
        out = out.replace(k, v)
    return out


def sanitize_filename(name: str) -> str:
    # NOTE: this already strips '<' and '>' along with the other characters Windows/
    # Telegram forbid in filenames. That means an Autorename Format containing
    # <Text> naturally comes out as plain "Text" in the final filename — no bold
    # markup, since filenames have no concept of bold. This is intentional: the <>
    # bold feature only actually applies to Autocaption / Top Post / Bottom Post,
    # where the result is sent as a real Telegram message and markdown can render.
    cleaned = re.sub(r'[<>:"/\\|?*]', '', name).strip()
    return cleaned or "unnamed"


DEFAULT_TOP_POST = "🎬 **{batch}**\n\n📚 Season {pseason} • Episode {pepisode} • {pquality}"


def fill_post_format(template: Optional[str], batch_name: str, pseason: str, pepisode: str, pquality: str) -> str:
    tpl = template or DEFAULT_TOP_POST
    filled = (
        tpl.replace("{pseason}", pseason)
           .replace("{pepisode}", pepisode)
           .replace("{pquality}", pquality)
           .replace("{batch}", batch_name)
    )
    # Applies to both the Sub/Backup Channel top post and the Main Channel(s) post,
    # since both are built from this same filled template (see process_job()).
    return apply_bold_tags(filled)


def compute_post_placeholders(files: List[dict]) -> Tuple[str, str, str]:
    seasons = sorted({f["season"] for f in files if f.get("season")})
    episodes = sorted({f["episode"] for f in files if f.get("episode")})
    qualities_seen = []
    for f in files:
        q = f.get("quality", -1)
        label = quality_label(q) if q is not None and q >= 0 else "HD"
        if label not in qualities_seen:
            qualities_seen.append(label)

    pseason = "/".join(f"{s:02d}" for s in seasons) if seasons else "00"
    if len(episodes) > 1:
        pepisode = f"{episodes[0]:02d}-{episodes[-1]:02d}"
    elif episodes:
        pepisode = f"{episodes[0]:02d}"
    else:
        pepisode = "00"
    pquality = "/".join(qualities_seen) if qualities_seen else "HD"
    return pseason, pepisode, pquality


def compute_ladder_placeholders(season: int, episode: int, ladder: List[str]) -> Tuple[str, str, str]:
    """Top Post placeholders for a torrent job. The quality placeholder lists every rung
    the ladder is actually going to produce (e.g. `1080p/720p/480p`), so the Top Post
    advertises the qualities that will appear underneath it."""
    pseason = f"{season:02d}" if season else "00"
    pepisode = f"{episode:02d}" if episode else "00"
    pquality = "/".join(ladder) if ladder else "HD"
    return pseason, pepisode, pquality



async def get_channel_join_link(client, chat_id: int) -> Optional[str]:
    """Returns the channel's existing PRIMARY invite link — the one Telegram already
    generated for the channel at creation time — WITHOUT creating a new additional
    invite link and WITHOUT regenerating/revoking the existing one.

    get_chat(chat_id).invite_link is a pure READ of the channel's current primary link,
    so this is safe to call as often as needed and will always reflect whatever the
    primary link currently is (even if it was rotated from outside the bot).

    Cached in the channel registry (channels.invite_link) after first successful read,
    purely to avoid an extra get_chat() call on every post — not because reading it is
    unsafe to repeat.

    export_chat_invite_link() is used ONLY as a last-resort fallback, for the rare case
    where the channel has no primary link yet for the bot to read (e.g. bot only just
    became admin and Telegram hasn't surfaced chat.invite_link). Note that
    export_chat_invite_link() DOES generate/replace the primary link — calling it
    repeatedly would keep replacing it — which is exactly why it's gated behind the
    get_chat() read above and its result is cached so it's only ever called once per
    channel.
    """
    cached = await db.get_channel_invite_link(chat_id)
    if cached:
        return cached

    try:
        chat = await client.get_chat(chat_id)
        if chat and getattr(chat, "invite_link", None):
            link = chat.invite_link
            await db.set_channel_invite_link(chat_id, link)
            return link
    except Exception as e:
        print(f"get_chat failed for {chat_id}: {e}")

    try:
        link = await client.export_chat_invite_link(chat_id)
        await db.set_channel_invite_link(chat_id, link)
        return link
    except Exception as e:
        print(f"export_chat_invite_link failed for {chat_id}: {e}")
        return None


def parse_message_link(link: str) -> Optional[Tuple[Any, int]]:
    link = link.strip()
    m = re.match(r'^https?://t\.me/c/(\d+)/(\d+)', link)
    if m:
        internal_id, msg_id = int(m.group(1)), int(m.group(2))
        chat_id = int(f"-100{internal_id}")
        return chat_id, msg_id
    m = re.match(r'^https?://t\.me/([A-Za-z0-9_]{4,})/(\d+)', link)
    if m:
        username, msg_id = m.group(1), int(m.group(2))
        return f"@{username}", msg_id
    return None



async def resolve_channel_input(client, text: str) -> Tuple[Optional[Any], Optional[str]]:
    text = text.strip()
    if re.match(r'^https?://t\.me/(c/|joinchat/|\+)', text):
        return None, ("That's a private-channel invite link, which I can't resolve directly. Please add me "
                       "as **admin** to the channel and post `/register` inside it instead.")

    m = re.match(r'^https?://t\.me/([A-Za-z0-9_]{4,})/?$', text)
    if m:
        identifier: Any = f"@{m.group(1)}"
    elif text.startswith('@'):
        identifier = text
    else:
        try:
            identifier = int(text)
        except ValueError:
            identifier = f"@{text}"

    try:
        chat = await client.get_chat(identifier)
    except Exception as e:
        return None, (f"Couldn't resolve that channel ({e}). Make sure I'm already added as **admin** there, "
                       "and that the @username/link/ID is correct.\n\n_For private channels without a public "
                       "username, add me as admin and post `/register` inside the channel instead._")
    return chat, None


async def send_bottom_post(dest_chat_id: int, bottom_post: Optional[dict]) -> bool:
    if not bottom_post:
        return False
    try:
        await app.copy_message(
            chat_id=dest_chat_id,
            from_chat_id=bottom_post["chat_id"],
            message_id=bottom_post["message_id"],
        )
        return True
    except Exception as e:
        print(f"Bottom Post copy failed to {dest_chat_id}: {e}")
        return False



# ==================== KEYBOARDS ====================
def kb_batches_list(batches: List[dict]) -> InlineKeyboardMarkup:
    rows = []
    for b in batches:
        rows.append([InlineKeyboardButton(f"📁 {b['name']}", callback_data=f"batch_open_{b['_id']}")])
    rows.append([InlineKeyboardButton("➕ New Batch (use /new_batch)", callback_data="noop")])
    return InlineKeyboardMarkup(rows)


def kb_autopost_batches(batches: List[dict], current_batch_id: Optional[str] = None) -> InlineKeyboardMarkup:
    rows = []
    for b in batches:
        bid = str(b["_id"])
        label = f"{'✅ ' if bid == current_batch_id else '📁 '}{b['name']}"
        rows.append([InlineKeyboardButton(label, callback_data=f"autopost_pick_{bid}")])
    rows.append([InlineKeyboardButton("❌ Cancel", callback_data="autopost_cancel")])
    return InlineKeyboardMarkup(rows)


def kb_batch_actions(batch_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Edit", callback_data=f"batch_edit_{batch_id}"),
         InlineKeyboardButton("🗑️ Delete", callback_data=f"batch_delconfirm_{batch_id}")],
        [InlineKeyboardButton("⬅️ Back to list", callback_data="batch_list")],
    ])


def kb_batch_edit_menu(batch_id: str) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton("🖼️ Thumbnail", callback_data=f"f_thumbnail_{batch_id}"),
         InlineKeyboardButton("🎨 Cover Image", callback_data=f"f_coverimage_{batch_id}")],
        [InlineKeyboardButton("🏷️ Metadata", callback_data=f"f_metadata_{batch_id}")],
        [InlineKeyboardButton("✏️ Autorename Format", callback_data=f"f_autorename_{batch_id}")],
        [InlineKeyboardButton("💬 Autocaption Format", callback_data=f"f_autocaption_{batch_id}")],
        [InlineKeyboardButton("🎞️ Mediatype", callback_data=f"f_mediatype_{batch_id}")],
        [InlineKeyboardButton("🔤 Anime Names", callback_data=f"f_animenames_{batch_id}")],
        [InlineKeyboardButton("🔝 Top Post Format", callback_data=f"f_toppost_{batch_id}"),
         InlineKeyboardButton("🔻 Bottom Post Format", callback_data=f"f_bottompost_{batch_id}")],
        [InlineKeyboardButton("📢 Sub Channel", callback_data=f"f_channel_{batch_id}"),
         InlineKeyboardButton("🏠 Main Channel(s)", callback_data=f"f_mainchannel_{batch_id}")],
        [InlineKeyboardButton("⬅️ Back", callback_data="batch_list")],
    ]
    return InlineKeyboardMarkup(rows)


def kb_back_field(batch_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data=f"batch_edit_{batch_id}")]])


def kb_metadata_menu(batch_id: str, enabled: bool) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("Title", callback_data=f"meta_title_{batch_id}"),
         InlineKeyboardButton("Author", callback_data=f"meta_author_{batch_id}")],
        [InlineKeyboardButton("Artist", callback_data=f"meta_artist_{batch_id}"),
         InlineKeyboardButton("Audio", callback_data=f"meta_audio_{batch_id}")],
        [InlineKeyboardButton("Subtitle", callback_data=f"meta_subtitle_{batch_id}"),
         InlineKeyboardButton("Video", callback_data=f"meta_video_{batch_id}")],
        [InlineKeyboardButton("Set All Fields", callback_data=f"meta_all_{batch_id}")],
        [InlineKeyboardButton(f"{'❌ Disable' if enabled else '✅ Enable'} Metadata",
                               callback_data=f"meta_toggle_{batch_id}")],
        [InlineKeyboardButton("⬅️ Back", callback_data=f"batch_edit_{batch_id}")],
    ])


def kb_mediatype(batch_id: str, current: str) -> InlineKeyboardMarkup:
    def lbl(t):
        return f"{'✅ ' if current == t else ''}{t.capitalize()}"
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(lbl("document"), callback_data=f"mt_document_{batch_id}"),
         InlineKeyboardButton(lbl("video"), callback_data=f"mt_video_{batch_id}"),
         InlineKeyboardButton(lbl("audio"), callback_data=f"mt_audio_{batch_id}")],
        [InlineKeyboardButton("⬅️ Back", callback_data=f"batch_edit_{batch_id}")],
    ])


def kb_channel_picker(batch_id: str, channels: List[dict], current_id: Optional[int], kind: str = "sub") -> InlineKeyboardMarkup:
    rows = []
    for c in channels:
        cid = c["_id"]
        title = c.get("title", "Channel")
        label = f"{'✅ ' if current_id == cid else ''}📢 {title}"
        rows.append([InlineKeyboardButton(label[:60], callback_data=f"chan_pick_{kind}_{batch_id}_{cid}")])
    rows.append([InlineKeyboardButton("➕ Add channel by link", callback_data=f"chan_addlink_{kind}_{batch_id}")])
    if current_id:
        rows.append([InlineKeyboardButton("🗑️ Remove Channel", callback_data=f"chan_remove_{kind}_{batch_id}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data=f"batch_edit_{batch_id}")])
    return InlineKeyboardMarkup(rows)


def kb_main_channel_picker(batch_id: str, channels: List[dict], current_ids: List[int]) -> InlineKeyboardMarkup:
    """Multi-select picker for a batch's Main Channel(s): tapping a channel toggles it
    in/out of the list instead of replacing a single value, so any number of Main
    Channels can be selected at once."""
    rows = []
    for c in channels:
        cid = c["_id"]
        title = c.get("title", "Channel")
        checked = cid in current_ids
        label = f"{'✅ ' if checked else '➕ '}📢 {title}"
        rows.append([InlineKeyboardButton(label[:60], callback_data=f"mainchan_toggle_{batch_id}_{cid}")])
    rows.append([InlineKeyboardButton("➕ Add channel by link", callback_data=f"chan_addlink_main_{batch_id}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data=f"batch_edit_{batch_id}")])
    return InlineKeyboardMarkup(rows)


def kb_bot_settings_menu(settings: dict) -> InlineKeyboardMarkup:
    backup_ch = settings.get("backup_channel")
    backup_lbl = f"🗄️ Backup Channel: {backup_ch['title']}" if backup_ch and backup_ch.get("id") else "🗄️ Set Backup Channel"
    thumb_ch = settings.get("thumb_channel")
    thumb_lbl = f"🖼️ Thumb/Cover Channel: {thumb_ch['title']}" if thumb_ch and thumb_ch.get("id") else "🖼️ Set Thumb/Cover Channel"
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(backup_lbl[:60], callback_data="gset_pick_menu_backup")],
        [InlineKeyboardButton(thumb_lbl[:60], callback_data="gset_pick_menu_thumbchannel")],
        [InlineKeyboardButton("🎬 Encode Settings (torrent ladder)", callback_data="enc_menu")],
    ])


def kb_global_channel_picker(kind: str, channels: List[dict], current_id: Optional[int]) -> InlineKeyboardMarkup:
    rows = []
    for c in channels:
        cid = c["_id"]
        title = c.get("title", "Channel")
        label = f"{'✅ ' if current_id == cid else ''}📢 {title}"
        rows.append([InlineKeyboardButton(label[:60], callback_data=f"gset_set_{kind}_{cid}")])
    rows.append([InlineKeyboardButton("➕ Add channel by link", callback_data=f"gset_addlink_{kind}")])
    if current_id:
        rows.append([InlineKeyboardButton("🗑️ Remove", callback_data=f"gset_remove_{kind}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="gset_menu")])
    return InlineKeyboardMarkup(rows)


def kb_encode_menu(enc: dict) -> InlineKeyboardMarkup:
    """Every rung of the ladder is a toggle, so a server that only wants 720p + 480p just
    switches 1080p off. Rungs are always encoded high -> low regardless of tap order."""
    ladder = enc["ladder"]
    rung_row = []
    for q in ("4K", "2K", "1080p", "720p", "480p", "360p"):
        rung_row.append(InlineKeyboardButton(f"{'✅' if q in ladder else '▫️'} {q}", callback_data=f"enc_rung_{q}"))
    rows = [rung_row[:3], rung_row[3:]]
    _, codec_label = resolve_codec(enc)
    rows.append([InlineKeyboardButton(f"🧬 Codec: {codec_label}", callback_data="enc_codec"),
                 InlineKeyboardButton(f"🎚️ CRF: {enc['crf']}", callback_data="enc_crf")])
    rows.append([InlineKeyboardButton(f"⚡ Preset: {enc['preset']}", callback_data="enc_preset"),
                 InlineKeyboardButton(f"🎨 Tune: {enc.get('tune', 'animation')}", callback_data="enc_tune")])
    rows.append([InlineKeyboardButton(f"🎯 Targets: {targets_summary(enc, compact=True)}",
                                       callback_data="enc_targets")])
    rows.append([InlineKeyboardButton(f"🔊 Audio: {'copy all' if enc['audio'] == 'copy' else ('auto' if enc['audio'] == 'auto' else 'AAC 128k')}",
                                       callback_data="enc_audio"),
                 InlineKeyboardButton(f"🔢 Depth: {enc.get('bit_depth', 8)}-bit", callback_data="enc_depth")])
    rows.append([InlineKeyboardButton(f"📦 Container: .{enc['container']}", callback_data="enc_container"),
                 InlineKeyboardButton(f"💬 Subs: {'on' if enc['keep_subs'] else 'off'}", callback_data="enc_subs")])
    rows.append([InlineKeyboardButton(f"🚫 Skip upscaling: {'on' if enc['skip_upscale'] else 'off'}",
                                       callback_data="enc_upscale")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="gset_menu")])
    return InlineKeyboardMarkup(rows)


def targets_summary(enc: dict, compact: bool = False) -> str:
    """`1080p 250 • 720p 150 • 480p 90`, or `250/150/90 MB` for the button label. Only covers the
    rungs actually enabled."""
    targets = enc.get("targets", {}) or {}
    mbs = [int(targets.get(q, DEFAULT_TARGET_MB.get(q, 0)) or 0) for q in enc.get("ladder", [])]
    if not mbs:
        return "none"
    if compact:
        return "/".join(str(mb) if mb else "∞" for mb in mbs) + " MB"
    return " • ".join(f"{q} {mb or 'off'}" for q, mb in zip(enc.get("ladder", []), mbs))


def kb_job_cancel(job_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("🛑 Cancel this job", callback_data=f"jobcancel_{job_id}")]])


def kb_sequence_sort(user_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("1️⃣ Season → Quality → Episode", callback_data=f"seqsort_1_{user_id}")],
        [InlineKeyboardButton("2️⃣ Season → Episode → Quality", callback_data=f"seqsort_2_{user_id}")],
        [InlineKeyboardButton("3️⃣ Quality → Season → Episode", callback_data=f"seqsort_3_{user_id}")],
        [InlineKeyboardButton("❌ Cancel", callback_data="seq_cancel")],
    ])


def kb_queue_confirm(user_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🚀 Add to Queue", callback_data=f"seq_enqueue_{user_id}"),
         InlineKeyboardButton("❌ Cancel", callback_data="seq_cancel")],
    ])


def kb_anime_names_menu(batch_id: str, names: List[str]) -> InlineKeyboardMarkup:
    rows = []
    for idx, name in enumerate(names):
        rows.append([InlineKeyboardButton(f"🗑️ {name[:45]}", callback_data=f"animename_del_{batch_id}_{idx}")])
    rows.append([InlineKeyboardButton("➕ Add Name(s)", callback_data=f"animename_add_{batch_id}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data=f"batch_edit_{batch_id}")])
    return InlineKeyboardMarkup(rows)


def kb_channels_list_for_delete(channels: List[dict]) -> InlineKeyboardMarkup:
    rows = []
    for c in channels:
        cid = c["_id"]
        title = c.get("title", "Channel")
        rows.append([InlineKeyboardButton(f"📢 {title}", callback_data=f"delchan_open_{cid}")])
    return InlineKeyboardMarkup(rows)


def kb_delete_channel_confirm(cid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Yes, delete", callback_data=f"delchan_yes_{cid}"),
         InlineKeyboardButton("❌ No", callback_data="delchan_list")],
    ])



# ==================== FILE PROCESSING HELPERS ====================
def find_binary(*names) -> Optional[str]:
    """Resolves an external tool once, checking PATH first and then the usual absolute
    locations Docker/VPS images put them in."""
    for name in names:
        found = shutil.which(name)
        if found:
            return found
    for name in names:
        for prefix in ("/usr/bin/", "/usr/local/bin/", "/bin/", "/opt/bin/"):
            candidate = prefix + name
            if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
                return candidate
    return None


FFMPEG = find_binary("ffmpeg")
FFPROBE = find_binary("ffprobe")
ARIA2C = find_binary("aria2c")


# ==================== ENCODER CAPABILITY DETECTION ====================
# Probed once at import, because the encode command has to be built from what this particular
# ffmpeg build can actually do. Listing an encoder in `-encoders` is NOT proof it works: every
# ffmpeg ships h264_nvenc/h264_qsv/h264_vaapi stubs that fail at runtime when the machine has
# no matching GPU (which is the normal case on a plain VPS or in a Codespace). So each hardware
# candidate gets a real one-frame smoke encode and only counts if that returns 0.
ENCODER_CAPS: dict = {
    "encoders": set(),      # names ffmpeg lists
    "x264_10bit": False,    # libx264 built with high-bit-depth support
    "x265": False,
    "x265_10bit": False,
    "hw": None,             # e.g. "h264_nvenc" — verified working, or None
    "hw_hevc": None,        # e.g. "hevc_nvenc" — verified working, or None
    "probed": False,
}

HW_H264_CANDIDATES = ["h264_nvenc", "h264_qsv", "h264_vaapi", "h264_amf", "h264_videotoolbox"]
HW_HEVC_CANDIDATES = ["hevc_nvenc", "hevc_qsv", "hevc_vaapi", "hevc_amf", "hevc_videotoolbox"]


def _ffmpeg_list_encoders() -> set:
    if not FFMPEG:
        return set()
    try:
        out = subprocess.run([FFMPEG, "-hide_banner", "-loglevel", "error", "-encoders"],
                              capture_output=True, timeout=30).stdout.decode("utf-8", "ignore")
    except Exception:
        return set()
    names = set()
    for line in out.splitlines():
        parts = line.split()
        # rows look like " V....D libx264   libx264 H.264 / AVC ..."
        if len(parts) >= 2 and len(parts[0]) == 6 and parts[0][0] in "VAS":
            names.add(parts[1])
    return names


def _encoder_supports_pixfmt(encoder: str, pix_fmt: str) -> bool:
    if not FFMPEG:
        return False
    try:
        out = subprocess.run([FFMPEG, "-hide_banner", "-loglevel", "error", "-h", f"encoder={encoder}"],
                              capture_output=True, timeout=30).stdout.decode("utf-8", "ignore")
    except Exception:
        return False
    for line in out.splitlines():
        if "Supported pixel formats" in line:
            return pix_fmt in line.split(":", 1)[-1].split()
    return False


def _hw_encoder_works(encoder: str) -> bool:
    """One-frame throwaway encode to the null muxer. This is the only reliable test — the
    encoder being listed says nothing about whether a usable device is present."""
    if not FFMPEG:
        return False
    pre = [FFMPEG, "-hide_banner", "-loglevel", "error", "-nostdin"]
    if encoder.endswith("_vaapi"):
        if not os.path.exists("/dev/dri/renderD128"):
            return False
        pre += ["-vaapi_device", "/dev/dri/renderD128"]
    cmd = pre + ["-f", "lavfi", "-i", "color=c=black:s=320x240:d=0.2:r=5"]
    if encoder.endswith("_vaapi"):
        cmd += ["-vf", "format=nv12,hwupload"]
    cmd += ["-frames:v", "1", "-c:v", encoder, "-f", "null", "-y", os.devnull]
    try:
        return subprocess.run(cmd, capture_output=True, timeout=60).returncode == 0
    except Exception:
        return False


def probe_encoder_caps(verbose: bool = False):
    """Fills ENCODER_CAPS. Safe to call more than once; only the first call does the work."""
    if ENCODER_CAPS["probed"] or not FFMPEG:
        ENCODER_CAPS["probed"] = True
        return
    names = _ffmpeg_list_encoders()
    ENCODER_CAPS["encoders"] = names
    ENCODER_CAPS["x264_10bit"] = "libx264" in names and _encoder_supports_pixfmt("libx264", "yuv420p10le")
    ENCODER_CAPS["x265"] = "libx265" in names
    ENCODER_CAPS["x265_10bit"] = ENCODER_CAPS["x265"] and _encoder_supports_pixfmt("libx265", "yuv420p10le")
    for cand in HW_H264_CANDIDATES:
        if cand in names and _hw_encoder_works(cand):
            ENCODER_CAPS["hw"] = cand
            break
    for cand in HW_HEVC_CANDIDATES:
        if cand in names and _hw_encoder_works(cand):
            ENCODER_CAPS["hw_hevc"] = cand
            break
    ENCODER_CAPS["probed"] = True
    if verbose:
        print(f"🎛️  Encoders: libx264 {'✅' if 'libx264' in names else '❌'}"
              f" (10-bit {'✅' if ENCODER_CAPS['x264_10bit'] else '❌'})"
              f" | libx265 {'✅' if ENCODER_CAPS['x265'] else '❌'}")
        if ENCODER_CAPS["hw"] or ENCODER_CAPS["hw_hevc"]:
            print(f"⚡ Hardware encoding available: "
                  f"{ENCODER_CAPS['hw'] or '—'} / {ENCODER_CAPS['hw_hevc'] or '—'} "
                  f"(verified with a real test encode)")
        else:
            print("🐢 No working hardware encoder — encoding on the CPU. "
                  "Speed is bound by core count (check `nproc`).")


def cpu_count() -> int:
    try:
        return len(os.sched_getaffinity(0))  # respects cgroup/container limits
    except AttributeError:
        return os.cpu_count() or 1


def torrent_backend() -> Optional[str]:
    """Which torrent engine this server will actually use. libtorrent wins when present
    because it can validate a torrent's metadata before downloading any content and grab
    only the one video file we want; aria2c is the fallback."""
    if lt is not None:
        return "libtorrent"
    if ARIA2C:
        return "aria2c"
    return None


async def cleanup_files(*paths):
    for path in paths:
        try:
            if path and os.path.exists(path):
                if os.path.isfile(path):
                    os.remove(path)
                elif os.path.isdir(path):
                    shutil.rmtree(path)
        except Exception as e:
            print(f"Error removing {path}: {e}")


async def cleanup_stale_directories():
    for folder in ("downloads", "temp", "torrents"):
        try:
            if not os.path.isdir(folder):
                continue
            entries = os.listdir(folder)
            for entry in entries:
                await cleanup_files(os.path.join(folder, entry))
            if entries:
                print(f"🧹 Startup sweep: cleared {len(entries)} leftover file(s) from {folder}/")
        except Exception as e:
            print(f"Startup sweep error in {folder}/: {e}")



async def process_thumbnail(thumb_path):
    """Resizes a downloaded image down to Telegram's `thumb=` requirements (<=320px, <200KB).
    This is ALWAYS required for the small in-chat preview thumb, regardless of source quality —
    it's a hard Telegram API limit, not something we can raise."""
    if not thumb_path or not os.path.exists(thumb_path):
        return None
    try:
        with Image.open(thumb_path) as img:
            if img.mode != "RGB":
                img = img.convert("RGB")
            img.thumbnail((320, 320))
            img.save(thumb_path, "JPEG", quality=85)
        return thumb_path
    except Exception as e:
        print(f"Thumbnail processing error: {e}")
        await cleanup_files(thumb_path)
        return None


async def process_cover(cover_path):
    """Unlike process_thumbnail, this does NOT force-resize to 320x320 or recompress at low
    quality — the whole point of the cover is a full-size poster image, not a squashed 200KB
    thumb. We only normalize to RGB JPEG (Telegram expects a photo-like format for `cover=`)
    and enforce Telegram's ~10MB upload ceiling for photo-style attachments."""
    if not cover_path or not os.path.exists(cover_path):
        return None
    try:
        if os.path.getsize(cover_path) > Config.MAX_COVER_SIZE:
            print(f"Cover image too large ({humanbytes(os.path.getsize(cover_path))}), skipping cover.")
            await cleanup_files(cover_path)
            return None
        with Image.open(cover_path) as img:
            if img.mode != "RGB":
                img = img.convert("RGB")
            img.save(cover_path, "JPEG", quality=95)
        return cover_path
    except Exception as e:
        print(f"Cover processing error: {e}")
        await cleanup_files(cover_path)
        return None


async def download_channel_image(chat_id: int, message_id: int, dest_path: str) -> Optional[str]:
    """Fetches a message from the Thumb/Cover Channel and downloads its photo at the best
    quality Telegram stored it at (the largest available size — Telegram itself compresses
    photos sent as 'photo' type, this downloads whatever the largest resulting size is)."""
    try:
        msg = await app.get_messages(chat_id, message_id)
        if not msg or getattr(msg, "empty", False) or not msg.photo:
            return None
        path = await app.download_media(msg, file_name=dest_path)
        return path
    except Exception as e:
        print(f"download_channel_image failed for {chat_id}/{message_id}: {e}")
        return None



async def progress_for_pyrogram(current, total, action_text, status_msg, start_time):
    if not status_msg:
        return
    now = time.time()
    diff = now - start_time
    if diff > 0 and round(diff % 3) != 0 and current != total:
        return
    try:
        percentage = (current * 100 / total) if total else 0
        speed = current / diff if diff > 0 else 0
        eta = TimeFormatter(((total - current) / speed) * 1000) if speed > 0 else "0s"
        await status_msg.edit_text(
            f"{action_text}\n\n"
            f"`{progress_bar(percentage)}` {percentage:.1f}%\n"
            f"» {humanbytes(current)} / {humanbytes(total)}\n"
            f"» Speed: {humanbytes(speed)}/s | ETA: {eta}"
        )
    except Exception:
        pass


class StatusUpdater:
    """Rate-limited wrapper around one status message.

    A torrent job emits progress from three different long-running stages (torrent download,
    each ffmpeg rung, each upload) into a single message. Telegram will happily FloodWait a
    bot that edits the same message every 200ms, so every write goes through here: identical
    text is dropped, and edits are spaced at least `interval` seconds apart unless forced.
    The inline keyboard is re-attached on every edit, because edit_text() drops the existing
    markup if you don't pass it again."""

    def __init__(self, message: Optional[Message], reply_markup=None, interval: float = 6.0):
        self.message = message
        self.reply_markup = reply_markup
        self.interval = interval
        self._last_text = ""
        self._last_at = 0.0

    async def set(self, text: str, force: bool = False):
        if not self.message:
            return
        now = time.time()
        if not force and (text == self._last_text or now - self._last_at < self.interval):
            return
        self._last_text = text
        self._last_at = now
        try:
            await self.message.edit_text(text, reply_markup=self.reply_markup)
        except Exception as e:
            # FloodWait / MessageNotModified / message deleted — back off rather than spam.
            wait = getattr(e, "value", None)
            if isinstance(wait, int):
                self._last_at = now + wait

    async def done(self, text: str):
        await self.set(text, force=True)

    def upload_progress_args(self, action_text: str):
        """Adapter so send_prepared_file()'s progress callback can write into this same
        status message instead of fighting it for the edit slot."""
        return (action_text, self.message, time.time())


async def probe_media(path: str) -> dict:
    """ffprobe -> duration/height/width/has_subs/audio plus the extra facts the encoder needs:
    how many font-style attachments the source carries (the cover-art flag has to be indexed
    past them) and how many kbps the audio tracks already use (so a rung's size budget can be
    split between video and audio instead of guessed at).
    Everything defaults to 0/False when ffprobe is unavailable or the file is unreadable, and
    every caller treats those defaults as "unknown" rather than as an error."""
    info = {"duration": 0, "height": 0, "width": 0, "has_subs": False, "audio": 0,
            "attachments": 0, "audio_kbps": 0, "vcodec": "", "fps": 0.0}
    if not FFPROBE or not path or not os.path.exists(path):
        return info
    cmd = [FFPROBE, "-v", "quiet", "-print_format", "json", "-show_format", "-show_streams", path]
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL)
        out, _ = await asyncio.wait_for(proc.communicate(), timeout=120)
        data = json.loads(out.decode("utf-8", errors="ignore") or "{}")
    except Exception as e:
        print(f"ffprobe failed for {path}: {e}")
        return info
    try:
        info["duration"] = int(float(data.get("format", {}).get("duration") or 0))
    except Exception:
        pass
    audio_bps = 0
    audio_unknown = 0
    for st in data.get("streams", []):
        codec_type = st.get("codec_type")
        if codec_type == "video" and st.get("disposition", {}).get("attached_pic", 0) != 1:
            if not info["height"]:
                info["height"] = int(st.get("height") or 0)
                info["width"] = int(st.get("width") or 0)
                info["vcodec"] = st.get("codec_name") or ""
                rate = st.get("avg_frame_rate") or st.get("r_frame_rate") or "0/1"
                try:
                    num, _, den = rate.partition("/")
                    info["fps"] = round(float(num) / float(den or 1), 3)
                except Exception:
                    pass
            if not info["duration"]:
                try:
                    info["duration"] = int(float(st.get("duration") or 0))
                except Exception:
                    pass
        elif codec_type == "audio":
            info["audio"] += 1
            try:
                audio_bps += int(st.get("bit_rate") or 0) or 0
                if not st.get("bit_rate"):
                    audio_unknown += 1
            except Exception:
                audio_unknown += 1
        elif codec_type == "subtitle":
            info["has_subs"] = True
        elif codec_type == "attachment":
            info["attachments"] += 1
    # MKV usually omits per-stream bit_rate. Assume 128 kbps per unmeasurable track rather than
    # treating it as free, so the size budget below never over-allocates to video.
    info["audio_kbps"] = int(audio_bps / 1000) + (audio_unknown * 128)
    return info



def ffmpeg_meta_args(meta: dict) -> List[str]:
    """The -metadata flags shared by the plain tagging path and the encode path."""
    def esc(t):
        return (t or "").replace('"', '\\"').replace("'", "\\'")
    return [
        "-metadata", f'title={esc(meta.get("title"))}',
        "-metadata", f'artist={esc(meta.get("artist"))}',
        "-metadata", f'author={esc(meta.get("author"))}',
        "-metadata:s:a", f'title={esc(meta.get("audio"))}',
        "-metadata:s:s", f'title={esc(meta.get("subtitle"))}',
    ]


async def add_metadata(input_path: str, output_path: str, meta: dict,
                        cover_path: Optional[str] = None, media_type: str = "video") -> str:
    """Tags metadata via ffmpeg, and — if cover_path is given and this isn't an audio-only
    file — embeds the cover image as an attached picture stream (same technique used for
    mp3 album art, works for mkv/mp4 containers too), so it shows as the file's own cover
    art at full/original quality, independent of Telegram's small in-chat thumb.

    Used by the FILE-UPLOAD pipeline (a file you forward to the bot), which only tags and
    never re-encodes. The TORRENT pipeline does its tagging inside the encode command
    instead — see encode_rung() — so it never writes a second full-size copy of the file
    just to attach metadata."""
    if not FFMPEG:
        shutil.copy2(input_path, output_path)
        return output_path

    def esc(t):
        return (t or "").replace('"', '\\"').replace("'", "\\'")

    use_cover = bool(cover_path and os.path.exists(cover_path) and media_type != "audio")

    if use_cover:
        cmd = [
            FFMPEG, "-i", input_path, "-i", cover_path,
            "-map", "0", "-map", "1",
            "-c", "copy", "-c:v:1", "mjpeg", "-disposition:v:1", "attached_pic",
            "-metadata", f'title={esc(meta.get("title"))}',
            "-metadata", f'artist={esc(meta.get("artist"))}',
            "-metadata", f'author={esc(meta.get("author"))}',
            "-metadata:s:v:0", f'title={esc(meta.get("video"))}',
            "-metadata:s:a", f'title={esc(meta.get("audio"))}',
            "-metadata:s:s", f'title={esc(meta.get("subtitle"))}',
            "-y", output_path,
        ]
    else:
        cmd = [
            FFMPEG, "-i", input_path, "-map", "0",
            "-c:v", "copy", "-c:a", "copy", "-c:s", "copy",
            "-metadata", f'title={esc(meta.get("title"))}',
            "-metadata", f'artist={esc(meta.get("artist"))}',
            "-metadata", f'author={esc(meta.get("author"))}',
            "-metadata:s:v", f'title={esc(meta.get("video"))}',
            "-metadata:s:a", f'title={esc(meta.get("audio"))}',
            "-metadata:s:s", f'title={esc(meta.get("subtitle"))}',
            "-y", output_path,
        ]

    try:
        process = await asyncio.wait_for(
            asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE),
            timeout=180,
        )
        _, stderr = await process.communicate()
        if process.returncode != 0 or not os.path.exists(output_path) or os.path.getsize(output_path) == 0:
            if use_cover:
                # Cover embedding is the more fragile path (extra input stream) — retry
                # once without it so metadata tagging still succeeds even if the cover
                # attach step itself fails for some reason.
                print(f"ffmpeg cover-embed failed, retrying without cover: {stderr.decode(errors='ignore')[:300]}")
                return await add_metadata(input_path, output_path, meta, cover_path=None, media_type=media_type)
            shutil.copy2(input_path, output_path)
    except asyncio.TimeoutError:
        shutil.copy2(input_path, output_path)
    return output_path


# ==================== VIDEO ENCODER (torrent pipeline) ====================
# Container overhead (MKV cluster headers, cues, seek index) plus a safety margin, so a rung
# aiming at 250 MB lands under 250 MB rather than at 253 MB.
SIZE_SAFETY = 0.97
# The share of a rung's bitrate budget audio is allowed to take before it gets re-encoded
# smaller. Without this a 480p rung aiming at 90 MB would spend a third of its budget on two
# copied 128 kbps tracks and starve the video.
AUDIO_BUDGET_SHARE = 0.28


def compute_size_budget(target_mb: int, duration: int, source_audio_kbps: int,
                        audio_tracks: int) -> dict:
    """Turns "this rung must fit in N MB" into concrete -maxrate/-bufsize numbers.

    Returns {"capped": bool, "video_kbps": int, "audio_mode": "copy"|"aac",
             "audio_kbps_each": int}. When the target is 0 (uncapped) or the duration is
    unknown, nothing is capped and CRF alone decides the size."""
    out = {"capped": False, "video_kbps": 0, "audio_mode": "copy", "audio_kbps_each": 0}
    if target_mb <= 0 or duration <= 0:
        return out
    total_kbps = (target_mb * 8388.608) / duration      # MiB -> kbit/s
    usable = total_kbps * SIZE_SAFETY
    tracks = max(1, audio_tracks)
    audio_ceiling = usable * AUDIO_BUDGET_SHARE
    if source_audio_kbps and source_audio_kbps <= audio_ceiling:
        audio_alloc = float(source_audio_kbps)          # copying fits — keep bit-exact audio
    else:
        audio_alloc = audio_ceiling
        # 80 kbps is the floor where AAC-LC stereo still sounds clean on a phone; below that the
        # audio degrades more noticeably than the ~20 kbps it hands back to the video would gain.
        per_track = int(max(80, min(160, audio_alloc / tracks)))
        out["audio_mode"] = "aac"
        out["audio_kbps_each"] = per_track
        audio_alloc = float(per_track * tracks)
    video = int(max(120, usable - audio_alloc))         # never propose an absurdly tiny video rate
    out["capped"] = True
    out["video_kbps"] = video
    return out


def _pix_fmt_for(encoder: str, bit_depth: int) -> str:
    """10-bit only when the build genuinely supports it — otherwise silently stay at 8-bit
    instead of failing every encode on a stock distro ffmpeg."""
    if bit_depth != 10:
        return "yuv420p"
    if encoder == "libx264" and ENCODER_CAPS.get("x264_10bit"):
        return "yuv420p10le"
    if encoder == "libx265" and ENCODER_CAPS.get("x265_10bit"):
        return "yuv420p10le"
    return "yuv420p"


# x264/x265 knobs that buy real compression on flat-shaded animation for very little CPU.
# aq-mode=3 biases bits toward dark areas (where anime banding shows up first); a longer
# rc-lookahead helps a lot on content with static backgrounds.
#
# Deliberately *not* here: b-adapt=2, ref=5 and rc-lookahead=60. Measured against this bot's own
# bitrate cap (SSIM/PSNR on a 1080p animation-like clip, 2 threads), they cost ~2.7x the encode
# time and scored no better than the cheaper set below — because once -maxrate pins the bitrate,
# the expensive decisions have almost nothing left to optimise. On a 2-vCPU box that difference
# is 20 minutes versus an hour per episode.
X264_QUALITY_PARAMS = "aq-mode=3:aq-strength=0.8:rc-lookahead=40:bframes=5:ref=3:deblock=1,1:psy-rd=1.0,0.1:qcomp=0.65"
X265_QUALITY_PARAMS = "aq-mode=3:rc-lookahead=40:bframes=6:ref=4:rd=3:psy-rd=1.5:rdoq-level=1"


def _video_encoder_args(encoder: str, enc: dict, crf: int, budget: dict, bit_depth: int) -> List[str]:
    """The -c:v:0 ... block for one rung. Everything is pinned to :v:0 because variant 1 can add
    the Cover Image as a SECOND video stream (mjpeg): an unscoped -profile:v/-pix_fmt/-level
    lands on that stream too, and mjpeg has no "high" profile, which aborts the whole encode."""
    pix = _pix_fmt_for(encoder, bit_depth)
    tune = enc.get("tune", "animation")
    args: List[str] = ["-c:v:0", encoder]
    maxrate = budget.get("video_kbps") if budget.get("capped") else 0
    # Hardware encoders need an explicit *average* bitrate to respect a cap; 85% of the peak is
    # the usual VBR relationship and leaves the encoder room to spend on hard scenes.
    hw_avg = int(maxrate * 0.85) if maxrate else 0

    if encoder == "libx264":
        args += ["-preset", enc["preset"], "-crf", str(crf), "-pix_fmt:v:0", pix,
                 "-profile:v:0", "high10" if pix.endswith("10le") else "high",
                 "-level:v:0", "4.1", "-x264-params", X264_QUALITY_PARAMS]
        if tune != "none":
            args += ["-tune", tune]
    elif encoder == "libx265":
        args += ["-preset", enc["preset"], "-crf", str(crf), "-pix_fmt:v:0", pix,
                 "-x265-params", X265_QUALITY_PARAMS + ":log-level=error"]
        if tune in ("animation", "grain"):
            args += ["-tune", tune]
        args += ["-tag:v", "hvc1"]          # lets Apple/QuickTime play the mp4 variant
    elif encoder.endswith("_nvenc"):
        # NVENC has no CRF; -rc vbr with -cq is its constant-quality mode. But a hardware
        # encoder in pure constant-quality mode IGNORES -maxrate — verified on QSV, where a
        # 1150k cap produced a 689 MB/episode file. So whenever there's a size target, an
        # explicit average bitrate has to be set and -cq becomes only a quality ceiling.
        args += ["-preset", "p4", "-tune", "hq", "-rc", "vbr", "-cq", str(crf),
                 "-b:v", f"{hw_avg}k" if hw_avg else "0", "-pix_fmt:v:0", pix,
                 "-rc-lookahead", "32", "-spatial_aq", "1", "-temporal_aq", "1",
                 "-bf", "3", "-b_ref_mode", "middle"]
    elif encoder.endswith("_qsv"):
        args += ["-preset", "medium", "-look_ahead", "1", "-pix_fmt:v:0", pix]
        if hw_avg:
            args += ["-b:v", f"{hw_avg}k"]
        else:
            args += ["-global_quality", str(crf)]
    elif encoder.endswith("_vaapi"):
        if hw_avg:
            args += ["-rc_mode", "VBR", "-b:v", f"{hw_avg}k", "-qp", str(crf)]
        else:
            args += ["-rc_mode", "CQP", "-qp", str(crf)]
        args += ["-compression_level", "1"]
    elif encoder.endswith("_amf"):
        if hw_avg:
            args += ["-rc", "vbr_peak", "-b:v", f"{hw_avg}k", "-quality", "quality",
                     "-pix_fmt:v:0", pix]
        else:
            args += ["-rc", "cqp", "-qp_i", str(crf), "-qp_p", str(crf), "-quality", "quality",
                     "-pix_fmt:v:0", pix]
    else:
        args += ["-crf", str(crf), "-pix_fmt:v:0", pix]

    if maxrate:
        # Capped CRF: quality still drives the allocation, but the stream can never average
        # above the rung's size target. bufsize = 2x maxrate is the standard VBV window.
        args += ["-maxrate:v:0", f"{maxrate}k", "-bufsize:v:0", f"{maxrate * 2}k"]
    return args


def build_encode_variants(input_path: str, output_path: str, target_height: int,
                           source_height: int, meta: dict, cover_path: Optional[str],
                           enc: dict, crf: Optional[int] = None,
                           budget: Optional[dict] = None,
                           src_attachments: int = 0) -> List[List[str]]:
    """Returns progressively more forgiving ffmpeg command variants for one ladder rung.

    Variant 1 is what we actually want: keep every audio track (so dual-audio releases stay
    dual-audio), keep soft subtitles and font attachments, re-encode only the video, attach
    the batch's Cover Image as the file's poster, and write all the batch metadata in the
    same pass. Real-world releases break that in a dozen ways (mov_text subs that can't go
    into mkv, PGS subs that can't go into mp4, exotic attachments, cover attach failures),
    so each later variant drops one more risky ingredient. The first one that produces a
    non-empty file wins.

    Scaling uses `scale=-2:H`, which derives the width from the source aspect ratio and
    rounds it to an even number (H.264 requires even dimensions). When the source is already
    at or below the target height and skip_upscale is on, no scale filter is added at all —
    upscaling a 720p source into a "1080p" file only wastes bitrate and time.

    `crf` overrides the stored CRF (each rung down the ladder gets a slightly higher one),
    `budget` comes from compute_size_budget() and turns the rung's MB target into
    -maxrate/-bufsize, and `src_attachments` is how many attachments the source has — needed
    to address the cover attachment by the right index.
    """
    keep_subs = bool(enc.get("keep_subs", True))
    budget = budget or {"capped": False}
    crf = int(enc["crf"] if crf is None else crf)
    encoder, _ = resolve_codec(enc)
    bit_depth = int(enc.get("bit_depth", 8))
    is_mkv = not output_path.lower().endswith(".mp4")
    needs_scale = not (enc.get("skip_upscale", True) and source_height and source_height <= target_height)

    base = [FFMPEG, "-hide_banner", "-nostdin", "-loglevel", "error", "-i", input_path]
    cover_ok = bool(cover_path and os.path.exists(cover_path))
    cover_is_png = os.path.splitext(cover_path or "")[1].lower() == ".png"
    cover_mime = "image/png" if cover_is_png else "image/jpeg"
    cover_name = "cover.png" if cover_is_png else "cover.jpg"

    meta_args = ffmpeg_meta_args(meta) + ["-metadata:s:v:0", f'title={(meta.get("video") or "")}']
    vfilter = ["-filter:v:0", f"scale=-2:{target_height}:flags={enc.get('scaler', 'lanczos')}"] if needs_scale else []
    vargs = _video_encoder_args(encoder, enc, crf, budget, bit_depth)
    subs_codec = ["-c:s", "copy"] if is_mkv else ["-c:s", "mov_text"]

    tail = ["-max_muxing_queue_size", "4096", "-progress", "pipe:1", "-nostats", "-y", output_path]
    if not is_mkv:
        tail = ["-movflags", "+faststart"] + tail

    # Copying audio keeps dual-audio releases bit-exact, but a rung with a tight MB target
    # can't always afford two 128 kbps tracks — compute_size_budget() makes that call and
    # reports it back through `budget`.
    if budget.get("audio_mode") == "aac" or enc.get("audio") == "aac":
        akbps = budget.get("audio_kbps_each") or 128
        audio = ["-c:a", "aac", "-b:a", f"{akbps}k", "-ac", "2"]
    else:
        audio = ["-c:a", "copy"]
    minimal_audio = ["-c:a", "aac", "-b:a", "128k", "-ac", "2"]

    variants: List[List[str]] = []

    def add(maps: List[str], *, cover: bool, subs: bool, attachments: bool,
            audio_args: Optional[List[str]] = None,
            video_args: Optional[List[str]] = None) -> None:
        """Assembles one variant.

        Cover art is container-specific, and getting that wrong is what broke every real
        release. MKV stores cover art as an *attachment* named cover.jpg with an image/*
        mimetype. Doing it the MP4 way there — a second mjpeg video stream tagged
        attached_pic — gets the disposition silently dropped by the matroska muxer (so no
        player shows it), and combined with `-map 0:t?` the muxer rejects packets outright
        ("Received a packet for an attachment stream"). The -metadata:s:t index has to skip
        the source's own attachments, or the mimetype lands on a font and the header write
        fails. MP4 has no attachment concept at all, so there the mjpeg stream is correct.
        """
        cmd = list(base)
        want_cover = cover and cover_ok
        if want_cover and not is_mkv:
            cmd += ["-i", cover_path]
        cmd += list(maps)
        if subs and keep_subs:
            cmd += ["-map", "0:s?"]
            if attachments and is_mkv:
                cmd += ["-map", "0:t?"]
        else:
            cmd += ["-sn", "-dn"]
        if want_cover and not is_mkv:
            cmd += ["-map", "1:v:0"]
        cmd += (vargs if video_args is None else video_args) + vfilter
        cmd += (audio if audio_args is None else audio_args)
        if subs and keep_subs:
            cmd += subs_codec
        if want_cover:
            if is_mkv:
                idx = src_attachments if (subs and keep_subs and attachments) else 0
                idx = max(0, idx)
                cmd += ["-attach", cover_path,
                        f"-metadata:s:t:{idx}", f"mimetype={cover_mime}",
                        f"-metadata:s:t:{idx}", f"filename={cover_name}"]
            else:
                cmd += ["-c:v:1", "mjpeg", "-disposition:v:1", "attached_pic"]
        cmd += meta_args + tail
        variants.append(cmd)

    all_streams = ["-map", "0:V:0", "-map", "0:a?"]

    # 1) Everything: all audio tracks, soft subs, the source's fonts, the Cover Image.
    if cover_ok:
        add(all_streams, cover=True, subs=True, attachments=True)
    # 2) Drop the source's attachments (exotic or mistyped ones can refuse to remux).
    if cover_ok and is_mkv and keep_subs:
        add(all_streams, cover=True, subs=True, attachments=False)
    # 3) Drop subtitles too — covers subtitle codecs the target container refuses.
    if cover_ok and keep_subs:
        add(all_streams, cover=True, subs=False, attachments=False)
    # 4) Same streams, no cover.
    add(all_streams, cover=False, subs=True, attachments=True)
    if keep_subs:
        add(all_streams, cover=False, subs=False, attachments=False)
    # 5) Last resort: one video + one audio, re-encoded, no subs. Always muxable.
    add(["-map", "0:V:0", "-map", "0:a:0?"], cover=False, subs=False, attachments=False,
        audio_args=minimal_audio)
    # 6) If the rung asked for x265 or a hardware encoder, keep one plain-libx264 attempt at
    #    the very end so a driver hiccup or an odd resolution can't fail the rung outright.
    if encoder != "libx264":
        add(["-map", "0:V:0", "-map", "0:a:0?"], cover=False, subs=False, attachments=False,
            audio_args=minimal_audio,
            video_args=_video_encoder_args("libx264", enc, crf, budget, 8))

    return variants



async def _drain_stderr(stream, buf: List[str], limit: int = 40):
    while True:
        line = await stream.readline()
        if not line:
            break
        text = line.decode("utf-8", errors="ignore").rstrip()
        if text:
            buf.append(text)
            if len(buf) > limit:
                buf.pop(0)


async def _kill_on_cancel(proc, cancel_event: asyncio.Event):
    try:
        await cancel_event.wait()
        if proc.returncode is None:
            proc.kill()
    except asyncio.CancelledError:
        pass


async def _run_ffmpeg_with_progress(cmd: List[str], duration: int, status: StatusUpdater,
                                     header: str, cancel_event: asyncio.Event) -> Tuple[int, str]:
    """Runs one ffmpeg command, streaming `-progress pipe:1` key=value output into a live
    percentage bar. Returns (returncode, tail-of-stderr).

    stdout and stderr are drained by two concurrent readers on purpose: ffmpeg writes to
    both, and reading them serially deadlocks as soon as the unread pipe's OS buffer fills.
    """
    proc = await asyncio.create_subprocess_exec(
        *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
    err_buf: List[str] = []
    err_task = asyncio.create_task(_drain_stderr(proc.stderr, err_buf))
    kill_task = asyncio.create_task(_kill_on_cancel(proc, cancel_event))
    started = time.time()
    out_time = 0
    speed = ""
    fps = ""
    try:
        while True:
            raw = await proc.stdout.readline()
            if not raw:
                break
            line = raw.decode("utf-8", errors="ignore").strip()
            if "=" not in line:
                continue
            key, _, value = line.partition("=")
            if key == "out_time_us" or key == "out_time_ms":
                try:
                    micros = int(value)
                    # out_time_ms is, confusingly, also microseconds in ffmpeg's output.
                    out_time = micros // 1_000_000
                except ValueError:
                    pass
            elif key == "speed":
                speed = value.strip()
            elif key == "fps":
                fps = value.strip()
            elif key == "progress" and value.strip() == "end":
                break

            if duration > 0:
                pct = min(99.9, out_time * 100.0 / duration)
                elapsed = time.time() - started
                rate = out_time / elapsed if elapsed > 0 else 0
                eta = TimeFormatter(((duration - out_time) / rate) * 1000) if rate > 0 else "—"
                await status.set(
                    f"{header}\n\n"
                    f"`{progress_bar(pct)}` {pct:.1f}%\n"
                    f"» {TimeFormatter(out_time * 1000)} / {TimeFormatter(duration * 1000)}\n"
                    f"» Speed: {speed or '—'} | FPS: {fps or '—'} | ETA: {eta}"
                )
            else:
                await status.set(f"{header}\n\n» Encoded {TimeFormatter(out_time * 1000)} so far "
                                 f"(Speed: {speed or '—'})")
        try:
            await asyncio.wait_for(proc.wait(), timeout=Config.ENCODE_TIMEOUT)
        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()
            return -9, "encode timed out"
    finally:
        kill_task.cancel()
        try:
            await asyncio.wait_for(err_task, timeout=5)
        except Exception:
            err_task.cancel()
    return proc.returncode if proc.returncode is not None else -1, "\n".join(err_buf[-12:])


async def encode_rung(input_path: str, output_path: str, quality: str, source_height: int,
                       duration: int, meta: dict, cover_path: Optional[str], enc: dict,
                       status: StatusUpdater, header: str,
                       cancel_event: asyncio.Event, target_mb: int = 0,
                       audio_kbps: int = 0, audio_tracks: int = 1,
                       src_attachments: int = 0) -> Tuple[bool, str]:
    """Encodes ONE ladder rung, tagging metadata and attaching the cover in the same pass.

    Tries each variant from build_encode_variants() in order and stops at the first one that
    yields a non-empty output file, so a release with unmuxable subtitle tracks degrades to
    "same video, no subs" instead of failing the whole job.

    Size is *enforced*, not hoped for. CRF on its own gives no size guarantee — a grainy or
    high-motion source at CRF 23 can easily land at double what a flat-shaded one does. So the
    rung's MB target is converted into a -maxrate/-bufsize cap (capped CRF: quality still
    drives bit allocation, but the average can't exceed the cap), and if the result still
    overshoots, the rung is re-encoded at a higher CRF with a tightened cap. Two extra
    attempts is enough in practice because each one shrinks the file by roughly 15-20%."""
    if not FFMPEG:
        return False, "ffmpeg is not installed on this server."
    target_height = QUALITY_HEIGHT.get(quality, 0)
    if not target_height:
        return False, f"`{quality}` isn't a resolution I know how to encode to."

    # Lower rungs can carry a slightly higher CRF for the same perceived quality: the picture
    # is smaller on screen, so the same quantisation is less visible.
    base_crf = int(enc.get("crf", 23)) + RUNG_CRF_OFFSET.get(quality, 0)
    limit_bytes = int(target_mb * 1024 * 1024) if target_mb > 0 else 0
    last_err = ""

    for attempt in range(3):
        crf = max(14, min(35, base_crf + attempt * 2))
        # Each retry also tightens the hard cap, so a stubborn source can't creep over.
        eff_target = int(target_mb * (1.0 - 0.06 * attempt)) if target_mb > 0 else 0
        budget = compute_size_budget(eff_target, duration, audio_kbps, audio_tracks)
        variants = build_encode_variants(input_path, output_path, target_height, source_height,
                                          meta, cover_path, enc, crf=crf, budget=budget,
                                          src_attachments=src_attachments)
        retry_note = "" if attempt == 0 else f"  _(size retry {attempt}, CRF {crf})_"
        produced = False
        for idx, cmd in enumerate(variants, 1):
            if cancel_event.is_set():
                return False, "cancelled"
            await cleanup_files(output_path)
            note = retry_note if idx == 1 else f"{retry_note}  _(fallback {idx})_"
            rc, err = await _run_ffmpeg_with_progress(cmd, duration, status, header + note,
                                                      cancel_event)
            if cancel_event.is_set():
                await cleanup_files(output_path)
                return False, "cancelled"
            if rc == 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0:
                produced = True
                break
            last_err = err or f"ffmpeg exited with code {rc}"
            print(f"[encode] {quality} variant {idx}/{len(variants)} failed (rc={rc}): {last_err[:400]}")
        if not produced:
            break
        size = os.path.getsize(output_path)
        if not limit_bytes or size <= limit_bytes or attempt == 2:
            if limit_bytes and size > limit_bytes:
                print(f"[encode] {quality} finished at {humanbytes(size)}, "
                      f"just over the {target_mb} MB target — shipping it anyway.")
            return True, ""
        print(f"[encode] {quality} came out {humanbytes(size)} > {target_mb} MB target; "
              f"re-encoding at CRF {min(35, base_crf + (attempt + 1) * 2)}.")

    await cleanup_files(output_path)
    return False, last_err[-500:] or "unknown ffmpeg failure"



# ==================== TORRENT SUPPORT ====================
MAGNET_RE = re.compile(r'magnet:\?[^\s\'"<>]+', re.IGNORECASE)
TORRENT_URL_RE = re.compile(r'https?://[^\s\'"<>]+?\.torrent(?:\?[^\s\'"<>]*)?', re.IGNORECASE)

VIDEO_EXTS = {".mkv", ".mp4", ".avi", ".m4v", ".mov", ".webm", ".flv", ".wmv",
              ".ts", ".m2ts", ".mpg", ".mpeg", ".ogv", ".rmvb", ".3gp"}
# Junk that shows up in release torrents and must never be mistaken for the episode.
JUNK_NAME_HINTS = ("sample", "trailer", "preview", "ncop", "nced", "extras/")


def extract_torrent_links(text: Optional[str]) -> List[str]:
    """Pulls every magnet URI and direct .torrent URL out of a message, in the order they
    appear. Sending three magnets in one message queues three jobs."""
    if not text:
        return []
    found: List[str] = []
    for m in MAGNET_RE.finditer(text):
        link = m.group(0).rstrip('.,;)')
        if link not in found:
            found.append(link)
    for m in TORRENT_URL_RE.finditer(text):
        link = m.group(0).rstrip('.,;)')
        if link not in found:
            found.append(link)
    return found


def strip_torrent_links(text: Optional[str]) -> str:
    """The message text with the links removed — whatever's left is treated as the user's
    own hint (e.g. `S02E07`), which takes priority over the torrent's own naming."""
    if not text:
        return ""
    cleaned = MAGNET_RE.sub(" ", text)
    cleaned = TORRENT_URL_RE.sub(" ", cleaned)
    return re.sub(r'\s+', ' ', cleaned).strip()


def magnet_display_name(link: str) -> Optional[str]:
    """The `dn=` (display name) parameter of a magnet URI. Most trackers set it to the
    release name, which is usually enough to read Season/Episode off before downloading
    a single byte."""
    m = re.search(r'[?&]dn=([^&]+)', link, re.IGNORECASE)
    if not m:
        return None
    try:
        return unquote_plus(m.group(1))
    except Exception:
        return None


def is_torrent_document(message: Message) -> bool:
    if not message or not message.document:
        return False
    name = (message.document.file_name or "").lower()
    return name.endswith(".torrent") or message.document.mime_type == "application/x-bittorrent"



def bdecode(data: bytes):
    """Minimal bencode decoder — just enough to read a .torrent file's name and file list.

    Used by the aria2c path, which (unlike libtorrent) has no API for inspecting a torrent:
    we ask aria2c for the metadata only, decode it here to find the episode file's index,
    then tell aria2c to download exactly that one file with --select-file."""
    def parse(i: int):
        ch = data[i:i + 1]
        if ch == b'i':
            j = data.index(b'e', i)
            return int(data[i + 1:j]), j + 1
        if ch == b'l':
            i += 1
            out = []
            while data[i:i + 1] != b'e':
                val, i = parse(i)
                out.append(val)
            return out, i + 1
        if ch == b'd':
            i += 1
            out = {}
            while data[i:i + 1] != b'e':
                key, i = parse(i)
                val, i = parse(i)
                out[key] = val
            return out, i + 1
        j = data.index(b':', i)
        length = int(data[i:j])
        return data[j + 1:j + 1 + length], j + 1 + length

    value, _ = parse(0)
    return value


def read_torrent_metainfo(path: str) -> Tuple[str, List[Tuple[str, int]]]:
    """(torrent name, [(relative path, size in bytes), ...]) for a .torrent on disk.
    Single-file torrents come back as a one-entry list, so callers don't need to special-case
    them."""
    with open(path, "rb") as fh:
        meta = bdecode(fh.read())
    info = meta[b"info"]
    name = info[b"name"].decode("utf-8", errors="ignore")
    entries: List[Tuple[str, int]] = []
    if b"files" in info:
        for f in info[b"files"]:
            parts = [p.decode("utf-8", errors="ignore") for p in f[b"path"]]
            entries.append(("/".join(parts), int(f[b"length"])))
    else:
        entries.append((name, int(info[b"length"])))
    return name, entries



def pick_video_entry(entries: List[Tuple[str, int]]) -> Optional[int]:
    """Index of the file inside a torrent that is actually the episode.

    Season packs, NCOP/NCED creditless openings, and 30-second "sample" files all live in the
    same torrent as the episode, so picking "the first file" or "the last file" gets it wrong
    regularly. Rule used here: among files with a video extension, ignore anything whose path
    looks like a sample/extra, then take the LARGEST remaining one. If nothing has a video
    extension at all, fall back to the largest file overall so a mislabelled release still has
    a chance (ffprobe will reject it later if it really isn't video)."""
    if not entries:
        return None
    candidates = []
    for idx, (path, size) in enumerate(entries):
        lower = path.lower()
        if os.path.splitext(lower)[1] not in VIDEO_EXTS:
            continue
        if any(hint in lower for hint in JUNK_NAME_HINTS):
            continue
        candidates.append((size, idx))
    if not candidates:
        for idx, (path, size) in enumerate(entries):
            if os.path.splitext(path.lower())[1] in VIDEO_EXTS:
                candidates.append((size, idx))
    if not candidates:
        candidates = [(size, idx) for idx, (path, size) in enumerate(entries)]
    candidates.sort(reverse=True)
    return candidates[0][1]


def find_largest_video(root: str) -> Optional[str]:
    """Largest non-sample video file anywhere under `root`. Used after an aria2c download that
    (for whatever reason) produced more than the single file we selected."""
    best = None
    best_size = -1
    for dirpath, _dirnames, filenames in os.walk(root):
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            if os.path.splitext(fn.lower())[1] not in VIDEO_EXTS:
                continue
            if any(hint in full.lower().replace("\\", "/") for hint in JUNK_NAME_HINTS):
                continue
            try:
                size = os.path.getsize(full)
            except OSError:
                continue
            if size > best_size:
                best, best_size = full, size
    return best


def enough_disk_space(path: str, needed: int) -> Tuple[bool, int]:
    try:
        free = shutil.disk_usage(path).free
    except Exception:
        return True, 0
    return free >= needed, free



# ---------- libtorrent backend ----------
DHT_BOOTSTRAP_NODES = ("router.bittorrent.com:6881,dht.transmissionbt.com:6881,"
                        "router.utorrent.com:6881,dht.libtorrent.org:25401")


def _lt_session():
    """A libtorrent session with DHT + all trackers enabled. Constructed per job and thrown
    away afterwards, so nothing keeps seeding in the background between jobs.

    Bootstrap nodes go in through the `dht_bootstrap_nodes` setting rather than
    `add_dht_router()`: the latter is deprecated in libtorrent 2.x and prints a warning on
    every job. libtorrent 1.x has no such setting, so there we fall back to add_dht_router —
    detected by reading the setting back rather than by version-sniffing."""
    settings = {
        "listen_interfaces": "0.0.0.0:6881,[::]:6881",
        "enable_dht": True,
        "enable_lsd": True,
        "enable_upnp": True,
        "enable_natpmp": True,
        "announce_to_all_trackers": True,
        "announce_to_all_tiers": True,
        "dht_bootstrap_nodes": DHT_BOOTSTRAP_NODES,
        "alert_mask": 0,
    }
    legacy = {k: v for k, v in settings.items() if k != "dht_bootstrap_nodes"}
    ses = None
    for cfg in (settings, legacy):
        try:
            ses = lt.session(cfg)
            break
        except Exception:
            continue
    if ses is None:
        ses = lt.session()
        for cfg in (settings, legacy):
            try:
                ses.apply_settings(cfg)
                break
            except Exception:
                continue

    bootstrapped = False
    try:
        bootstrapped = "router.bittorrent.com" in (ses.get_settings().get("dht_bootstrap_nodes") or "")
    except Exception:
        pass
    if not bootstrapped:
        for host, port in (("router.bittorrent.com", 6881), ("dht.transmissionbt.com", 6881),
                           ("router.utorrent.com", 6881), ("dht.libtorrent.org", 25401)):
            try:
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore")
                    ses.add_dht_router(host, port)
            except Exception:
                pass
    return ses


def _lt_add_torrent(ses, source: str, is_local: bool, save_dir: str):
    if is_local:
        info = lt.torrent_info(source)
        params = {"ti": info, "save_path": save_dir}
        return ses.add_torrent(params)
    atp = lt.parse_magnet_uri(source)
    if isinstance(atp, dict):
        atp["save_path"] = save_dir
        return ses.add_torrent(atp)
    atp.save_path = save_dir
    return ses.add_torrent(atp)


def _lt_has_metadata(handle) -> bool:
    try:
        return bool(handle.status().has_metadata)
    except Exception:
        try:
            return bool(handle.has_metadata())
        except Exception:
            return False


def _lt_info(handle):
    for attr in ("torrent_file", "get_torrent_info"):
        fn = getattr(handle, attr, None)
        if not fn:
            continue
        try:
            info = fn()
            if info:
                return info
        except Exception:
            continue
    return None



async def _torrent_via_libtorrent(source: str, is_local: bool, save_dir: str,
                                   status: StatusUpdater, cancel_event: asyncio.Event,
                                   precheck) -> dict:
    """Downloads exactly one file (the episode) out of a torrent using libtorrent.

    Two-phase on purpose. Phase 1 fetches only the torrent's metadata, which is enough to run
    `precheck` — so a magnet whose Season/Episode can't be worked out is rejected before any
    content is transferred. Phase 2 sets every other file's priority to 0 and downloads just
    the selected one, then the torrent is removed from the session so nothing seeds."""
    ses = _lt_session()
    handle = None
    try:
        try:
            handle = _lt_add_torrent(ses, source, is_local, save_dir)
        except Exception as e:
            return {"ok": False, "error": f"couldn't read that torrent/magnet ({e})"}

        # ---- Phase 1: metadata only ----
        deadline = time.time() + Config.TORRENT_METADATA_TIMEOUT
        while not _lt_has_metadata(handle):
            if cancel_event.is_set():
                return {"ok": False, "error": "cancelled"}
            if time.time() > deadline:
                return {"ok": False, "error": (f"no peers answered within "
                                                f"{Config.TORRENT_METADATA_TIMEOUT}s, so I never got the "
                                                f"torrent's metadata. The magnet may be dead.")}
            st = handle.status()
            await status.set(
                f"🧲 **Fetching torrent metadata…**\n\n"
                f"» Peers: {getattr(st, 'num_peers', 0)} | Seeds: {getattr(st, 'num_seeds', 0)}\n"
                f"» Waiting up to {Config.TORRENT_METADATA_TIMEOUT}s for the swarm to answer."
            )
            await asyncio.sleep(1.5)

        info = _lt_info(handle)
        if info is None:
            return {"ok": False, "error": "libtorrent reported metadata but wouldn't hand it over"}
        fs = info.files()
        entries = [(fs.file_path(i), int(fs.file_size(i))) for i in range(fs.num_files())]
        name = info.name()
        total_size = int(info.total_size())

        err = await precheck(name, entries, total_size)
        if err:
            return {"ok": False, "error": err}

        idx = pick_video_entry(entries)
        if idx is None:
            return {"ok": False, "error": "this torrent doesn't contain any files"}
        rel_path, wanted_size = entries[idx]
        if os.path.splitext(rel_path.lower())[1] not in VIDEO_EXTS:
            return {"ok": False, "error": (f"the biggest file in this torrent isn't a video "
                                            f"(`{os.path.basename(rel_path)[:60]}`)")}

        # ---- Phase 2: download only the selected file ----
        try:
            handle.prioritize_files([0] * len(entries))
            handle.file_priority(idx, 7)
        except Exception as e:
            print(f"[torrent] file-priority selection failed, downloading everything: {e}")

        try:
            handle.resume()
        except Exception:
            pass

        started = time.time()
        last_done = -1
        last_change = time.time()
        while True:
            if cancel_event.is_set():
                return {"ok": False, "error": "cancelled"}
            st = handle.status()
            done = int(getattr(st, "total_wanted_done", 0))
            wanted = int(getattr(st, "total_wanted", 0)) or wanted_size
            progress = float(getattr(st, "progress", 0.0)) * 100
            rate = int(getattr(st, "download_rate", 0))
            if done != last_done:
                last_done = done
                last_change = time.time()
            elif time.time() - last_change > Config.TORRENT_STALL_TIMEOUT:
                return {"ok": False, "error": (f"download stalled — no new data for "
                                                f"{Config.TORRENT_STALL_TIMEOUT // 60} minutes.")}

            if progress >= 99.999 or (wanted and done >= wanted) or bool(getattr(st, "is_seeding", False)):
                break

            eta = TimeFormatter(((wanted - done) / rate) * 1000) if rate > 0 and wanted else "—"
            await status.set(
                f"🧲 **Downloading torrent…**\n`{os.path.basename(rel_path)[:55]}`\n\n"
                f"`{progress_bar(progress)}` {progress:.1f}%\n"
                f"» {humanbytes(done)} / {humanbytes(wanted)}\n"
                f"» Speed: {humanbytes(rate)}/s | ETA: {eta}\n"
                f"» Peers: {getattr(st, 'num_peers', 0)} | Seeds: {getattr(st, 'num_seeds', 0)}"
            )
            await asyncio.sleep(2)

        video_path = os.path.join(save_dir, rel_path.replace("/", os.sep))
        if not os.path.exists(video_path):
            found = find_largest_video(save_dir)
            if not found:
                return {"ok": False, "error": "the torrent finished but I can't find the video on disk"}
            video_path = found
        elapsed = time.time() - started
        print(f"[torrent] libtorrent finished '{name}' in {TimeFormatter(elapsed * 1000)}")
        return {"ok": True, "video_path": video_path, "name": name, "entries": entries}
    finally:
        if handle is not None:
            try:
                ses.remove_torrent(handle)   # stop seeding immediately
            except Exception:
                pass
        del ses



# ---------- aria2c backend ----------
ARIA_PCT_RE = re.compile(r'\((\d{1,3})%\)')
ARIA_SIZE_RE = re.compile(r'(\S+?)/(\S+?)\(\d{1,3}%\)')
ARIA_DL_RE = re.compile(r'DL:(\S+?)[\s\]]')
ARIA_ETA_RE = re.compile(r'ETA:(\S+?)[\s\]]')
ARIA_PEERS_RE = re.compile(r'CN:(\d+)')
ARIA_SEEDS_RE = re.compile(r'SD:(\d+)')

ARIA_COMMON = [
    "--seed-time=0", "--seed-ratio=0.0", "--bt-remove-unselected-file=true",
    "--summary-interval=2", "--console-log-level=warn", "--enable-color=false",
    "--file-allocation=none", "--check-certificate=false", "--allow-overwrite=true",
    "--auto-file-renaming=false", "--continue=true", "--max-connection-per-server=16",
    "--bt-max-peers=200", "--bt-request-peer-speed-limit=50M", "--split=16",
    "--min-split-size=1M", "--bt-tracker-connect-timeout=30",
    "--enable-dht=true", "--enable-peer-exchange=true", "--bt-enable-lpd=true",
]


async def _run_aria2(cmd: List[str], status: StatusUpdater, header: str,
                     cancel_event: asyncio.Event, timeout: int) -> Tuple[int, str]:
    """Runs aria2c and turns its console summary lines into the same progress bar the
    libtorrent path shows. aria2c writes both progress and errors to stdout, so one reader
    is enough here (stderr is merged into it)."""
    proc = await asyncio.create_subprocess_exec(
        *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT)
    kill_task = asyncio.create_task(_kill_on_cancel(proc, cancel_event))
    tail: List[str] = []
    deadline = time.time() + timeout
    try:
        while True:
            try:
                raw = await asyncio.wait_for(proc.stdout.readline(), timeout=30)
            except asyncio.TimeoutError:
                if time.time() > deadline:
                    proc.kill()
                    return -9, "aria2c timed out"
                continue
            if not raw:
                break
            line = raw.decode("utf-8", errors="ignore").strip()
            if not line:
                continue
            if "%)" in line and line.startswith("["):
                pct_m = ARIA_PCT_RE.search(line)
                pct = float(pct_m.group(1)) if pct_m else 0.0
                size_m = ARIA_SIZE_RE.search(line)
                sizes = f"{size_m.group(1)} / {size_m.group(2)}" if size_m else "—"
                dl_m = ARIA_DL_RE.search(line + " ")
                eta_m = ARIA_ETA_RE.search(line + " ")
                peers_m = ARIA_PEERS_RE.search(line)
                seeds_m = ARIA_SEEDS_RE.search(line)
                await status.set(
                    f"{header}\n\n"
                    f"`{progress_bar(pct)}` {pct:.0f}%\n"
                    f"» {sizes}\n"
                    f"» Speed: {dl_m.group(1) if dl_m else '—'}/s | ETA: {eta_m.group(1) if eta_m else '—'}\n"
                    f"» Peers: {peers_m.group(1) if peers_m else 0} | Seeds: {seeds_m.group(1) if seeds_m else 0}"
                )
            else:
                tail.append(line)
                if len(tail) > 40:
                    tail.pop(0)
        try:
            await asyncio.wait_for(proc.wait(), timeout=60)
        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()
    finally:
        kill_task.cancel()
    return (proc.returncode if proc.returncode is not None else -1), "\n".join(tail[-12:])


async def _aria2_fetch_metainfo(source: str, is_local: bool, work_dir: str,
                                status: StatusUpdater, header: str,
                                cancel_event: asyncio.Event) -> Tuple[Optional[str], str]:
    """Returns (path_to_dot_torrent, error). For magnets this runs aria2c in metadata-only
    mode so we can read the file list *before* pulling any content."""
    if is_local:
        return source, ""
    if source.lower().startswith("magnet:"):
        await status.set(f"{header}\n\n» Fetching torrent metadata from the DHT…", force=True)
        before = set(glob.glob(os.path.join(work_dir, "*.torrent")))
        cmd = [ARIA2C, "--bt-metadata-only=true", "--bt-save-metadata=true",
               f"--dir={work_dir}"] + ARIA_COMMON + [source]
        rc, tail = await _run_aria2(cmd, status, header, cancel_event,
                                   Config.TORRENT_METADATA_TIMEOUT)
        if cancel_event.is_set():
            return None, "cancelled"
        found = sorted(set(glob.glob(os.path.join(work_dir, "*.torrent"))) - before,
                       key=os.path.getmtime, reverse=True)
        if not found:
            found = sorted(glob.glob(os.path.join(work_dir, "*.torrent")),
                           key=os.path.getmtime, reverse=True)
        if not found:
            return None, f"couldn't get torrent metadata (no peers?){chr(10) + tail if tail else ''}"
        return found[0], ""
    # plain http(s) .torrent url
    await status.set(f"{header}\n\n» Downloading the .torrent file…", force=True)
    dest = os.path.join(work_dir, "source.torrent")
    cmd = [ARIA2C, f"--dir={work_dir}", "--out=source.torrent",
           "--console-log-level=warn", "--enable-color=false", "--allow-overwrite=true",
           "--check-certificate=false", "--max-tries=3"] + [source]
    rc, tail = await _run_aria2(cmd, status, header, cancel_event, 300)
    if not os.path.exists(dest):
        return None, f"couldn't download that .torrent file{chr(10) + tail if tail else ''}"
    return dest, ""


async def _torrent_via_aria2(source: str, is_local: bool, save_dir: str,
                             status: StatusUpdater, cancel_event: asyncio.Event,
                             precheck) -> dict:
    """aria2c fallback backend. Same contract as _torrent_via_libtorrent."""
    header = "🧲 **Torrent**"
    work_dir = os.path.join("torrents", uuid.uuid4().hex[:8])
    os.makedirs(work_dir, exist_ok=True)
    try:
        tpath, err = await _aria2_fetch_metainfo(source, is_local, work_dir,
                                                 status, header, cancel_event)
        if not tpath:
            return {"ok": False, "error": err or "metadata failed"}

        name, entries = read_torrent_metainfo(tpath)
        if not entries:
            return {"ok": False, "error": "that torrent has no readable file list"}
        total_size = sum(sz for _, sz in entries)

        pre_err = await precheck(name, entries, total_size)
        if pre_err:
            return {"ok": False, "error": pre_err}

        idx = pick_video_entry(entries)
        if idx is None:
            return {"ok": False, "error": "no video file found inside that torrent"}
        rel_path, size = entries[idx]
        if os.path.splitext(rel_path)[1].lower() not in VIDEO_EXTS:
            return {"ok": False, "error": f"the biggest file (`{os.path.basename(rel_path)}`) isn't a video"}

        ok_space, free = enough_disk_space(save_dir, size)
        if not ok_space:
            return {"ok": False, "error": f"not enough disk space — need ~{humanbytes(int(size * Config.DISK_HEADROOM_FACTOR))}, free {humanbytes(free)}"}

        await status.set(
            f"{header}\n\n**{name[:60]}**\n» Selected: `{os.path.basename(rel_path)}`\n"
            f"» Size: {humanbytes(size)}\n» Connecting to peers…", force=True)

        started = time.time()
        # aria2's --select-file is 1-based over the torrent's file order
        cmd = [ARIA2C, f"--dir={save_dir}", f"--select-file={idx + 1}"] + ARIA_COMMON + [tpath]
        rc, tail = await _run_aria2(cmd, status, header, cancel_event,
                                    Config.TORRENT_STALL_TIMEOUT)
        if cancel_event.is_set():
            return {"ok": False, "error": "cancelled"}

        video_path = os.path.join(save_dir, rel_path.replace("/", os.sep))
        if not os.path.exists(video_path) or os.path.getsize(video_path) < size * 0.98:
            found = find_largest_video(save_dir)
            if not found:
                return {"ok": False, "error": f"torrent download failed (aria2c rc={rc}){chr(10) + tail if tail else ''}"}
            video_path = found
        print(f"[torrent] aria2c finished '{name}' in {TimeFormatter((time.time() - started) * 1000)}")
        return {"ok": True, "video_path": video_path, "name": name, "entries": entries}
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)


async def resolve_and_download_torrent(source: str, is_local: bool, save_dir: str,
                                       status: StatusUpdater, cancel_event: asyncio.Event,
                                       precheck) -> dict:
    """Picks whichever torrent backend this machine actually has."""
    backend = torrent_backend()
    if backend == "libtorrent":
        return await _torrent_via_libtorrent(source, is_local, save_dir, status,
                                             cancel_event, precheck)
    if backend == "aria2c":
        return await _torrent_via_aria2(source, is_local, save_dir, status,
                                        cancel_event, precheck)
    return {"ok": False, "error": "no torrent backend installed on the server — "
                                  "`pip install libtorrent` or install `aria2c`. Run /torrent_check."}

# ==================== FILE PREPARATION ====================
async def download_and_prepare_file(message: Message, batch: dict, season: int, episode: int,
                                     quality_idx: int, status_msg=None, file_label: str = "") -> Optional[dict]:
    """
    Downloads, tags metadata, and attaches a thumbnail + cover image for one file.

    Cleanup guarantee: every path this call writes to disk (download, metadata copy,
    thumb, cover) is tracked in `created_paths` and wiped before returning None on any
    failure, so nothing lingers between files.
    """
    if message.document:
        file_name = message.document.file_name or "file"
        file_size = message.document.file_size
        media_type = "document"
        duration = 0
    elif message.video:
        file_name = message.video.file_name or "video.mp4"
        file_size = message.video.file_size
        media_type = "video"
        duration = message.video.duration or 0
    elif message.audio:
        file_name = message.audio.file_name or "audio.mp3"
        file_size = message.audio.file_size
        media_type = "audio"
        duration = message.audio.duration or 0
    else:
        return None

    if file_size and file_size > Config.MAX_FILE_SIZE:
        if status_msg:
            try:
                await status_msg.edit_text(
                    f"❌ `{file_name[:50]}` is {humanbytes(file_size)}, which exceeds the "
                    f"{humanbytes(Config.MAX_FILE_SIZE)} limit. Skipped."
                )
            except Exception:
                pass
        return None

    base_name = os.path.splitext(file_name)[0]
    original_ext = os.path.splitext(file_name)[1] or (".mp4" if media_type == "video" else ".mp3")

    mediapref = batch.get("mediatype", "document")
    send_as = mediapref if mediapref in ("document", "video", "audio") else "document"
    display_ext = original_ext

    rename_fmt = batch.get("autorename_format") or "{filename} S{season}E{episode} {quality}"
    new_filename = apply_per_file_format(rename_fmt, base_name, season, episode, quality_idx, file_size, duration)
    new_filename = sanitize_filename(new_filename)
    final_filename = new_filename + display_ext
    download_path = f"downloads/{message.chat.id}_{message.id}_{int(time.time())}{original_ext}"
    created_paths: List[str] = [download_path]

    try:
        # ---------- DOWNLOAD ----------
        start_time = time.time()
        try:
            file_path = await message.download(
                file_name=download_path,
                progress=progress_for_pyrogram,
                progress_args=(f"📥 Downloading {file_label}".strip(), status_msg, start_time),
            )
        except Exception as e:
            print(f"Download failed for `{file_name}`: {e}")
            raise

        if not file_path or not os.path.exists(file_path):
            print(f"Download incomplete for `{file_name}` (no file on disk after download() returned)")
            raise RuntimeError("download_incomplete")

        # ---------- COVER IMAGE (full quality, embedded into the file + used as Telegram's
        # native video poster via send_video(cover=...) when supported) ----------
        cover_path = None
        cover_ref = as_channel_ref(batch.get("cover_image"))
        if cover_ref:
            candidate_cover_path = f"temp/{message.chat.id}_{message.id}_cover.jpg"
            created_paths.append(candidate_cover_path)
            downloaded_cover = await download_channel_image(cover_ref["chat_id"], cover_ref["message_id"], candidate_cover_path)
            if downloaded_cover:
                cover_path = await process_cover(downloaded_cover)
            if not cover_path:
                print(f"Cover image fetch failed for batch `{batch.get('name')}` — continuing without it.")

        # ---------- METADATA (+ cover embed) ----------
        output_path = file_path
        meta = batch.get("metadata", {})
        if meta.get("enabled", True) or cover_path:
            if status_msg:
                try:
                    await status_msg.edit_text(f"⚙️ Adding metadata {file_label}\n`{file_name[:50]}`".strip())
                except Exception:
                    pass
            metadata_path = f"temp/{message.chat.id}_{message.id}_meta{original_ext}"
            created_paths.append(metadata_path)
            try:
                effective_meta = meta if meta.get("enabled", True) else {}
                output_path = await add_metadata(file_path, metadata_path, effective_meta,
                                                  cover_path=cover_path, media_type=media_type)
                if output_path != file_path:
                    await cleanup_files(file_path)
            except Exception as e:
                print(f"Metadata error for `{file_name}`: {e}")
                output_path = file_path
        if output_path not in created_paths:
            created_paths.append(output_path)

        # ---------- THUMBNAIL (small preview shown in the chat, per Telegram's hard limits) ----------
        thumb_path = None
        thumb_ref = as_channel_ref(batch.get("thumbnail"))
        if thumb_ref:
            candidate_thumb_path = f"temp/{message.chat.id}_{message.id}_thumb.jpg"
            created_paths.append(candidate_thumb_path)
            downloaded = await download_channel_image(thumb_ref["chat_id"], thumb_ref["message_id"], candidate_thumb_path)
            if downloaded:
                thumb_path = await process_thumbnail(downloaded)
            else:
                print(f"Thumbnail fetch failed for batch `{batch.get('name')}` — continuing without it.")

        # ---------- CAPTION ----------
        caption_fmt = batch.get("autocaption_format") or "{filename}"
        caption = apply_bold_tags(
            apply_per_file_format(caption_fmt, base_name, season, episode, quality_idx, file_size, duration)
        )

        return {
            "output_path": output_path,
            "download_path": download_path,
            "final_filename": final_filename,
            "thumb_path": thumb_path,
            "cover_path": cover_path,
            "send_as": send_as,
            "caption": caption,
            "duration": duration,
        }

    except Exception as e:
        print(f"download_and_prepare_file aborted for `{file_name}`: {e}")
        await cleanup_files(*created_paths)
        return None

def prepare_local_upload(path: str, batch: dict, base_name: str, season: int, episode: int,
                         quality_idx: int, thumb_path: Optional[str], cover_path: Optional[str],
                         duration: int) -> dict:
    """Builds the same `prepared` dict that download_and_prepare_file() returns, but for a file
    the ENCODER produced instead of one Telegram sent us.

    Differences that matter:
      • no download step — the bytes are already on disk;
      • no metadata pass — metadata + cover were baked in during the encode, so there is never
        a second full-size copy of a multi-GB file on disk;
      • `download_path` is deliberately absent. The torrent pipeline deletes rung files itself,
        in a very specific order (1080p is kept alive until the 720p rung has been uploaded),
        so nothing else is allowed to clean them up.
    """
    ext = os.path.splitext(path)[1] or ".mkv"
    try:
        file_size = os.path.getsize(path)
    except OSError:
        file_size = 0

    mediapref = batch.get("mediatype", "document")
    send_as = mediapref if mediapref in ("document", "video", "audio") else "document"

    rename_fmt = batch.get("autorename_format") or "{filename} S{season}E{episode} {quality}"
    final_filename = sanitize_filename(
        apply_per_file_format(rename_fmt, base_name, season, episode, quality_idx, file_size, duration)
    ) + ext

    caption_fmt = batch.get("autocaption_format") or "{filename}"
    caption = apply_bold_tags(
        apply_per_file_format(caption_fmt, base_name, season, episode, quality_idx, file_size, duration)
    )

    return {
        "output_path": path,
        "final_filename": final_filename,
        "thumb_path": thumb_path,
        "cover_path": cover_path,
        "send_as": send_as,
        "caption": caption,
        "duration": duration,
    }

async def send_prepared_file(target_chat_id, prepared: dict, status_msg=None, file_label: str = "",
                             progress_args=None) -> Optional[Message]:
    """`progress_args` lets the torrent pipeline route upload progress into its own single
    status message (see StatusUpdater.upload_progress_args); every other caller keeps the
    original behaviour of writing into `status_msg`."""
    send_as = prepared["send_as"]
    start_time = time.time()
    common = dict(
        chat_id=target_chat_id,
        caption=prepared["caption"][:1024] if prepared["caption"] else None,
        thumb=prepared["thumb_path"],
        file_name=prepared["final_filename"],
        progress=progress_for_pyrogram,
        progress_args=progress_args or (f"📤 Uploading {file_label}".strip(), status_msg, start_time),
    )
    try:
        if send_as == "video":
            video_kwargs = dict(common)
            # Only pass `cover` if we actually have one AND the installed Pyrogram build
            # supports it — otherwise send_video() would raise TypeError on an unexpected
            # keyword argument. This is Telegram's own native full-quality video poster
            # (Bot API 8.3+), separate from the small `thumb=` preview and from the
            # ffmpeg-embedded attached_pic stream inside the file itself.
            if prepared.get("cover_path") and SEND_VIDEO_SUPPORTS_COVER:
                video_kwargs["cover"] = prepared["cover_path"]
            return await app.send_video(video=prepared["output_path"], duration=prepared["duration"], **video_kwargs)
        elif send_as == "audio":
            return await app.send_audio(audio=prepared["output_path"], duration=prepared["duration"], **common)
        else:
            return await app.send_document(document=prepared["output_path"], **common)
    except Exception as e:
        print(f"Send failed as {send_as}, falling back to document: {e}")
        try:
            return await app.send_document(
                document=prepared["output_path"],
                chat_id=target_chat_id,
                caption=prepared["caption"][:1024] if prepared["caption"] else None,
                thumb=prepared["thumb_path"],
                file_name=prepared["final_filename"],
            )
        except Exception as e2:
            print(f"Fallback document send also failed: {e2}")
            return None

# ==================== QUEUE WORKER ====================
async def _send_post(chat_id: int, thumbnail_ref: Optional[dict], caption: str,
                      reply_markup: Optional[InlineKeyboardMarkup] = None) -> bool:
    """Sends a Top/Bottom-style post: a photo+caption if a thumbnail is configured (copied
    straight from the Thumb Channel message, no re-download needed), else plain text."""
    try:
        ref = as_channel_ref(thumbnail_ref)
        if ref:
            await app.copy_message(
                chat_id=chat_id,
                from_chat_id=ref["chat_id"],
                message_id=ref["message_id"],
                caption=caption[:1024],
                reply_markup=reply_markup,
            )
        else:
            # No thumbnail -> plain text, which allows 4096 rather than a caption's 1024.
            await app.send_message(chat_id, caption[:TG_TEXT_LIMIT], reply_markup=reply_markup)
        return True
    except Exception as e:
        print(f"Post send failed to {chat_id}: {e}")
        return False


async def process_job(job: dict):
    # Torrent jobs run a completely different pipeline (download -> encode ladder -> post),
    # so they branch out here before any of the Telegram-file logic below.
    if job.get("type") == "torrent":
        await process_torrent_job(job)
        return

    batch = await db.get_batch(job["batch_id"])
    requested_by = job.get("requested_by")

    if not batch:
        if requested_by:
            try:
                await app.send_message(requested_by, "❌ This batch no longer exists (it may have been deleted). Job skipped.")
            except Exception:
                pass
        return

    files = job["files"]
    total = len(files)
    thumbnail = batch.get("thumbnail")

    sub_channel = batch.get("sub_channel")
    main_channels = get_main_channels(batch)
    settings = await db.get_settings()
    backup_channel = settings.get("backup_channel")

    has_sub = bool(sub_channel and sub_channel.get("id"))
    has_backup = bool(backup_channel and backup_channel.get("id"))
    posting_mode = has_sub and has_backup
    if not posting_mode:
        target_chat_id = job.get("chat_id", requested_by)
        if not has_sub:
            reason = "⚠️ No Sub Channel linked yet — set one via /edit_batch → 📢 Sub Channel."
        else:
            reason = "⚠️ No Backup Channel set yet — an admin needs to set one via /bot_settings before channel posting works."
        status_msg = None
        if requested_by:
            try:
                status_msg = await app.send_message(
                    requested_by,
                    f"🔄 **Processing batch `{batch['name']}`** — {total} file(s)\n{reason}\nSending here instead."
                )
            except Exception:
                status_msg = None
        completed, failed = await _process_files_to_targets(
            batch, files, [target_chat_id], status_msg=status_msg, requested_by=requested_by,
        )
        if status_msg:
            try:
                await status_msg.delete()
            except Exception:
                pass
        if requested_by:
            summary = f"✅ **Batch `{batch['name']}` done!** {completed} file(s) sent here"
            if failed:
                summary += f", {failed} failed"
            summary += "."
            try:
                await app.send_message(requested_by, summary)
            except Exception:
                pass
        return

    # Upload target order matters here: the FIRST id in this list is where the actual
    # file bytes get uploaded from disk; every subsequent id gets the file via
    # copy_message() (server-side copy, no re-upload) inside _process_files_to_targets.
    # Backup Channel first, then Sub Channel copies from it — per the requested setup of
    # "upload once to Backup, forward/copy from there to Sub" instead of uploading twice.
    mirror_targets = [backup_channel["id"], sub_channel["id"]]

    pseason, pepisode, pquality = compute_post_placeholders(files)
    top_caption = fill_post_format(batch.get("top_post_format"), batch["name"], pseason, pepisode, pquality)
    bottom_post = batch.get("bottom_post")

    status_msg = None
    if requested_by:
        dest_names = f"{sub_channel.get('title', 'Sub Channel')} + {backup_channel.get('title', 'Backup Channel')}"
        try:
            status_msg = await app.send_message(
                requested_by,
                f"🔄 **Processing batch `{batch['name']}`** — {total} file(s)\n📢 Posting to **{dest_names}**"
            )
        except Exception:
            status_msg = None
    for cid in mirror_targets:
        ok = await _send_post(cid, thumbnail, top_caption)
        if not ok and requested_by:
            try:
                await app.send_message(requested_by, f"❌ Couldn't post the Top Post to `{cid}`. Check my admin rights there.")
            except Exception:
                pass

    completed, failed = await _process_files_to_targets(
        batch, files, mirror_targets, status_msg=status_msg, requested_by=requested_by,
    )

    if bottom_post:
        for cid in mirror_targets:
            ok = await send_bottom_post(cid, bottom_post)
            if not ok and requested_by:
                try:
                    await app.send_message(requested_by, f"❌ Couldn't copy the Bottom Post to `{cid}`. Check my admin rights there.")
                except Exception:
                    pass

    if main_channels:
        join_link = await get_channel_join_link(app, sub_channel["id"])
        button = None
        if join_link:
            button = InlineKeyboardMarkup([[InlineKeyboardButton("🍁DOWNLOAD🍁", url=join_link)]])
        for mc in main_channels:
            ok = await _send_post(mc["id"], thumbnail, top_caption, reply_markup=button)
            if not ok and requested_by:
                try:
                    await app.send_message(requested_by, f"❌ Couldn't post to Main Channel **{mc.get('title')}**. Check my admin rights there.")
                except Exception:
                    pass
            if bottom_post:
                ok2 = await send_bottom_post(mc["id"], bottom_post)
                if not ok2 and requested_by:
                    try:
                        await app.send_message(requested_by, f"❌ Couldn't copy the Bottom Post to Main Channel **{mc.get('title')}**.")
                    except Exception:
                        pass

    if status_msg:
        try:
            await status_msg.delete()
        except Exception:
            pass
    if requested_by:
        summary = f"✅ **Batch `{batch['name']}` done!** {completed} file(s) posted to **{sub_channel.get('title')}**"
        if backup_channel and backup_channel.get("id"):
            summary += f" + **{backup_channel.get('title')}**"
        if main_channels:
            names = ", ".join(c.get("title", "Channel") for c in main_channels)
            summary += f", hub post sent to **{names}**"
        if failed:
            summary += f", {failed} failed"
        summary += "."
        try:
            await app.send_message(requested_by, summary)
        except Exception:
            pass


async def _process_files_to_targets(batch: dict, files: List[dict], target_chat_ids: List[int],
                                     status_msg=None, requested_by: Optional[int] = None) -> Tuple[int, int]:
    """
    Sends each prepared file to every chat in target_chat_ids.

    IMPORTANT: only the FIRST chat in target_chat_ids gets an actual upload (the local
    file is read from disk and pushed to Telegram there). Every other chat in the list
    receives the file via copy_message() from that first upload — a server-side copy
    that doesn't touch local disk or re-upload any bytes. This is what makes "Sub Channel
    + Backup Channel" a single upload instead of two.

    If the primary upload fails outright, or a copy_message() to a specific mirror target
    fails (e.g. bot isn't admin there), that individual target falls back to a direct
    re-upload so the file still has the best chance of reaching it.
    """
    total = len(files)
    completed = 0
    failed = 0

    if not target_chat_ids:
        return 0, 0

    primary_target = target_chat_ids[0]
    mirror_targets = target_chat_ids[1:]

    for idx, f in enumerate(files, 1):
        message = f["message"]
        label = f"({idx}/{total})" if total > 1 else ""
        fname = get_msg_fname(message)
        prepared = None
        try:
            if status_msg:
                try:
                    await status_msg.edit_text(f"🔄 **File {idx}/{total}**\n`{fname[:50]}`\n\n📥 Downloading...")
                except Exception:
                    pass
            prepared = await download_and_prepare_file(
                message, batch, f["season"], f["episode"], f["quality"],
                status_msg=status_msg, file_label=label,
            )

            if prepared:
                if status_msg:
                    try:
                        await status_msg.edit_text(
                            f"🔄 **File {idx}/{total}**\n`{prepared['final_filename'][:50]}`\n\n📤 Posting..."
                        )
                    except Exception:
                        pass

                any_sent = False

                # ---- Primary upload (actual bytes go out here) ----
                primary_msg = await send_prepared_file(primary_target, prepared, status_msg=status_msg, file_label=label)
                if primary_msg:
                    any_sent = True
                elif requested_by:
                    try:
                        await app.send_message(
                            requested_by,
                            f"❌ Failed to send `{prepared['final_filename'][:50]}` to `{primary_target}`. "
                            f"Check I'm still an admin there with permission to post files."
                        )
                    except Exception:
                        pass

                # ---- Mirror targets: copy from the primary upload, no re-upload ----
                for cid in mirror_targets:
                    sent_ok = False
                    if primary_msg:
                        try:
                            await app.copy_message(chat_id=cid, from_chat_id=primary_target, message_id=primary_msg.id)
                            sent_ok = True
                        except Exception as e:
                            print(f"copy_message to {cid} failed, falling back to re-upload: {e}")
                    if not sent_ok:
                        # Either the primary upload itself failed, or the copy failed
                        # (e.g. bot not admin in cid) — fall back to a direct re-upload
                        # for just this target so the file still has a chance to arrive.
                        sent = await send_prepared_file(cid, prepared, status_msg=status_msg, file_label=label)
                        sent_ok = bool(sent)
                    if sent_ok:
                        any_sent = True
                    elif requested_by:
                        try:
                            await app.send_message(
                                requested_by,
                                f"❌ Failed to send `{prepared['final_filename'][:50]}` to `{cid}`. "
                                f"Check I'm still an admin there with permission to post files."
                            )
                        except Exception:
                            pass
                if any_sent:
                    completed += 1
                else:
                    failed += 1
            else:
                failed += 1
                if requested_by:
                    try:
                        await app.send_message(requested_by, f"❌ Failed to process `{fname[:50]}`. Temp files cleaned up.")
                    except Exception:
                        pass
        except Exception as e:
            failed += 1
            print(f"Error processing file in job: {e}")
        finally:
            if prepared:
                await cleanup_files(
                    prepared.get("download_path"),
                    prepared.get("output_path"),
                    prepared.get("thumb_path"),
                    prepared.get("cover_path"),
                )
    return completed, failed

# ==================== TORRENT JOB: download -> 1080p -> 720p -> 480p -> post ====================
async def process_torrent_job(job: dict):
    """The torrent pipeline, in exactly the order it was asked for:

      1. download the video out of the torrent;
      2. encode it to the FIRST (highest) ladder rung — 1080p by default — renaming it,
         tagging metadata and embedding the cover in that same pass;
      3. upload that rung to the **Backup Channel**;
      4. keep the 1080p on disk, and delete the ORIGINAL torrent download now;
      5. encode 720p **from the 1080p**, upload it, and only then delete the 1080p;
      6. encode 480p **from the 720p**, upload it, then delete every remaining file;
      7. copy the whole set into the **Sub Channel** — in **ascending** quality order
         (480p → 720p → 1080p) regardless of the order they were encoded/uploaded to the
         Backup Channel in — and make the **Main Channel(s)** post exactly the way the
         normal file flow does.

    Step 7 works on files that no longer exist locally because the Sub Channel copies come
    from the Backup Channel messages via copy_message() — a server-side copy.
    """
    job_id = job.get("job_id") or new_job_id()
    requested_by = job.get("requested_by")
    display = job.get("display") or "torrent"
    info = active_jobs.get(job_id)
    if info is None:
        register_job(job_id, requested_by or 0, display)
        info = active_jobs[job_id]
    cancel_event = info["cancel"]
    info["running"] = True

    work_dir = os.path.join("downloads", f"t_{job_id}")
    status = StatusUpdater(None)
    on_disk: List[str] = []          # everything we must delete before returning
    uploaded: List[Tuple[str, int]] = []   # (quality label, Backup Channel message id)

    async def notify(text: str):
        if requested_by:
            try:
                await app.send_message(requested_by, text)
            except Exception:
                pass

    try:
        batch = await db.get_batch(job["batch_id"])
        if not batch:
            await notify("❌ The batch for this torrent job no longer exists. Job skipped.")
            return
        settings = await db.get_settings()
        enc = get_encode_settings(settings)
        backup_channel = settings.get("backup_channel")
        sub_channel = batch.get("sub_channel")
        main_channels = get_main_channels(batch)
        # ---- Hard requirements, checked before a single byte is downloaded ----
        if not (backup_channel and backup_channel.get("id")):
            await notify("❌ No **Backup Channel** set — an admin needs to set one via /bot_settings "
                          "before torrent jobs can run (every encoded rung is uploaded there first).")
            return
        if not FFMPEG:
            await notify("❌ **ffmpeg isn't installed on this server**, so I can't encode anything. "
                          "Install it (`apt install ffmpeg`) and try again. Run /torrent_check to verify.")
            return
        if not torrent_backend():
            await notify("❌ **No torrent backend installed.** Install one of:\n"
                          "• `pip install libtorrent` (recommended)\n• `apt install aria2`\n\n"
                          "Then run /torrent_check.")
            return
        ladder = [q for q in enc["ladder"] if q in QUALITY_HEIGHT]
        if not ladder:
            await notify("❌ The encode ladder is empty. Enable at least one rung in /encode_settings.")
            return

        os.makedirs(work_dir, exist_ok=True)
        first_msg = None
        if requested_by:
            try:
                first_msg = await app.send_message(
                    requested_by,
                    f"🧲 **Torrent job started**\n`{display[:70]}`\n\n"
                    f"Ladder: **{' → '.join(ladder)}** • CRF {enc['crf']} • {enc['preset']}\n"
                    f"Backend: `{torrent_backend()}`\n\n» Resolving metadata…",
                    reply_markup=kb_job_cancel(job_id),
                )
            except Exception:
                first_msg = None
        status = StatusUpdater(first_msg, reply_markup=kb_job_cancel(job_id))

        # ---- Season/Episode gate, run on the torrent's METADATA (no content downloaded yet) ----
        detected = {"season": 0, "episode": 0, "base": ""}

        async def precheck(name: str, entries: List[Tuple[str, int]], total_size: int) -> Optional[str]:
            if Config.MAX_TORRENT_SIZE and total_size > Config.MAX_TORRENT_SIZE:
                return (f"that torrent is {humanbytes(total_size)}, over the "
                        f"{humanbytes(Config.MAX_TORRENT_SIZE)} limit (MAX_TORRENT_SIZE_GB in .env)")
            idx = pick_video_entry(entries)
            vname = os.path.basename(entries[idx][0]) if idx is not None else ""
            season, episode = extract_season_episode_from_sources(job.get("hint"), vname, name)
            if not season or not episode:
                missing = "Season" if not season else "Episode"
                return (f"couldn't detect the **{missing}** for this torrent.\n\n"
                        f"» Torrent: `{name[:60]}`\n» File: `{vname[:60]}`\n\n"
                        f"Send the link again with the info in the same message, e.g.\n"
                        f"`S02E07 <your magnet link>`")
            detected["season"], detected["episode"] = season, episode
            detected["base"] = os.path.splitext(vname)[0] or name
            return None
        # ---------- STEP 1: download the video out of the torrent ----------
        result = await resolve_and_download_torrent(
            job["source"], bool(job.get("is_local")), work_dir, status, cancel_event, precheck)

        if job.get("is_local") and job.get("cleanup_source"):
            await cleanup_files(job["source"])   # the .torrent file the user uploaded

        if not result.get("ok"):
            err = result.get("error", "unknown error")
            if err == "cancelled" or cancel_event.is_set():
                await status.done(f"🛑 **Job cancelled.**\n`{display[:60]}`")
            else:
                await status.done(f"❌ **Torrent failed**\n`{display[:60]}`\n\n{err}")
            return

        source_path = result["video_path"]
        on_disk.append(source_path)
        season, episode = detected["season"], detected["episode"]
        base_name = detected["base"] or os.path.splitext(os.path.basename(source_path))[0]

        # ---------- probe the source so we know its real height + duration ----------
        await status.set(f"🔍 **Probing** `{os.path.basename(source_path)[:50]}`…", force=True)
        probe = await probe_media(source_path)
        duration = probe["duration"]
        source_height = probe["height"]
        src_size = os.path.getsize(source_path) if os.path.exists(source_path) else 0

        # Don't burn hours encoding a "1080p" rung out of a 720p source — that rung would be
        # a byte-for-byte duplicate of the 720p one at a bigger filename.
        effective_ladder = list(ladder)
        dropped = []
        if enc["skip_upscale"] and source_height:
            keep = [q for q in effective_ladder if QUALITY_HEIGHT[q] <= source_height]
            dropped = [q for q in effective_ladder if q not in keep]
            if keep:
                effective_ladder = keep
            else:
                # Source is smaller than every configured rung — keep only the lowest one and
                # let it pass through unscaled rather than producing nothing at all.
                effective_ladder = [effective_ladder[-1]]
                dropped = [q for q in ladder if q not in effective_ladder]

        pseason, pepisode, pquality = compute_ladder_placeholders(season, episode, effective_ladder)
        top_caption = fill_post_format(batch.get("top_post_format"), batch["name"], pseason, pepisode, pquality)
        bottom_post = batch.get("bottom_post")
        thumbnail = batch.get("thumbnail")
        # ---------- fetch the batch's thumbnail + cover ONCE, reused by every rung ----------
        thumb_path = None
        thumb_ref = as_channel_ref(thumbnail)
        if thumb_ref:
            cand = os.path.join(work_dir, "thumb.jpg")
            got = await download_channel_image(thumb_ref["chat_id"], thumb_ref["message_id"], cand)
            if got:
                thumb_path = await process_thumbnail(got)
            if thumb_path:
                on_disk.append(thumb_path)
            else:
                print(f"[torrent] thumbnail fetch failed for batch `{batch.get('name')}`")

        cover_path = None
        cover_ref = as_channel_ref(batch.get("cover_image"))
        if cover_ref:
            cand = os.path.join(work_dir, "cover.jpg")
            got = await download_channel_image(cover_ref["chat_id"], cover_ref["message_id"], cand)
            if got:
                cover_path = await process_cover(got)
            if cover_path:
                on_disk.append(cover_path)
            else:
                print(f"[torrent] cover fetch failed for batch `{batch.get('name')}`")

        meta = batch.get("metadata", {}) or {}
        effective_meta = meta if meta.get("enabled", True) else {}

        note_dropped = f"\n⚠️ Skipped (source is only {source_height}p): {', '.join(dropped)}" if dropped else ""
        await status.set(
            f"✅ **Downloaded** `{os.path.basename(source_path)[:50]}`\n"
            f"» {humanbytes(src_size)} • {source_height or '?'}p • {TimeFormatter(duration * 1000)}\n"
            f"» Audio tracks: {probe['audio']} • Subs: {'yes' if probe['has_subs'] else 'no'}\n\n"
            f"🎬 Encoding ladder: **{' → '.join(effective_ladder)}**{note_dropped}",
            force=True,
        )

        # ---------- Top Post goes into the Backup Channel first, so the rungs land under it ----------
        if not await _send_post(backup_channel["id"], thumbnail, top_caption):
            await notify(f"❌ Couldn't post the Top Post to the Backup Channel `{backup_channel['id']}`. "
                          f"Check my admin rights there. Continuing with the files anyway.")
        # ---------- STEPS 2-6: the ladder. Each rung is encoded FROM the previous rung's
        # output, and the file it was encoded from is deleted only AFTER this rung has been
        # uploaded — which is exactly the ordering that was asked for. This part stays
        # high -> low (1080p -> 720p -> 480p) no matter what, because each rung is encoded
        # FROM the previous rung's output. Only the later Sub Channel copy order changes. ----------
        current_source = source_path
        current_height = source_height
        # Tracked per rung because rung 2 encodes from rung 1's output, not from the original:
        # by then the file has one attachment (the cover we just embedded) and possibly
        # re-encoded audio, and both numbers feed the next rung's size budget and cover index.
        cur_attachments = probe["attachments"]
        cur_audio_kbps = probe["audio_kbps"]
        cur_audio_tracks = probe["audio"]
        failures: List[Tuple[str, str]] = []

        for i, q in enumerate(effective_ladder, 1):
            if cancel_event.is_set():
                break

            out_path = os.path.join(
                work_dir, f"{sanitize_filename(base_name)[:70]}.{q}.{enc['container']}")
            try:
                need = os.path.getsize(current_source)
            except OSError:
                need = 0
            ok_space, free = enough_disk_space(work_dir, need)
            if not ok_space:
                failures.append((q, f"not enough free disk space ({humanbytes(free)} left)"))
                break

            target_mb = int(enc.get("targets", {}).get(q, DEFAULT_TARGET_MB.get(q, 0)) or 0)
            header = (f"🎬 **Encoding {q}** ({i}/{len(effective_ladder)})\n"
                      f"`{base_name[:45]}`\n_source: {current_height or '?'}p_"
                      + (f" • target ≤ {target_mb} MB" if target_mb else ""))
            ok, err = await encode_rung(current_source, out_path, q, current_height, duration,
                                        effective_meta, cover_path, enc, status, header,
                                        cancel_event, target_mb=target_mb,
                                        audio_kbps=cur_audio_kbps, audio_tracks=cur_audio_tracks,
                                        src_attachments=cur_attachments)
            if cancel_event.is_set():
                break
            if not ok:
                failures.append((q, err))
                await notify(f"❌ **{q} encode failed** for `{base_name[:45]}`\n\n`{err[:300]}`\n\n"
                              f"_Continuing with the remaining rungs._")
                continue

            on_disk.append(out_path)
            prepared = prepare_local_upload(out_path, batch, base_name, season, episode,
                                            QUALITY_INDEX.get(q, -1), thumb_path, cover_path, duration)
            await status.set(f"📤 **Uploading {q}** ({i}/{len(effective_ladder)})\n"
                             f"`{prepared['final_filename'][:55]}`\n"
                             f"» {humanbytes(os.path.getsize(out_path))}", force=True)
            sent = await send_prepared_file(
                backup_channel["id"], prepared, file_label=q,
                progress_args=status.upload_progress_args(f"📤 Uploading **{q}**"),
            )
            if sent:
                uploaded.append((q, sent.id))
            else:
                failures.append((q, "upload to the Backup Channel failed"))
                await notify(f"❌ Couldn't upload the **{q}** file to the Backup Channel. "
                              f"Check I'm still an admin there with permission to post files.")
            # The delete that makes the whole chain fit on one disk: the previous file (the
            # original torrent download for the first rung, the 1080p for the second, the 720p
            # for the third) goes away only now, after this rung is safely on Telegram.
            if current_source != out_path:
                await cleanup_files(current_source)
                if current_source in on_disk:
                    on_disk.remove(current_source)
                print(f"[torrent] deleted {os.path.basename(current_source)} "
                      f"(the {q} upload is done)")

            current_source = out_path
            next_h = QUALITY_HEIGHT[q]
            if enc["skip_upscale"] and current_height and current_height <= next_h:
                next_h = current_height   # the scale filter was skipped, so height is unchanged
            current_height = next_h
            # Re-probe so the next rung budgets against what it will actually read.
            try:
                nxt = await probe_media(out_path)
                cur_attachments = nxt["attachments"]
                cur_audio_kbps = nxt["audio_kbps"]
                cur_audio_tracks = nxt["audio"]
            except Exception as e:
                print(f"[torrent] re-probe of the {q} output failed ({e}); "
                      f"reusing the previous stream counts.")

        # ---------- STEP 6b: nothing stays on the server ----------
        await cleanup_files(*on_disk)
        on_disk = []
        shutil.rmtree(work_dir, ignore_errors=True)

        if cancel_event.is_set():
            await status.done(
                f"🛑 **Job cancelled** — every temporary file has been deleted.\n"
                f"`{display[:60]}`\n\n"
                + (f"Already uploaded to the Backup Channel: {', '.join(q for q, _ in uploaded)}"
                   if uploaded else "Nothing was uploaded.")
            )
            return

        if not uploaded:
            detail = "\n".join(f"• **{q}** — {e[:120]}" for q, e in failures) or "unknown failure"
            await status.done(f"❌ **Nothing could be produced** for `{display[:50]}`.\n\n{detail}")
            return

        # ---------- Bottom Post into the Backup Channel, closing that run out ----------
        if bottom_post and not await send_bottom_post(backup_channel["id"], bottom_post):
            await notify("❌ Couldn't copy the Bottom Post to the Backup Channel.")
        # ---------- STEP 7: forward into the Sub Channel, then post in the Main Channel(s),
        # exactly the way the normal file flow does it. The local files are already gone, which
        # is fine: these are server-side copies of the Backup Channel messages.
        #
        # `uploaded` is in the ENCODE/UPLOAD order (high -> low: 1080p, 720p, 480p — required
        # so each rung can be encoded from the previous one). The Sub Channel copy, however,
        # is requested in ASCENDING quality order (480p -> 720p -> 1080p), so it's re-sorted
        # here just for this step. This does NOT touch `uploaded` itself — the job summary,
        # cancel-time listing, etc. below still read it in its original high->low order. ----------
        await status.set(f"📢 **Posting** {len(uploaded)} file(s) to the channels…", force=True)

        # Ascending quality (480p -> 720p -> 1080p) for the Sub Channel / fallback-DM copy only.
        sub_post_order = sorted(uploaded, key=lambda x: QUALITY_HEIGHT.get(x[0], 0))

        if sub_channel and sub_channel.get("id"):
            sub_id = sub_channel["id"]
            if not await _send_post(sub_id, thumbnail, top_caption):
                await notify(f"❌ Couldn't post the Top Post to **{sub_channel.get('title')}**. "
                              f"Check my admin rights there.")
            for q, mid in sub_post_order:
                try:
                    await app.copy_message(chat_id=sub_id, from_chat_id=backup_channel["id"], message_id=mid)
                except Exception as e:
                    print(f"[torrent] copy of the {q} file to the Sub Channel failed: {e}")
                    await notify(f"❌ Couldn't copy the **{q}** file into **{sub_channel.get('title')}** ({e}). "
                                  f"It's still safe in the Backup Channel.")
                await asyncio.sleep(0.5)   # gentle on Telegram's per-chat rate limit
            if bottom_post and not await send_bottom_post(sub_id, bottom_post):
                await notify(f"❌ Couldn't copy the Bottom Post to **{sub_channel.get('title')}**.")
        else:
            await notify("⚠️ No **Sub Channel** linked for this batch, so the encoded files are only in the "
                          "Backup Channel. Set one via /edit_batch → 📢 Sub Channel. Sending you copies here.")
            for q, mid in sub_post_order:
                try:
                    await app.copy_message(chat_id=requested_by, from_chat_id=backup_channel["id"], message_id=mid)
                except Exception:
                    pass

        if main_channels and sub_channel and sub_channel.get("id"):
            join_link = await get_channel_join_link(app, sub_channel["id"])
            button = None
            if join_link:
                button = InlineKeyboardMarkup([[InlineKeyboardButton("🍁DOWNLOAD🍁", url=join_link)]])
            for mc in main_channels:
                if not await _send_post(mc["id"], thumbnail, top_caption, reply_markup=button):
                    await notify(f"❌ Couldn't post to Main Channel **{mc.get('title')}**. "
                                  f"Check my admin rights there.")
                if bottom_post and not await send_bottom_post(mc["id"], bottom_post):
                    await notify(f"❌ Couldn't copy the Bottom Post to Main Channel **{mc.get('title')}**.")
        elif main_channels:
            await notify("⚠️ Skipped the Main Channel post — it needs a Sub Channel to link to.")
        summary = (f"✅ **Torrent job done** — `{batch['name']}` S{season:02d}E{episode:02d}\n\n"
                   f"📤 Uploaded: **{', '.join(q for q, _ in uploaded)}**\n"
                   f"🗄️ Backup: **{backup_channel.get('title')}**")
        if sub_channel and sub_channel.get("id"):
            summary += f"\n📢 Sub: **{sub_channel.get('title')}**"
        if main_channels and sub_channel and sub_channel.get("id"):
            summary += f"\n🏠 Main: **{', '.join(c.get('title', 'Channel') for c in main_channels)}**"
        if failures:
            summary += "\n\n⚠️ " + "; ".join(f"{q}: {e[:80]}" for q, e in failures)
        summary += "\n\n🧹 Server disk is clean."
        await status.done(summary)

    except Exception as e:
        print(f"[torrent] job {job_id} crashed: {e}")
        import traceback
        traceback.print_exc()
        try:
            await status.done(f"❌ **Torrent job crashed:** `{str(e)[:300]}`\n\nTemporary files were cleaned up.")
        except Exception:
            pass
        await notify(f"❌ Torrent job failed unexpectedly: `{str(e)[:200]}`")
    finally:
        # Belt and braces: whatever happened above (crash, cancel, early return), nothing is
        # left behind on disk and the job leaves the cancellable registry.
        await cleanup_files(*on_disk)
        shutil.rmtree(work_dir, ignore_errors=True)
        active_jobs.pop(job_id, None)


async def queue_worker():
    print("👷 Queue Worker: Started")
    while True:
        job = await file_queue.get()
        try:
            await process_job(job)
        except Exception as e:
            print(f"⚠️ Job processing error: {e}")
        file_queue.task_done()

# ==================== COMMAND HANDLERS ====================
NON_INPUT_COMMANDS = ["start", "help", "new_batch", "edit_batch", "ssequence", "esequence", "sequence_mode",
                       "cancel", "bot_settings", "delete_channel", "auto_post", "stop_auto_post",
                       "cancel_job", "encode_settings", "torrent_check"]


@app.on_message(filters.command("start") & filters.private & staff_filter)
async def start_cmd(client, message: Message):
    await db.add_user(message.from_user.id)
    await reply_long(
        message,
        "**👋 Welcome to the Auto-Rename & Posting Bot!**\n\n"
        "Set up a **batch** once per anime — thumbnail, cover image, autorename format, caption format, "
        "metadata, output type, a **Sub Channel**, this batch's own **Main Channel(s)**, a Top Post template, "
        "and a Bottom Post — and I'll remember it. Send a file (or sequence of files) after that and I'll "
        "rename it, tag metadata, embed the cover, then post it:\n\n"
        "1️⃣ **Top Post** (thumbnail + your template) → Backup Channel + Sub Channel\n"
        "2️⃣ the renamed file(s), in order → Backup Channel (uploaded once), then copied to Sub Channel\n"
        "3️⃣ **Bottom Post** (copied exactly as-is, no forward tag) → Backup Channel + Sub Channel\n"
        "4️⃣ Top Post + a redirect button to THIS batch's Sub Channel (using the channel's original primary "
        "invite link) → this batch's own Main Channel(s)\n"
        "5️⃣ Bottom Post → Main Channel(s)\n\n"
        "⚠️ **Backup Channel** and a **Thumb/Cover Channel** must be set (via /bot_settings, admins only) "
        "before posting/thumbnails work — they're bot-wide. Main Channel(s) is set **per batch**, and a "
        "batch can have more than one.\n\n"
        "**🧲 Torrent → multi-quality encode (new):**\n"
        "Turn on /auto_post, pick a batch, then just **send a magnet link or a `.torrent`** (file or URL). "
        "I'll:\n"
        "• download the video from the torrent,\n"
        "• encode **1080p** first, rename it, tag metadata, embed the cover, and upload it to the "
        "**Backup Channel**,\n"
        "• delete the original torrent file (keeping the 1080p),\n"
        "• encode **720p from the 1080p**, upload it, then delete the 1080p,\n"
        "• encode **480p from the 720p**, upload it, then delete everything from the server,\n"
        "• finally copy the whole set into the **Sub Channel** — in **480p → 720p → 1080p** order — and "
        "post to the **Main Channel(s)** as usual.\n\n"
        "Season/Episode still have to be detectable — from the torrent name, or just type it in the same "
        "message: `S02E07 magnet:?xt=...`. Quality is *not* detected: the ladder decides it.\n"
        "Rungs, codec, CRF, preset, tune, bit depth, audio handling, container and the **per-rung "
        "size targets** are all configurable in /encode_settings — each rung is hard-capped to its "
        "target MB (1080p ≤ 250, 720p ≈ 150, 480p ≈ 90 by default) and re-encoded at a higher CRF "
        "if it overshoots. "
        "Use /cancel_job to abort a running download/encode, and /torrent_check to see what's "
        "installed and how fast this server can encode.\n\n"
        "**Batch management:**\n"
        "• /new_batch — create a new batch\n"
        "• /edit_batch — edit or delete an existing batch\n\n"
        "**Channel registry:**\n"
        "• Post `/register` inside a channel (as admin) to register it, or add one by link from the "
        "batch/settings menus.\n"
        "• /delete_channel — remove a registered channel from the registry (auto-unlinks it from any "
        "batch/setting that was using it)\n\n"
        "**Anime Names:** a batch can have multiple — add or remove them individually from "
        "🔤 Anime Names in the batch editor. A file matches if ANY of a batch's names appears in its "
        "filename (case-insensitive, and `.`/`_`/`-` are treated the same as spaces).\n\n"
        "**Auto Post Mode:** skip Anime Names matching entirely and route every file you send to one "
        "chosen batch until you turn it off:\n"
        "• /auto_post — pick a batch from a button list\n"
        "• /stop_auto_post — turn it off, back to normal Anime Names matching\n"
        "Season/Episode/Quality detection still applies in Auto Post Mode — only the name-matching step "
        "is skipped. Torrent links are **only** accepted while Auto Post Mode is on, since a magnet has no "
        "filename to match a batch with.\n\n"
        "**Thumbnail vs Cover Image:**\n"
        "• 🖼️ Thumbnail — the small preview shown in the Telegram chat/list (Telegram limits this to a "
        "small size no matter the source).\n"
        "• 🎨 Cover Image — Telegram's full-quality video poster (when supported by the installed Pyrogram "
        "build) plus embedded into the video file itself at full quality (like album art), independent of "
        "Telegram's small preview limit.\n"
        "Both are stored by forwarding your photo into the Thumb/Cover Channel and re-downloaded fresh "
        "at processing time.\n\n"
        "**Bold text with `<...>`:** in the Autocaption Format and Top Post Format, wrap anything in "
        "`<angle brackets>` to render it **bold** — e.g. `<{filename}>` sends the filename in bold. "
        "(In the Autorename Format the brackets are just stripped, since filenames can't be bold.)\n\n"
        "**Detecting Season / Episode / Quality:**\n"
        "I check each filename for Season, then Episode, then Quality — in that order. If any of "
        "them can't be detected, I **stop immediately** and tell you exactly which one is missing, "
        "instead of guessing or checking the rest. Nothing gets queued until the filename gives me all three.\n\n"
        "**Sequence mode (multiple files, sorted order):**\n"
        "• /ssequence — start collecting files\n"
        "• /esequence — finish, choose sort mode, review order, then add to queue\n"
        "• /sequence_mode [1|2|3] — view/set your default sort mode\n\n"
        "Just send a file directly (outside sequence mode) any time and I'll auto-identify its batch and queue it.\n\n"
        "Use /cancel any time to abort whatever I'm currently asking you for."
    )


@app.on_message(filters.command("help") & filters.private & staff_filter)
async def help_cmd(client, message: Message):
    await start_cmd(client, message)


@app.on_message(filters.command("cancel") & filters.private & staff_filter)
async def cancel_cmd(client, message: Message):
    uid = message.from_user.id
    had_state = uid in conversation_state
    conversation_state.pop(uid, None)
    if uid in sequence_sessions:
        sequence_sessions.pop(uid, None)
        had_state = True
    await message.reply_text("✅ Cancelled." if had_state else "Nothing to cancel.")

@app.on_message(filters.command("cancel_job") & filters.private & staff_filter)
async def cancel_job_cmd(client, message: Message):
    """Aborts a running torrent/encode job. The cancel Event is polled by the torrent loop and
    kills the live ffmpeg process, so a multi-hour encode stops within a second or two and its
    partial files are deleted."""
    uid = message.from_user.id
    mine = {jid: i for jid, i in active_jobs.items() if i["user"] == uid}
    if len(message.command) > 1:
        jid = message.command[1].strip()
        info = active_jobs.get(jid)
        if not info:
            await message.reply_text(f"❌ No active job with id `{jid}`.")
            return
        if info["user"] != uid and not is_admin(uid):
            await message.reply_text("❌ That job belongs to someone else.")
            return
        info["cancel"].set()
        await message.reply_text(f"🛑 Cancelling `{jid}` — it'll stop within a moment and clean up after itself.")
        return
    if not mine:
        await message.reply_text("ℹ️ You have no running torrent/encode jobs.\n\n"
                                  "_Queued-but-not-started jobs can't be cancelled — they'll report their own "
                                  "cancel button once they begin._")
        return
    n = cancel_jobs_for_user(uid)
    lines = "\n".join(f"• `{jid}` — {i['desc'][:50]}" for jid, i in mine.items())
    await message.reply_text(f"🛑 **Cancelling {n} job(s):**\n{lines}\n\nAll temporary files will be deleted.")


@app.on_message(filters.command("torrent_check") & filters.private & staff_filter)
async def torrent_check_cmd(client, message: Message):
    backend = torrent_backend()
    lines = ["🔧 **Torrent / encode dependencies**\n"]
    lines.append(f"{'✅' if lt else '❌'} libtorrent — {'available' if lt else 'not installed (`pip install libtorrent`)'}")
    lines.append(f"{'✅' if ARIA2C else '❌'} aria2c — {ARIA2C or 'not installed (`apt install aria2`)'}")
    lines.append(f"{'✅' if FFMPEG else '❌'} ffmpeg — {FFMPEG or 'not installed (`apt install ffmpeg`)'}")
    lines.append(f"{'✅' if FFPROBE else '❌'} ffprobe — {FFPROBE or 'not installed (ships with ffmpeg)'}")
    lines.append("")
    if backend and FFMPEG:
        lines.append(f"**Torrent jobs are ready.** Backend in use: `{backend}`.")
    elif not backend:
        lines.append("⚠️ **No torrent backend** — magnet/.torrent links can't be downloaded. "
                      "Install libtorrent or aria2c.")
    if not FFMPEG:
        lines.append("⚠️ **No ffmpeg** — nothing can be encoded or tagged.")
    try:
        total, used, free = shutil.disk_usage(os.path.abspath("downloads"))
        lines.append(f"\n💾 Disk: {humanbytes(free)} free of {humanbytes(total)}")
    except Exception:
        pass
    lines.append(f"📦 Max torrent size: {humanbytes(Config.MAX_TORRENT_SIZE)} "
                  f"(headroom factor {Config.DISK_HEADROOM_FACTOR}×)")

    # ---- encoder horsepower: the single biggest factor in how long a job takes ----
    probe_encoder_caps()
    cores = cpu_count()
    lines.append(f"\n🧮 Usable CPU cores: **{cores}**")
    hw = ENCODER_CAPS.get("hw")
    hw_hevc = ENCODER_CAPS.get("hw_hevc")
    if hw or hw_hevc:
        lines.append(f"⚡ Hardware encoder: `{hw or '—'}` (H.264), `{hw_hevc or '—'}` (HEVC) — "
                      f"selectable as **Codec: hw** in /encode_settings")
    else:
        lines.append("🐢 No working hardware encoder — encoding speed is bound by core count. "
                      f"With {cores} core(s), expect roughly {cores * 16}–{cores * 26} fps at 1080p on "
                      "the `faster` preset; a 24-minute episode is about "
                      f"{max(1, round(24 * 60 * 24 / max(1, cores * 21)) // 60)} minute(s) per rung.")
    lines.append(f"🎨 libx265: {'yes' if ENCODER_CAPS.get('x265') else 'no'} • "
                  f"x264 10-bit: {'yes' if ENCODER_CAPS.get('x264_10bit') else 'no'}")
    await message.reply_text("\n".join(lines))

def encode_settings_text(enc: dict) -> str:
    encoder, codec_label = resolve_codec(enc)
    hw_note = ""
    if enc.get("codec") == "hw" and encoder == "libx264":
        hw_note = "\n_⚠️ No working hardware encoder was found on this server, so x264 is used instead._"
    elif enc.get("codec") == "x265" and encoder == "libx264":
        hw_note = "\n_⚠️ This ffmpeg build has no libx265, so x264 is used instead._"
    return (
        "🎬 **Encode Settings** (bot-wide, used by torrent jobs)\n\n"
        f"**Ladder:** {' → '.join(enc['ladder']) if enc['ladder'] else '_none — jobs will refuse to run_'}\n"
        "_Each rung is encoded from the previous one (1080p from the torrent, 720p from the 1080p, "
        "480p from the 720p), which is far faster than re-encoding the source three times. Backup Channel "
        "receives them in that same high→low order; the Sub Channel copy is re-ordered to low→high "
        "(480p → 720p → 1080p) afterward._\n\n"
        f"**Codec:** {codec_label}{hw_note}\n"
        f"**CRF:** {enc['crf']} — lower is bigger/better; 20–26 is the sane range. Lower rungs "
        f"automatically get +1/+2 on top of this.\n"
        f"**Preset:** {enc['preset']} — with the size targets below doing the compressing, slower "
        f"presets mostly just cost time; raise it only if this server has cores to spare\n"
        f"**Tune:** {enc.get('tune', 'animation')} — `animation` is what makes anime compress well\n"
        f"**Bit depth:** {enc.get('bit_depth', 8)}-bit"
        f"{' — smaller files, but many phones cannot hardware-decode 10-bit H.264' if enc.get('bit_depth') == 10 else ' — universally playable'}\n"
        f"**Size targets:** {targets_summary(enc)} (MB)\n"
        "_Each rung is hard-capped to its target with maxrate/bufsize, and if it still overshoots "
        "it is re-encoded at a higher CRF — so the numbers above are ceilings, not wishes._\n"
        f"**Audio:** {'copy every track (keeps dual audio)' if enc['audio'] == 'copy' else ('auto — copied unless it would eat the size budget, then AAC' if enc['audio'] == 'auto' else 're-encode to AAC 128k stereo')}\n"
        f"**Container:** .{enc['container']} — mkv keeps multi-audio, soft subs and font attachments\n"
        f"**Subtitles:** {'copied into the output' if enc['keep_subs'] else 'dropped'}\n"
        f"**Skip upscaling:** {'on — a 720p source never gets a 1080p rung' if enc['skip_upscale'] else 'off — every rung is always produced'}\n\n"
        "Metadata, thumbnail and cover come from the **batch**, not from here."
    )


@app.on_message(filters.command("encode_settings") & filters.private & staff_filter)
async def encode_settings_cmd(client, message: Message):
    if not is_admin(message.from_user.id):
        return  # moderators can't change how the server encodes; silently ignore
    enc = await db.get_encode()
    await message.reply_text(encode_settings_text(enc), reply_markup=kb_encode_menu(enc))


@app.on_message(filters.command("new_batch") & filters.private & staff_filter)
async def new_batch_cmd(client, message: Message):
    conversation_state[message.from_user.id] = {"action": "new_batch_name"}
    await message.reply_text(
        "**📁 New Batch**\n\nSend me the name for this batch (e.g. the anime's name).\nUse /cancel to abort."
    )


@app.on_message(filters.command("edit_batch") & filters.private & staff_filter)
async def edit_batch_cmd(client, message: Message):
    batches = await db.list_batches()
    if not batches:
        await message.reply_text("📭 No batches yet. Use /new_batch to create one.")
        return
    await message.reply_text("**📁 Your Batches**\n\nTap a batch to edit or delete it:", reply_markup=kb_batches_list(batches))


@app.on_message(filters.command("sequence_mode") & filters.private & staff_filter)
async def sequence_mode_cmd(client, message: Message):
    uid = message.from_user.id
    await db.add_user(uid)
    MODES = {1: "Season → Quality → Episode", 2: "Season → Episode → Quality", 3: "Quality → Season → Episode"}
    if len(message.command) == 1:
        current = await db.get_sequence_mode(uid)
        await message.reply_text(
            f"🔄 **Current Sequence Mode:** `{current}` — {MODES[current]}\n\n"
            "**Available modes:**\n• 1: Season → Quality → Episode\n• 2: Season → Episode → Quality\n"
            "• 3: Quality → Season → Episode\n\nUse `/sequence_mode [1|2|3]` to change."
        )
        return
    try:
        mode = int(message.command[1])
        assert mode in (1, 2, 3)
    except (ValueError, AssertionError):
        await message.reply_text("❌ Use 1, 2, or 3.")
        return
    await db.set_sequence_mode(uid, mode)
    await message.reply_text(f"✅ Sequence mode set to **{mode}** — {MODES[mode]}")


@app.on_message(filters.command("ssequence") & filters.private & staff_filter)
async def ssequence_cmd(client, message: Message):
    uid = message.from_user.id
    if uid in sequence_sessions and sequence_sessions[uid].get("active"):
        await message.reply_text("⚠️ You're already collecting files for a sequence. Use /esequence to finish, or /cancel to abort.")
        return
    sequence_sessions[uid] = {"active": True, "batch_id": None, "files": []}
    await message.reply_text(
        "🔄 **Sequence mode started!**\n\nSend me all the files for this batch of episodes. "
        "They'll be saved (not processed) until you run /esequence.\n\n"
        "If a file's Season, Episode, or Quality can't be detected, I'll stop and tell you which one — "
        "that file won't be added until it's fixed.\n\nUse /cancel to abort."
    )


@app.on_message(filters.command("esequence") & filters.private & staff_filter)
async def esequence_cmd(client, message: Message):
    uid = message.from_user.id
    session = sequence_sessions.get(uid)
    if not session or not session.get("active"):
        await message.reply_text("❌ You're not in sequence mode. Start with /ssequence first.")
        return
    session["active"] = False
    files = session["files"]
    if not files:
        sequence_sessions.pop(uid, None)
        await message.reply_text("⚠️ No files were saved. Sequence cancelled.")
        return
    await message.reply_text(f"📁 **{len(files)} file(s) saved.**\n\nChoose a sort mode:", reply_markup=kb_sequence_sort(uid))


@app.on_message(filters.command("auto_post") & filters.private & staff_filter)
async def auto_post_cmd(client, message: Message):
    batches = await db.list_batches()
    if not batches:
        await message.reply_text("📭 No batches yet. Use /new_batch to create one.")
        return
    uid = message.from_user.id
    current = auto_post_sessions.get(uid, {}).get("batch_id")
    backend = torrent_backend()
    torrent_line = (f"\n\n🧲 **Torrent links work here too:** once a batch is selected, send a magnet link or a "
                    f"`.torrent` and I'll run the full **{' → '.join((await db.get_encode())['ladder']) or 'ladder'}** "
                    f"encode ladder into it."
                    + ("" if (backend and FFMPEG) else "\n⚠️ _Not usable yet — run /torrent_check to see what's missing._"))
    await message.reply_text(
        "🤖 **Auto Post Mode**\n\nTap a batch below. Once selected, **every file you send** goes straight "
        "to that batch — Anime Names matching is skipped entirely, so files don't need to match anything.\n\n"
        "Season/Episode/Quality still need to be detectable in the filename, same as normal." + torrent_line + "\n\n"
        "Use /stop_auto_post any time to turn this off.",
        reply_markup=kb_autopost_batches(batches, current),
    )

@app.on_message(filters.command("stop_auto_post") & filters.private & staff_filter)
async def stop_auto_post_cmd(client, message: Message):
    uid = message.from_user.id
    had = auto_post_sessions.pop(uid, None)
    await message.reply_text("✅ **Auto Post Mode stopped.** Back to normal Anime Names matching." if had
                              else "ℹ️ Auto Post Mode wasn't active.")


# ---------- Channel registry commands (run INSIDE the target channel; Telegram's admin
# requirement on posting in the channel is the access control here) ----------
@app.on_message(filters.channel & filters.command("register"))
async def register_channel_cmd(client, message: Message):
    chat = message.chat
    await db.register_channel(chat.id, chat.title or "Untitled Channel")
    try:
        await message.reply_text(
            f"✅ **This channel is now registered!**\n\n"
            f"Channel ID: `{chat.id}`\n\n"
            f"Link it in DM: /edit_batch → pick a batch → 📢 Sub Channel or 🏠 Main Channel(s), or /bot_settings "
            f"for the Backup Channel / Thumb-Cover Channel. To remove it later, use /delete_channel in DM."
        )
    except Exception as e:
        print(f"Failed replying in channel {chat.id}: {e}")


@app.on_message(filters.channel & filters.command("unregister"))
async def unregister_channel_cmd(client, message: Message):
    await db.unregister_channel(message.chat.id)
    await db.remove_channel_references(message.chat.id)
    try:
        await message.reply_text("🗑️ This channel has been unregistered and can no longer be linked to batches.")
    except Exception as e:
        print(f"Failed replying in channel {message.chat.id}: {e}")


@app.on_message(filters.command("delete_channel") & filters.private & staff_filter)
async def delete_channel_cmd(client, message: Message):
    channels = await db.list_channels()
    if not channels:
        await message.reply_text(
            "📭 No registered channels yet.\n\n"
            "_Register one by posting `/register` inside it (as admin), or by adding it directly via link "
            "from /edit_batch or /bot_settings._"
        )
        return
    await message.reply_text(
        "🗑️ **Delete a Registered Channel**\n\nTap a channel to remove it from the registry. I won't leave "
        "the channel itself — this only forgets it here. Any batch's Sub Channel / Main Channel(s), or the "
        "bot-wide Backup Channel / Thumb-Cover Channel, currently pointing at it will be automatically unlinked.",
        reply_markup=kb_channels_list_for_delete(channels),
    )

@app.on_message(filters.command("bot_settings") & filters.private & staff_filter)
async def bot_settings_cmd(client, message: Message):
    if not is_admin(message.from_user.id):
        return  # moderators can't touch bot-wide settings; silently ignore
    settings = await db.get_settings()
    await message.reply_text(
        "⚙️ **Bot Settings** (admins only)\n\n"
        "🗄️ **Backup Channel** mirrors everything every batch's Sub Channel gets. Bot-wide, mandatory "
        "before any channel posting works.\n\n"
        "🖼️ **Thumb/Cover Channel** is where every batch's Thumbnail and Cover Image photos are stored "
        "(so they can be re-downloaded at full quality when processing files). Bot-wide, required before "
        "🖼️ Thumbnail / 🎨 Cover Image can be set on any batch.\n\n"
        "🎬 **Encode Settings** control the torrent ladder (which qualities, CRF, preset, container).\n\n"
        "_Main Channel(s) is set per batch via /edit_batch → 🏠 Main Channel(s)._\n\n"
        "Pick a channel already registered with `/register`, or add a new one directly by link.",
        reply_markup=kb_bot_settings_menu(settings),
    )


# ==================== SEQUENCE SORT HELPERS ====================
def sort_key_for_mode(finfo: Tuple[int, int, int], mode: int):
    season, episode, quality = finfo
    q = quality if quality >= 0 else 0
    if mode == 1:
        return (season, q, episode)
    elif mode == 2:
        return (season, episode, q)
    else:
        return (q, season, episode)


def generate_sort_summary(sorted_entries: List[dict], mode: int) -> str:
    """Capped at MAX_SUMMARY_ROWS entries — a long sequence would otherwise build a text past
    Telegram's 4096-char limit and the whole sort preview would fail to send."""
    if not sorted_entries:
        return "No files."
    MAX_SUMMARY_ROWS = 55
    lines = []
    label = {1: "Season › Quality › Episode", 2: "Season › Episode › Quality", 3: "Quality › Season › Episode"}[mode]
    lines.append(f"🔀 **Sorted: {label}**\n")
    for e in sorted_entries[:MAX_SUMMARY_ROWS]:
        s, ep, q = e["season"], e["episode"], e["quality"]
        qlabel = quality_label(q) if q >= 0 else "HD"
        lines.append(f"• S{s:02d}E{ep:02d} - {qlabel} - `{get_msg_fname(e['message'])[:40]}`")
    extra = len(sorted_entries) - MAX_SUMMARY_ROWS
    if extra > 0:
        lines.append(f"\n_…and {extra} more file(s), in the same sorted order._")
    return "\n".join(lines)


# ==================== BOTTOM POST CAPTURE (runs BEFORE the file/conversation handlers) ====================
def _bottompost_pending(user_id: Optional[int]) -> bool:
    if not user_id:
        return False
    st = conversation_state.get(user_id)
    return bool(st and st.get("action") == "edit_field" and st.get("field") == "bottompost")


bottompost_pending_filter = filters.create(lambda _, __, m: _bottompost_pending(m.from_user.id if m.from_user else None))

@app.on_message(
    filters.private & staff_filter & bottompost_pending_filter & ~filters.command(NON_INPUT_COMMANDS),
    group=-1,  # must run before file_handler / conversation_input_handler (group 0)
)
async def bottompost_capture_handler(client, message: Message):
    uid = message.from_user.id
    state = conversation_state.get(uid)
    batch_id = state.get("batch_id") if state else None
    batch = await db.get_batch(batch_id) if batch_id else None
    if not batch:
        conversation_state.pop(uid, None)
        await message.reply_text("❌ This batch no longer exists.")
        raise StopPropagation

    settings = await db.get_settings()
    thumb_channel = settings.get("thumb_channel")
    if not thumb_channel or not thumb_channel.get("id"):
        await message.reply_text(
            "❌ No **Thumb/Cover Channel** has been set yet. Ask an admin to set one first via "
            "/bot_settings → 🖼️ Set Thumb/Cover Channel, then try again, or /cancel."
        )
        raise StopPropagation

    try:
        copied = await client.copy_message(
            chat_id=thumb_channel["id"], from_chat_id=message.chat.id, message_id=message.id,
        )
    except Exception as e:
        await message.reply_text(f"❌ Couldn't save that as the Bottom Post ({e}). Try again, or /cancel.")
        raise StopPropagation

    bottom_post = {
        "chat_id": thumb_channel["id"],
        "message_id": copied.id,
        "title": thumb_channel.get("title", "Storage Channel"),
    }
    await db.update_batch_field(batch_id, "bottom_post", bottom_post)
    conversation_state.pop(uid, None)

    try:
        await client.copy_message(chat_id=uid, from_chat_id=bottom_post["chat_id"], message_id=bottom_post["message_id"])
    except Exception:
        pass

    await message.reply_text(
        f"✅ **Bottom Post saved for `{batch['name']}`** — that's a preview of it above.\n\n"
        "It'll be copied exactly like that (no forward tag) after every posting run.",
        reply_markup=kb_back_field(batch_id),
    )
    raise StopPropagation

# ==================== TORRENT LINK / .torrent HANDLER ====================
# Registered in group=-1 *after* bottompost_capture_handler, so a pending Bottom Post capture
# still wins (Pyrogram runs the first matching handler in a group, in registration order). It
# also refuses to fire while the user is mid-conversation, because a link they send then is an
# answer to a prompt, not a job.
def _has_torrent_input(m: Message) -> bool:
    if not m.from_user or m.from_user.id in conversation_state:
        return False
    if is_torrent_document(m):
        return True
    return bool(extract_torrent_links(m.text or m.caption or ""))


torrent_input_filter = filters.create(lambda _, __, m: _has_torrent_input(m))


@app.on_message(
    filters.private & staff_filter & torrent_input_filter & ~filters.command(NON_INPUT_COMMANDS),
    group=-1,
)
async def torrent_link_handler(client, message: Message):
    uid = message.from_user.id
    await db.add_user(uid)

    autopost = auto_post_sessions.get(uid)
    if not autopost:
        await message.reply_text(
            "🧲 **That looks like a torrent, but Auto Post Mode is off.**\n\n"
            "A magnet link has no filename I can match against a batch's Anime Names, so torrent jobs need a "
            "batch chosen up front:\n\n"
            "1️⃣ /auto_post → tap the batch\n2️⃣ send the link again\n\n"
            "_Use /stop_auto_post when you're done._"
        )
        raise StopPropagation

    batch = await db.get_batch(autopost["batch_id"])
    if not batch:
        auto_post_sessions.pop(uid, None)
        await message.reply_text("❌ The batch selected for Auto Post Mode no longer exists. Auto Post Mode has "
                                  "been turned off — use /auto_post to pick another.")
        raise StopPropagation

    if not FFMPEG or not torrent_backend():
        missing = []
        if not torrent_backend():
            missing.append("a torrent backend (`pip install libtorrent` or `apt install aria2`)")
        if not FFMPEG:
            missing.append("`ffmpeg`")
        await message.reply_text(f"❌ Can't run torrent jobs — this server is missing {', and '.join(missing)}.\n\n"
                                  f"Run /torrent_check for details.")
        raise StopPropagation
    enc = await db.get_encode()
    ladder = [q for q in enc["ladder"] if q in QUALITY_HEIGHT]
    if not ladder:
        await message.reply_text("❌ The encode ladder is empty — enable at least one rung in /encode_settings.")
        raise StopPropagation

    raw_text = message.text or message.caption or ""
    sources: List[Tuple[str, bool, str, bool]] = []   # (source, is_local, display, cleanup_source)

    if is_torrent_document(message):
        note = await message.reply_text("📥 Saving that `.torrent` file…")
        local = os.path.join("torrents", f"{uid}_{message.id}_{int(time.time())}.torrent")
        try:
            got = await message.download(file_name=local)
        except Exception as e:
            await note.edit_text(f"❌ Couldn't download that .torrent file ({e}).")
            raise StopPropagation
        if not got or not os.path.exists(got):
            await note.edit_text("❌ Couldn't download that .torrent file.")
            raise StopPropagation
        try:
            tname, _entries = read_torrent_metainfo(got)
        except Exception:
            tname = os.path.basename(got)
        sources.append((got, True, tname, True))
        try:
            await note.delete()
        except Exception:
            pass
    else:
        for link in extract_torrent_links(raw_text):
            display = magnet_display_name(link) or link[:60]
            sources.append((link, False, display, False))

    hint = strip_torrent_links(raw_text)

    queued = []
    for source, is_local, display, cleanup_source in sources:
        job_id = new_job_id()
        register_job(job_id, uid, display)
        await file_queue.put({
            "type": "torrent",
            "job_id": job_id,
            "batch_id": str(batch["_id"]),
            "source": source,
            "is_local": is_local,
            "cleanup_source": cleanup_source,
            "hint": hint,
            "display": display,
            "requested_by": uid,
            "chat_id": message.chat.id,
        })
        queued.append((job_id, display))
    sub_channel = batch.get("sub_channel")
    dest_note = (f"📢 Will post to **{sub_channel['title']}**" if sub_channel and sub_channel.get("id")
                 else "⚠️ No Sub Channel linked — the files will only reach the Backup Channel "
                      "(set one via /edit_batch → 📢 Sub Channel)")
    hint_note = f"\n📝 Using your text as the naming hint: `{hint[:60]}`" if hint else ""
    lines = "\n".join(f"• `{jid}` — {disp[:55]}" for jid, disp in queued)
    await message.reply_text(
        f"🧲 **{len(queued)} torrent job(s) queued** for batch `{batch['name']}`\n{lines}\n\n"
        f"🎬 Ladder: **{' → '.join(ladder)}** (each rung encoded from the one above it)\n"
        f"{dest_note}{hint_note}\n\n"
        f"📥 Jobs ahead of this in the queue: {max(file_queue.qsize() - len(queued), 0)}\n\n"
        f"_Order per job: download → 1080p → upload to Backup → delete the original → 720p from the 1080p → "
        f"upload → delete the 1080p → 480p from the 720p → upload → delete everything → copy into the Sub "
        f"Channel (480p → 720p → 1080p) → post to the Main Channel(s)._\n\n"
        f"Use /cancel_job (or the 🛑 button on the progress message) to abort."
    )
    raise StopPropagation


# ==================== FILE HANDLER ====================
@app.on_message(filters.private & staff_filter & (filters.document | filters.video | filters.audio))
async def file_handler(client, message: Message):
    uid = message.from_user.id
    await db.add_user(uid)

    # Belt and braces: a .torrent document is a job, never a file to rename. The group=-1
    # handler above normally takes it first (and raises StopPropagation), so this only fires if
    # that handler was skipped — e.g. the user was mid-conversation when they sent it.
    if is_torrent_document(message):
        await message.reply_text(
            "🧲 That's a `.torrent` file. Turn on /auto_post (and finish or /cancel whatever I'm currently "
            "asking you for) and then send it again to start a torrent job."
        )
        return

    file_name = get_msg_fname(message)

    session = sequence_sessions.get(uid)
    if session and session.get("active"):
        batch = await db.find_batch_for_filename(file_name)
        if not batch:
            await message.reply_text(f"❌ Can't identify a batch for `{file_name[:60]}` — not added to sequence.")
            return
        if session["batch_id"] is None:
            session["batch_id"] = str(batch["_id"])
        elif session["batch_id"] != str(batch["_id"]):
            await message.reply_text(
                f"⚠️ `{file_name[:60]}` belongs to a different batch than the rest of this sequence — skipped.\n"
                "A sequence session can only contain files from one batch."
            )
            return
        # Validate Season -> Episode -> Quality, in that order. Stop at the first
        # missing one instead of continuing to check the rest.
        season, episode, quality = extract_file_info(file_name)
        missing_field = find_missing_field(season, episode, quality)
        if missing_field:
            await message.reply_text(
                missing_field_message(
                    file_name, missing_field, season, episode, quality,
                    extra_context="this file was **not** added to the sequence",
                )
            )
            return

        session["files"].append(message)
        await message.reply_text(f"📥 Saved for sequencing ({len(session['files'])} file(s) so far).")
        return

    # ---- Auto Post Mode: batch is whatever was picked via /auto_post, no Anime Names check ----
    autopost = auto_post_sessions.get(uid)
    if autopost:
        batch = await db.get_batch(autopost["batch_id"])
        if not batch:
            auto_post_sessions.pop(uid, None)
            await message.reply_text(
                "❌ The batch selected for Auto Post Mode no longer exists. Auto Post Mode has been turned "
                "off — use /auto_post to pick another."
            )
            return
    else:
        batch = await db.find_batch_for_filename(file_name)
        if not batch:
            await message.reply_text(
                f"❌ **Can't identify this file.**\n\n`{file_name[:80]}`\n\n"
                "No batch's Anime Names matched this filename.\n\n"
                "_Tip: check /edit_batch → the batch → 🔤 Anime Names has the right name(s), and that the name "
                "is actually a substring of your filename (dots/underscores/dashes are treated as spaces). "
                "Or use /auto_post to route every file to one batch without matching._"
            )
            return

    # Validate Season -> Episode -> Quality, in that order. Stop at the first missing
    # one — nothing gets queued until the filename gives us all three. (Applies in
    # Auto Post Mode too — only the Anime Names step is skipped, not this.)
    season, episode, quality = extract_file_info(file_name)
    missing_field = find_missing_field(season, episode, quality)
    if missing_field:
        await message.reply_text(
            missing_field_message(
                file_name, missing_field, season, episode, quality,
                batch_name=batch["name"],
                extra_context="**nothing was queued**",
            )
        )
        return
    job = {
        "batch_id": str(batch["_id"]),
        "files": [{"message": message, "season": season, "episode": episode, "quality": quality}],
        "requested_by": uid,
        "chat_id": message.chat.id,
    }
    await file_queue.put(job)
    sub_channel = batch.get("sub_channel")
    dest_note = f"📢 Will post to **{sub_channel['title']}**" if sub_channel and sub_channel.get("id") \
        else "⚠️ No Sub Channel linked yet — will send here (set one via /edit_batch → 📢 Sub Channel)"
    mode_note = "\n🤖 _(Auto Post Mode — Anime Names matching skipped)_" if autopost else ""
    await message.reply_text(
        f"✅ **Identified as batch `{batch['name']}`.**{mode_note}\n"
        f"Detected: S{season:02d}E{episode:02d} - {quality_label(quality)}\n"
        f"{dest_note}\n\n"
        f"📥 Queued for processing (jobs ahead: {file_queue.qsize() - 1})."
    )


# ==================== CONVERSATION INPUT HANDLER (text/photo) ====================
@app.on_message(filters.private & staff_filter & (filters.text | filters.photo) & ~filters.command(NON_INPUT_COMMANDS))
async def conversation_input_handler(client, message: Message):
    uid = message.from_user.id
    state = conversation_state.get(uid)
    if not state:
        return

    action = state.get("action")

    if action == "new_batch_name":
        if not message.text:
            await message.reply_text("❌ Please send a text name for the batch.")
            return
        name = message.text.strip()
        if not name:
            await message.reply_text("❌ Batch name can't be empty.")
            return
        if await db.name_exists(name):
            await message.reply_text("❌ A batch with that name already exists. Choose a different name, or /cancel.")
            return
        batch_id = await db.create_batch(name)
        conversation_state.pop(uid, None)
        await message.reply_text(
            f"✅ **Batch `{name}` created!**\n\nNow configure it:",
            reply_markup=kb_batch_edit_menu(batch_id),
        )
        return
    if action == "add_channel_link":
        kind = state["kind"]
        batch_id = state.get("batch_id")
        if not message.text:
            await message.reply_text("❌ Please send this as text (a channel link or @username), or /cancel.")
            return
        chat, error = await resolve_channel_input(client, message.text.strip())
        if error:
            await message.reply_text(f"❌ {error}\n\nTry again, or /cancel.")
            return
        title = chat.title or "Untitled Channel"
        await db.register_channel(chat.id, title)
        conversation_state.pop(uid, None)
        if kind in ("backup", "thumbchannel"):
            await db.set_setting(f"{kind}_channel" if kind == "backup" else "thumb_channel", {"id": chat.id, "title": title})
            label = "Backup Channel" if kind == "backup" else "Thumb/Cover Channel"
            await message.reply_text(f"✅ **{label} set to:** {title}")
            return
        if not batch_id:
            await message.reply_text("❌ Missing batch context — please try again from /edit_batch.")
            return
        if kind == "main":
            # Main Channel is multi-value: append this one to the batch's existing list
            # instead of overwriting it, so a batch can accumulate several Main Channels.
            batch = await db.get_batch(batch_id)
            current_list = get_main_channels(batch) if batch else []
            if any(c.get("id") == chat.id for c in current_list):
                await message.reply_text(
                    f"ℹ️ **{title}** is already linked as a Main Channel for this batch.",
                    reply_markup=kb_back_field(batch_id),
                )
                return
            current_list.append({"id": chat.id, "title": title})
            await db.update_batch_field(batch_id, "main_channels", current_list)
            await message.reply_text(
                f"✅ **Main Channel added:** {title}\n\nTotal Main Channel(s) linked: {len(current_list)}",
                reply_markup=kb_back_field(batch_id),
            )
            return
        field_key = "sub_channel"
        label = "Sub Channel"
        await db.update_batch_field(batch_id, field_key, {"id": chat.id, "title": title})
        await message.reply_text(f"✅ **{label} set to:** {title}", reply_markup=kb_back_field(batch_id))
        return
    if action == "add_anime_names":
        batch_id = state["batch_id"]
        batch = await db.get_batch(batch_id)
        if not batch:
            conversation_state.pop(uid, None)
            await message.reply_text("❌ This batch no longer exists.")
            return
        if not message.text:
            await message.reply_text("❌ Please send this as text, or /cancel.")
            return
        new_names = [n.strip() for n in re.split(r'[,\n]', message.text) if n.strip()]
        if not new_names:
            await message.reply_text("❌ No valid names found. Try again, or /cancel.")
            return
        existing = batch.get("anime_names", [])
        existing_norm = {normalize_for_match(n) for n in existing}
        added = []
        for n in new_names:
            if normalize_for_match(n) not in existing_norm:
                existing.append(n)
                existing_norm.add(normalize_for_match(n))
                added.append(n)
        await db.update_batch_field(batch_id, "anime_names", existing)
        conversation_state.pop(uid, None)
        note = f"✅ Added: `{', '.join(added)}`" if added else "ℹ️ Those name(s) were already in the list."
        await message.reply_text(
            f"{note}\n\n**Current Anime Names for `{batch['name']}`:**\n" +
            ("\n".join(f"• {n}" for n in existing) if existing else "_none set_"),
            reply_markup=kb_anime_names_menu(batch_id, existing),
        )
        return
    if action == "edit_field":
        batch_id = state["batch_id"]
        field = state["field"]
        batch = await db.get_batch(batch_id)
        if not batch:
            conversation_state.pop(uid, None)
            await message.reply_text("❌ This batch no longer exists.")
            return

        if field in ("thumbnail", "coverimage"):
            if not message.photo:
                await message.reply_text("❌ Please send a **photo**, or /cancel.")
                return
            settings = await db.get_settings()
            thumb_channel = settings.get("thumb_channel")
            if not thumb_channel or not thumb_channel.get("id"):
                await message.reply_text(
                    "❌ No **Thumb/Cover Channel** has been set yet. Ask an admin to set one first via "
                    "/bot_settings → 🖼️ Set Thumb/Cover Channel, then try again."
                )
                return
            try:
                copied = await client.copy_message(
                    chat_id=thumb_channel["id"], from_chat_id=message.chat.id, message_id=message.id,
                )
            except Exception as e:
                await message.reply_text(f"❌ Couldn't save that image to the Thumb/Cover Channel ({e}). Try again, or /cancel.")
                return
            field_key = "thumbnail" if field == "thumbnail" else "cover_image"
            label = "Thumbnail" if field == "thumbnail" else "Cover Image"
            await db.update_batch_field(batch_id, field_key, {"chat_id": thumb_channel["id"], "message_id": copied.id})
            conversation_state.pop(uid, None)
            note = "" if field == "thumbnail" else (
                "\n\n_Note: Telegram compresses photos on upload, so this is the best quality Telegram allows "
                "for a photo message. It'll be used as Telegram's native video poster (if supported) and "
                "embedded into each file as full-quality cover art at process time._"
            )
            await message.reply_text(f"✅ {label} updated!{note}", reply_markup=kb_back_field(batch_id))
            return
        if field in ("autorename", "autocaption", "toppost"):
            if not message.text:
                await message.reply_text("❌ Please send this as text, or /cancel.")
                return
            text = message.text.strip()

            if field == "autorename":
                await db.update_batch_field(batch_id, "autorename_format", text)
                conversation_state.pop(uid, None)
                await message.reply_text(f"✅ Autorename format set:\n`{text}`", reply_markup=kb_back_field(batch_id))
                return

            if field == "autocaption":
                await db.update_batch_field(batch_id, "autocaption_format", text)
                conversation_state.pop(uid, None)
                await message.reply_text(f"✅ Autocaption format set:\n`{text}`", reply_markup=kb_back_field(batch_id))
                return

            if field == "toppost":
                await db.update_batch_field(batch_id, "top_post_format", text)
                conversation_state.pop(uid, None)
                await message.reply_text(f"✅ Top Post format set:\n{text}", reply_markup=kb_back_field(batch_id))
                return
        if field == "bottompost":
            await message.reply_text("↩️ Just send (or forward) the message you want as the Bottom Post, or /cancel.")
            return
        return

    if action == "edit_metadata_field":
        batch_id = state["batch_id"]
        field = state["field"]
        if not message.text:
            await message.reply_text("❌ Please send this as text, or /cancel.")
            return
        text = message.text.strip()
        if field == "all":
            for f in ("title", "author", "artist", "audio", "subtitle", "video"):
                await db.update_batch_field(batch_id, f"metadata.{f}", text)
            conversation_state.pop(uid, None)
            await message.reply_text(f"✅ All metadata fields set to: `{text}`", reply_markup=kb_back_field(batch_id))
            return
        else:
            await db.update_batch_field(batch_id, f"metadata.{field}", text)
            conversation_state.pop(uid, None)
            await message.reply_text(f"✅ Metadata `{field}` set to: `{text}`", reply_markup=kb_back_field(batch_id))
            return
    # ---- New: numeric CRF input for /encode_settings → 🎚️ CRF ----
    if action == "encode_crf":
        if not is_admin(uid):
            conversation_state.pop(uid, None)
            return
        if not message.text:
            await message.reply_text("❌ Please send a **number** between 14 and 35, or /cancel.")
            return
        raw = message.text.strip()
        try:
            crf = int(raw)
        except ValueError:
            await message.reply_text(f"❌ `{raw[:20]}` isn't a whole number. Send something like `23`, or /cancel.")
            return
        if not 14 <= crf <= 35:
            await message.reply_text(
                f"❌ CRF `{crf}` is outside the usable range.\n\n"
                "Send a number between **14** (huge, near-transparent) and **35** (tiny, visibly soft). "
                "20–26 is the sane range for anime."
            )
            return
        await db.set_encode_field("crf", crf)
        conversation_state.pop(uid, None)
        enc = await db.get_encode()
        await message.reply_text(f"✅ CRF set to **{crf}**.\n\n" + encode_settings_text(enc),
                                 reply_markup=kb_encode_menu(enc))
        return

    # ---- New: per-rung MB targets for /encode_settings → 🎯 Size targets ----
    if action == "encode_targets":
        if not is_admin(uid):
            conversation_state.pop(uid, None)
            return
        if not message.text:
            await message.reply_text("❌ Send them as text, e.g. `1080p=250, 720p=150, 480p=90`, or /cancel.")
            return
        enc = await db.get_encode()
        targets = dict(enc.get("targets", {}) or {})
        parsed, bad = {}, []
        for token in re.split(r"[,\n;]+", message.text.strip()):
            token = token.strip()
            if not token:
                continue
            m = re.match(r"^([0-9]{3,4}p|4K|2K)\s*[=:]\s*([0-9]{1,5})\s*(?:mb)?$", token, re.IGNORECASE)
            if not m:
                bad.append(token)
                continue
            q = m.group(1)
            # Normalise the case the buttons use ("1080p", "4K") so lookups match the ladder.
            q = q.upper() if q.upper() in ("4K", "2K") else q.lower()
            if q not in QUALITY_HEIGHT:
                bad.append(token)
                continue
            parsed[q] = int(m.group(2))
        if not parsed:
            await message.reply_text(
                "❌ Nothing I could read in that.\n\nUse `quality=MB` pairs, like:\n"
                "`1080p=250, 720p=150, 480p=90`\n\nUse /cancel to abort."
            )
            return
        targets.update(parsed)
        await db.set_encode_field("targets", targets)
        conversation_state.pop(uid, None)
        enc = await db.get_encode()
        note = f"\n⚠️ Ignored: `{', '.join(bad[:6])}`" if bad else ""
        await message.reply_text(
            f"✅ Size targets updated: {', '.join(f'{q} → {mb} MB' for q, mb in parsed.items())}{note}\n\n"
            + encode_settings_text(enc), reply_markup=kb_encode_menu(enc))
        return

# ==================== CALLBACK QUERY HANDLER ====================
FIELD_PROMPTS = {
    "autorename": "✏️ **Autorename Format**\n\nSend the format string. Available variables:\n"
                  "`{filename}` `{season}` `{episode}` `{quality}` `{filesize}` `{duration}`\n\n"
                  "Example: `JujutsuKaisen S{season} - E{episode} [Dual] {quality} @AnimeMultiDub`\n\n"
                  "_Note: `<text>` is NOT rendered bold here — filenames can't be bold, so the `<>` are just "
                  "removed, leaving plain text._",
    "autocaption": "💬 **Autocaption Format**\n\nSame variables as autorename. Send the new caption format.\n\n"
                   "_Tip: wrap anything in `<angle brackets>` to make it **bold** — e.g. `<{filename}>` sends "
                   "the filename in bold._",
    "toppost": "🔝 **Top Post Format**\n\nSent with the batch's thumbnail before the files. Available variables:\n"
               "`{batch}` `{pseason}` `{pepisode}` `{pquality}`\n\n"
               "Example:\n`🎬 <{batch}>\\nSeason {pseason} • Episode {pepisode} • {pquality}`\n\n"
               "_Tip: wrap anything in `<angle brackets>` to make it **bold** — e.g. `<{batch}>` sends the "
               "batch name in bold. This same format is also used for the Main Channel(s) post._",
    "bottompost": "🔻 **Bottom Post**\n\nJust send (or forward) me the actual message you want copied after "
                  "the files each time — a sticker, a text note, a photo, a video, anything. I'll store it "
                  "myself, so it works even for private channels.\n\n"
                  "It'll be copied exactly as-is (no forward tag) after every posting run.",
    "thumbnail": "🖼️ **Thumbnail**\n\nSend a **photo** to use as the small in-chat preview for this batch's files.\n\n"
                 "_Telegram limits this preview to a small size no matter what you send — for a full-quality "
                 "cover embedded in the file itself, use 🎨 Cover Image instead._",
    "coverimage": "🎨 **Cover Image**\n\nSend a **photo** to use as this batch's full-quality video poster "
                  "(Telegram's native `cover`, when supported) and to embed as full-quality cover art inside "
                  "each video file (like album art — visible in media players, independent of Telegram's small "
                  "chat preview).",
}


async def render_batch_channel_picker(cq, batch_id: str, kind: str):
    batch = await db.get_batch(batch_id)
    if not batch:
        await cq.message.edit_text("❌ This batch no longer exists.")
        return
    channels = await db.list_channels()

    if kind == "main":
        current_list = get_main_channels(batch)
        current_ids = [c["id"] for c in current_list if c.get("id")]
        text = ("🏠 **Main Channel(s)**\n\nTap a channel to add/remove it — you can select **multiple** "
                "Main Channels for this batch. Every post goes out to all of them.\n\nTap "
                "**➕ Add channel by link** to link a new one directly.")
        if current_list:
            text += "\n\nCurrently linked: " + clip_for_display(
                ", ".join(c.get("title", "Channel") for c in current_list), 400)
        await cq.message.edit_text(text, reply_markup=kb_main_channel_picker(batch_id, channels, current_ids))
        return

    field_key = "sub_channel"
    label = "Sub Channel"
    current = batch.get(field_key)
    current_id = current.get("id") if current else None
    text = (f"📢 **{label}**\n\nPick an already-registered channel below, or tap "
            f"**➕ Add channel by link** to link a new one directly.")
    if current and current.get("id"):
        text += f"\n\nCurrently linked: **{current.get('title')}**"
    await cq.message.edit_text(text, reply_markup=kb_channel_picker(batch_id, channels, current_id, kind))

async def show_batch_info(cq, batch_id: str):
    batch = await db.get_batch(batch_id)
    if not batch:
        await cq.message.edit_text("❌ This batch no longer exists.")
        return
    meta = batch.get("metadata", {})
    channel = batch.get("sub_channel")
    channel_line = f"📢 Sub Channel: ✅ {channel.get('title', 'Linked')}" if channel and channel.get("id") \
        else "📢 Sub Channel: ❌ Not set"
    main_channels = get_main_channels(batch)
    if main_channels:
        titles = clip_for_display(", ".join(c.get("title", "Channel") for c in main_channels), 400)
        main_line = f"🏠 Main Channel(s): ✅ {titles}"
    else:
        main_line = "🏠 Main Channel(s): ❌ Not set"
    lines = [
        f"**📁 Batch: {batch['name']}**\n",
        f"🖼️ Thumbnail: {'✅ Set' if batch.get('thumbnail') else '❌ Not set'}",
        f"🎨 Cover Image: {'✅ Set' if batch.get('cover_image') else '❌ Not set'}"
        + ("" if SEND_VIDEO_SUPPORTS_COVER else " _(Pyrogram build has no native cover support yet)_"),
        f"🏷️ Metadata: {'✅ Enabled' if meta.get('enabled', True) else '❌ Disabled'}",
        f"✏️ Autorename: `{clip_for_display(batch.get('autorename_format')) or 'Not set (using default)'}`",
        f"💬 Autocaption: `{clip_for_display(batch.get('autocaption_format')) or 'Not set (using default)'}`",
        f"🎞️ Mediatype: `{batch.get('mediatype', 'document')}`",
        f"🔤 Anime Names: `{clip_for_display(', '.join(batch.get('anime_names', [])), 400) or 'Not set'}`",
        f"🔝 Top Post: `{clip_for_display(batch.get('top_post_format')) or 'Not set (using default)'}`",
        f"🔻 Bottom Post: {'✅ Linked (from ' + batch['bottom_post']['title'] + ')' if batch.get('bottom_post') else '❌ Not set'}",
        channel_line,
        main_line,
    ]
    await cq.message.edit_text("\n".join(lines), reply_markup=kb_batch_actions(batch_id))


@app.on_callback_query()
async def callback_handler(client, cq):
    uid = cq.from_user.id if cq.from_user else None
    if not is_staff(uid):
        # No response to non-staff at all — just stop the button's loading spinner.
        try:
            await cq.answer()
        except Exception:
            pass
        return
    try:
        data = cq.data

        if data == "noop":
            await cq.answer()
            return
        # ---- New: torrent/encode job cancellation from the 🛑 button on a status message ----
        if data.startswith("jobcancel_"):
            job_id = data[len("jobcancel_"):]
            info = active_jobs.get(job_id)
            if not info:
                await cq.answer("That job already finished.", show_alert=True)
                return
            if info["user"] != uid and not is_admin(uid):
                await cq.answer("That isn't your job.", show_alert=True)
                return
            if info["cancel"].is_set():
                await cq.answer("Already cancelling…", show_alert=True)
                return
            info["cancel"].set()
            await cq.answer("🛑 Cancelling — the current download/encode is being stopped.", show_alert=True)
            return

        # ---- New: bot-wide Encode Settings menu (admins only) ----
        if data == "enc_menu" or data.startswith("enc_"):
            if not is_admin(uid):
                await cq.answer("Admins only.", show_alert=True)
                return
            enc = await db.get_encode()

            if data == "enc_menu":
                pass  # just render below

            elif data.startswith("enc_rung_"):
                q = data[len("enc_rung_"):]
                if q not in QUALITY_HEIGHT:
                    await cq.answer("Unknown quality.", show_alert=True)
                    return
                ladder = list(enc["ladder"])
                if q in ladder:
                    if len(ladder) == 1:
                        await cq.answer("The ladder needs at least one rung.", show_alert=True)
                        return
                    ladder.remove(q)
                else:
                    ladder.append(q)
                ladder.sort(key=lambda x: QUALITY_HEIGHT[x], reverse=True)
                await db.set_encode_field("ladder", ladder)
                enc = await db.get_encode()
                await cq.answer(f"{q} {'removed' if q not in ladder else 'added'}")

            elif data == "enc_crf":
                conversation_state[uid] = {"action": "encode_crf"}
                await cq.message.edit_text(
                    "🎚️ **CRF (quality)**\n\nSend a whole number between **14** and **35**.\n\n"
                    "• Lower = bigger file, better picture\n• Higher = smaller file, softer picture\n"
                    f"• Current: **{enc['crf']}** — 20–26 is the sane range for anime\n\nUse /cancel to abort.",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="enc_menu")]]),
                )
                await cq.answer()
                return
            elif data == "enc_preset":
                # Cycle through the preset list rather than opening a submenu — one tap per step.
                try:
                    i = ENCODE_PRESETS.index(enc["preset"])
                except ValueError:
                    i = ENCODE_PRESETS.index(DEFAULT_ENCODE["preset"])
                nxt = ENCODE_PRESETS[(i + 1) % len(ENCODE_PRESETS)]
                await db.set_encode_field("preset", nxt)
                enc = await db.get_encode()
                await cq.answer(f"Preset: {nxt}")

            elif data == "enc_codec":
                try:
                    i = ENCODE_CODECS.index(enc.get("codec", "x264"))
                except ValueError:
                    i = 0
                nxt = ENCODE_CODECS[(i + 1) % len(ENCODE_CODECS)]
                await db.set_encode_field("codec", nxt)
                enc = await db.get_encode()
                _, label = resolve_codec(enc)
                await cq.answer(f"Codec: {label}")

            elif data == "enc_tune":
                try:
                    i = ENCODE_TUNES.index(enc.get("tune", "animation"))
                except ValueError:
                    i = 0
                nxt = ENCODE_TUNES[(i + 1) % len(ENCODE_TUNES)]
                await db.set_encode_field("tune", nxt)
                enc = await db.get_encode()
                await cq.answer(f"Tune: {nxt}")

            elif data == "enc_depth":
                nxt = 10 if int(enc.get("bit_depth", 8)) == 8 else 8
                await db.set_encode_field("bit_depth", nxt)
                enc = await db.get_encode()
                await cq.answer(f"{nxt}-bit" + (" — ~8% smaller, but not hardware-decodable "
                                                "on many phones" if nxt == 10 else ""))

            elif data == "enc_targets":
                conversation_state[uid] = {"action": "encode_targets"}
                await cq.message.edit_text(
                    "🎯 **Per-rung size targets (MB)**\n\n"
                    "Send them as `quality=MB`, one per line or comma-separated:\n"
                    "`1080p=250, 720p=150, 480p=90`\n\n"
                    f"• Current: {targets_summary(enc)}\n"
                    "• Each rung is hard-capped to its target, and re-encoded at a higher CRF if it "
                    "still overshoots.\n"
                    "• Send `0` for a rung to leave it uncapped (CRF alone decides the size).\n\n"
                    "Use /cancel to abort.",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="enc_menu")]]),
                )
                await cq.answer()
                return

            elif data == "enc_audio":
                order = ["auto", "copy", "aac"]
                try:
                    i = order.index(enc["audio"])
                except ValueError:
                    i = 0
                nxt = order[(i + 1) % len(order)]
                await db.set_encode_field("audio", nxt)
                enc = await db.get_encode()
                await cq.answer({"auto": "Audio: auto (copy unless it breaks the size budget)",
                                 "copy": "Audio: copy all tracks",
                                 "aac": "Audio: AAC 128k stereo"}[nxt])

            elif data == "enc_container":
                nxt = "mp4" if enc["container"] == "mkv" else "mkv"
                await db.set_encode_field("container", nxt)
                enc = await db.get_encode()
                await cq.answer(f"Container: .{nxt}")

            elif data == "enc_subs":
                nxt = not enc["keep_subs"]
                await db.set_encode_field("keep_subs", nxt)
                enc = await db.get_encode()
                await cq.answer("Subtitles copied" if nxt else "Subtitles dropped")

            elif data == "enc_upscale":
                nxt = not enc["skip_upscale"]
                await db.set_encode_field("skip_upscale", nxt)
                enc = await db.get_encode()
                await cq.answer("Skip upscaling: on" if nxt else "Skip upscaling: off")

            else:
                await cq.answer()
                return

            try:
                await cq.message.edit_text(encode_settings_text(enc), reply_markup=kb_encode_menu(enc))
            except Exception:
                pass  # "message is not modified" — the toast already told them what changed
            if data == "enc_menu":
                await cq.answer()
            return
        if data == "batch_list":
            batches = await db.list_batches()
            if not batches:
                await cq.message.edit_text("📭 No batches yet. Use /new_batch to create one.")
            else:
                await cq.message.edit_text("**📁 Your Batches**\n\nTap a batch to edit or delete it:", reply_markup=kb_batches_list(batches))
            await cq.answer()
            return

        if data.startswith("batch_open_"):
            batch_id = data[len("batch_open_"):]
            await show_batch_info(cq, batch_id)
            await cq.answer()
            return

        if data.startswith("batch_edit_"):
            batch_id = data[len("batch_edit_"):]
            batch = await db.get_batch(batch_id)
            if not batch:
                await cq.message.edit_text("❌ This batch no longer exists.")
                await cq.answer()
                return
            await cq.message.edit_text(f"**✏️ Editing: {batch['name']}**\n\nChoose a field:", reply_markup=kb_batch_edit_menu(batch_id))
            await cq.answer()
            return

        if data.startswith("batch_delconfirm_"):
            batch_id = data[len("batch_delconfirm_"):]
            buttons = InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Yes, delete", callback_data=f"batch_delyes_{batch_id}"),
                 InlineKeyboardButton("❌ No", callback_data=f"batch_open_{batch_id}")],
            ])
            await cq.message.edit_text("⚠️ **Are you sure you want to delete this batch?** This cannot be undone.", reply_markup=buttons)
            await cq.answer()
            return

        if data.startswith("batch_delyes_"):
            batch_id = data[len("batch_delyes_"):]
            await db.delete_batch(batch_id)
            await cq.message.edit_text("🗑️ Batch deleted.")
            await cq.answer("Deleted")
            return
        if data.startswith("f_"):
            rest = data[len("f_"):]
            field, batch_id = rest.split("_", 1)
            batch = await db.get_batch(batch_id)
            if not batch:
                await cq.message.edit_text("❌ This batch no longer exists.")
                await cq.answer()
                return

            if field in ("thumbnail", "coverimage"):
                conversation_state[uid] = {"action": "edit_field", "field": field, "batch_id": batch_id}
                await cq.message.edit_text(FIELD_PROMPTS[field] + "\n\nUse /cancel to abort.", reply_markup=kb_back_field(batch_id))
            elif field == "metadata":
                meta = batch.get("metadata", {})
                await cq.message.edit_text("🏷️ **Metadata Settings**\n\nChoose a field to edit:",
                                            reply_markup=kb_metadata_menu(batch_id, meta.get("enabled", True)))
            elif field == "animenames":
                names = batch.get("anime_names", [])
                text = ("🔤 **Anime Names**\n\nTap a name to remove it, or add new ones. A file matches if ANY "
                        "of these appears in its filename (case-insensitive, separators normalized).\n\n"
                        "**Current:**\n" + ("\n".join(f"• {n}" for n in names) if names else "_none set_"))
                await cq.message.edit_text(text, reply_markup=kb_anime_names_menu(batch_id, names))
            elif field in ("autorename", "autocaption", "toppost", "bottompost"):
                conversation_state[uid] = {"action": "edit_field", "field": field, "batch_id": batch_id}
                await cq.message.edit_text(FIELD_PROMPTS[field] + "\n\nUse /cancel to abort.", reply_markup=kb_back_field(batch_id))
            elif field == "mediatype":
                await cq.message.edit_text("🎞️ **Choose output media type:**", reply_markup=kb_mediatype(batch_id, batch.get("mediatype", "document")))
            elif field == "channel":
                await render_batch_channel_picker(cq, batch_id, "sub")
            elif field == "mainchannel":
                await render_batch_channel_picker(cq, batch_id, "main")
            await cq.answer()
            return

        if data.startswith("animename_del_"):
            rest = data[len("animename_del_"):]
            batch_id, idx_str = rest.rsplit("_", 1)
            batch = await db.get_batch(batch_id)
            if not batch:
                await cq.message.edit_text("❌ This batch no longer exists.")
                await cq.answer()
                return
            names = batch.get("anime_names", [])
            idx = int(idx_str)
            removed = None
            if 0 <= idx < len(names):
                removed = names.pop(idx)
                await db.update_batch_field(batch_id, "anime_names", names)
            text = ("🔤 **Anime Names**\n\n" + (f"🗑️ Removed: `{removed}`\n\n" if removed else "") +
                    "**Current:**\n" + ("\n".join(f"• {n}" for n in names) if names else "_none set_"))
            await cq.message.edit_text(text, reply_markup=kb_anime_names_menu(batch_id, names))
            await cq.answer("Removed" if removed else "Already gone")
            return
        if data.startswith("animename_add_"):
            batch_id = data[len("animename_add_"):]
            conversation_state[uid] = {"action": "add_anime_names", "batch_id": batch_id}
            await cq.message.edit_text(
                "➕ **Add Anime Name(s)**\n\nSend one or more names (comma or newline separated). "
                "They'll be added to the existing list — nothing gets overwritten.\n\nUse /cancel to abort.",
                reply_markup=kb_back_field(batch_id),
            )
            await cq.answer()
            return

        if data.startswith("mainchan_toggle_"):
            rest = data[len("mainchan_toggle_"):]
            batch_id, cid_str = rest.rsplit("_", 1)
            cid = int(cid_str)
            batch = await db.get_batch(batch_id)
            if not batch:
                await cq.message.edit_text("❌ This batch no longer exists.")
                await cq.answer()
                return
            current_list = get_main_channels(batch)
            current_ids = [c["id"] for c in current_list]
            if cid in current_ids:
                current_list = [c for c in current_list if c["id"] != cid]
                toast = "Removed"
            else:
                chan = await db.get_channel(cid)
                title = chan.get("title", "Channel") if chan else "Channel"
                current_list.append({"id": cid, "title": title})
                toast = "Added"
            await db.update_batch_field(batch_id, "main_channels", current_list)
            channels = await db.list_channels()
            new_ids = [c["id"] for c in current_list]
            text = ("🏠 **Main Channel(s)**\n\nTap a channel to add/remove it — you can select **multiple** "
                    "Main Channels for this batch. Every post goes out to all of them.\n\nTap "
                    "**➕ Add channel by link** to link a new one directly.")
            if current_list:
                text += "\n\nCurrently linked: " + clip_for_display(
                ", ".join(c.get("title", "Channel") for c in current_list), 400)
            await cq.message.edit_text(text, reply_markup=kb_main_channel_picker(batch_id, channels, new_ids))
            await cq.answer(toast)
            return
        if data.startswith("chan_pick_"):
            rest = data[len("chan_pick_"):]
            kind, batch_id, cid_str = rest.split("_", 2)
            cid = int(cid_str)
            chan = await db.get_channel(cid)
            title = chan.get("title", "Channel") if chan else "Channel"
            field_key = "sub_channel" if kind == "sub" else "main_channel"
            label = "Sub Channel" if kind == "sub" else "Main Channel"
            await db.update_batch_field(batch_id, field_key, {"id": cid, "title": title})
            channels = await db.list_channels()
            text = (f"✅ **Linked to:** {title}\n\n📢 **{label}**\n\nPick an already-registered channel below, "
                    f"or tap **➕ Add channel by link** to link a new one directly.")
            await cq.message.edit_text(text, reply_markup=kb_channel_picker(batch_id, channels, cid, kind))
            await cq.answer("Linked!")
            return

        if data.startswith("chan_remove_"):
            rest = data[len("chan_remove_"):]
            kind, batch_id = rest.split("_", 1)
            field_key = "sub_channel" if kind == "sub" else "main_channel"
            label = "Sub Channel" if kind == "sub" else "Main Channel"
            await db.update_batch_field(batch_id, field_key, None)
            channels = await db.list_channels()
            text = (f"🗑️ **Channel unlinked.**\n\n📢 **{label}**\n\nPick an already-registered channel below, "
                    f"or tap **➕ Add channel by link** to link a new one directly.")
            await cq.message.edit_text(text, reply_markup=kb_channel_picker(batch_id, channels, None, kind))
            await cq.answer("Removed")
            return

        if data.startswith("chan_addlink_"):
            rest = data[len("chan_addlink_"):]
            kind, batch_id = rest.split("_", 1)
            conversation_state[uid] = {"action": "add_channel_link", "kind": kind, "batch_id": batch_id}
            label = "Sub Channel" if kind == "sub" else "Main Channel"
            await cq.message.edit_text(
                f"🔗 **Add {label} by link**\n\nSend the channel's `@username` or `https://t.me/username` link.\n\n"
                "⚠️ I must already be an **admin** in that channel. For **private** channels without a public "
                "username, this won't work — instead add me as admin and post `/register` inside the channel.\n\n"
                "Use /cancel to abort.",
                reply_markup=kb_back_field(batch_id),
            )
            await cq.answer()
            return
        if data == "gset_menu":
            settings = await db.get_settings()
            await cq.message.edit_text(
                "⚙️ **Bot Settings** (admins only)\n\nBackup Channel mirrors every batch's Sub Channel, for "
                "redundancy. Thumb/Cover Channel stores Thumbnail/Cover Image photos. Both are bot-wide.\n\n"
                "🎬 **Encode Settings** controls the torrent pipeline's quality ladder (CRF, preset, audio, "
                "container) — it's also bot-wide.",
                reply_markup=kb_bot_settings_menu(settings),
            )
            await cq.answer()
            return

        if data in ("gset_pick_menu_backup", "gset_pick_menu_thumbchannel"):
            if not is_admin(uid):
                await cq.answer("Admins only.", show_alert=True)
                return
            kind = "backup" if data.endswith("backup") else "thumbchannel"
            channels = await db.list_channels()
            settings = await db.get_settings()
            setting_field = "backup_channel" if kind == "backup" else "thumb_channel"
            current = settings.get(setting_field)
            current_id = current.get("id") if current else None
            label = "Backup Channel" if kind == "backup" else "Thumb/Cover Channel"
            await cq.message.edit_text(f"📢 **Pick the {label}, or add one by link:**",
                                        reply_markup=kb_global_channel_picker(kind, channels, current_id))
            await cq.answer()
            return

        if data.startswith("gset_addlink_"):
            if not is_admin(uid):
                await cq.answer("Admins only.", show_alert=True)
                return
            kind = data[len("gset_addlink_"):]
            conversation_state[uid] = {"action": "add_channel_link", "kind": kind, "batch_id": None}
            label = "Backup Channel" if kind == "backup" else "Thumb/Cover Channel"
            await cq.message.edit_text(
                f"🔗 **Add {label} by link**\n\nSend the channel's `@username` or `https://t.me/username` link.\n\n"
                "⚠️ I must already be an **admin** in that channel. For private channels without a public "
                "username, add me as admin and post `/register` inside instead.\n\nUse /cancel to abort.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="gset_menu")]]),
            )
            await cq.answer()
            return
        if data.startswith("gset_set_"):
            if not is_admin(uid):
                await cq.answer("Admins only.", show_alert=True)
                return
            rest = data[len("gset_set_"):]
            kind, cid_str = rest.split("_", 1)
            cid = int(cid_str)
            chan = await db.get_channel(cid)
            title = chan.get("title", "Channel") if chan else "Channel"
            setting_field = "backup_channel" if kind == "backup" else "thumb_channel"
            await db.set_setting(setting_field, {"id": cid, "title": title})
            channels = await db.list_channels()
            label = "Backup Channel" if kind == "backup" else "Thumb/Cover Channel"
            await cq.message.edit_text(f"✅ **{label} set to:** {title}\n\n📢 **Pick the {label}, or add one by link:**",
                                        reply_markup=kb_global_channel_picker(kind, channels, cid))
            await cq.answer("Set!")
            return

        if data.startswith("gset_remove_"):
            if not is_admin(uid):
                await cq.answer("Admins only.", show_alert=True)
                return
            kind = data[len("gset_remove_"):]
            setting_field = "backup_channel" if kind == "backup" else "thumb_channel"
            await db.set_setting(setting_field, None)
            channels = await db.list_channels()
            label = "Backup Channel" if kind == "backup" else "Thumb/Cover Channel"
            await cq.message.edit_text(f"🗑️ **{label} removed.**\n\n📢 **Pick the {label}, or add one by link:**",
                                        reply_markup=kb_global_channel_picker(kind, channels, None))
            await cq.answer("Removed")
            return
        if data == "delchan_list":
            channels = await db.list_channels()
            if not channels:
                await cq.message.edit_text("📭 No registered channels left.")
            else:
                await cq.message.edit_text(
                    "🗑️ **Delete a Registered Channel**\n\nTap a channel to remove it from the registry.",
                    reply_markup=kb_channels_list_for_delete(channels),
                )
            await cq.answer()
            return

        if data.startswith("delchan_open_"):
            cid = int(data[len("delchan_open_"):])
            chan = await db.get_channel(cid)
            title = chan.get("title", "Channel") if chan else "Channel"
            await cq.message.edit_text(
                f"⚠️ **Delete `{title}`?**\n\nChannel ID: `{cid}`\n\n"
                "This removes it from my registry only — I won't leave the channel. Any batch's Sub Channel / "
                "Main Channel(s), or the bot-wide Backup Channel / Thumb-Cover Channel, currently pointing at it "
                "will be automatically unlinked. This cannot be undone.",
                reply_markup=kb_delete_channel_confirm(cid),
            )
            await cq.answer()
            return

        if data.startswith("delchan_yes_"):
            cid = int(data[len("delchan_yes_"):])
            chan = await db.get_channel(cid)
            title = chan.get("title", "Channel") if chan else "Channel"
            await db.unregister_channel(cid)
            await db.remove_channel_references(cid)
            await cq.message.edit_text(
                f"🗑️ **`{title}` deleted from the registry** and unlinked from any batches/settings that "
                "referenced it."
            )
            await cq.answer("Deleted")
            return
        if data.startswith("meta_"):
            rest = data[len("meta_"):]
            field, batch_id = rest.split("_", 1)
            batch = await db.get_batch(batch_id)
            if not batch:
                await cq.message.edit_text("❌ This batch no longer exists.")
                await cq.answer()
                return
            if field == "toggle":
                meta = batch.get("metadata", {})
                new_val = not meta.get("enabled", True)
                await db.update_batch_field(batch_id, "metadata.enabled", new_val)
                meta["enabled"] = new_val
                await cq.message.edit_text("🏷️ **Metadata Settings**\n\nChoose a field to edit:",
                                            reply_markup=kb_metadata_menu(batch_id, new_val))
                await cq.answer(f"Metadata {'enabled' if new_val else 'disabled'}")
                return
            conversation_state[uid] = {"action": "edit_metadata_field", "field": field, "batch_id": batch_id}
            label = "all fields" if field == "all" else field
            await cq.message.edit_text(f"🏷️ Send the new value for **{label}**.\nUse /cancel to abort.", reply_markup=kb_back_field(batch_id))
            await cq.answer()
            return

        if data.startswith("mt_"):
            rest = data[len("mt_"):]
            media_type, batch_id = rest.split("_", 1)
            await db.update_batch_field(batch_id, "mediatype", media_type)
            await cq.message.edit_text(f"🎞️ **Mediatype updated!**\nCurrent: `{media_type}`", reply_markup=kb_mediatype(batch_id, media_type))
            await cq.answer(f"Set to {media_type}")
            return
        if data.startswith("seqsort_"):
            rest = data[len("seqsort_"):]
            mode_str, session_uid_str = rest.split("_", 1)
            mode = int(mode_str)
            session_uid = int(session_uid_str)
            if uid != session_uid:
                await cq.answer("This isn't for you.", show_alert=True)
                return
            session = sequence_sessions.get(session_uid)
            if not session or not session.get("files"):
                await cq.answer("No files found.", show_alert=True)
                return

            await cq.message.edit_text("🔀 **Sorting files...**")

            entries = []
            skipped = []
            for msg in session["files"]:
                fname = get_msg_fname(msg)
                s, e, q = extract_file_info(fname)
                missing_field = find_missing_field(s, e, q)
                if missing_field:
                    skipped.append((fname, missing_field))
                    continue
                entries.append({"message": msg, "season": s, "episode": e, "quality": q})

            if skipped:
                lines = [f"🛑 **{len(skipped)} file(s) skipped** — required info missing:"]
                for fname, mf in skipped[:55]:
                    lines.append(f"• `{fname[:50]}` — {mf} not found")
                if len(skipped) > 55:
                    lines.append(f"\n_…and {len(skipped) - 55} more._")
                await client.send_message(session_uid, "\n".join(lines))

            if not entries:
                sequence_sessions.pop(session_uid, None)
                await client.send_message(session_uid, "❌ No files left to sort — sequence cancelled.")
                await cq.answer("Nothing to sort")
                return

            entries.sort(key=lambda x: sort_key_for_mode((x["season"], x["episode"], x["quality"]), mode))
            session["sorted_entries"] = entries
            session["mode"] = mode

            for e in entries:
                try:
                    await e["message"].copy(chat_id=session_uid)
                    await asyncio.sleep(0.3)
                except Exception as ex:
                    print(f"Failed to forward file during sort preview: {ex}")

            summary = generate_sort_summary(entries, mode)
            await client.send_message(session_uid, f"📁 **{len(entries)} file(s) sorted.**\n\n{summary}",
                                       reply_markup=kb_queue_confirm(session_uid))
            await cq.answer("Sorted!")
            return
        if data.startswith("seq_enqueue_"):
            session_uid = int(data[len("seq_enqueue_"):])
            if uid != session_uid:
                await cq.answer("This isn't for you.", show_alert=True)
                return
            session = sequence_sessions.get(session_uid)
            if not session or "sorted_entries" not in session:
                await cq.answer("No sorted files to enqueue.", show_alert=True)
                return
            entries = session["sorted_entries"]
            job = {
                "batch_id": session["batch_id"],
                "files": [{"message": e["message"], "season": e["season"], "episode": e["episode"], "quality": e["quality"]} for e in entries],
                "requested_by": session_uid,
                "chat_id": session_uid,
            }
            await file_queue.put(job)
            sequence_sessions.pop(session_uid, None)
            await cq.message.edit_text(f"✅ **{len(entries)} file(s) added to the queue in sorted order!**", reply_markup=None)
            await cq.answer("Queued!")
            return

        if data == "seq_cancel":
            sequence_sessions.pop(uid, None)
            await cq.message.edit_text("❌ Sequence cancelled.")
            await cq.answer("Cancelled")
            return
        if data.startswith("autopost_pick_"):
            batch_id = data[len("autopost_pick_"):]
            batch = await db.get_batch(batch_id)
            if not batch:
                await cq.message.edit_text("❌ This batch no longer exists.")
                await cq.answer()
                return
            auto_post_sessions[uid] = {"batch_id": batch_id}
            batches = await db.list_batches()
            enc = await db.get_encode()
            ladder = " → ".join(enc["ladder"]) if enc["ladder"] else "none configured"
            await cq.message.edit_text(
                f"✅ **Auto Post Mode ON** — batch set to `{batch['name']}`.\n\n"
                "Every file you send now goes straight to this batch, no Anime Names matching. "
                "Tap another batch to switch, or /stop_auto_post to turn this off.\n\n"
                f"🧲 You can also send a **magnet link / .torrent** now — I'll download the video and build the "
                f"**{ladder}** ladder for this batch. Include the season/episode in the same message if the "
                "torrent name doesn't have it, e.g. `S02E07 <magnet>`.",
                reply_markup=kb_autopost_batches(batches, batch_id),
            )
            await cq.answer(f"Auto Post → {batch['name']}")
            return

        if data == "autopost_cancel":
            await cq.message.edit_text("❌ Cancelled.")
            await cq.answer()
            return

        await cq.answer()
    except Exception as e:
        print(f"Error in callback handler: {e}")
        try:
            await cq.answer("Something went wrong.", show_alert=True)
        except Exception:
            pass

# ==================== UNAUTHORIZED-ACCESS LOGGER ====================
# Deliberately silent to the user (outsiders get no reply at all, by design), but it prints
# the ID to the console. Without this, "the bot ignores me" is indistinguishable from "the bot
# is broken" — this is how you find out whether the ID in your .env is actually yours.
_logged_strangers: set = set()


@app.on_message(filters.private & ~filters.me, group=-3)
async def unauthorized_logger(client, message: Message):
    uid = message.from_user.id if message.from_user else None
    if not uid or is_staff(uid):
        return
    if uid in _logged_strangers:
        return          # log each stranger once, so a spammer can't flood the console
    _logged_strangers.add(uid)
    uname = f"@{message.from_user.username}" if message.from_user.username else "(no username)"
    name = message.from_user.first_name or ""
    print("=" * 60)
    print(f"🚫 IGNORED a message from a NON-STAFF user: {name} {uname}")
    print(f"   Their Telegram user ID is:  {uid}")
    if not Config.STAFF:
        print("   STAFF is EMPTY — set ADMIN in your .env, then restart:")
        print(f"       ADMIN={uid}")
    else:
        print(f"   Currently allowed: ADMIN={Config.ADMIN} MODERATOR={Config.MODERATOR}")
        print(f"   If {uid} is you, add it to ADMIN in .env and restart.")
    print("=" * 60)


# ==================== MAIN ====================
async def main():
    await cleanup_stale_directories()
    await app.start()
    await db.init_db()
    asyncio.create_task(queue_worker())
    me = await app.get_me()
    print(f"✅ Bot started as @{me.username}")
    print(f"✅ Bot ID: {me.id}")
    print(f"👑 Admins: {Config.ADMIN}")
    print(f"🛡️ Moderators: {Config.MODERATOR}")
    if not Config.STAFF:
        print("\n" + "!" * 60)
        print("🚨 NO ADMIN OR MODERATOR CONFIGURED — THE BOT WILL IGNORE EVERY MESSAGE.")
        print("!" * 60)
        print("The bot is connected to Telegram and looks healthy, but every handler is")
        print("gated on ADMIN/MODERATOR, so nothing you send it will get a reply.")
        print("")
        print("Fix it:")
        print("  1. Message @userinfobot on Telegram to get your numeric user ID.")
        print("  2. Put it in a file named exactly `.env`, NEXT TO bot.py:")
        print("         ADMIN=123456789")
        print("  3. Restart the bot.")
        print("")
        print(f"Looking for .env in: {os.path.abspath('.')}")
        print(f"   .env found here: {'YES' if os.path.isfile('.env') else 'NO  <-- this is the problem'}")
        if not os.path.isfile(".env"):
            strays = [f for f in os.listdir(".") if f.lower().startswith(".env") or f.lower() == "env.txt"]
            if strays:
                print(f"   ⚠️ But I DO see: {strays} — Windows Notepad silently appends `.txt`.")
                print("      Rename it to exactly `.env` (no extension).")
        print("!" * 60 + "\n")
    enc = get_encode_settings(await db.get_settings())
    _, codec_label = resolve_codec(enc)
    print(f"🎬 Encode ladder: {' → '.join(enc['ladder'])} ({codec_label}, CRF {enc['crf']}, "
          f"preset {enc['preset']}, tune {enc.get('tune')}, {enc.get('bit_depth', 8)}-bit, "
          f".{enc['container']}, audio {enc['audio']})")
    print(f"🎯 Size targets: {targets_summary(enc)} MB — enforced with maxrate/bufsize plus a "
          f"higher-CRF re-encode if a rung overshoots")
    settings = await db.get_settings()
    backup = settings.get("backup_channel")
    if backup and backup.get("id"):
        print(f"💾 Backup Channel: {backup.get('title')} — torrent rungs upload here first")
    else:
        print("⚠️ No Backup Channel set — torrent jobs will refuse to run until one is set via /bot_settings.")
    print("✅ Batch Auto-Rename Bot is ready.")
    await idle()
    await app.stop()

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    if FFMPEG:
        print(f"✅ FFmpeg is installed and working ({FFMPEG})")
    else:
        print("⚠️ WARNING: FFmpeg not found! Metadata embedding, Cover Image embedding and ALL torrent "
              "encoding will not work.")
    if FFPROBE:
        print(f"✅ FFprobe found ({FFPROBE})")
    else:
        print("⚠️ WARNING: FFprobe not found — durations and source resolution can't be detected, so "
              "upscale-skipping and encode progress percentages will be unavailable.")

    backend = torrent_backend()
    if backend == "libtorrent":
        print("✅ Torrent backend: libtorrent (preferred — inspects metadata before downloading)")
    elif backend == "aria2c":
        print(f"✅ Torrent backend: aria2c ({ARIA2C})")
        print("   _Tip: `pip install libtorrent` for metadata pre-checks and single-file selection._")
    else:
        print("⚠️ WARNING: No torrent backend! Magnet/.torrent links will be refused.")
        print("   Install one:  pip install libtorrent   —or—   apt install aria2")

    # Smoke-tests the hardware encoders and prints what this machine can actually do. Done here,
    # once, before the event loop starts, because each probe spawns a short ffmpeg run.
    probe_encoder_caps(verbose=True)

    print("\n" + "=" * 60)
    print("🚀 Starting Batch Auto-Rename Bot...")
    print("=" * 60)
    print(f"👑 Admins: {Config.ADMIN}")
    print(f"🛡️ Moderators: {Config.MODERATOR}")
    print(f"📦 Max File Size: {humanbytes(Config.MAX_FILE_SIZE)}")
    print(f"🧲 Max Torrent Size: {humanbytes(Config.MAX_TORRENT_SIZE) if Config.MAX_TORRENT_SIZE else 'unlimited'}")
    print("📁 Commands: /new_batch /edit_batch /delete_channel")
    print("📢 Channel: /register (in a channel, as admin) or add-by-link → Sub/Main Channel via /edit_batch, "
          "Backup/Thumb-Cover Channel via /bot_settings (admins only)")
    print("🔄 Sequence: /ssequence /esequence /sequence_mode [1|2|3]")
    print("🤖 Auto Post: /auto_post /stop_auto_post")
    print("🧲 Torrent: send a magnet/.torrent while /auto_post is on — /encode_settings /torrent_check /cancel_job")
    print("🤖 Bot is running. Press Ctrl+C to stop.")
    print("=" * 60 + "\n")
    try:
        app.run(main())
    except KeyboardInterrupt:
        print("\n👋 Bot stopped by user")
    except Exception as e:
        print(f"❌ Error: {e}")
        import traceback
        traceback.print_exc()
