"""Unified cross-agent memory hub (AI-to-AI temporal facts + single Obsidian vault wiki).

Operates directly on one Obsidian vault (MEMORY_VAULT_DIR) so Claude, ChatGPT,
Hermes (and its profiles), Antigravity and Obsidian share ONE memory system.

Enforces global read (except 'personal/*', which is strictly private to owner)
and scoped write:
  - open scopes (settings "open_scopes", default shared, projects/<slug>, resources/books):
    writable by all authenticated agents
  - agents/claude, agents/chatgpt, agents/antigravity: writable ONLY by that agent (+ owner)
  - agents/<hermes-profile> (settings "hermes.subagents"): writable ONLY by that profile (+ owner)
  - agents/hermes & agents/{decisions,gotchas,playbooks,research}: writable by any Hermes profile (+ owner)
  - personal/*: strictly never indexed or writable by AI agents

Deployment-specific names (areas, aliases, Hermes profiles, dashboard layout, timezone)
come from the JSON file named by MEMORY_SETTINGS; see settings.example.json.
"""
from __future__ import annotations

import base64
import hashlib
import hmac
import html
import io
import json
import os
import queue
import re
import secrets
import sqlite3
import stat
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import xml.parsers.expat as expat
import zipfile
import zlib
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path


def _load_settings() -> dict:
    path = os.environ.get("MEMORY_SETTINGS", "").strip()
    if not path:
        return {}
    raw = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("MEMORY_SETTINGS must be a JSON object")
    for k in ("open_scopes", "briefing_areas", "areas", "nested_scopes"):
        if k in raw and (not isinstance(raw[k], list) or not all(isinstance(x, str) for x in raw[k])):
            raise ValueError(f"MEMORY_SETTINGS.{k} must be a list of strings")
    for k in ("scope_aliases", "hermes", "dashboard"):
        if k in raw and not isinstance(raw[k], dict):
            raise ValueError(f"MEMORY_SETTINGS.{k} must be an object")
    if "hermes" in raw:
        h = raw["hermes"]
        for k in ("subagents", "extra_write"):
            if k in h and (not isinstance(h[k], list) or not all(isinstance(x, str) for x in h[k])):
                raise ValueError(f"MEMORY_SETTINGS.hermes.{k} must be a list of strings")
        if "aliases" in h and not isinstance(h["aliases"], dict):
            raise ValueError("MEMORY_SETTINGS.hermes.aliases must be an object")
    return raw


SETTINGS: dict = _load_settings()
LOCAL_TZ = ZoneInfo(SETTINGS.get("timezone") or "UTC")
SUPPORTED_VAULT_EXTENSIONS = (".md", ".docx", ".pdf")
MAX_BINARY_DOC_BYTES = 64 * 1024 * 1024
MAX_UPLOAD_BODY_BYTES = 32 * 1024 * 1024
MAX_DOCX_ZIP_ENTRIES = 10_000
AGENTS = ("claude", "chatgpt", "hermes", "antigravity")
_HERMES = SETTINGS.get("hermes", {})
HERMES_SUBAGENTS: tuple[str, ...] = tuple(_HERMES.get("subagents", ["default"]))
# Other names for a profile, e.g. {"main": "default"}; the scope is agents/<target>.
HERMES_ALIASES: dict[str, str] = dict(_HERMES.get("aliases", {}))
# Extra scopes any Hermes profile may write besides its own and the shared Hermes ones.
HERMES_EXTRA_WRITE: tuple[str, ...] = tuple(_HERMES.get("extra_write", []))
HERMES_SHARED_AGENT_SCOPES = (
    "agents/hermes",
    "agents/decisions",
    "agents/gotchas",
    "agents/playbooks",
    "agents/research",
)
# Scopes every agent may write; "x/*" also covers x and everything under it.
OPEN_SCOPES: tuple[str, ...] = tuple(SETTINGS.get("open_scopes", ["shared", "projects/*", "resources/books"]))
DEFAULT_SCOPE: str = SETTINGS.get("default_scope", "shared")
# Areas whose facts the briefing lists separately as "<area>_facts".
BRIEFING_AREAS: tuple[str, ...] = tuple(SETTINGS.get("briefing_areas", []))
# Top-level vault folders whose second segment is a scope (projects/<slug>, business/<area>, ...).
AREAS: tuple[str, ...] = tuple(SETTINGS.get("areas", ["projects", "business", "resources"]))
# Folders whose children are scopes one level deeper (e.g. "career/company" -> career/company/<name>).
NESTED_SCOPES: tuple[str, ...] = tuple(SETTINGS.get("nested_scopes", []))
READABLE_SCOPES: list[str] = ["shared", *(f"{a}/*" for a in AREAS), "agents/*", "daily", "inbox"]
# Shorthand -> scope prefix rewrites, e.g. {"acme": "career/company/acme"}; longest key wins.
SCOPE_ALIASES: dict[str, str] = {k.lower(): v.lower() for k, v in SETTINGS.get("scope_aliases", {}).items()}
SKIP_VAULT_TOP_DIRS = {".obsidian", ".sync", ".git", "personal", "templates", "memory"}
SKIP_VAULT_ROOT_FILES = {"Home.md", "README.md", "AGENTS.md", "INDEX.md", "00-AI-Memory-Snapshot.md"}
SKIP_VAULT_GENERATED_FILES = {"shared/00-AI-Memory-Snapshot.md", "shared/00-Memory-Index.md"}


VALID_CATEGORIES = ("weakness", "strength", "progress", "decision", "preference", "question", "fact")
TOKEN_ENV_MAP = {
    "owner": "MEMORY_OWNER_TOKEN",
    "hermes": "MEMORY_HERMES_TOKEN",
    "claude": "MEMORY_CLAUDE_TOKEN",
    "chatgpt": "MEMORY_CHATGPT_TOKEN",
    "antigravity": "MEMORY_ANTIGRAVITY_TOKEN",
}

DATA_DIR = Path(os.environ.get("MEMORY_DATA_DIR", "/data"))
_raw_vault_dir = Path(os.environ.get("MEMORY_VAULT_DIR", "/opt/vault"))
VAULT_DIR = (
    _raw_vault_dir.parent
    if (_raw_vault_dir.name == "memory" and _raw_vault_dir.parent.name == "vault")
    else _raw_vault_dir
)
PUBLIC_URL = os.environ.get("MEMORY_PUBLIC_URL", "http://127.0.0.1:8770").rstrip("/")
# Optional Omni sign-in for the web dashboard and MCP OAuth (empty = owner token only).
OMNI_PUBLIC_URL = os.environ.get("OMNI_PUBLIC_URL", "").rstrip("/")
OMNI_INTERNAL_URL = os.environ.get("OMNI_INTERNAL_URL", OMNI_PUBLIC_URL).rstrip("/")
OMNI_MEMORY_KEY = os.environ.get("OMNI_MEMORY_KEY", "").strip()
MEMORY_ADMIN_EMAILS = {
    e.strip().lower()
    for e in os.environ.get("MEMORY_ADMIN_EMAILS", "").split(",")
    if e.strip()
}
PORT = int(os.environ.get("MEMORY_PORT", "8770"))
# Hosts allowed to receive OAuth codes; any other https host could phish a code through the owner's approval click.
OAUTH_REDIRECT_HOSTS = {
    h.strip().lower()
    for h in os.environ.get("MEMORY_OAUTH_REDIRECT_HOSTS", "claude.ai,claude.com,chatgpt.com,chat.openai.com").split(",")
    if h.strip()
}


class MemoryError(Exception):
    """User-safe validation or lookup error."""
    status = 400


class MemoryPermissionError(MemoryError):
    """Raised when an agent attempts to write outside its allowed scopes."""
    status = 403


class MemoryPayloadTooLargeError(MemoryError):
    """Raised when a request body exceeds the allowed byte ceiling."""
    status = 413


class MemoryLengthRequiredError(MemoryError):
    """Raised when Transfer-Encoding is sent instead of a bounded Content-Length."""
    status = 411


def _safe_int(val: object, field: str, default: int = 0) -> int:
    if val is None or val == "" or isinstance(val, bool):
        return default
    try:
        return int(str(val).strip())
    except (ValueError, TypeError) as exc:
        raise MemoryError(f"Invalid integer for {field}: {val!r}") from exc


def allowed_admin_emails() -> set[str]:
    raw = os.environ.get("MEMORY_ADMIN_EMAILS", "").strip()
    if raw:
        return {e.strip().lower() for e in raw.split(",") if e.strip()}
    return MEMORY_ADMIN_EMAILS


def now_local() -> str:
    return datetime.now(LOCAL_TZ).strftime("%Y-%m-%d %H:%M:%S %Z")


def configured_tokens() -> dict[str, str]:
    out: dict[str, str] = {}
    for role, env_key in TOKEN_ENV_MAP.items():
        val = os.environ.get(env_key, "").strip()
        if val:
            out[role] = val
    return out


def normalize_actor(actor: str, subagent: str | None = None) -> str:
    base = (actor or "").strip().lower()
    sub = (subagent or "").strip().lower()
    if base.startswith("hermes/"):
        _, bound_sub = base.split("/", 1)
        if sub:
            cleaned_req = slugify_segment(sub).lower()
            if cleaned_req != bound_sub:
                raise MemoryPermissionError(
                    f"Cannot override bound Hermes sub-agent identity {base!r} with {sub!r}"
                )
        return f"hermes/{bound_sub}"
    if sub and base not in ("hermes", "owner"):
        raise MemoryPermissionError(f"Actor {base!r} cannot assume Hermes sub-agent identity {sub!r}")
    if base == "hermes" and sub:
        cleaned_sub = slugify_segment(sub).lower()
        if cleaned_sub not in HERMES_SUBAGENTS:
            raise MemoryError(
                f"Unknown Hermes sub-agent {sub!r}; expected one of: {', '.join(HERMES_SUBAGENTS)}"
            )
        return f"hermes/{cleaned_sub}"
    return base


def owner_session_email() -> str:
    """Session email for browser sessions opened with MEMORY_OWNER_TOKEN, bound to the current token value
    so rotating or removing the token ends them."""
    tok = configured_tokens().get("owner", "")
    return "owner@token:" + hashlib.sha256(tok.encode()).hexdigest()[:32] if tok else ""


def owner_email_ok(email: str) -> bool:
    """A browser session or approval email that still grants owner: listed in MEMORY_ADMIN_EMAILS (Omni sign-in)
    or equal to the current owner-token session email."""
    email = email.strip().lower()
    owner_email = owner_session_email()
    return email in allowed_admin_emails() or bool(owner_email and hmac.compare_digest(email, owner_email))


def web_session_email(db: sqlite3.Connection, token: str) -> str | None:
    """Email of a live vms_ browser session that still grants owner, else None."""
    if not token.startswith("vms_"):
        return None
    with DB_LOCK:
        sess = db.execute(
            "SELECT email, expires_at FROM web_sessions WHERE token_hash = ?",
            (hashlib.sha256(token.encode()).hexdigest(),),
        ).fetchone()
    if sess and sess["expires_at"] > time.time() and owner_email_ok(str(sess["email"] or "")):
        return str(sess["email"]).strip().lower()
    return None


def oauth_parent_valid(parent: str, actor: str) -> bool:
    """An OAuth code/token stays valid only while the credential that approved it does:
    'role:<sha256 of the role token>' or 'email:<approving session email>'."""
    kind, _, ref = parent.partition(":")
    if kind == "role":
        return any(
            hmac.compare_digest(hashlib.sha256(v.encode()).hexdigest(), ref)
            for r, v in configured_tokens().items()
            if r != "owner"
        )
    if kind == "email":
        return owner_email_ok(ref)
    # ponytail: rows from before parent binding keep working for agent roles so existing phone connectors
    # survive the upgrade; owner-actor rows are revoked. Delete oauth_tokens rows to force a reconnect.
    return not parent and actor != "owner"


def resolve_actor_from_token(
    candidate: str | None,
    db: sqlite3.Connection | None = None,
    subagent: str | None = None,
) -> str | None:
    if not candidate:
        return None
    token = candidate.strip()
    if not token:
        return None
    for role, secret in configured_tokens().items():
        if hmac.compare_digest(secret, token):
            return normalize_actor(role, subagent if role == "hermes" else None)
    if db is not None:
        tok_hash = hashlib.sha256(token.encode()).hexdigest()
        now_ts = time.time()
        with DB_LOCK:
            if token.startswith("vms_"):
                return "owner" if web_session_email(db, token) else None
            row = db.execute(
                "SELECT actor, parent, last_used, expires_at FROM oauth_tokens WHERE token_hash = ?",
                (tok_hash,),
            ).fetchone()
            if row and now_ts - row["last_used"] > 300:  # for the Connected apps page; at most one write per 5 min
                db.execute("UPDATE oauth_tokens SET last_used = ? WHERE token_hash = ?", (now_ts, tok_hash))
                db.commit()
        if row and row["expires_at"] > now_ts and oauth_parent_valid(str(row["parent"]), str(row["actor"])):
            stored_actor = str(row["actor"])
            return normalize_actor(stored_actor, subagent if stored_actor == "hermes" else None)
    return None


def slugify_segment(part: str) -> str:
    cleaned = re.sub(r"[^a-zA-Z0-9._-]+", "-", part.strip()).strip("-.")
    if not cleaned or cleaned in (".", ".."):
        raise MemoryError(f"Invalid path or scope segment: {part!r}")
    return cleaned


def valid_agent_scope_names() -> tuple[str, ...]:
    return (
        *AGENTS,
        *HERMES_SUBAGENTS,
        *HERMES_ALIASES,
        "decisions",
        "gotchas",
        "playbooks",
        "research",
        "memories",
        "content",
    )


def hermes_profile(name: str) -> str | None:
    """Canonical Hermes profile for a profile name or alias, or None if unknown."""
    name = HERMES_ALIASES.get(name, name)
    return name if name in HERMES_SUBAGENTS else None


def apply_scope_aliases(value: str) -> str:
    """Rewrite a leading shorthand from settings scope_aliases (case-insensitive, longest key first)."""
    for _ in range(4):
        low = value.lower()
        key = next(
            (k for k in sorted(SCOPE_ALIASES, key=len, reverse=True) if low == k or low.startswith(k + "/")),
            None,
        )
        if key is None:
            break
        value = SCOPE_ALIASES[key] + value[len(key):]
    return value


def area_scope_depth(parts: list[str]) -> int:
    """How many leading segments of an area path (with a file name last) form its scope."""
    if len(parts) < 3:
        return 1
    if len(parts) >= 4 and "/".join(parts[:2]).lower() in NESTED_SCOPES:
        return 3
    return 2


def _normalize_scope_once(raw_scope: str | None) -> str:
    s = (raw_scope or "").strip().strip("/")
    if not s or s.lower() in ("common", "global", "shared"):
        return "shared"
    lower = apply_scope_aliases(s.lower())
    if lower == "personal" or lower.startswith("personal/"):
        raise MemoryPermissionError("Scope 'personal' is strictly private and never accessible via vyn-memory.")
    if lower.startswith("hermes/"):
        prof = hermes_profile(slugify_segment(lower.split("/", 1)[1]).lower())
        if prof:
            return f"agents/{prof}"
    if lower in valid_agent_scope_names():
        return f"agents/{HERMES_ALIASES.get(lower, lower)}"
    if lower.startswith("agent/"):
        lower = "agents/" + lower.split("/", 1)[1]
    if lower.startswith("agents/"):
        parts = [p for p in lower.split("/") if p]
        if len(parts) >= 3 and parts[1] == "hermes" and hermes_profile(parts[2]):
            return f"agents/{hermes_profile(parts[2])}"
        if len(parts) < 2 or parts[1] not in valid_agent_scope_names():
            raise MemoryError(
                f"Invalid agent scope {raw_scope!r}; expected 'agents/<agent>' where <agent> is one of: "
                + ", ".join(valid_agent_scope_names())
            )
        return f"agents/{HERMES_ALIASES.get(parts[1], parts[1])}"
    if lower.startswith("project/"):
        lower = "projects/" + lower.split("/", 1)[1]
    if lower.startswith("projects/"):
        slug = slugify_segment(lower.split("/", 1)[1].split("/")[0]).lower()
        return f"projects/{slug}"
    top = lower.split("/", 1)[0]
    if top in AREAS:
        segs = [slugify_segment(p).lower() for p in lower.split("/") if p]
        return "/".join(segs[: 3 if "/".join(segs[:2]) in NESTED_SCOPES else 2])
    if lower in ("daily", "inbox"):
        return lower
    return f"projects/{slugify_segment(lower).lower()}"


def normalize_scope(raw_scope: str | None) -> str:
    """Normalize a scope string to a canonical fixpoint (idempotent across aliases and slugification)."""
    first = _normalize_scope_once(raw_scope)
    second = _normalize_scope_once(first)
    return second


def _scope_matches(norm: str, pattern: str) -> bool:
    base = pattern.removesuffix("/*")
    return norm == base or norm.startswith(base + "/")


def writable_scopes_for(actor: str) -> list[str]:
    norm_actor = (actor or "").strip().lower()
    hermes_shared = [*HERMES_SHARED_AGENT_SCOPES, *HERMES_EXTRA_WRITE]
    if norm_actor == "owner":
        return list(dict.fromkeys([*OPEN_SCOPES, "agents/*", *(f"{a}/*" for a in AREAS), "daily", "inbox"]))
    if norm_actor in ("claude", "chatgpt", "antigravity"):
        return [*OPEN_SCOPES, f"agents/{norm_actor}"]
    if norm_actor == "hermes":
        return [*OPEN_SCOPES, *hermes_shared]
    if norm_actor.startswith("hermes/"):
        sub = norm_actor.split("/", 1)[1]
        return [*OPEN_SCOPES, f"agents/{sub}", *hermes_shared]
    return []


def can_write(actor: str, scope: str) -> bool:
    norm = normalize_scope(scope)
    norm_actor = (actor or "").strip().lower()
    if norm == "personal" or norm.startswith("personal/"):
        return False
    if norm_actor == "owner":
        return True
    if any(_scope_matches(norm, p) for p in OPEN_SCOPES):
        return norm_actor in AGENTS or norm_actor.startswith("hermes/")
    if norm_actor in ("claude", "chatgpt", "antigravity"):
        return norm == f"agents/{norm_actor}"
    hermes_shared = (*HERMES_SHARED_AGENT_SCOPES, *HERMES_EXTRA_WRITE)
    if norm_actor == "hermes":
        return norm in hermes_shared
    if norm_actor.startswith("hermes/"):
        sub = norm_actor.split("/", 1)[1]
        return norm in (f"agents/{sub}", f"agents/{HERMES_ALIASES.get(sub, sub)}") or norm in hermes_shared
    return False


def check_write_permission(actor: str, scope: str) -> str:
    norm = normalize_scope(scope)
    if not can_write(actor, norm):
        allowed = ", ".join(repr(s) for s in writable_scopes_for(actor))
        raise MemoryPermissionError(
            f"Scope {norm!r} is read-only for actor {actor!r}. "
            f"All agents can read {norm!r}, but only its owning agent/sub-agent (or 'owner') may write to it. "
            f"Writable scopes for {actor!r}: {allowed}."
        )
    return norm


def normalize_note_path(
    raw_path: str,
    explicit_scope: str = "",
    *,
    allow_binary_ext: bool = False,
) -> tuple[str, str]:
    """Return (scope, relative_vault_path) for a note/document path in the unified Obsidian vault."""
    cleaned = (raw_path or "").strip().replace("\\", "/").lstrip("/")
    if not cleaned:
        raise MemoryError("Note path is required")
    parts = [p for p in cleaned.split("/") if p and p != "."]
    if any(p == ".." for p in parts):
        raise MemoryError("Relative parent traversal ('..') is not allowed")
    if parts[0].lower() == "memory" and len(parts) > 1:
        # Transparently strip legacy 'memory/' prefix so old links resolve cleanly
        parts = parts[1:]
    parts = [p for p in apply_scope_aliases("/".join(parts)).split("/") if p]
    if parts[0].lower() in SKIP_VAULT_TOP_DIRS:
        raise MemoryPermissionError(f"Directory {parts[0]!r} is not accessible via vyn-memory")
    top = parts[0].lower()

    if explicit_scope.strip():
        scope = normalize_scope(explicit_scope)
        scope_parts = scope.split("/")
        norm_head = [p.lower() for p in parts[: len(scope_parts)]]
        if norm_head == scope_parts:
            rel_parts = parts[len(scope_parts) :]
        elif top == "agents" and len(parts) >= 3 and parts[1].lower() == "hermes" and scope == f"agents/{parts[2].lower()}":
            rel_parts = parts[3:]
        else:
            rel_parts = parts
    elif top == "shared":
        scope = "shared"
        rel_parts = parts[1:]
    elif top in ("agents", "agent") and len(parts) >= 2:
        if parts[1].lower() == "hermes" and len(parts) >= 3 and parts[2].lower() in HERMES_SUBAGENTS:
            scope = f"agents/{HERMES_ALIASES.get(parts[2].lower(), parts[2].lower())}"
            rel_parts = parts[3:]
        else:
            scope = normalize_scope(f"agents/{parts[1]}")
            rel_parts = parts[2:]
    elif top in ("projects", "project") and len(parts) >= 2:
        scope = normalize_scope(f"projects/{parts[1]}")
        rel_parts = parts[2:]
    elif top in AREAS and len(parts) >= 2:
        depth = area_scope_depth(parts)
        scope = "/".join(slugify_segment(p).lower() for p in parts[:depth])
        rel_parts = parts[depth:]
    elif top in ("daily", "inbox") and len(parts) >= 2:
        scope = top
        rel_parts = parts[1:]
    elif top in valid_agent_scope_names() and len(parts) >= 2:
        scope = f"agents/{HERMES_ALIASES.get(top, top)}"
        rel_parts = parts[1:]
    elif len(parts) >= 2:
        scope = normalize_scope(f"projects/{parts[0]}")
        rel_parts = parts[1:]
    else:
        scope = normalize_scope(DEFAULT_SCOPE)
        rel_parts = parts

    if not rel_parts:
        raise MemoryError(f"Note filename missing after scope {scope!r}")
    safe_rel = [slugify_segment(seg) for seg in rel_parts]
    last_low = safe_rel[-1].lower()
    if allow_binary_ext and last_low.endswith(SUPPORTED_VAULT_EXTENSIONS):
        pass
    elif not last_low.endswith(".md"):
        safe_rel[-1] = f"{safe_rel[-1]}.md"
    full_rel = "/".join([*scope.split("/"), *safe_rel])
    return scope, full_rel


SCHEMA = """
PRAGMA journal_mode = WAL;
PRAGMA synchronous = NORMAL;
PRAGMA foreign_keys = ON;

CREATE TABLE IF NOT EXISTS facts (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    scope TEXT NOT NULL,
    subject TEXT NOT NULL DEFAULT '',
    category TEXT NOT NULL DEFAULT 'fact',
    fact TEXT NOT NULL,
    author TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'active',
    superseded_by INTEGER,
    supersedes_id INTEGER,
    invalidated_by TEXT NOT NULL DEFAULT '',
    invalidated_reason TEXT NOT NULL DEFAULT '',
    valid_from TEXT NOT NULL,
    valid_until TEXT,
    updated_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS ix_facts_scope_status ON facts(scope, status);
CREATE INDEX IF NOT EXISTS ix_facts_subject ON facts(scope, subject, status);

CREATE VIRTUAL TABLE IF NOT EXISTS facts_fts USING fts5(
    scope,
    subject,
    category,
    fact,
    author
);

CREATE TABLE IF NOT EXISTS notes (
    path TEXT PRIMARY KEY,
    scope TEXT NOT NULL,
    title TEXT NOT NULL,
    summary TEXT NOT NULL DEFAULT '',
    tags TEXT NOT NULL DEFAULT '[]',
    body TEXT NOT NULL,
    updated_by TEXT NOT NULL DEFAULT 'owner',
    updated_at TEXT NOT NULL,
    sha256 TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS ix_notes_scope ON notes(scope);

CREATE VIRTUAL TABLE IF NOT EXISTS notes_fts USING fts5(
    path,
    scope,
    title,
    summary,
    tags,
    body
);

CREATE TABLE IF NOT EXISTS note_links (
    source_path TEXT NOT NULL,
    target_slug TEXT NOT NULL,
    relation_type TEXT NOT NULL DEFAULT 'links_to',
    PRIMARY KEY (source_path, target_slug)
);
CREATE INDEX IF NOT EXISTS ix_note_links_target ON note_links(target_slug);

CREATE TABLE IF NOT EXISTS note_observations (
    source_path TEXT NOT NULL,
    category TEXT NOT NULL,
    observation TEXT NOT NULL,
    tags TEXT NOT NULL DEFAULT '[]',
    line_num INTEGER NOT NULL DEFAULT 0
);
CREATE INDEX IF NOT EXISTS ix_note_obs_source ON note_observations(source_path);
CREATE INDEX IF NOT EXISTS ix_note_obs_cat ON note_observations(category);

CREATE TABLE IF NOT EXISTS oauth_codes (
    code_hash TEXT PRIMARY KEY,
    actor TEXT NOT NULL,
    client_id TEXT NOT NULL,
    redirect_uri TEXT NOT NULL,
    code_challenge TEXT NOT NULL,
    resource TEXT NOT NULL DEFAULT '',
    parent TEXT NOT NULL DEFAULT '',
    expires_at REAL NOT NULL
);

CREATE TABLE IF NOT EXISTS oauth_tokens (
    token_hash TEXT PRIMARY KEY,
    refresh_hash TEXT NOT NULL DEFAULT '',
    actor TEXT NOT NULL,
    client_id TEXT NOT NULL,
    resource TEXT NOT NULL DEFAULT '',
    parent TEXT NOT NULL DEFAULT '',
    label TEXT NOT NULL DEFAULT '',
    last_used REAL NOT NULL DEFAULT 0,
    created_at REAL NOT NULL,
    expires_at REAL NOT NULL
);

CREATE TABLE IF NOT EXISTS device_codes (
    device_hash TEXT PRIMARY KEY,
    user_code TEXT NOT NULL UNIQUE,
    label TEXT NOT NULL,
    role_hint TEXT NOT NULL,
    ip TEXT NOT NULL,
    actor TEXT NOT NULL DEFAULT '',
    parent TEXT NOT NULL DEFAULT '',
    expires_at REAL NOT NULL
);

CREATE TABLE IF NOT EXISTS web_auth_states (
    state_hash TEXT PRIMARY KEY,
    next_path TEXT NOT NULL,
    expires_at REAL NOT NULL
);

CREATE TABLE IF NOT EXISTS web_sessions (
    token_hash TEXT PRIMARY KEY,
    email TEXT NOT NULL,
    created_at REAL NOT NULL,
    expires_at REAL NOT NULL
);
"""

DB_LOCK = threading.RLock()


def ensure_schema_migrations(conn: sqlite3.Connection) -> None:
    fact_cols = {r["name"] for r in conn.execute("PRAGMA table_info(facts)").fetchall()}
    if "invalidated_by" not in fact_cols:
        conn.execute("ALTER TABLE facts ADD COLUMN invalidated_by TEXT NOT NULL DEFAULT ''")
    if "invalidated_reason" not in fact_cols:
        conn.execute("ALTER TABLE facts ADD COLUMN invalidated_reason TEXT NOT NULL DEFAULT ''")
    link_cols = {r["name"] for r in conn.execute("PRAGMA table_info(note_links)").fetchall()}
    if "relation_type" not in link_cols:
        conn.execute("ALTER TABLE note_links ADD COLUMN relation_type TEXT NOT NULL DEFAULT 'links_to'")
    oauth_tok_cols = {r["name"] for r in conn.execute("PRAGMA table_info(oauth_tokens)").fetchall()}
    if "refresh_hash" not in oauth_tok_cols:
        conn.execute("ALTER TABLE oauth_tokens ADD COLUMN refresh_hash TEXT NOT NULL DEFAULT ''")
    if "parent" not in oauth_tok_cols:
        conn.execute("ALTER TABLE oauth_tokens ADD COLUMN parent TEXT NOT NULL DEFAULT ''")
    if "label" not in oauth_tok_cols:
        conn.execute("ALTER TABLE oauth_tokens ADD COLUMN label TEXT NOT NULL DEFAULT ''")
        conn.execute("ALTER TABLE oauth_tokens ADD COLUMN last_used REAL NOT NULL DEFAULT 0")
    if "parent" not in {r["name"] for r in conn.execute("PRAGMA table_info(oauth_codes)").fetchall()}:
        conn.execute("ALTER TABLE oauth_codes ADD COLUMN parent TEXT NOT NULL DEFAULT ''")
    conn.commit()


def open_db() -> sqlite3.Connection:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    db_file = DATA_DIR / "memory.db"
    conn = sqlite3.connect(str(db_file), timeout=15.0, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    conn.executescript(SCHEMA)
    ensure_schema_migrations(conn)
    return conn


def serialize_fact(row: sqlite3.Row | dict[str, object]) -> dict[str, object]:
    d = dict(row)
    status = str(d.get("status") or "active")
    is_valid = status == "active"
    d["is_valid"] = is_valid
    d["validity"] = "valid" if is_valid else "invalid"
    d["invalidated_at"] = d.get("valid_until")
    return d


_VAULT_STAT_CACHE: dict[str, tuple[tuple[int, int, int], str]] = {}  # rel -> ((inode, mtime_ns, size), sha256)


def assert_safe_vault_path(target: Path, *, allow_root_dashboard: bool = False) -> Path:
    """Reject symlinks along any path component and enforce containment within VAULT_DIR."""
    VAULT_DIR.mkdir(parents=True, exist_ok=True)
    vault_real = VAULT_DIR.resolve()
    try:
        rel_parts = target.relative_to(VAULT_DIR).parts
    except ValueError:
        try:
            rel_parts = target.relative_to(vault_real).parts
        except ValueError as exc:
            raise MemoryPermissionError("Target path escapes the Obsidian vault root") from exc

    cur = VAULT_DIR
    for part in rel_parts:
        if part in ("", ".", ".."):
            raise MemoryPermissionError("Invalid relative path component in vault path")
        cur = cur / part
        if cur.is_symlink():
            raise MemoryPermissionError(f"Symlinks inside the vault are not accessible via vyn-memory: {part!r}")

    resolved = cur.resolve()
    if not resolved.is_relative_to(vault_real):
        raise MemoryPermissionError("Resolved path escapes the Obsidian vault root")
    rel_posix = resolved.relative_to(vault_real).as_posix()
    if not allow_root_dashboard and not should_index_vault_file(rel_posix):
        raise MemoryPermissionError(f"Vault path {rel_posix!r} is restricted and not accessible via vyn-memory")
    return resolved


def _vault_dir_fd(parts: list[str], *, create: bool = False) -> int:
    """fd of VAULT_DIR/<parts> reached without following any symlink (O_NOFOLLOW per component).
    Checking a path and then reopening it by name lets a swapped-in symlink win, so reads and writes go through fds."""
    if any(p in ("", ".", "..") for p in parts):
        raise MemoryPermissionError("Invalid vault path")
    dfd = os.open(VAULT_DIR, os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in parts:
            if create:
                try:
                    os.mkdir(part, 0o755, dir_fd=dfd)
                except FileExistsError:
                    pass
            nfd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=dfd)
            os.close(dfd)
            dfd = nfd
    except OSError as exc:
        os.close(dfd)
        raise MemoryPermissionError("Vault path is not a plain directory inside the vault") from exc
    return dfd


def atomic_write_bytes(target: Path, raw_bytes: bytes, *, allow_root_dashboard: bool = False) -> Path:
    safe_target = assert_safe_vault_path(target, allow_root_dashboard=allow_root_dashboard)
    *dirs, leaf = safe_target.relative_to(VAULT_DIR.resolve()).parts
    dfd = _vault_dir_fd(dirs, create=True)
    tmp = f".{leaf}.{secrets.token_hex(4)}.tmp"
    try:
        fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644, dir_fd=dfd)
        with os.fdopen(fd, "wb") as fh:
            fh.write(raw_bytes)
        os.replace(tmp, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
    finally:
        os.close(dfd)
    return safe_target


def atomic_write_text(target: Path, text: str, *, allow_root_dashboard: bool = False) -> None:
    atomic_write_bytes(target, text.encode("utf-8"), allow_root_dashboard=allow_root_dashboard)


def read_vault_file(rel: str) -> tuple[bytes, os.stat_result]:
    """Read VAULT_DIR/rel as a regular single-link file, without following any symlink."""
    *dirs, leaf = [p for p in rel.split("/") if p] or [""]
    if leaf in ("", ".", ".."):
        raise MemoryPermissionError("Invalid vault path")
    dfd = _vault_dir_fd(dirs)
    try:
        fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
    except OSError as exc:
        raise MemoryPermissionError("Vault path is not a plain file inside the vault") from exc
    finally:
        os.close(dfd)
    with os.fdopen(fd, "rb") as fh:
        st = os.fstat(fh.fileno())
        if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
            raise MemoryPermissionError("Vault path is not a plain file inside the vault")
        return fh.read(), st


class _DoctypeFound(Exception):
    pass


def _declares_doctype(xml_bytes: bytes) -> bool:
    """True if the XML has a DOCTYPE, in any encoding expat reads (a byte search misses UTF-16)."""
    probe = expat.ParserCreate()

    def _stop(*_args: object) -> None:
        raise _DoctypeFound

    def _root(*_args: object) -> None:
        raise StopIteration  # a DOCTYPE can only come before the root element; stop reading there

    probe.StartDoctypeDeclHandler = _stop
    probe.StartElementHandler = _root
    try:
        probe.Parse(xml_bytes, True)
    except _DoctypeFound:
        return True
    except StopIteration:
        return False
    except expat.ExpatError:
        return False  # ET.fromstring reports the parse error itself
    return False


def extract_docx_markdown(file_path: Path, data: bytes, max_chars: int = 250_000) -> tuple[str, str]:
    """Extract clean Markdown (headings, bullet lists, and tables) from a .docx archive using stdlib only."""
    doc_title = file_path.stem.replace("-", " ").replace("_", " ")
    w_ns = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"
    dc_title_ns = "{http://purl.org/dc/elements/1.1/}title"
    lines: list[str] = []
    total_chars = 0
    truncated = False

    def _para_text(p_elem: ET.Element) -> str:
        parts: list[str] = []
        for elem in p_elem.iter():
            if elem.tag == f"{w_ns}t" and elem.text:
                parts.append(elem.text)
            elif elem.tag == f"{w_ns}tab":
                parts.append("\t")
            elif elem.tag in (f"{w_ns}br", f"{w_ns}cr"):
                parts.append("\n")
        return "".join(parts).strip()

    try:
        with zipfile.ZipFile(io.BytesIO(data), "r") as zf:
            if len(zf.infolist()) > MAX_DOCX_ZIP_ENTRIES:
                return doc_title, f"# {doc_title}\n\n*(DOCX archive rejected: exceeds {MAX_DOCX_ZIP_ENTRIES:,} ZIP entries.)*\n"
            names = set(zf.namelist())
            if "docProps/core.xml" in names:
                with zf.open("docProps/core.xml") as fp:
                    core_bytes = fp.read(1024 * 1024 + 1)
                if len(core_bytes) <= 1024 * 1024 and not _declares_doctype(core_bytes):
                    core_root = ET.fromstring(core_bytes)
                    t_el = core_root.find(f".//{dc_title_ns}")
                    if t_el is not None and t_el.text and t_el.text.strip():
                        doc_title = t_el.text.strip()

            if "word/document.xml" not in names:
                return doc_title, f"# {doc_title}\n\n*(No word/document.xml stream found in DOCX archive.)*\n"
            with zf.open("word/document.xml") as fp:
                doc_bytes = fp.read(8 * 1024 * 1024 + 1)
            if len(doc_bytes) > 8 * 1024 * 1024:
                return doc_title, f"# {doc_title}\n\n*(DOCX XML exceeds 8 MB safety limit.)*\n"
            if _declares_doctype(doc_bytes):
                return doc_title, f"# {doc_title}\n\n*(DOCX XML rejected: DTD declarations are not permitted.)*\n"
            root = ET.fromstring(doc_bytes)
    except (zipfile.BadZipFile, ET.ParseError, OSError) as exc:
        return doc_title, f"# {doc_title}\n\n*(Could not parse DOCX archive: {exc})*\n"

    body_el = root.find(f"{w_ns}body")
    container = body_el if body_el is not None else root
    for child in list(container):
        if total_chars >= max_chars:
            truncated = True
            break
        if child.tag == f"{w_ns}p":
            txt = _para_text(child)[: max_chars - total_chars]
            if not txt:
                continue
            style_val = ""
            is_list = False
            ppr = child.find(f"{w_ns}pPr")
            if ppr is not None:
                pstyle = ppr.find(f"{w_ns}pStyle")
                if pstyle is not None:
                    style_val = (pstyle.attrib.get(f"{w_ns}val") or "").lower()
                if ppr.find(f"{w_ns}numPr") is not None or "list" in style_val:
                    is_list = True
            if style_val in ("title", "heading1", "h1"):
                if doc_title == file_path.stem.replace("-", " ").replace("_", " "):
                    doc_title = txt
                line = f"# {txt}"
            elif style_val in ("heading2", "h2", "subtitle"):
                line = f"## {txt}"
            elif style_val.startswith("heading"):
                line = f"### {txt}"
            elif is_list:
                line = f"- {txt.replace(chr(10), ' ')}"
            else:
                line = txt
            lines.append(line)
            total_chars += len(line) + 1
        elif child.tag == f"{w_ns}tbl":
            rows_md: list[list[str]] = []
            for tr in child.findall(f".//{w_ns}tr"):
                row_cells: list[str] = []
                for tc in tr.findall(f"./{w_ns}tc"):
                    cell_paras = [_para_text(p) for p in tc.findall(f".//{w_ns}p")]
                    cell_txt = " ".join(x for x in cell_paras if x).replace("|", "\\|").replace("\n", " ").strip()
                    row_cells.append(cell_txt)
                if any(row_cells):
                    rows_md.append(row_cells)
            if rows_md:
                col_count = max(len(r) for r in rows_md)
                padded = [r + [""] * (col_count - len(r)) for r in rows_md]
                header = "| " + " | ".join(padded[0]) + " |"
                sep = "| " + " | ".join(["---"] * col_count) + " |"
                tbl_lines = [header, sep, *("| " + " | ".join(r) + " |" for r in padded[1:])]
                tbl_str = "\n".join(tbl_lines)[: max_chars - total_chars]
                lines.append(tbl_str)
                total_chars += len(tbl_str) + 1

    if not lines or not lines[0].startswith("# "):
        lines.insert(0, f"# {doc_title}")
    if truncated:
        lines.append(f"\n> *[Truncated at {max_chars:,} characters; open the original DOCX to view the remainder.]*")
    return doc_title, "\n\n".join(lines).strip() + "\n"


def _extract_pdf_text_stdlib(raw_pdf: bytes, max_chars: int = 250_000) -> str:
    """Lightweight stdlib fallback for extracting text streams from simple PDFs when pypdf is absent."""
    chunks: list[str] = []
    total = 0
    max_stream_decomp = 2 * 1024 * 1024

    def _unescape_pdf_str(s: bytes) -> str:
        out = bytearray()
        i = 0
        n = len(s)
        while i < n:
            b = s[i]
            if b == 92 and i + 1 < n:  # backslash
                nxt = s[i + 1]
                if nxt in (110, 114, 116):
                    out.append({110: 10, 114: 13, 116: 9}[nxt])
                    i += 2
                    continue
                out.append(nxt)
                i += 2
            else:
                out.append(b)
                i += 1
        return out.decode("latin-1", errors="ignore")

    # Linear scans only: a regex search for "stream...endstream" rescans the rest of the input from every
    # unterminated "stream", which a small crafted upload turns into seconds of work under DB_LOCK.
    pos = 0
    for _ in range(250):
        if total >= max_chars:
            break
        start = raw_pdf.find(b"stream", pos)
        if start < 0:
            break
        body_start = start + 6 + (2 if raw_pdf.startswith(b"\r\n", start + 6) else 1)
        end = raw_pdf.find(b"endstream", body_start)
        if end < 0:
            break
        pos = end + 9
        data = raw_pdf[body_start:end].rstrip(b"\r\n")
        try:
            dobj = zlib.decompressobj()
            decomp = dobj.decompress(data, max_stream_decomp)
        except zlib.error:
            decomp = data[:max_stream_decomp]
        if b"BT" not in decomp and b"Tj" not in decomp and b"TJ" not in decomp:
            continue
        pieces: list[str] = []
        for str_m in re.finditer(rb"\((?:\\.|[^\\()])*\)\s*Tj|\[((?:\\.|[^\]\\])*)\]\s*TJ", decomp, flags=re.S):
            grp = str_m.group(0)
            for lit in re.finditer(rb"\(((?:\\.|[^\\()])*)\)", grp):
                txt = _unescape_pdf_str(lit.group(1))
                if txt:
                    pieces.append(txt)
        if pieces:
            joined = " ".join(pieces).strip()
            if joined:
                rem = max_chars - total
                if len(joined) > rem:
                    joined = joined[:rem]
                chunks.append(joined)
                total += len(joined)
    return "\n\n".join(chunks)


def extract_pdf_markdown(
    file_path: Path,
    data: bytes,
    *,
    max_pages: int = 120,
    max_chars: int = 250_000,
) -> tuple[str, str]:
    """Extract clean Markdown from a PDF file using pypdf (with stdlib fallback)."""
    doc_title = file_path.stem.replace("-", " ").replace("_", " ")
    try:
        from pypdf import PdfReader  # type: ignore[import-not-found]
        try:
            import pypdf.filters as _pypdf_filters  # type: ignore[import-not-found]
            if hasattr(_pypdf_filters, "ZLIB_MAX_OUTPUT_LENGTH"):
                _pypdf_filters.ZLIB_MAX_OUTPUT_LENGTH = min(
                    int(_pypdf_filters.ZLIB_MAX_OUTPUT_LENGTH or 0) or (4 * 1024 * 1024),
                    4 * 1024 * 1024,
                )
        except ImportError:
            pass
        reader = PdfReader(io.BytesIO(data))
        meta = reader.metadata
        if meta and getattr(meta, "title", None):
            cand_title = str(meta.title).strip()
            if cand_title and cand_title.lower() not in ("untitled", "none"):
                doc_title = cand_title
        total_pages = len(reader.pages)
        sections: list[str] = [f"# {doc_title}", f"> 📄 **PDF Document** · {total_pages} page(s)"]
        chars = 0
        extracted_pages = 0
        truncated = False
        for idx in range(min(total_pages, max_pages)):
            if chars >= max_chars:
                break
            try:
                raw_page_txt = (reader.pages[idx].extract_text() or "").strip()
            except Exception:
                raw_page_txt = ""
            extracted_pages = idx + 1
            if not raw_page_txt:
                continue
            rem = max_chars - chars
            if len(raw_page_txt) > rem:
                page_txt = raw_page_txt[:rem]
                truncated = True
            else:
                page_txt = raw_page_txt
            if total_pages > 1:
                block = f"## Page {idx + 1}\n\n{page_txt}"
            else:
                block = page_txt
            sections.append(block)
            chars += len( page_txt )
        if total_pages > extracted_pages or chars >= max_chars or truncated:
            sections.append(
                f"> *[Indexed first {extracted_pages} of {total_pages} pages ({chars:,} chars) to keep search fast. "
                "Use the Open Original PDF button above to view the complete PDF.]*"
            )
        return doc_title, "\n\n".join(sections).strip() + "\n"
    except ImportError:
        pass
    except Exception as exc:
        return doc_title, f"# {doc_title}\n\n*(Could not parse PDF via pypdf: {exc})*\n"

    try:
        raw_bytes = data[: 16 * 1024 * 1024]
        fallback_txt = _extract_pdf_text_stdlib(raw_bytes, max_chars=max_chars).strip()
        if fallback_txt:
            return doc_title, f"# {doc_title}\n\n{fallback_txt}\n"
    except OSError:
        pass
    return doc_title, f"# {doc_title}\n\n*(PDF binary stored at `{file_path.name}`.)*\n"


def _clean_frontmatter_scalar(val: object) -> str:
    return re.sub(r"[\r\n]+", " ", str(val)).replace("---", "- - -").strip()


def parse_frontmatter(raw: str) -> tuple[dict[str, object], str]:
    if not raw.startswith("---\n"):
        return {}, raw
    end = raw.find("\n---\n", 4)
    if end == -1:
        return {}, raw
    meta_text = raw[4:end]
    body = raw[end + 5 :].lstrip("\n")
    meta: dict[str, object] = {}
    for line in meta_text.splitlines():
        if ":" not in line:
            continue
        k, v = line.split(":", 1)
        key = k.strip()
        val = v.strip()
        if val.startswith("[") and val.endswith("]"):
            items = [x.strip().strip("'\"") for x in val[1:-1].split(",") if x.strip()]
            meta[key] = items
        else:
            meta[key] = val.strip("'\"")
    return meta, body


def format_frontmatter(meta: dict[str, object], body: str) -> str:
    lines = ["---"]
    for key, val in meta.items():
        safe_key = re.sub(r"[^a-zA-Z0-9_-]", "", str(key))
        if not safe_key:
            continue
        if isinstance(val, list):
            cleaned_items = [
                _clean_frontmatter_scalar(x).replace(",", " ").replace("[", "").replace("]", "")
                for x in val
                if _clean_frontmatter_scalar(x)
            ]
            lines.append(f"{safe_key}: [{', '.join(cleaned_items)}]")
        else:
            safe = _clean_frontmatter_scalar(val)
            lines.append(f"{safe_key}: {safe}")
    lines.append("---")
    lines.append("")
    lines.append(body.rstrip() + "\n")
    return "\n".join(lines)


def extract_wikilinks_with_relations(text: str) -> list[tuple[str, str]]:
    """Extract (target_slug, relation_type) from Obsidian [[wikilinks]], including Basic-Memory relation lines."""
    found: dict[str, str] = {}
    for line in text.splitlines():
        rel_match = re.match(r"^\s*[-*]\s+([a-zA-Z0-9_-]+)\s+\[\[([^\]|#]+)(?:[|#][^\]]*)?\]\]", line)
        if rel_match:
            rel_type = rel_match.group(1).strip().lower()
            target = rel_match.group(2).strip().removeprefix("memory/")
            if target:
                found[target.lower()] = rel_type
    for match in re.finditer(r"\[\[([^\]|#]+)(?:[|#][^\]]*)?\]\]", text):
        target = match.group(1).strip().removeprefix("memory/")
        if target and target.lower() not in found:
            found[target.lower()] = "links_to"
    return list(found.items())


def extract_inline_observations(text: str) -> list[dict[str, object]]:
    """Extract Basic-Memory-style inline observations ('- [category] fact text #tag') from Markdown."""
    out: list[dict[str, object]] = []
    in_code = False
    for idx, line in enumerate(text.splitlines(), start=1):
        if line.strip().startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        m = re.match(r"^\s*[-*]\s+\[([a-zA-Z0-9_-]{2,32})\]\s+(.+)$", line)
        if not m:
            continue
        cat = m.group(1).strip().lower()
        rest = m.group(2).strip()
        # Ignore Markdown links like '- [label](url)'
        if rest.startswith("("):
            continue
        obs_tags = re.findall(r"(?:^|\s)#([a-zA-Z0-9_-]+)", rest)
        out.append(
            {
                "category": cat,
                "observation": rest,
                "tags": obs_tags,
                "line_num": idx,
            }
        )
    return out


def index_note_row(
    conn: sqlite3.Connection,
    rel_path: str,
    scope: str,
    title: str,
    summary: str,
    tags: list[str],
    body: str,
    updated_by: str,
    updated_at: str,
    sha256: str,
) -> None:
    tags_json = json.dumps(tags)
    conn.execute(
        """
        INSERT INTO notes(path, scope, title, summary, tags, body, updated_by, updated_at, sha256)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(path) DO UPDATE SET
            scope=excluded.scope,
            title=excluded.title,
            summary=excluded.summary,
            tags=excluded.tags,
            body=excluded.body,
            updated_by=excluded.updated_by,
            updated_at=excluded.updated_at,
            sha256=excluded.sha256
        """,
        (rel_path, scope, title, summary, tags_json, body, updated_by, updated_at, sha256),
    )
    conn.execute("DELETE FROM notes_fts WHERE path = ?", (rel_path,))
    conn.execute(
        "INSERT INTO notes_fts(path, scope, title, summary, tags, body) VALUES (?, ?, ?, ?, ?, ?)",
        (rel_path, scope, title, summary, " ".join(tags), body),
    )
    conn.execute("DELETE FROM note_links WHERE source_path = ?", (rel_path,))
    for target_slug, rel_type in extract_wikilinks_with_relations(body):
        conn.execute(
            "INSERT OR IGNORE INTO note_links(source_path, target_slug, relation_type) VALUES (?, ?, ?)",
            (rel_path, target_slug, rel_type),
        )
    conn.execute("DELETE FROM note_observations WHERE source_path = ?", (rel_path,))
    for obs in extract_inline_observations(body):
        conn.execute(
            "INSERT INTO note_observations(source_path, category, observation, tags, line_num) VALUES (?, ?, ?, ?, ?)",
            (rel_path, str(obs["category"]), str(obs["observation"]), json.dumps(obs["tags"]), int(obs["line_num"])),
        )


def infer_vault_scope(rel_path: str, meta: dict[str, object] | None = None) -> str:
    """Derive scope strictly from the canonical vault directory path (never trust frontmatter scope overrides)."""
    parts = [p.lower() for p in apply_scope_aliases(rel_path).split("/") if p]
    if not parts:
        return "shared"
    top = parts[0]
    if top == "shared":
        return "shared"
    if top == "projects" and len(parts) >= 2:
        if len(parts) == 2 and parts[1] == "readme.md":
            return "projects/overview"
        return f"projects/{slugify_segment(parts[1])}"
    if top == "agents":
        if len(parts) >= 2 and parts[1] in valid_agent_scope_names():
            return f"agents/{parts[1]}"
        return "agents/hermes"
    if top in AREAS:
        return "/".join(slugify_segment(p).lower() for p in parts[: area_scope_depth(parts)])
    if top in ("daily", "inbox"):
        return top
    return "shared"


def should_index_vault_file(rel_path: str) -> bool:
    if rel_path in SKIP_VAULT_GENERATED_FILES:
        return False
    parts = rel_path.split("/")
    if any(p.startswith(".") for p in parts):
        return False
    if parts[0].lower() in SKIP_VAULT_TOP_DIRS:
        return False
    if len(parts) == 1 and parts[0] in SKIP_VAULT_ROOT_FILES:
        return False
    return True


def sync_vault_notes(conn: sqlite3.Connection) -> None:
    """Index Markdown, DOCX, and PDF files across the unified Obsidian vault (excluding symlinks, personal/, templates/, .obsidian/, .sync/)."""
    VAULT_DIR.mkdir(parents=True, exist_ok=True)
    vault_real = VAULT_DIR.resolve()
    seen: set[str] = set()
    for root_str, dirs, files in os.walk(VAULT_DIR, followlinks=False):
        root_path = Path(root_str)
        try:
            rel_dir = root_path.relative_to(VAULT_DIR)
        except ValueError:
            dirs[:] = []
            continue
        # Prune skipped top-level directories, hidden directories, and any symlinked directories immediately
        filtered_dirs: list[str] = []
        for d in sorted(dirs):
            if d.startswith("."):
                continue
            if rel_dir == Path(".") and d.lower() in SKIP_VAULT_TOP_DIRS:
                continue
            d_path = root_path / d
            if d_path.is_symlink():
                continue
            try:
                if not d_path.resolve().is_relative_to(vault_real):
                    continue
            except OSError:
                continue
            filtered_dirs.append(d)
        dirs[:] = filtered_dirs

        for fname in sorted(files):
            fname_low = fname.lower()
            if not fname_low.endswith(SUPPORTED_VAULT_EXTENSIONS) or fname.startswith("."):
                continue
            file = root_path / fname
            if file.is_symlink():
                continue
            try:
                resolved_file = file.resolve()
                if not resolved_file.is_relative_to(vault_real):
                    continue
                rel = resolved_file.relative_to(vault_real).as_posix()
            except OSError:
                continue
            if not should_index_vault_file(rel):
                continue
            try:
                st = file.stat(follow_symlinks=False)
            except OSError:
                continue
            if not fname_low.endswith(".md") and st.st_size > MAX_BINARY_DOC_BYTES:
                continue
            seen.add(rel)
            cached = _VAULT_STAT_CACHE.get(rel)
            if cached and cached[0] == (st.st_ino, st.st_mtime_ns, st.st_size):
                existing = conn.execute("SELECT sha256 FROM notes WHERE path = ?", (rel,)).fetchone()
                if existing and existing["sha256"] == cached[1]:
                    continue
            try:
                data, st = read_vault_file(rel)
            except (MemoryError, OSError):
                seen.discard(rel)
                continue
            sha = hashlib.sha256(data).hexdigest()
            _VAULT_STAT_CACHE[rel] = ((st.st_ino, st.st_mtime_ns, st.st_size), sha)
            existing = conn.execute("SELECT sha256 FROM notes WHERE path = ?", (rel,)).fetchone()
            if existing and existing["sha256"] == sha:
                continue

            if fname_low.endswith(".md"):
                meta, body = parse_frontmatter(data.decode("utf-8", errors="replace"))
                scope = infer_vault_scope(rel, meta)
                heading_match = re.search(r"^#\s+(.+)$", body, flags=re.M)
                title = str(meta.get("title") or (heading_match.group(1).strip() if heading_match else file.stem))
                summary = str(meta.get("summary") or meta.get("symptom") or "")
                tags_raw = meta.get("tags")
                tags = [str(x) for x in tags_raw] if isinstance(tags_raw, list) else []
                if meta.get("type") and str(meta["type"]) not in tags:
                    tags.append(str(meta["type"]))
                updated_by = str(meta.get("updated_by") or meta.get("agent") or "owner")
                updated_at = str(
                    meta.get("updated_at")
                    or meta.get("created")
                    or datetime.fromtimestamp(st.st_mtime, LOCAL_TZ).strftime("%Y-%m-%d %H:%M:%S %Z")
                )
            else:
                ext_tag = "docx" if fname_low.endswith(".docx") else "pdf"
                if ext_tag == "docx":
                    title, body = extract_docx_markdown(file, data)
                else:
                    title, body = extract_pdf_markdown(file, data)
                scope = infer_vault_scope(rel)
                summary = f"{ext_tag.upper()} document ({st.st_size / 1024:.1f} KB)"
                tags = [ext_tag, "binary-doc"]
                updated_by = "owner"
                updated_at = datetime.fromtimestamp(st.st_mtime, LOCAL_TZ).strftime("%Y-%m-%d %H:%M:%S %Z")

            index_note_row(conn, rel, scope, title, summary, tags, body, updated_by, updated_at, sha)

    db_paths = [r["path"] for r in conn.execute("SELECT path FROM notes").fetchall()]
    for old_path in db_paths:
        if old_path not in seen:
            _VAULT_STAT_CACHE.pop(old_path, None)
            conn.execute("DELETE FROM notes WHERE path = ?", (old_path,))
            conn.execute("DELETE FROM notes_fts WHERE path = ?", (old_path,))
            conn.execute("DELETE FROM note_links WHERE source_path = ?", (old_path,))
            conn.execute("DELETE FROM note_observations WHERE source_path = ?", (old_path,))
    conn.commit()


def refresh_human_dashboards(conn: sqlite3.Connection) -> None:
    """Write 00-AI-Memory-Snapshot.md and INDEX.md in the root Obsidian vault."""
    VAULT_DIR.mkdir(parents=True, exist_ok=True)
    active_facts = conn.execute(
        "SELECT * FROM facts WHERE status = 'active' ORDER BY scope ASC, category ASC, id DESC"
    ).fetchall()
    invalid_facts = conn.execute(
        "SELECT * FROM facts WHERE status != 'active' ORDER BY updated_at DESC, id DESC LIMIT 50"
    ).fetchall()
    notes = conn.execute(
        "SELECT path, scope, title, summary, tags, updated_by, updated_at FROM notes ORDER BY scope ASC, path ASC"
    ).fetchall()

    snap_lines = [
        "---",
        "title: AI-to-AI Memory Snapshot",
        "type: memory-snapshot",
        f"updated_at: {now_local()}",
        "---",
        "",
        "# AI-to-AI Memory Snapshot (Valid & Invalid Temporal Facts)",
        "",
        "> Auto-generated from the live SQLite temporal fact store (`memory.db`).",
        "> Every agent (`claude`, `chatgpt`, `hermes/<sub-agent>`, `antigravity`) can **read** all scopes across the unified vault.",
        f"> {', '.join(f'`{s}`' for s in OPEN_SCOPES)} are writable by all agents; `agents/<name>` is writable only by `<name>`.",
        "",
        "## ✅ Active (Valid) Facts",
        "",
    ]
    if not active_facts:
        snap_lines.append("_No active AI-to-AI facts recorded yet._")
        snap_lines.append("")
    else:
        by_scope: dict[str, list[sqlite3.Row]] = {}
        for row in active_facts:
            by_scope.setdefault(row["scope"], []).append(row)
        for scope, rows in by_scope.items():
            snap_lines.append(f"### Scope: `{scope}`")
            snap_lines.append("")
            for r in rows:
                subj = f"**[{r['subject']}]** " if r["subject"] else ""
                snap_lines.append(
                    f"- `#{r['id']}` **[VALID]** ({r['category']}) {subj}{r['fact']} "
                    f"— *by `{r['author']}` (valid from {r['valid_from']})*"
                )
            snap_lines.append("")

    if invalid_facts:
        snap_lines.append("## ❌ Invalidated & Superseded History (Temporal Audit Trail)")
        snap_lines.append("")
        for r in invalid_facts:
            subj = f"[{r['subject']}] " if r["subject"] else ""
            state_label = "SUPERSEDED" if r["status"] == "superseded" else "INVALIDATED"
            repl = f" → superseded by `#{r['superseded_by']}`" if r["superseded_by"] else ""
            reason = f" — reason: *{r['invalidated_reason']}*" if r["invalidated_reason"] else ""
            by_who = f" by `{r['invalidated_by']}`" if r["invalidated_by"] else ""
            snap_lines.append(
                f"- ~~`#{r['id']}` [{r['scope']}] ({r['category']}) {subj}{r['fact']}~~ "
                f"**[{state_label}]** *(valid {r['valid_from']} → {r['valid_until'] or r['updated_at']}{by_who}{repl}{reason})*"
            )
        snap_lines.append("")

    snap_text = "\n".join(snap_lines)
    atomic_write_text(VAULT_DIR / "00-AI-Memory-Snapshot.md", snap_text, allow_root_dashboard=True)
    atomic_write_text(VAULT_DIR / "shared" / "00-AI-Memory-Snapshot.md", snap_text, allow_root_dashboard=True)

    idx_lines = [
        "---",
        "title: Unified Memory Index",
        "type: memory-index",
        f"updated_at: {now_local()}",
        "---",
        "",
        "# Unified Obsidian Vault & Cross-Agent Memory Index",
        "",
        "- [[00-AI-Memory-Snapshot|00-AI-Memory-Snapshot.md]] — Live snapshot of active (`valid`) and historical (`invalid`/`superseded`) AI-to-AI facts",
        *(f"- [[{path.removesuffix('.md')}|{path}]] — {label}" for path, label in DASHBOARD["pinned"]),
        "",
        "## Scope Access Rules (Single Unified Obsidian Vault)",
        "",
        "| Vault Path / Scope | Readable By | Writable By | Purpose |",
        "| :--- | :--- | :--- | :--- |",
        *(f"| `{s}` | All agents + Owner | All agents + Owner | Open to every agent |" for s in OPEN_SCOPES),
        "| `agents/claude/` | All agents + Owner | **Claude only** (+ Owner) | Claude-specific memory & notes |",
        "| `agents/chatgpt/` | All agents + Owner | **ChatGPT only** (+ Owner) | ChatGPT-specific memory & notes |",
        "| `agents/antigravity/` | All agents + Owner | **Antigravity only** (+ Owner) | Antigravity-specific memory & notes |",
        "| `agents/<hermes-subagent>/` | All agents + Owner | **That Hermes sub-agent only** (+ Owner) | Per-profile memory |",
        "| `agents/{hermes,decisions,gotchas,playbooks,research}/` | All agents + Owner | **Any Hermes sub-agent** (+ Owner) | Shared Hermes engineering & ops knowledge |",
        "| everything else (`daily/`, `inbox/`, other areas) | All agents + Owner | Owner"
        + (f" (+ Hermes for {', '.join(f'`{s}`' for s in HERMES_EXTRA_WRITE)})" if HERMES_EXTRA_WRITE else "")
        + " | Vault context indexed for AI search |",
        "| `personal/*` | **Owner only** | **Owner only** | Strictly private; excluded from `vyn-memory` |",
        "",
        "## Indexed Vault & Study Documents by Scope",
        "",
    ]
    if not notes:
        idx_lines.append("_No Markdown notes indexed yet._")
    else:
        notes_by_scope: dict[str, list[sqlite3.Row]] = {}
        for n in notes:
            notes_by_scope.setdefault(n["scope"], []).append(n)
        for scope, snotes in notes_by_scope.items():
            idx_lines.append(f"### `{scope}`")
            idx_lines.append("")
            for n in snotes:
                summary_part = f" — {n['summary']}" if n["summary"] else ""
                idx_lines.append(
                    f"- [[{n['path']}|{n['title']}]] (`{n['path']}`){summary_part} "
                    f"*(updated by `{n['updated_by']}`, {n['updated_at']})*"
                )
            idx_lines.append("")

    idx_text = "\n".join(idx_lines)
    atomic_write_text(VAULT_DIR / "INDEX.md", idx_text, allow_root_dashboard=True)
    atomic_write_text(VAULT_DIR / "shared" / "00-Memory-Index.md", idx_text, allow_root_dashboard=True)



def seed_initial_scaffold(conn: sqlite3.Connection) -> None:
    """Create the shared and per-agent README notes in the vault if absent (folder layouts come from the vault template)."""
    starters = [
        (
            "shared/README.md",
            "shared",
            "Shared Cross-Agent Memory",
            "Global notes readable and writable by Claude, ChatGPT, Hermes, and Antigravity.",
            ["shared"],
            "# Shared Cross-Agent Memory\n\nNotes in `shared/` can be read and updated by every connected agent.\n",
        ),
        *[
            (
                f"agents/{agent}/README.md",
                f"agents/{agent}",
                f"{agent.capitalize()} Agent-Specific Memory",
                f"Readable by all agents; writable only by {agent} (and owner).",
                ["agent-memory", agent],
                (
                    f"# {agent.capitalize()} Specific Memory (`agents/{agent}`)\n\n"
                    f"- **Read access:** Every agent (`claude`, `chatgpt`, `hermes`, `antigravity`) and the owner.\n"
                    f"- **Write access:** **Only `{agent}`** (and `owner`). Other agents are blocked from modifying this scope.\n"
                ),
            )
            for agent in AGENTS
        ],
    ]
    wrote_any = False
    for rel_path, scope, title, summary, tags, body in starters:
        target = VAULT_DIR / rel_path
        if not target.exists():
            text = format_frontmatter(
                {
                    "title": title,
                    "scope": scope,
                    "summary": summary,
                    "tags": tags,
                    "updated_by": "owner",
                    "updated_at": now_local(),
                },
                body,
            )
            atomic_write_text(target, text)
            wrote_any = True
    sync_vault_notes(conn)
    if (
        wrote_any
        or not (VAULT_DIR / "INDEX.md").exists()
        or not (VAULT_DIR / "00-AI-Memory-Snapshot.md").exists()
        or not (VAULT_DIR / "shared" / "00-AI-Memory-Snapshot.md").exists()
        or not (VAULT_DIR / "shared" / "00-Memory-Index.md").exists()
    ):
        refresh_human_dashboards(conn)


# ── Core Operations (called by both MCP tools and REST API) ───────────────


def op_remember_fact(
    conn: sqlite3.Connection,
    actor: str,
    *,
    fact: str,
    scope: str = DEFAULT_SCOPE,
    subject: str = "",
    category: str = "fact",
    supersedes_id: int = 0,
    supersede_subject: bool = True,
) -> dict[str, object]:
    with DB_LOCK:
        norm_scope = check_write_permission(actor, scope)
        text = (fact or "").strip()
        if not text:
            raise MemoryError("fact text cannot be empty")
        cat = (category or "fact").strip().lower()
        if cat not in VALID_CATEGORIES:
            raise MemoryError(f"Invalid category {category!r}; valid: {', '.join(VALID_CATEGORIES)}")
        subj = slugify_segment(subject).lower() if (subject or "").strip() else ""
        ts = now_local()

        existing_exact = conn.execute(
            """
            SELECT * FROM facts
            WHERE scope = ? AND subject = ? AND category = ? AND fact = ? AND status = 'active'
            """,
            (norm_scope, subj, cat, text),
        ).fetchone()
        if existing_exact and not supersedes_id:
            conn.execute("UPDATE facts SET updated_at = ? WHERE id = ?", (ts, existing_exact["id"]))
            conn.commit()
            return {
                "status": "unchanged_existing",
                "fact": serialize_fact(existing_exact),
                "superseded_ids": [],
            }

        to_supersede: list[int] = []
        if supersedes_id:
            old = conn.execute("SELECT * FROM facts WHERE id = ?", (int(supersedes_id),)).fetchone()
            if not old:
                raise MemoryError(f"Fact #{supersedes_id} not found")
            check_write_permission(actor, old["scope"])
            if old["status"] == "active":
                to_supersede.append(int(old["id"]))

        if subj and supersede_subject:
            related_cats = (
                ("weakness", "strength", "progress")
                if cat in ("weakness", "strength", "progress")
                else (cat,)
            )
            placeholders = ",".join("?" for _ in related_cats)
            rows = conn.execute(
                f"""
                SELECT id FROM facts
                WHERE scope = ? AND subject = ? AND status = 'active'
                  AND category IN ({placeholders})
                """,
                (norm_scope, subj, *related_cats),
            ).fetchall()
            for r in rows:
                if int(r["id"]) not in to_supersede:
                    to_supersede.append(int(r["id"]))

        cur = conn.execute(
            """
            INSERT INTO facts(scope, subject, category, fact, author, status, supersedes_id, valid_from, updated_at)
            VALUES (?, ?, ?, ?, ?, 'active', ?, ?, ?)
            """,
            (
                norm_scope,
                subj,
                cat,
                text,
                actor,
                to_supersede[0] if to_supersede else None,
                ts,
                ts,
            ),
        )
        new_id = int(cur.lastrowid)
        conn.execute(
            "INSERT INTO facts_fts(rowid, scope, subject, category, fact, author) VALUES (?, ?, ?, ?, ?, ?)",
            (new_id, norm_scope, subj, cat, text, actor),
        )
        for old_id in to_supersede:
            conn.execute(
                """
                UPDATE facts
                SET status = 'superseded',
                    superseded_by = ?,
                    invalidated_by = ?,
                    invalidated_reason = 'superseded by newer fact on same subject',
                    valid_until = ?,
                    updated_at = ?
                WHERE id = ?
                """,
                (new_id, actor, ts, ts, old_id),
            )
        conn.commit()
        refresh_human_dashboards(conn)
        created = conn.execute("SELECT * FROM facts WHERE id = ?", (new_id,)).fetchone()
        # Surface any other active facts in the same scope that share keywords so agents catch contradictions early.
        fts_q = fts_query_tokens(f"{subj} {text}")
        potential_conflicts: list[dict[str, object]] = []
        if fts_q:
            conflict_rows = conn.execute(
                """
                SELECT f.*
                FROM facts_fts fts
                JOIN facts f ON f.id = fts.rowid
                WHERE facts_fts MATCH ? AND f.scope = ? AND f.status = 'active' AND f.id != ?
                ORDER BY bm25(facts_fts), f.id DESC
                LIMIT 3
                """,
                (fts_q, norm_scope, new_id),
            ).fetchall()
            potential_conflicts = [serialize_fact(r) for r in conflict_rows]
        return {
            "status": "saved",
            "actor": actor,
            "fact": serialize_fact(created),
            "superseded_ids": to_supersede,
            "potential_conflicts": potential_conflicts,
        }


def op_check_facts(
    conn: sqlite3.Connection,
    *,
    statement: str = "",
    scope: str = "",
    subject: str = "",
    limit: int = 8,
) -> dict[str, object]:
    """Fact-check a claim or topic against active facts, retired/superseded history, and vault notes before saving."""
    with DB_LOCK:
        sync_vault_notes(conn)
        cap = max(1, min(int(limit or 8), 25))
        norm_scope = normalize_scope(scope) if (scope or "").strip() else ""
        esc_scope = _escape_like(norm_scope)
        subj = slugify_segment(subject).lower() if (subject or "").strip() else ""
        stmt = (statement or "").strip()
        if not stmt and not subj:
            raise MemoryError("Either statement or subject is required for fact checking")

        active_by_id: dict[int, dict[str, object]] = {}
        history_by_id: dict[int, dict[str, object]] = {}

        if subj:
            sql_subj = "SELECT * FROM facts WHERE subject = ?"
            params_s: list[object] = [subj]
            if norm_scope:
                sql_subj += " AND (scope = ? OR scope LIKE ? ESCAPE '\\')"
                params_s.extend([norm_scope, f"{esc_scope}/%"])
            sql_subj += " ORDER BY id DESC LIMIT ?"
            params_s.append(cap * 2)
            for r in conn.execute(sql_subj, params_s).fetchall():
                item = serialize_fact(r)
                if item["is_valid"]:
                    active_by_id[int(r["id"])] = item
                else:
                    history_by_id[int(r["id"])] = item

        fts_q = fts_query_tokens(f"{subj} {stmt}")
        if fts_q:
            sql_fts = """
                SELECT f.*
                FROM facts_fts fts
                JOIN facts f ON f.id = fts.rowid
                WHERE facts_fts MATCH ?
            """
            params_f: list[object] = [fts_q]
            if norm_scope:
                sql_fts += " AND (f.scope = ? OR f.scope LIKE ? ESCAPE '\\')"
                params_f.extend([norm_scope, f"{esc_scope}/%"])
            else:
                sql_fts += " AND f.scope != 'resources/books' AND f.scope NOT LIKE 'resources/books/%'"
            sql_fts += " ORDER BY bm25(facts_fts), f.id DESC LIMIT ?"
            params_f.append(cap * 2)
            for r in conn.execute(sql_fts, params_f).fetchall():
                item = serialize_fact(r)
                fid = int(r["id"])
                if item["is_valid"]:
                    active_by_id.setdefault(fid, item)
                else:
                    history_by_id.setdefault(fid, item)

        matching_active = list(active_by_id.values())[:cap]
        matching_history = list(history_by_id.values())[:cap]
        related_notes = (
            op_search(conn, query=stmt or subj, scope=norm_scope, limit=min(cap, 5))["notes"]
            if (stmt or subj)
            else []
        )
        if matching_active:
            guidance = (
                f"Found {len(matching_active)} active fact(s) on this topic. "
                "Verify whether your statement matches, supersedes (pass supersedes_id or same subject), "
                "or contradicts an existing active fact (retire stale ones with forget)."
            )
        elif matching_history:
            guidance = (
                f"No active facts matched, but {len(matching_history)} retired/superseded fact(s) exist in history. "
                "Review history before re-asserting an outdated claim."
            )
        else:
            guidance = "No conflicting active or historical facts found."
        return {
            "statement": stmt,
            "scope_filter": norm_scope or "all",
            "subject": subj,
            "matching_active_facts": matching_active,
            "matching_history_facts": matching_history,
            "related_notes": related_notes,
            "guidance": guidance,
        }


def op_forget_fact(
    conn: sqlite3.Connection,
    actor: str,
    *,
    fact_id: int,
    reason: str = "",
    resolution: str = "invalidated",
) -> dict[str, object]:
    with DB_LOCK:
        row = conn.execute("SELECT * FROM facts WHERE id = ?", (int(fact_id),)).fetchone()
        if not row:
            raise MemoryError(f"Fact #{fact_id} not found")
        check_write_permission(actor, row["scope"])
        final_status = "superseded" if resolution == "superseded" else "invalidated"
        ts = now_local()
        conn.execute(
            """
            UPDATE facts
            SET status = ?,
                invalidated_by = ?,
                invalidated_reason = ?,
                valid_until = ?,
                updated_at = ?
            WHERE id = ?
            """,
            (final_status, actor, (reason or "").strip(), ts, ts, int(fact_id)),
        )
        conn.commit()
        refresh_human_dashboards(conn)
        updated = conn.execute("SELECT * FROM facts WHERE id = ?", (int(fact_id),)).fetchone()
        return {
            "status": final_status,
            "validity": "invalid",
            "actor": actor,
            "reason": reason,
            "fact": serialize_fact(updated),
        }


def replace_or_append_section(existing_body: str, section_heading: str, new_section_content: str) -> str:
    heading = section_heading.strip().lstrip("#").strip()
    if not heading:
        return existing_body.rstrip() + "\n\n" + new_section_content.strip() + "\n"
    pattern = re.compile(
        rf"(^##\s+{re.escape(heading)}\s*$)(.*?)(?=^##\s+|\Z)",
        flags=re.M | re.S,
    )
    replacement_block = f"## {heading}\n\n{new_section_content.strip()}\n\n"
    if pattern.search(existing_body):
        return pattern.sub(lambda _: replacement_block, existing_body, count=1).rstrip() + "\n"
    return existing_body.rstrip() + "\n\n" + replacement_block


def op_write_note(
    conn: sqlite3.Connection,
    actor: str,
    *,
    path: str,
    content: str,
    title: str = "",
    scope: str = "",
    summary: str = "",
    tags: list[str] | None = None,
    mode: str = "replace",
    section: str = "",
) -> dict[str, object]:
    with DB_LOCK:
        resolved_scope, rel_path = normalize_note_path(path, explicit_scope=scope)
        check_write_permission(actor, resolved_scope)
        check_write_permission(actor, infer_vault_scope(rel_path))
        if mode not in ("replace", "append", "section"):
            raise MemoryError("mode must be one of: 'replace', 'append', 'section'")
        if not (content or "").strip():
            raise MemoryError("Note content cannot be empty")

        target = assert_safe_vault_path(VAULT_DIR / rel_path)
        existing_meta: dict[str, object] = {}
        existing_body = ""
        if target.exists():
            existing_meta, existing_body = parse_frontmatter(read_vault_file(rel_path)[0].decode("utf-8", errors="replace"))

        if mode == "replace":
            final_body = content.strip() + "\n"
        elif mode == "append":
            stamp = f"\n\n<!-- appended by {actor} at {now_local()} -->\n"
            final_body = (existing_body.rstrip() + stamp + content.strip() + "\n") if existing_body.strip() else (content.strip() + "\n")
        else:
            if not section.strip():
                raise MemoryError("section heading is required when mode='section'")
            base_body = existing_body if existing_body.strip() else f"# {title or Path(rel_path).stem}\n"
            final_body = replace_or_append_section(base_body, section, content)

        heading_match = re.search(r"^#\s+(.+)$", final_body, flags=re.M)
        final_title = (
            title.strip()
            or str(existing_meta.get("title") or "")
            or (heading_match.group(1).strip() if heading_match else Path(rel_path).stem.replace("-", " ").title())
        )
        if not re.search(r"^#\s+", final_body, flags=re.M):
            final_body = f"# {final_title}\n\n{final_body}"

        final_summary = summary.strip() or str(existing_meta.get("summary") or "")
        existing_tags = existing_meta.get("tags") if isinstance(existing_meta.get("tags"), list) else []
        final_tags = list(dict.fromkeys([*(tags or []), *[str(t) for t in existing_tags]]))
        ts = now_local()

        meta_to_write = dict(existing_meta)
        meta_to_write.update(
            {
                "title": final_title,
                "scope": resolved_scope,
                "summary": final_summary,
                "tags": final_tags,
                "updated_by": actor,
                "updated_at": ts,
            }
        )
        full_text = format_frontmatter(meta_to_write, final_body)
        atomic_write_text(target, full_text)
        _VAULT_STAT_CACHE.pop(rel_path, None)
        sha = hashlib.sha256(full_text.encode("utf-8")).hexdigest()
        index_note_row(
            conn,
            rel_path,
            resolved_scope,
            final_title,
            final_summary,
            final_tags,
            final_body,
            actor,
            ts,
            sha,
        )
        conn.commit()
        refresh_human_dashboards(conn)
        return {
            "status": "saved",
            "actor": actor,
            "path": rel_path,
            "scope": resolved_scope,
            "title": final_title,
            "summary": final_summary,
            "tags": final_tags,
            "mode": mode,
            "updated_at": ts,
        }


def op_upload_document(
    conn: sqlite3.Connection,
    actor: str,
    *,
    filename: str,
    raw_bytes: bytes | None = None,
    base64_content: str = "",
    scope: str = DEFAULT_SCOPE,
    title: str = "",
    summary: str = "",
    tags: list[str] | None = None,
) -> dict[str, object]:
    """Save a .pdf, .docx, .md, or .txt document into the vault and index its extracted Markdown into memory.db."""
    with DB_LOCK:
        raw_name = Path((filename or "").strip().replace("\\", "/")).name
        if not raw_name:
            raise MemoryError("filename is required")
        ext_low = Path(raw_name).suffix.lower()
        if ext_low == ".txt":
            raw_name = f"{Path(raw_name).stem}.md"
            ext_low = ".md"
        if ext_low not in SUPPORTED_VAULT_EXTENSIONS:
            raise MemoryError(
                f"Unsupported document extension {ext_low!r}; supported extensions: {', '.join(SUPPORTED_VAULT_EXTENSIONS)}, .txt"
            )
        if raw_bytes is None:
            b64_clean = re.sub(r"\s+", "", (base64_content or "").strip())
            if b64_clean.startswith("data:") and "," in b64_clean:
                b64_clean = b64_clean.split(",", 1)[1]
            if not b64_clean:
                raise MemoryError("Either raw_bytes or base64_content is required")
            try:
                raw_bytes = base64.b64decode(b64_clean, validate=False)
            except Exception as exc:
                raise MemoryError("Invalid base64_content payload") from exc
        if not raw_bytes:
            raise MemoryError("Uploaded document cannot be empty")
        if len(raw_bytes) > MAX_UPLOAD_BODY_BYTES:
            raise MemoryPayloadTooLargeError(f"Document exceeds maximum upload size of {MAX_UPLOAD_BODY_BYTES} bytes")

        resolved_scope, rel_path = normalize_note_path(
            raw_name,
            explicit_scope=scope or DEFAULT_SCOPE,
            allow_binary_ext=True,
        )
        check_write_permission(actor, resolved_scope)
        check_write_permission(actor, infer_vault_scope(rel_path))
        if ext_low == ".md":
            text_content = raw_bytes.decode("utf-8", errors="replace")
            return op_write_note(
                conn,
                actor,
                path=rel_path,
                content=text_content,
                title=title,
                scope=resolved_scope,
                summary=summary,
                tags=tags,
                mode="replace",
            )

        if ext_low == ".pdf":
            if b"%PDF-" not in raw_bytes[:1024]:
                raise MemoryError("Invalid PDF file: missing %PDF- header")
        elif ext_low == ".docx":
            if raw_bytes[:4] != b"PK\x03\x04":
                raise MemoryError("Invalid DOCX file: missing ZIP header")
            try:
                with zipfile.ZipFile(io.BytesIO(raw_bytes), "r") as zf_check:
                    if len(zf_check.infolist()) > MAX_DOCX_ZIP_ENTRIES:
                        raise MemoryError(f"Invalid DOCX file: exceeds {MAX_DOCX_ZIP_ENTRIES:,} ZIP entries")
                    if "word/document.xml" not in zf_check.namelist():
                        raise MemoryError("Invalid DOCX file: missing word/document.xml stream")
            except zipfile.BadZipFile as exc:
                raise MemoryError("Invalid DOCX file: corrupt ZIP archive") from exc

        target = assert_safe_vault_path(VAULT_DIR / rel_path)
        atomic_write_bytes(target, raw_bytes)
        _VAULT_STAT_CACHE.pop(rel_path, None)
        sha = hashlib.sha256(raw_bytes).hexdigest()
        ext_tag = "docx" if ext_low == ".docx" else "pdf"
        if ext_tag == "docx":
            extracted_title, extracted_body = extract_docx_markdown(target, raw_bytes)
        else:
            extracted_title, extracted_body = extract_pdf_markdown(target, raw_bytes)

        final_title = title.strip() or extracted_title
        final_summary = summary.strip() or f"{ext_tag.upper()} document ({len(raw_bytes) / 1024:.1f} KB)"
        final_tags = list(dict.fromkeys([*(tags or []), ext_tag, "binary-doc"]))
        ts = now_local()
        index_note_row(
            conn,
            rel_path,
            resolved_scope,
            final_title,
            final_summary,
            final_tags,
            extracted_body,
            actor,
            ts,
            sha,
        )
        conn.commit()
        refresh_human_dashboards(conn)
        return {
            "status": "uploaded",
            "actor": actor,
            "path": rel_path,
            "scope": resolved_scope,
            "title": final_title,
            "summary": final_summary,
            "tags": final_tags,
            "size_bytes": len(raw_bytes),
            "extracted_chars": len(extracted_body),
            "updated_at": ts,
        }


def _escape_like(val: str) -> str:
    return (val or "").replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


def op_read_note(conn: sqlite3.Connection, path: str) -> dict[str, object]:
    with DB_LOCK:
        sync_vault_notes(conn)
        cleaned = (path or "").strip().lstrip("/").removeprefix("memory/")
        if not cleaned:
            raise MemoryError("path is required")
        if cleaned.split("/")[0].lower() == "personal":
            raise MemoryPermissionError("Directory 'personal' is strictly private and not accessible via vyn-memory")
        row = conn.execute("SELECT * FROM notes WHERE path = ?", (cleaned,)).fetchone()
        if not row and not cleaned.lower().endswith(SUPPORTED_VAULT_EXTENSIONS):
            for ext in SUPPORTED_VAULT_EXTENSIONS:
                row = conn.execute("SELECT * FROM notes WHERE path = ?", (f"{cleaned}{ext}",)).fetchone()
                if row:
                    break
        if not row:
            try:
                _, norm_rel = normalize_note_path(cleaned, allow_binary_ext=True)
                row = conn.execute("SELECT * FROM notes WHERE path = ?", (norm_rel,)).fetchone()
            except MemoryError:
                row = None
        if not row:
            stem = Path(cleaned).stem.lower()
            if re.search(r"[a-z0-9]", stem):
                esc_stem = _escape_like(stem)
                matches = conn.execute(
                    "SELECT * FROM notes WHERE lower(path) LIKE ? ESCAPE '\\' OR lower(path) LIKE ? ESCAPE '\\' OR lower(path) LIKE ? ESCAPE '\\' ORDER BY updated_at DESC",
                    (f"%/{esc_stem}.md", f"%/{esc_stem}.pdf", f"%/{esc_stem}.docx"),
                ).fetchall()
                if len(matches) == 1:
                    row = matches[0]
                elif len(matches) > 1:
                    raise MemoryError(
                        f"Ambiguous note name {path!r}; specify full path: "
                        + ", ".join(m["path"] for m in matches)
                    )
        if not row:
            raise MemoryError(f"Note {path!r} not found")
        assert_safe_vault_path(VAULT_DIR / str(row["path"]))

        stem_lower = Path(row["path"]).stem.lower()
        outgoing_rows = conn.execute(
            "SELECT target_slug, relation_type FROM note_links WHERE source_path = ?",
            (row["path"],),
        ).fetchall()
        outgoing = [r["target_slug"] for r in outgoing_rows]
        relations = [{"target": r["target_slug"], "relation": r["relation_type"]} for r in outgoing_rows]
        backlinks = [
            r["source_path"]
            for r in conn.execute(
                "SELECT source_path FROM note_links WHERE target_slug IN (?, ?)",
                (stem_lower, row["path"].lower().removesuffix(".md")),
            ).fetchall()
        ]
        # 1-hop connected note summaries (Basic Memory style graph neighborhood)
        connected_paths = set(backlinks)
        for slug in outgoing:
            slug_clean = slug.removesuffix(".md")
            esc_slug_name = _escape_like(Path(slug_clean).name)
            for m in conn.execute(
                "SELECT path FROM notes WHERE lower(path) IN (?, ?) OR lower(path) LIKE ? ESCAPE '\\'",
                (f"{slug_clean}.md", slug_clean, f"%/{esc_slug_name}.md"),
            ).fetchall():
                connected_paths.add(m["path"])
        connected_paths.discard(row["path"])
        connected_notes = []
        if connected_paths:
            ph = ",".join("?" for _ in connected_paths)
            connected_notes = [
                {"path": r["path"], "title": r["title"], "scope": r["scope"], "summary": r["summary"]}
                for r in conn.execute(
                    f"SELECT path, title, scope, summary FROM notes WHERE path IN ({ph})",
                    tuple(sorted(connected_paths)),
                ).fetchall()
            ]

        observations = [
            {
                "category": r["category"],
                "observation": r["observation"],
                "tags": json.loads(r["tags"] or "[]"),
                "line_num": r["line_num"],
            }
            for r in conn.execute(
                "SELECT category, observation, tags, line_num FROM note_observations WHERE source_path = ? ORDER BY line_num ASC",
                (row["path"],),
            ).fetchall()
        ]
        related_facts = [
            serialize_fact(f)
            for f in conn.execute(
                "SELECT * FROM facts WHERE scope = ? AND status = 'active' ORDER BY id DESC LIMIT 20",
                (row["scope"],),
            ).fetchall()
        ]
        return {
            "path": row["path"],
            "scope": row["scope"],
            "title": row["title"],
            "summary": row["summary"],
            "tags": json.loads(row["tags"] or "[]"),
            "updated_by": row["updated_by"],
            "updated_at": row["updated_at"],
            "content": row["body"],
            "observations": observations,
            "outgoing_links": outgoing,
            "relations": relations,
            "backlinks": backlinks,
            "connected_notes": connected_notes,
            "scope_active_facts": related_facts,
        }


def op_build_context(
    conn: sqlite3.Connection,
    target: str,
    *,
    depth: int = 1,
) -> dict[str, object]:
    """Traverse 1-2 hops of [[wikilinks]] & semantic relations plus active/historical temporal facts (Basic Memory + Graphiti)."""
    with DB_LOCK:
        sync_vault_notes(conn)
        cleaned = (target or "").strip().lstrip("/").removeprefix("memory/")
        if not cleaned:
            raise MemoryError("target is required for memory_build_context")
        hops = max(1, min(int(depth or 1), 2))

        root_note: dict[str, object] | None = None
        frontier_paths: set[str] = set()
        try:
            root_note = op_read_note(conn, cleaned)
            frontier_paths.add(str(root_note["path"]))
        except MemoryError:
            root_note = None

        visited_paths: set[str] = set(frontier_paths)
        graph_edges: list[dict[str, str]] = []

        for _ in range(hops):
            if not frontier_paths:
                break
            next_frontier: set[str] = set()
            for src in sorted(frontier_paths):
                stem_lower = Path(src).stem.lower()
                no_ext = src.lower().removesuffix(".md")
                # Outgoing edges from src
                for r in conn.execute(
                    "SELECT target_slug, relation_type FROM note_links WHERE source_path = ?",
                    (src,),
                ).fetchall():
                    slug = str(r["target_slug"]).removesuffix(".md")
                    rel_t = str(r["relation_type"])
                    esc_slug_name = _escape_like(Path(slug).name)
                    for m in conn.execute(
                        "SELECT path FROM notes WHERE lower(path) IN (?, ?) OR lower(path) LIKE ? ESCAPE '\\'",
                        (f"{slug}.md", slug, f"%/{esc_slug_name}.md"),
                    ).fetchall():
                        dst = str(m["path"])
                        graph_edges.append({"source": src, "relation": rel_t, "target": dst})
                        if dst not in visited_paths:
                            visited_paths.add(dst)
                            next_frontier.add(dst)
                # Incoming backlinks to src
                for r in conn.execute(
                    "SELECT source_path, relation_type FROM note_links WHERE target_slug IN (?, ?)",
                    (stem_lower, no_ext),
                ).fetchall():
                    in_src = str(r["source_path"])
                    rel_t = str(r["relation_type"])
                    graph_edges.append({"source": in_src, "relation": rel_t, "target": src})
                    if in_src not in visited_paths:
                        visited_paths.add(in_src)
                        next_frontier.add(in_src)
            frontier_paths = next_frontier

        neighbor_paths = sorted(visited_paths - ({str(root_note["path"])} if root_note else set()))
        neighbor_notes: list[dict[str, object]] = []
        if neighbor_paths:
            ph = ",".join("?" for _ in neighbor_paths)
            neighbor_notes = [
                {
                    "path": r["path"],
                    "scope": r["scope"],
                    "title": r["title"],
                    "summary": r["summary"],
                    "updated_by": r["updated_by"],
                    "updated_at": r["updated_at"],
                }
                for r in conn.execute(
                    f"SELECT path, scope, title, summary, updated_by, updated_at FROM notes WHERE path IN ({ph})",
                    tuple(neighbor_paths),
                ).fetchall()
            ]

        all_paths = sorted(visited_paths)
        observations: list[dict[str, object]] = []
        if all_paths:
            ph = ",".join("?" for _ in all_paths)
            observations = [
                {
                    "source_path": r["source_path"],
                    "category": r["category"],
                    "observation": r["observation"],
                    "tags": json.loads(r["tags"] or "[]"),
                    "line_num": r["line_num"],
                }
                for r in conn.execute(
                    f"SELECT source_path, category, observation, tags, line_num FROM note_observations WHERE source_path IN ({ph}) ORDER BY source_path, line_num",
                    tuple(all_paths),
                ).fetchall()
            ]

        subj_slug = slugify_segment(Path(cleaned).stem).lower()
        target_scope = str(root_note["scope"]) if root_note else ""
        if target_scope:
            fact_rows = conn.execute(
                "SELECT * FROM facts WHERE scope = ? OR subject = ? ORDER BY id DESC LIMIT 40",
                (target_scope, subj_slug),
            ).fetchall()
        else:
            esc_subj = _escape_like(subj_slug)
            fact_rows = conn.execute(
                "SELECT * FROM facts WHERE subject = ? OR scope LIKE ? ESCAPE '\\' ORDER BY id DESC LIMIT 40",
                (subj_slug, f"%{esc_subj}%"),
            ).fetchall()

        serialized_facts = [serialize_fact(f) for f in fact_rows]
        return {
            "target": target,
            "depth": hops,
            "root_note": root_note,
            "connected_notes": neighbor_notes,
            "graph_edges": graph_edges,
            "inline_observations": observations,
            "valid_facts": [f for f in serialized_facts if f["is_valid"]],
            "invalid_and_superseded_facts": [f for f in serialized_facts if not f["is_valid"]],
        }


def op_list_notes(conn: sqlite3.Connection, scope: str = "") -> dict[str, object]:
    with DB_LOCK:
        sync_vault_notes(conn)
        if (scope or "").strip():
            norm = normalize_scope(scope)
            esc_norm = _escape_like(norm)
            rows = conn.execute(
                "SELECT path, scope, title, summary, tags, updated_by, updated_at FROM notes WHERE scope = ? OR scope LIKE ? ESCAPE '\\' ORDER BY path ASC",
                (norm, f"{esc_norm}/%"),
            ).fetchall()
        else:
            rows = conn.execute(
                "SELECT path, scope, title, summary, tags, updated_by, updated_at FROM notes ORDER BY scope ASC, path ASC"
            ).fetchall()
        return {
            "count": len(rows),
            "notes": [
                {
                    "path": r["path"],
                    "scope": r["scope"],
                    "title": r["title"],
                    "summary": r["summary"],
                    "tags": json.loads(r["tags"] or "[]"),
                    "updated_by": r["updated_by"],
                    "updated_at": r["updated_at"],
                }
                for r in rows
            ],
        }


def fts_query_tokens(query: str) -> str:
    words = re.findall(r"[a-zA-Z0-9_]+", query or "")
    if not words:
        return ""
    return " OR ".join(f'"{w}"*' for w in words[:12])


def op_search(
    conn: sqlite3.Connection,
    *,
    query: str = "",
    scope: str = "",
    category: str = "",
    include_history: bool = False,
    validity: str = "",
    limit: int = 15,
) -> dict[str, object]:
    with DB_LOCK:
        sync_vault_notes(conn)
        cap = max(1, min(int(limit or 15), 50))
        norm_scope = normalize_scope(scope) if (scope or "").strip() else ""
        esc_scope = _escape_like(norm_scope)
        fts_q = fts_query_tokens(query)
        val_mode = (validity or ("all" if include_history else "valid")).strip().lower()
        if val_mode not in ("valid", "invalid", "all"):
            val_mode = "valid"

        if fts_q:
            sql_facts = """
                SELECT f.*
                FROM facts_fts fts
                JOIN facts f ON f.id = fts.rowid
                WHERE facts_fts MATCH ?
            """
            params_f: list[object] = [fts_q]
            if norm_scope:
                sql_facts += " AND (f.scope = ? OR f.scope LIKE ? ESCAPE '\\')"
                params_f.extend([norm_scope, f"{esc_scope}/%"])
            else:
                sql_facts += " AND f.scope != 'resources/books' AND f.scope NOT LIKE 'resources/books/%'"
            if category.strip():
                sql_facts += " AND f.category = ?"
                params_f.append(category.strip().lower())
            if val_mode == "valid":
                sql_facts += " AND f.status = 'active'"
            elif val_mode == "invalid":
                sql_facts += " AND f.status != 'active'"
            sql_facts += " ORDER BY bm25(facts_fts), f.id DESC LIMIT ?"
            params_f.append(cap)
            fact_rows = conn.execute(sql_facts, params_f).fetchall()

            sql_notes = """
                SELECT n.path, n.scope, n.title, n.summary, n.tags, n.updated_by, n.updated_at,
                       snippet(notes_fts, 5, '[', ']', ' … ', 24) AS snippet
                FROM notes_fts
                JOIN notes n ON n.path = notes_fts.path
                WHERE notes_fts MATCH ?
            """
            params_n: list[object] = [fts_q]
            if norm_scope:
                sql_notes += " AND (n.scope = ? OR n.scope LIKE ? ESCAPE '\\')"
                params_n.extend([norm_scope, f"{esc_scope}/%"])
            else:
                sql_notes += " AND n.scope != 'resources/books' AND n.scope NOT LIKE 'resources/books/%'"
            sql_notes += " ORDER BY bm25(notes_fts) LIMIT ?"
            params_n.append(cap)
            note_rows = conn.execute(sql_notes, params_n).fetchall()
        else:
            sql_facts = "SELECT * FROM facts WHERE 1=1"
            params_f = []
            if norm_scope:
                sql_facts += " AND (scope = ? OR scope LIKE ? ESCAPE '\\')"
                params_f.extend([norm_scope, f"{esc_scope}/%"])
            else:
                sql_facts += " AND scope != 'resources/books' AND scope NOT LIKE 'resources/books/%'"
            if category.strip():
                sql_facts += " AND category = ?"
                params_f.append(category.strip().lower())
            if val_mode == "valid":
                sql_facts += " AND status = 'active'"
            elif val_mode == "invalid":
                sql_facts += " AND status != 'active'"
            sql_facts += " ORDER BY id DESC LIMIT ?"
            params_f.append(cap)
            fact_rows = conn.execute(sql_facts, params_f).fetchall()

            sql_notes = "SELECT path, scope, title, summary, tags, updated_by, updated_at, substr(body, 1, 240) AS snippet FROM notes WHERE 1=1"
            params_n = []
            if norm_scope:
                sql_notes += " AND (scope = ? OR scope LIKE ? ESCAPE '\\')"
                params_n.extend([norm_scope, f"{esc_scope}/%"])
            else:
                sql_notes += " AND scope != 'resources/books' AND scope NOT LIKE 'resources/books/%'"
            sql_notes += " ORDER BY updated_at DESC LIMIT ?"
            params_n.append(cap)
            note_rows = conn.execute(sql_notes, params_n).fetchall()

        sql_obs = """
            SELECT o.source_path, n.scope, o.category, o.observation, o.tags, o.line_num
            FROM note_observations o
            JOIN notes n ON n.path = o.source_path
            WHERE 1=1
        """
        params_o: list[object] = []
        if norm_scope:
            sql_obs += " AND (n.scope = ? OR n.scope LIKE ? ESCAPE '\\')"
            params_o.extend([norm_scope, f"{esc_scope}/%"])
        else:
            sql_obs += " AND n.scope != 'resources/books' AND n.scope NOT LIKE 'resources/books/%'"
        if category.strip():
            sql_obs += " AND o.category = ?"
            params_o.append(category.strip().lower())
        if (query or "").strip():
            sql_obs += " AND lower(o.observation) LIKE ? ESCAPE '\\'"
            params_o.append(f"%{_escape_like(query.strip().lower())}%")
        sql_obs += " ORDER BY o.source_path, o.line_num LIMIT ?"
        params_o.append(cap)
        obs_rows = conn.execute(sql_obs, params_o).fetchall()

        return {
            "query": query,
            "scope_filter": norm_scope or "all",
            "validity_filter": val_mode,
            "facts": [serialize_fact(r) for r in fact_rows],
            "observations": [
                {
                    "source_path": r["source_path"],
                    "scope": r["scope"],
                    "category": r["category"],
                    "observation": r["observation"],
                    "tags": json.loads(r["tags"] or "[]"),
                    "line_num": r["line_num"],
                }
                for r in obs_rows
            ],
            "notes": [
                {
                    "path": r["path"],
                    "scope": r["scope"],
                    "title": r["title"],
                    "summary": r["summary"],
                    "tags": json.loads(r["tags"] or "[]"),
                    "updated_by": r["updated_by"],
                    "updated_at": r["updated_at"],
                    "snippet": r["snippet"],
                }
                for r in note_rows
            ],
        }


def op_briefing(
    conn: sqlite3.Connection,
    actor: str,
    *,
    scope: str = "",
    project: str = "",
) -> dict[str, object]:
    with DB_LOCK:
        sync_vault_notes(conn)
        if (scope or "").strip():
            project_scope = normalize_scope(scope)
        elif (project or "").strip():
            proj = project.strip()
            project_scope = normalize_scope(proj if proj.startswith((*AREAS, "shared", "agents/")) else f"projects/{proj}")
        else:
            project_scope = normalize_scope(DEFAULT_SCOPE)
        if actor.startswith("hermes/"):
            own_agent_scope = f"agents/{actor.split('/', 1)[1]}"
        elif actor in AGENTS:
            own_agent_scope = f"agents/{actor}"
        else:
            own_agent_scope = None

        active_facts = [
            serialize_fact(r)
            for r in conn.execute(
                "SELECT * FROM facts WHERE status = 'active' ORDER BY scope ASC, category ASC, id DESC LIMIT 100"
            ).fetchall()
        ]
        recent_invalid_or_superseded = [
            serialize_fact(r)
            for r in conn.execute(
                "SELECT * FROM facts WHERE status != 'active' ORDER BY updated_at DESC, id DESC LIMIT 20"
            ).fetchall()
        ]
        notes = op_list_notes(conn)["notes"]

        agent_buckets: dict[str, list[dict[str, object]]] = {}
        for f in active_facts:
            sc = str(f["scope"])
            if sc.startswith("agents/"):
                agent_buckets.setdefault(sc, []).append(f)
        for a in AGENTS:
            agent_buckets.setdefault(f"agents/{a}", [])
        if own_agent_scope:
            agent_buckets.setdefault(own_agent_scope, [])

        return {
            "authenticated_actor": actor,
            "permissions": {
                "readable_scopes": READABLE_SCOPES,
                "private_excluded_scopes": ["personal/*"],
                "writable_scopes": writable_scopes_for(actor),
                "own_agent_scope": own_agent_scope,
            },
            "focus_project_scope": project_scope,
            "focus_project_facts": [
                f for f in active_facts
                if f["scope"] == project_scope or str(f["scope"]).startswith(f"{project_scope}/")
            ],
            "shared_facts": [f for f in active_facts if f["scope"] == "shared"],
            # Facts of each settings "briefing_areas" area that the focus list above does not already carry.
            **{
                f"{area}_facts": [
                    f for f in active_facts
                    if _scope_matches(str(f["scope"]), area) and not _scope_matches(str(f["scope"]), project_scope)
                ]
                for area in BRIEFING_AREAS
            },
            "agent_specific_facts": agent_buckets,
            "recent_invalidated_and_superseded_facts": recent_invalid_or_superseded,
            # The focus scope's newest notes only: the whole vault index (531 notes, ~60k tokens)
            # made every briefing expensive. memory_list_notes / list-notes gives the rest.
            "notes_total": len(notes),
            "notes_index": sorted(
                (n for n in notes if n["scope"] == project_scope or str(n["scope"]).startswith(f"{project_scope}/")),
                key=lambda n: str(n.get("updated_at") or ""),
                reverse=True,
            )[:40],
        }


# ── MCP Tool Schema & Dispatcher ──────────────────────────────────────────

MCP_TOOLS = [
    {
        "name": "memory_briefing",
        "description": (
            "Load the complete cross-agent memory briefing from the unified Obsidian vault (active valid facts, "
            "invalidated/superseded history, shared facts, per-area facts, each "
            "agent/sub-agent's readable memory, and the 40 newest notes in the focus scope; "
            "use memory_list_notes or memory_search for other notes)."
        ),
        "annotations": {"readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "properties": {
                "scope": {"type": "string", "description": f"Optional focus scope (default: {DEFAULT_SCOPE!r}; e.g. 'shared', 'projects/<slug>').", "default": DEFAULT_SCOPE},
                "project": {"type": "string", "description": "Optional project slug if focusing on 'projects/<slug>'.", "default": ""},
                "subagent": {"type": "string", "description": "Optional Hermes profile name (e.g. 'default').", "default": ""},
            },
        },
    },
    {
        "name": "memory_search",
        "description": (
            "Search across ALL AI-to-AI temporal facts (valid and/or invalid/superseded), inline Markdown observations "
            "('- [category] text #tag'), and Markdown notes across the entire unified Obsidian vault "
            f"({', '.join(READABLE_SCOPES)})."
        ),
        "annotations": {"readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "properties": {
                "query": {"type": "string", "description": "Keywords or question to search for (leave empty to list recent)."},
                "scope": {"type": "string", "description": "Optional scope or prefix filter (e.g. 'shared', 'projects/<slug>', 'agents/claude').", "default": ""},
                "category": {"type": "string", "description": "Optional fact/observation category filter (weakness, strength, progress, decision, preference, question, fact).", "default": ""},
                "validity": {"type": "string", "enum": ["valid", "invalid", "all"], "description": "Filter facts by temporal validity: 'valid' (default, active only), 'invalid' (superseded/invalidated only), or 'all'.", "default": "valid"},
                "include_history": {"type": "boolean", "description": "Alias for validity='all' (include superseded and invalidated facts).", "default": False},
                "limit": {"type": "integer", "description": "Max results (1-50).", "default": 15},
            },
        },
    },
    {
        "name": "memory_build_context",
        "description": (
            "Build multi-hop graph & temporal context around any vault note or topic (combines Basic Memory's build_context "
            "graph traversal across [[wikilinks]] and '- relation [[Target]]' edges with Graphiti's valid + invalidated/superseded temporal facts)."
        ),
        "annotations": {"readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "required": ["target"],
            "properties": {
                "target": {"type": "string", "description": "Note path, note filename, or subject slug (e.g. 'projects/<slug>/README.md' or 'release-process')."},
                "depth": {"type": "integer", "description": "Graph traversal depth in hops (1 or 2).", "default": 1},
            },
        },
    },
    {
        "name": "memory_read_note",
        "description": (
            "Read any full Markdown, PDF, or DOCX document from the unified Obsidian vault (e.g. 'shared/notes.md', "
            "'resources/books/...', 'projects/...', 'agents/gotchas/...'), "
            "along with its inline observations, [[wikilinks]], backlinks, 1-hop connected note summaries, and active facts."
        ),
        "annotations": {"readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "required": ["path"],
            "properties": {
                "path": {"type": "string", "description": "Document path or filename in the vault (.md, .pdf, or .docx, e.g. 'shared/notes.md' or 'resources/books/manual.pdf')."},
            },
        },
    },
    {
        "name": "memory_list_notes",
        "description": f"List all indexed Markdown, PDF, and DOCX documents across the unified Obsidian vault ({', '.join(READABLE_SCOPES)}).",
        "annotations": {"readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "properties": {
                "scope": {"type": "string", "description": "Optional scope or prefix filter (e.g. 'resources/books', 'projects/<slug>', 'agents/gotchas').", "default": ""},
            },
        },
    },
    {
        "name": "memory_check_facts",
        "description": (
            "Fact-check a claim, decision, or topic against active facts, superseded/invalidated history, and vault notes "
            "before answering or saving new memory. Returns matching_active_facts, matching_history_facts, related_notes, "
            "and concrete reconciliation guidance so agents catch contradictions and stale claims."
        ),
        "annotations": {"readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "properties": {
                "statement": {"type": "string", "description": "Claim, question, or statement to verify against memory."},
                "scope": {"type": "string", "description": "Optional scope or prefix filter (e.g. 'shared', 'projects/<slug>').", "default": ""},
                "subject": {"type": "string", "description": "Optional topic slug to check exact subject history (e.g. 'release-process').", "default": ""},
                "limit": {"type": "integer", "description": "Max matching facts per bucket (1-25).", "default": 8},
            },
        },
    },
    {
        "name": "memory_remember_fact",
        "description": (
            "Save or update an atomic AI-to-AI temporal fact (marked 'valid' from now). "
            "Call memory_check_facts first when unsure whether an older fact exists. "
            f"Write rules: {', '.join(OPEN_SCOPES)} are writable by all agents; "
            "'agents/<agent>' is writable ONLY by that owning agent or Hermes profile. "
            "Set 'subject' (e.g. 'release-process') so older active facts on the same subject in that scope "
            "are automatically marked 'superseded' with a valid_until timestamp. Also returns 'potential_conflicts' "
            "for other active facts in the same scope sharing keywords."
        ),
        "annotations": {"readOnlyHint": False, "destructiveHint": False, "idempotentHint": False, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "required": ["fact"],
            "properties": {
                "fact": {"type": "string", "description": "Clear, self-contained atomic statement to remember."},
                "scope": {
                    "type": "string",
                    "description": f"Target scope ({DEFAULT_SCOPE!r} by default), e.g. 'shared', 'projects/<slug>', or your own 'agents/<your-agent-or-profile>'.",
                    "default": DEFAULT_SCOPE,
                },
                "subject": {"type": "string", "description": "Short topic slug (e.g. 'release-process', 'preferred-editor') so future updates supersede this fact cleanly.", "default": ""},
                "category": {
                    "type": "string",
                    "enum": list(VALID_CATEGORIES),
                    "description": "Fact category: weakness, strength, progress, decision, preference, question, or fact.",
                    "default": "fact",
                },
                "supersedes_id": {"type": "integer", "description": "Optional specific fact ID this update replaces.", "default": 0},
                "supersede_subject": {"type": "boolean", "description": "Automatically supersede older state on the same subject in this scope.", "default": True},
                "subagent": {"type": "string", "description": "Optional Hermes profile identity (e.g. 'default').", "default": ""},
            },
        },
    },
    {
        "name": "memory_forget_fact",
        "description": (
            "Retire an outdated, contradicted, or incorrect AI-to-AI fact (marks it 'invalidated' or 'superseded' "
            "with a valid_until timestamp, preserving audit history). Always provide a brief 'reason' when retiring a wrong or stale claim. "
            "Requires write access to the fact's scope."
        ),
        "annotations": {"readOnlyHint": False, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "required": ["fact_id"],
            "properties": {
                "fact_id": {"type": "integer", "description": "ID of the fact to mark invalid/superseded."},
                "reason": {"type": "string", "description": "Brief reason for invalidating/retiring.", "default": ""},
                "resolution": {"type": "string", "enum": ["invalidated", "superseded"], "description": "Whether the fact was 'invalidated' (false/obsolete) or 'superseded'.", "default": "invalidated"},
                "subagent": {"type": "string", "description": "Optional Hermes sub-agent identity.", "default": ""},
            },
        },
    },
    {
        "name": "memory_write_note",
        "description": (
            "Create or update a human-readable Markdown note directly in the Obsidian vault. "
            f"Write rules: any agent may write to {', '.join(OPEN_SCOPES)}; "
            "only the owning agent/Hermes profile may write to 'agents/<agent>/*'."
        ),
        "annotations": {"readOnlyHint": False, "destructiveHint": False, "idempotentHint": False, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "required": ["path", "content"],
            "properties": {
                "path": {"type": "string", "description": "Path in the vault such as 'projects/<slug>/design.md', 'shared/notes.md', or 'agents/claude/preferences.md'."},
                "content": {"type": "string", "description": "Clean Markdown content (use [[wikilinks]], headings, and bullet points)."},
                "title": {"type": "string", "description": "Document title.", "default": ""},
                "scope": {"type": "string", "description": "Optional explicit scope ('shared', 'resources/books', 'projects/<slug>', 'agents/<self>').", "default": ""},
                "summary": {"type": "string", "description": "One-line summary for the master index and Home.md Dataview.", "default": ""},
                "tags": {"type": "array", "items": {"type": "string"}, "description": "Tags for filtering.", "default": []},
                "mode": {
                    "type": "string",
                    "enum": ["replace", "append", "section"],
                    "description": "'replace' (overwrite note), 'append' (add to end), or 'section' (update one ## Heading section).",
                    "default": "replace",
                },
                "section": {"type": "string", "description": "Section heading name when mode='section'.", "default": ""},
                "subagent": {"type": "string", "description": "Optional Hermes sub-agent identity.", "default": ""},
            },
        },
    },
    {
        "name": "memory_upload_document",
        "description": (
            "Upload and index a binary .pdf or .docx document (or .md/.txt file) into the Obsidian vault using Base64 content. "
            "Automatically extracts structured Markdown text, headings, and tables into FTS5 search while preserving the original binary file in the vault."
        ),
        "annotations": {"readOnlyHint": False, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "inputSchema": {
            "type": "object",
            "required": ["filename", "base64_content"],
            "properties": {
                "filename": {"type": "string", "description": "Target filename or vault path ending in .pdf, .docx, .md, or .txt (e.g. 'projects/<slug>/spec.docx' or 'resources/books/manual.pdf')."},
                "base64_content": {"type": "string", "description": "Base64-encoded file bytes."},
                "scope": {"type": "string", "description": "Target scope ('shared', 'resources/books', 'projects/<slug>').", "default": DEFAULT_SCOPE},
                "title": {"type": "string", "description": "Optional human-readable document title.", "default": ""},
                "summary": {"type": "string", "description": "Optional one-line summary for the index.", "default": ""},
                "tags": {"type": "array", "items": {"type": "string"}, "description": "Optional tags.", "default": []},
                "subagent": {"type": "string", "description": "Optional Hermes sub-agent identity.", "default": ""},
            },
        },
    },
]


def call_mcp_tool(conn: sqlite3.Connection, actor: str, name: str, arguments: dict[str, object]) -> dict[str, object]:
    args = arguments or {}
    effective_actor = normalize_actor(actor, str(args.get("subagent") or "")) if args.get("subagent") else actor
    if name == "memory_briefing":
        return op_briefing(
            conn,
            effective_actor,
            scope=str(args.get("scope") or ""),
            project=str(args.get("project") or ""),
        )
    if name == "memory_search":
        return op_search(
            conn,
            query=str(args.get("query") or ""),
            scope=str(args.get("scope") or ""),
            category=str(args.get("category") or ""),
            include_history=bool(args.get("include_history", False)),
            validity=str(args.get("validity") or ""),
            limit=_safe_int(args.get("limit"), "limit", default=15),
        )
    if name == "memory_check_facts":
        return op_check_facts(
            conn,
            statement=str(args.get("statement") or ""),
            scope=str(args.get("scope") or ""),
            subject=str(args.get("subject") or ""),
            limit=_safe_int(args.get("limit"), "limit", default=8),
        )
    if name == "memory_build_context":
        return op_build_context(
            conn,
            target=str(args.get("target") or ""),
            depth=_safe_int(args.get("depth"), "depth", default=1),
        )
    if name == "memory_read_note":
        return op_read_note(conn, str(args.get("path") or ""))
    if name == "memory_list_notes":
        return op_list_notes(conn, str(args.get("scope") or ""))
    if name == "memory_remember_fact":
        return op_remember_fact(
            conn,
            effective_actor,
            fact=str(args.get("fact") or ""),
            scope=str(args.get("scope") or DEFAULT_SCOPE),
            subject=str(args.get("subject") or ""),
            category=str(args.get("category") or "fact"),
            supersedes_id=_safe_int(args.get("supersedes_id"), "supersedes_id", default=0),
            supersede_subject=bool(args.get("supersede_subject", True)),
        )
    if name == "memory_forget_fact":
        return op_forget_fact(
            conn,
            effective_actor,
            fact_id=_safe_int(args.get("fact_id"), "fact_id", default=0),
            reason=str(args.get("reason") or ""),
            resolution=str(args.get("resolution") or "invalidated"),
        )
    if name == "memory_write_note":
        raw_tags = args.get("tags")
        tags = [str(x) for x in raw_tags] if isinstance(raw_tags, list) else []
        return op_write_note(
            conn,
            effective_actor,
            path=str(args.get("path") or ""),
            content=str(args.get("content") or ""),
            title=str(args.get("title") or ""),
            scope=str(args.get("scope") or ""),
            summary=str(args.get("summary") or ""),
            tags=tags,
            mode=str(args.get("mode") or "replace"),
            section=str(args.get("section") or ""),
        )
    if name == "memory_upload_document":
        raw_tags = args.get("tags")
        tags = [str(x) for x in raw_tags] if isinstance(raw_tags, list) else []
        return op_upload_document(
            conn,
            effective_actor,
            filename=str(args.get("filename") or ""),
            base64_content=str(args.get("base64_content") or ""),
            scope=str(args.get("scope") or DEFAULT_SCOPE),
            title=str(args.get("title") or ""),
            summary=str(args.get("summary") or ""),
            tags=tags,
        )
    raise MemoryError(f"Unknown tool: {name}")


def handle_jsonrpc_message(conn: sqlite3.Connection, actor: str, msg: dict[str, object]) -> dict[str, object] | None:
    method = msg.get("method")
    req_id = msg.get("id")
    params = msg.get("params") if isinstance(msg.get("params"), dict) else {}

    # Notifications have no id and expect no response object.
    if req_id is None:
        return None

    if method == "initialize":
        offered_version = str(params.get("protocolVersion") or "2025-03-26")
        return {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "protocolVersion": offered_version,
                "capabilities": {
                    "tools": {"listChanged": False},
                    "resources": {"subscribe": False, "listChanged": False},
                    "prompts": {"listChanged": False},
                },
                "serverInfo": {
                    "name": "vyn-memory",
                    "version": "1.3.0",
                },
                "instructions": (
                    f"Authenticated as '{actor}'. You have complete read access across the unified Obsidian vault "
                    f"({', '.join(READABLE_SCOPES)}). "
                    f"You can write to {', '.join(writable_scopes_for(actor))}. "
                    "Before saving or relying on a changing claim, call memory_check_facts to check active facts and retired history; "
                    "always pass a stable 'subject' slug on memory_remember_fact so newer state supersedes older facts cleanly, "
                    "and reconcile any returned potential_conflicts with memory_forget_fact."
                ),
            },
        }
    if method == "ping":
        return {"jsonrpc": "2.0", "id": req_id, "result": {}}
    if method == "tools/list":
        return {"jsonrpc": "2.0", "id": req_id, "result": {"tools": MCP_TOOLS}}
    if method == "resources/list":
        try:
            notes = op_list_notes(conn)["notes"]
        except MemoryError as exc:
            return {"jsonrpc": "2.0", "id": req_id, "error": {"code": -32602, "message": str(exc)}}
        resources = [
            {
                "uri": f"memory://{n['path']}",
                "name": n["title"],
                "description": f"[{n['scope']}] {n['summary']}".strip(),
                "mimeType": "text/markdown",
            }
            for n in notes
        ]
        return {"jsonrpc": "2.0", "id": req_id, "result": {"resources": resources}}
    if method == "resources/read":
        uri = str(params.get("uri") or "")
        rel = uri.removeprefix("memory://").lstrip("/")
        try:
            note = op_read_note(conn, rel)
        except MemoryError as exc:
            return {
                "jsonrpc": "2.0",
                "id": req_id,
                "error": {"code": -32602, "message": str(exc)},
            }
        return {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "contents": [
                    {
                        "uri": uri,
                        "mimeType": "text/markdown",
                        "text": note["content"],
                    }
                ]
            },
        }
    if method == "prompts/list":
        return {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "prompts": [
                    {
                        "name": "vault-memory-briefing",
                        "description": "Load the complete cross-agent vault memory briefing (facts, shared facts, projects and agent memory).",
                        "arguments": [],
                    }
                ]
            },
        }
    if method == "prompts/get":
        try:
            brief = op_briefing(conn, actor, scope=DEFAULT_SCOPE)
        except MemoryError as exc:
            return {"jsonrpc": "2.0", "id": req_id, "error": {"code": -32602, "message": str(exc)}}
        return {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "description": "Unified Obsidian vault & cross-agent memory context",
                "messages": [
                    {
                        "role": "user",
                        "content": {
                            "type": "text",
                            "text": "Here is my live unified Obsidian vault and cross-agent memory briefing:\n\n"
                            + json.dumps(brief, indent=2),
                        },
                    }
                ],
            },
        }
    if method == "tools/call":
        tool_name = str(params.get("name") or "")
        tool_args = params.get("arguments") if isinstance(params.get("arguments"), dict) else {}
        try:
            data = call_mcp_tool(conn, actor, tool_name, tool_args)
            return {
                "jsonrpc": "2.0",
                "id": req_id,
                "result": {
                    "content": [{"type": "text", "text": json.dumps(data, indent=2, ensure_ascii=False)}],
                    "isError": False,
                },
            }
        except MemoryError as exc:
            return {
                "jsonrpc": "2.0",
                "id": req_id,
                "result": {
                    "content": [{"type": "text", "text": json.dumps({"error": str(exc), "actor": actor}, indent=2)}],
                    "isError": True,
                },
            }

    return {
        "jsonrpc": "2.0",
        "id": req_id,
        "error": {"code": -32601, "message": f"Method not found: {method}"},
    }


# ── Simple Markdown-to-HTML Renderer for Human Reading UI ─────────────────


_LATEX_SYMBOL_MAP: tuple[tuple[str, str], ...] = (
    (r"\mu", "µ"),
    (r"\times", "×"),
    (r"\cdot", "·"),
    (r"\approx", "≈"),
    (r"\le", "≤"),
    (r"\leq", "≤"),
    (r"\ge", "≥"),
    (r"\geq", "≥"),
    (r"\ne", "≠"),
    (r"\neq", "≠"),
    (r"\pm", "±"),
    (r"\rightarrow", "→"),
    (r"\to", "→"),
    (r"\leftarrow", "←"),
    (r"\leftrightarrow", "↔"),
    (r"\Rightarrow", "⇒"),
    (r"\infty", "∞"),
    (r"\alpha", "α"),
    (r"\beta", "β"),
    (r"\gamma", "γ"),
    (r"\delta", "δ"),
    (r"\Delta", "Δ"),
    (r"\lambda", "λ"),
    (r"\Omega", "Ω"),
    (r"\omega", "ω"),
    (r"\pi", "π"),
    (r"\sigma", "σ"),
    (r"\theta", "θ"),
    (r"\%", "%"),
)

_SUPERSCRIPT_DIGITS = str.maketrans("0123456789+-nN", "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻ⁿᴺ")
_SUBSCRIPT_DIGITS = str.maketrans("0123456789+-", "₀₁₂₃₄₅₆₇₈₉₊₋")


def _clean_latex_fragment(expr: str) -> str:
    """Convert an inline LaTeX math fragment into clean human-readable Unicode."""
    out = expr.strip()
    out = re.sub(r"\\(?:text|mathrm|mathbf|mathit)\{([^{}]*)\}", r"\1", out)
    out = re.sub(r"\\frac\{([^{}]+)\}\{([^{}]+)\}", r"(\1/\2)", out)
    for src, dst in _LATEX_SYMBOL_MAP:
        out = out.replace(src, dst)
    out = re.sub(
        r"\^\{([0-9+\-nN]+)\}",
        lambda m: m.group(1).translate(_SUPERSCRIPT_DIGITS),
        out,
    )
    out = re.sub(
        r"\^([0-9nN])",
        lambda m: m.group(1).translate(_SUPERSCRIPT_DIGITS),
        out,
    )
    out = re.sub(
        r"_\{([0-9+\-]+)\}",
        lambda m: m.group(1).translate(_SUBSCRIPT_DIGITS),
        out,
    )
    out = re.sub(
        r"_\{([A-Za-z0-9_]+)\}",
        r"_\1",
        out,
    )
    out = re.sub(
        r"_([0-9])",
        lambda m: m.group(1).translate(_SUBSCRIPT_DIGITS),
        out,
    )
    out = out.replace("{", "").replace("}", "")
    return out


def _clean_latex_inline(text: str) -> str:
    """Convert inline $...$ LaTeX math into human-readable Unicode while preserving currency amounts."""
    if "$" not in text and "\\" not in text:
        return text
    cleaned = re.sub(
        r"\$(?!\s)([^\$\n]{1,120}?)(?<!\s)\$",
        lambda m: (
            m.group(0)
            if re.match(r"^\d[\d,.]*(?:\s*(?:k|m|b|usd|inr|mo|yr))?$", m.group(1).strip(), re.I)
            else _clean_latex_fragment(m.group(1))
        ),
        text,
    )
    for src, dst in _LATEX_SYMBOL_MAP:
        if src in cleaned:
            cleaned = cleaned.replace(src, dst)
    return cleaned


def _heading_slug(text: str, index: int) -> str:
    plain = re.sub(r"[`*_~\[\]()]", "", _clean_latex_inline(text))
    slug = re.sub(r"[^a-z0-9]+", "-", plain.lower()).strip("-")[:48]
    return f"sec-{index}-{slug or 'section'}"


def extract_toc_headings(md_text: str) -> list[dict[str, object]]:
    """Extract H2 and H3 headings with deterministic section anchor IDs for the 'On this page' outline."""
    toc: list[dict[str, object]] = []
    in_code = False
    sec_idx = 0
    for raw_line in md_text.splitlines():
        stripped = raw_line.strip()
        if stripped.startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        if stripped.startswith("# "):
            sec_idx += 1
        elif stripped.startswith("## "):
            sec_idx += 1
            label = re.sub(r"[`*_~]", "", _clean_latex_inline(stripped[3:].strip()))
            toc.append({"level": 2, "id": _heading_slug(stripped[3:], sec_idx), "title": label})
        elif stripped.startswith("### "):
            sec_idx += 1
            label = re.sub(r"[`*_~]", "", _clean_latex_inline(stripped[4:].strip()))
            toc.append({"level": 3, "id": _heading_slug(stripped[4:], sec_idx), "title": label})
        elif stripped.startswith("#### "):
            sec_idx += 1
    return toc


def render_markdown_html(md_text: str, prefix: str = "") -> str:
    """Clean, dependency-free Markdown renderer supporting headings with anchors, code blocks, lists, tables, links, and [[wikilinks]]."""
    safe_prefix = html.escape(prefix or "/", quote=True)
    lines = md_text.splitlines()
    out: list[str] = []
    in_code = False
    in_ul = False
    in_ol = False
    in_table = False
    in_quote = False
    sec_idx = 0

    def close_blocks() -> None:
        nonlocal in_ul, in_ol, in_table, in_quote
        if in_ul:
            out.append("</ul>")
            in_ul = False
        if in_ol:
            out.append("</ol>")
            in_ol = False
        if in_quote:
            out.append("</blockquote>")
            in_quote = False
        if in_table:
            out.append("</tbody></table></div>")
            in_table = False

    def inline_fmt(s: str) -> str:
        code_spans: list[str] = []
        raw_codes: list[str] = []
        link_spans: list[str] = []
        clean_s = s.replace("\x00", "")

        def _stash_code(m: re.Match[str]) -> str:
            idx = len(code_spans)
            raw_codes.append(m.group(1))
            code_spans.append(f"<code>{html.escape(m.group(1))}</code>")
            return f"\x00CODE{idx}\x00"

        def _restore_raw_codes(val: str) -> str:
            for idx, rc in enumerate(raw_codes):
                val = val.replace(f"\x00CODE{idx}\x00", rc)
            return val

        def _stash_link(anchor_html: str) -> str:
            idx = len(link_spans)
            link_spans.append(anchor_html)
            return f"\x00LINK{idx}\x00"

        def _render_md_link_local(m: re.Match[str]) -> str:
            label_html = m.group(1)
            raw_target = _restore_raw_codes(html.unescape(m.group(2).strip()))
            if raw_target.startswith(("http://", "https://", "mailto:")):
                return _stash_link(
                    f'<a class="ext-link" href="{html.escape(raw_target, quote=True)}" target="_blank" rel="noopener">{label_html}</a>'
                )
            if raw_target.startswith("#"):
                return _stash_link(f'<a class="wikilink" href="{html.escape(raw_target, quote=True)}">{label_html}</a>')
            clean_note = raw_target.split("#", 1)[0].strip().lstrip("./").removeprefix("memory/")
            return _stash_link(f'<a class="wikilink" href="{safe_prefix}?note={urllib.parse.quote(clean_note)}">{label_html}</a>')

        with_code_tokens = re.sub(r"`([^`]+)`", _stash_code, clean_s)
        humanized = _clean_latex_inline(with_code_tokens)
        escaped = html.escape(humanized)
        escaped = re.sub(
            r"\[\[([^\]|]+)\|([^\]]+)\]\]",
            lambda m: _stash_link(
                f'<a class="wikilink" href="{safe_prefix}?note={urllib.parse.quote(_restore_raw_codes(html.unescape(m.group(1))).strip().removeprefix("memory/"))}">{m.group(2)}</a>'
            ),
            escaped,
        )
        escaped = re.sub(
            r"\[\[([^\]]+)\]\]",
            lambda m: _stash_link(
                f'<a class="wikilink" href="{safe_prefix}?note={urllib.parse.quote(_restore_raw_codes(html.unescape(m.group(1))).strip().removeprefix("memory/"))}">{m.group(1)}</a>'
            ),
            escaped,
        )
        escaped = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)", _render_md_link_local, escaped)
        escaped = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", escaped)
        escaped = re.sub(r"~~([^~]+)~~", r"<del>\1</del>", escaped)
        escaped = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<em>\1</em>", escaped)
        for idx, anchor_html in enumerate(link_spans):
            escaped = escaped.replace(f"\x00LINK{idx}\x00", anchor_html)
        for idx, span_html in enumerate(code_spans):
            escaped = escaped.replace(f"\x00CODE{idx}\x00", span_html)
        return escaped

    for line in lines:
        if line.strip().startswith("```"):
            close_blocks()
            if not in_code:
                in_code = True
                lang = line.strip()[3:].strip()
                lang_badge = f'<div class="code-lang">{html.escape(lang)}</div>' if lang else ""
                out.append(f'<div class="code-block">{lang_badge}<pre><code>')
            else:
                in_code = False
                out.append("</code></pre></div>")
            continue
        if in_code:
            out.append(html.escape(line))
            continue
        stripped = line.strip()
        if not stripped:
            close_blocks()
            continue
        if re.match(r"^(?:-{3,}|\*{3,}|_{3,})$", stripped):
            close_blocks()
            out.append("<hr>")
            continue
        if stripped.startswith("|") and stripped.endswith("|"):
            cells = [c.strip() for c in stripped.strip("|").split("|")]
            if all(re.match(r"^:?-{2,}:?$", c) for c in cells):
                continue
            if not in_table:
                close_blocks()
                in_table = True
                out.append('<div class="table-wrap"><table><thead><tr>' + "".join(f"<th>{inline_fmt(c)}</th>" for c in cells) + "</tr></thead><tbody>")
            else:
                out.append("<tr>" + "".join(f"<td>{inline_fmt(c)}</td>" for c in cells) + "</tr>")
            continue
        if stripped.startswith(">"):
            if in_ul or in_ol or in_table:
                close_blocks()
            if not in_quote:
                in_quote = True
                out.append("<blockquote>")
            q_body = stripped[1:].lstrip()
            if q_body:
                out.append(f"<p>{inline_fmt(q_body)}</p>")
            continue
        if stripped.startswith("- ") or stripped.startswith("* "):
            if in_ol or in_quote or in_table:
                close_blocks()
            if not in_ul:
                in_ul = True
                out.append("<ul>")
            out.append(f"<li>{inline_fmt(stripped[2:])}</li>")
            continue
        ol_match = re.match(r"^(\d+)[.)]\s+(.*)$", stripped)
        if ol_match:
            if in_ul or in_quote or in_table:
                close_blocks()
            if not in_ol:
                in_ol = True
                out.append("<ol>")
            out.append(f"<li>{inline_fmt(ol_match.group(2))}</li>")
            continue
        close_blocks()
        if stripped.startswith("# "):
            sec_idx += 1
            hid = _heading_slug(stripped[2:], sec_idx)
            out.append(f'<h1 id="{hid}">{inline_fmt(stripped[2:])}</h1>')
        elif stripped.startswith("## "):
            sec_idx += 1
            hid = _heading_slug(stripped[3:], sec_idx)
            out.append(f'<h2 id="{hid}">{inline_fmt(stripped[3:])}</h2>')
        elif stripped.startswith("### "):
            sec_idx += 1
            hid = _heading_slug(stripped[4:], sec_idx)
            out.append(f'<h3 id="{hid}">{inline_fmt(stripped[4:])}</h3>')
        elif stripped.startswith("#### "):
            sec_idx += 1
            hid = _heading_slug(stripped[5:], sec_idx)
            out.append(f'<h4 id="{hid}">{inline_fmt(stripped[5:])}</h4>')
        else:
            out.append(f"<p>{inline_fmt(stripped)}</p>")
    close_blocks()
    if in_code:
        out.append("</code></pre></div>")
    return "\n".join(out)


_FALLBACK_CSRF_SECRET = secrets.token_hex(32)


def _upload_csrf_secret() -> bytes:
    owner_tok = configured_tokens().get("owner", "").strip()
    raw = (owner_tok or _FALLBACK_CSRF_SECRET).encode("utf-8")
    return hashlib.sha256(b"vyn-memory-csrf:" + raw).digest()


def _csrf_session_tag(session_token: str) -> str:
    cleaned = (session_token or "").strip()
    return hashlib.sha256(cleaned.encode("utf-8")).hexdigest()[:16] if cleaned else ""


def _mint_upload_csrf(now_ts: float | None = None, *, purpose: str = "upload", session_token: str = "") -> str:
    ts = str(int(now_ts if now_ts is not None else time.time()))
    purpose_clean = (purpose or "upload").strip().lower()
    sess_tag = _csrf_session_tag(session_token)
    msg = f"{purpose_clean}:{sess_tag}:{ts}".encode("utf-8")
    sig = hmac.new(_upload_csrf_secret(), msg, hashlib.sha256).hexdigest()
    return f"{ts}.{sig}"


def _verify_upload_csrf(
    token: str,
    max_age: int = 86400 * 7,
    *,
    purpose: str = "upload",
    session_token: str = "",
) -> bool:
    cleaned = (token or "").strip()
    if "." not in cleaned:
        return False
    ts_str, sig = cleaned.split(".", 1)
    if not ts_str.isdigit():
        return False
    ts = int(ts_str)
    age = time.time() - ts
    if age < -60 or age > max_age:
        return False
    purpose_clean = (purpose or "upload").strip().lower()
    sess_tag = _csrf_session_tag(session_token)
    msg = f"{purpose_clean}:{sess_tag}:{ts_str}".encode("utf-8")
    expected = hmac.new(_upload_csrf_secret(), msg, hashlib.sha256).hexdigest()
    return hmac.compare_digest(expected, sig)


# Dashboard layout; settings "dashboard" replaces any of these keys.
DASHBOARD: dict = {
    "title": "Vyn Memory",
    # Sidebar groups in display order: [key, label, open by default].
    "groups": [
        ["projects", "🚀 Projects", True],
        ["books", "📚 Resources", True],
        ["business", "💼 Business", False],
        ["inbox", "📥 Inbox", True],
        ["daily", "📅 Daily Logs", False],
        ["agent_gotchas", "⚠️ Agent Gotchas & Fixes", True],
        ["agent_decisions", "🧭 Decisions", False],
        ["agent_hermes", "🦾 Hermes Profiles & Playbooks", False],
        ["agent_external", "🧠 Claude, ChatGPT & Antigravity", False],
        ["shared", "🌐 Shared", False],
        ["other", "📁 General Notes", False],
    ],
    # [regex matched at the start of the lowercase note path, group key]; first match wins, else "other".
    "rules": [
        ["resources/", "books"], ["projects/", "projects"], ["business/", "business"], ["inbox/", "inbox"],
        ["daily/", "daily"], ["agents/gotchas/", "agent_gotchas"], ["agents/decisions/", "agent_decisions"],
        ["agents/(claude|chatgpt|antigravity)/", "agent_external"], ["agents/", "agent_hermes"], ["shared/", "shared"],
    ],
    # Scope pills across the top: [scope, label].
    "folders": [
        ["", "🗂️ Entire Vault"], ["projects", "🚀 Projects"], ["business", "💼 Business"],
        ["daily", "🗓️ Daily & Inbox"], ["agents", "🤖 AI Agents"], ["resources/books", "📚 Books"],
    ],
    "scopes": ["", "shared", "projects", "resources/books", "business", "daily", "inbox", "agents"],
    "pinned": [],  # [path, label] quick links
    "landing": ["agents/gotchas/README.md"],  # first existing note opens by default
    "upload_scopes": ["shared", "projects", "resources/books", "daily", "inbox", "agents"],
} | SETTINGS.get("dashboard", {})


def _classify_confluence_bucket(path_str: str) -> str:
    low = path_str.strip("/").lower()
    return next((key for pattern, key in DASHBOARD["rules"] if re.match(pattern, low)), "other")


def _humanize_note_title(title: str, path_str: str) -> str:
    cleaned = _clean_latex_inline(title.strip())
    if cleaned and not re.match(r"^[a-z0-9_\-]+$", cleaned):
        return cleaned
    stem = path_str.rsplit("/", 1)[-1].rsplit(".", 1)[0]
    stem = re.sub(r"^00-", "", stem)
    return stem.replace("-", " ").replace("_", " ").title() or title


def render_dashboard_page(
    conn: sqlite3.Connection,
    actor: str,
    *,
    selected_note: str = "",
    scope_filter: str = "",
    search_query: str = "",
    base_path: str = "/",
    session_token: str = "",
) -> str:
    safe_base_path = html.escape(base_path or "/", quote=True)
    upload_csrf = _mint_upload_csrf(purpose="upload", session_token=session_token)
    facts_csrf = _mint_upload_csrf(purpose="facts", session_token=session_token)
    with DB_LOCK:
        sync_vault_notes(conn)
    try:
        all_scope_notes = op_list_notes(conn, scope=scope_filter)["notes"]
    except MemoryError:
        scope_filter = ""
        all_scope_notes = op_list_notes(conn, scope="")["notes"]
    if scope_filter == "daily":
        inbox_notes = op_list_notes(conn, scope="inbox")["notes"]
        seen_p = {str(n["path"]) for n in all_scope_notes}
        all_scope_notes = list(inbox_notes) + [n for n in all_scope_notes if str(n["path"]) not in seen_p]
    search_res = op_search(conn, query=search_query, scope=scope_filter, include_history=True, limit=40)

    if search_query.strip():
        matched_paths = {str(n["path"]) for n in search_res["notes"]}
        notes = [n for n in all_scope_notes if str(n["path"]) in matched_paths] or list(search_res["notes"])
    else:
        notes = all_scope_notes

    note_paths_set = {str(n["path"]) for n in all_scope_notes}
    preferred_defaults = DASHBOARD["landing"]
    default_landing = next(
        (cand for cand in preferred_defaults if cand in note_paths_set),
        str(notes[0]["path"]) if notes else "",
    )
    target_note = selected_note or (default_landing if not search_query else (str(notes[0]["path"]) if notes else ""))

    note_html = ""
    active_note_meta = None
    toc_items: list[dict[str, object]] = []
    if target_note:
        try:
            active_note_meta = op_read_note(conn, target_note)
            raw_md = str(active_note_meta["content"])
            note_html = render_markdown_html(raw_md, prefix=base_path)
            toc_items = extract_toc_headings(raw_md)
        except MemoryError:
            active_note_meta = None

    root_folders = DASHBOARD["folders"]
    all_known_scopes = DASHBOARD["scopes"]
    dashboard_title = str(DASHBOARD.get("title") or "Vyn Memory")

    def _is_folder_active(root_sc: str) -> bool:
        if not root_sc:
            return scope_filter == ""
        if root_sc == "daily" and scope_filter in ("daily", "inbox"):
            return True
        return scope_filter == root_sc or scope_filter.startswith(root_sc + "/")

    scope_pills = "".join(
        f'<a class="pill {"active" if _is_folder_active(s) else ""}" '
        f'href="{safe_base_path}?scope={urllib.parse.quote(s)}">{label}</a>'
        for s, label in root_folders
    )

    def _note_badge(path_str: str) -> str:
        low = path_str.lower()
        if low.endswith(".pdf"):
            return " <span class='badge scope-badge'>PDF</span>"
        if low.endswith(".docx"):
            return " <span class='badge scope-badge'>DOCX</span>"
        return ""

    # Quick-access pinned links tailored to the active root folder
    pinned_specs = DASHBOARD["pinned"]
    active_path_str = str(active_note_meta["path"]) if active_note_meta else ""
    pinned_links_list: list[str] = []
    for p_path, p_label in pinned_specs:
        if p_path in note_paths_set:
            is_act = "active-note" if active_path_str == p_path else ""
            pinned_links_list.append(
                f'<a class="quick-link {is_act}" '
                f'href="{safe_base_path}?scope={urllib.parse.quote(scope_filter)}&note={urllib.parse.quote(p_path)}">'
                f"{p_label}</a>"
            )
    quick_links_html = (
        '<div class="quick-links"><div class="sidebar-section-label">⚡ Quick Access</div>'
        + "".join(pinned_links_list)
        + "</div>"
        if pinned_links_list
        else ""
    )

    # Group notes into collapsible folder tree
    buckets: dict[str, list[dict[str, object]]] = {k: [] for k, _, _ in DASHBOARD["groups"]}
    for n in notes:
        b_key = _classify_confluence_bucket(str(n["path"]))
        buckets.setdefault(b_key, []).append(n)

    def _note_sort_key(n: dict[str, object]) -> tuple[int, str]:
        p = str(n["path"])
        fname = p.rsplit("/", 1)[-1].lower()
        is_overview = 0 if (fname.startswith("00-") or fname == "readme.md" or fname.startswith("master-")) else 1
        return (is_overview, _humanize_note_title(str(n["title"]), p).lower())

    non_empty_bucket_keys = [k for k, _, _ in DASHBOARD["groups"] if buckets.get(k)]
    tree_groups_html: list[str] = []
    for b_key, b_label, default_open in DASHBOARD["groups"]:
        b_notes = buckets.get(b_key, [])
        if not b_notes:
            continue
        if b_key == "daily":
            b_notes_sorted = sorted(b_notes, key=lambda x: str(x["path"]), reverse=True)
        else:
            b_notes_sorted = sorted(b_notes, key=_note_sort_key)
        has_active = any(str(n["path"]) == active_path_str for n in b_notes_sorted)
        should_open = (
            has_active
            or default_open
            or bool(search_query.strip())
            or len(non_empty_bucket_keys) <= 3
        ) and not (b_key in ("qbanks", "archive", "biz_vynq") and not has_active and not search_query.strip() and len(non_empty_bucket_keys) > 1)
        items_html: list[str] = []
        for n in b_notes_sorted:
            n_path = str(n["path"])
            n_fname = n_path.rsplit("/", 1)[-1].lower()
            icon = "📘" if (n_fname.startswith("00-") or n_fname == "readme.md") else "📄"
            is_act = "active-note" if active_path_str == n_path else ""
            clean_title = _humanize_note_title(str(n["title"]), n_path)
            sub_hint = ""
            if b_key == "company":
                parts = n_path.split("/")
                if len(parts) >= 3 and parts[2].lower() != "readme.md":
                    sub_hint = f"<span class='tree-sub'>{html.escape(parts[2].upper())}</span> "
            elif b_key == "agent_hermes":
                parts = n_path.split("/")
                if len(parts) >= 2:
                    sub_hint = f"<span class='tree-sub'>{html.escape(parts[1].upper())}</span> "
            items_html.append(
                f'<li><a class="tree-item {is_act}" '
                f'href="{safe_base_path}?scope={urllib.parse.quote(scope_filter)}&note={urllib.parse.quote(n_path)}" '
                f'title="{html.escape(n_path)}">'
                f'<span class="tree-icon">{icon}</span>'
                f'<span class="tree-title">{sub_hint}{html.escape(clean_title)}{_note_badge(n_path)}</span>'
                f"</a></li>"
            )
        open_attr = " open" if should_open else ""
        tree_groups_html.append(
            f'<details class="tree-group"{open_attr}>'
            f'<summary class="tree-summary">'
            f'<span class="tree-folder-name">{b_label}</span>'
            f'<span class="tree-count">{len(b_notes_sorted)}</span>'
            f"</summary>"
            f'<ul class="note-list">{"".join(items_html)}</ul>'
            f"</details>"
        )
    notes_tree_html = "".join(tree_groups_html) or '<p class="muted">No matching pages in this folder.</p>'

    # Breadcrumbs for the active article
    breadcrumbs_html = ""
    if active_note_meta:
        parts = str(active_note_meta["path"]).split("/")
        crumbs: list[str] = [f'<a href="{safe_base_path}?scope=">🏠 Vault</a>']
        accum: list[str] = []
        for folder in parts[:-1]:
            accum.append(folder)
            sc_path = "/".join(accum)
            folder_label = folder.replace("-", " ").replace("_", " ").title()
            if folder.lower() in ("c", "os", "arm", "dsa", "bsp"):
                folder_label = folder.upper()
            crumbs.append(
                f'<a href="{safe_base_path}?scope={urllib.parse.quote(sc_path)}">{html.escape(folder_label)}</a>'
            )
        doc_title = _humanize_note_title(str(active_note_meta["title"]), str(active_note_meta["path"]))
        crumbs.append(f'<span class="crumb-current">{html.escape(doc_title)}</span>')
        breadcrumbs_html = '<nav class="breadcrumbs" aria-label="Breadcrumb">' + ' <span class="crumb-sep">›</span> '.join(crumbs) + "</nav>"

    active_download_btn = ""
    if active_note_meta and str(active_note_meta["path"]).lower().endswith((".pdf", ".docx")):
        ext_label = "PDF" if str(active_note_meta["path"]).lower().endswith(".pdf") else "DOCX"
        dl_href = f"{safe_base_path.rstrip('/')}/download?path={urllib.parse.quote(str(active_note_meta['path']))}"
        active_download_btn = (
            f" · <a class='dl-btn' href='{dl_href}' target='_blank' rel='noopener'>"
            f"⬇️ Open Original {ext_label}</a>"
        )

    # Connected notes & backlinks at the bottom of the article
    connected_html = ""
    if active_note_meta and active_note_meta.get("connected_notes"):
        conn_cards: list[str] = []
        for cn in active_note_meta["connected_notes"][:12]:  # type: ignore[index]
            cn_path = str(cn["path"])
            cn_title = _humanize_note_title(str(cn["title"]), cn_path)
            conn_cards.append(
                f'<a class="conn-card" href="{safe_base_path}?scope={urllib.parse.quote(scope_filter)}&note={urllib.parse.quote(cn_path)}">'
                f"<strong>📄 {html.escape(cn_title)}</strong>"
                f"<span class='muted'>{html.escape(cn_path)}</span></a>"
            )
        connected_html = (
            '<section class="connected-section">'
            '<h2 class="connected-title">🔗 Connected Pages &amp; Backlinks</h2>'
            f'<div class="connected-grid">{"".join(conn_cards)}</div>'
            "</section>"
        )

    # Sticky Right-Hand "On this page" Table of Contents
    if toc_items:
        toc_links = "".join(
            f'<a class="toc-link toc-h{item["level"]}" href="#{html.escape(str(item["id"]), quote=True)}">'
            f'{html.escape(str(item["title"]))}</a>'
            for item in toc_items
        )
        toc_html = f'<nav class="toc-nav" aria-label="On this page"><div class="toc-header">📑 On this page</div>{toc_links}</nav>'
    else:
        toc_html = '<div class="toc-nav"><div class="toc-header">📑 On this page</div><p class="muted">Open any page with headings to jump straight to a section.</p></div>'

    upload_scope_default = scope_filter if scope_filter in all_known_scopes and scope_filter else DEFAULT_SCOPE
    upload_scope_options = "".join(
        f'<option value="{html.escape(sc)}" {"selected" if sc == upload_scope_default else ""}>{html.escape(sc)}</option>'
        for sc in DASHBOARD["upload_scopes"]
    )
    category_options = "".join(
        f'<option value="{html.escape(cat)}" {"selected" if cat == "fact" else ""}>{html.escape(cat)}</option>'
        for cat in VALID_CATEGORIES
    )

    cur_qs: list[tuple[str, str]] = [("scope", scope_filter)]
    if active_path_str:
        cur_qs.append(("note", active_path_str))
    if search_query.strip():
        cur_qs.append(("q", search_query.strip()))
    current_page_url = f"{base_path or '/'}?{urllib.parse.urlencode(cur_qs)}"

    all_facts = list(search_res["facts"])
    active_fact_count = sum(1 for f in all_facts if f.get("is_valid", True))
    retired_fact_count = len(all_facts) - active_fact_count
    facts_html_rows: list[str] = []
    for f in all_facts:
        is_inv = not f.get("is_valid", True)
        badge_cls = f"cat-{html.escape(str(f['category']))}"
        subj = f"<strong>[{html.escape(str(f['subject']))}]</strong> " if f.get("subject") else ""
        row_text = f"{subj}{html.escape(_clean_latex_inline(str(f['fact'])))}"
        state_badge = "<span class='badge valid-badge'>VALID</span>"
        history_note = ""
        action_html = ""
        if is_inv:
            label = "SUPERSEDED" if f.get("status") == "superseded" else "INVALIDATED"
            state_badge = f"<span class='badge invalid-badge'>{label}</span>"
            row_text = f"<del>{row_text}</del>"
            extra_parts: list[str] = []
            if f.get("superseded_by"):
                extra_parts.append(f"replaced by #{f['superseded_by']}")
            if f.get("invalidated_reason"):
                extra_parts.append(html.escape(str(f["invalidated_reason"])))
            if f.get("invalidated_by"):
                extra_parts.append(f"by {html.escape(str(f['invalidated_by']))}")
            if extra_parts:
                history_note = f"<div class='fact-reason'>{' · '.join(extra_parts)}</div>"
        elif actor == "owner":
            action_html = (
                f"<form class='fact-retire-form' method='post' action='{safe_base_path.rstrip('/')}/facts'>"
                f"<input type='hidden' name='csrf_token' value='{html.escape(facts_csrf, quote=True)}'>"
                f"<input type='hidden' name='action' value='forget'>"
                f"<input type='hidden' name='fact_id' value='{int(f['id'])}'>"
                f"<input type='hidden' name='next' value='{html.escape(current_page_url, quote=True)}'>"
                f"<input type='hidden' name='reason' value='Retired by owner in web UI'>"
                f"<button type='submit' class='fact-retire-btn' aria-label='Retire fact #{int(f['id'])}'>Retire</button>"
                f"</form>"
            )
        facts_html_rows.append(
            f"<div class='fact-card {'superseded' if is_inv else ''}'>"
            f"<div class='fact-head'><div class='fact-badges'>{state_badge} "
            f"<span class='badge {badge_cls}'>{html.escape(str(f['category']))}</span> "
            f"<span class='badge scope-badge'>{html.escape(str(f['scope']))}</span></div>{action_html}</div>"
            f"<div class='fact-text'>{row_text}</div>"
            f"{history_note}"
            f"<div class='fact-meta'>#{f['id']} · by <code>{html.escape(str(f['author']))}</code> · {html.escape(str(f['valid_from'])[:10])}"
            + (f" → {html.escape(str(f['valid_until'])[:10])}" if f.get("valid_until") else "")
            + "</div></div>"
        )
    facts_block = "\n".join(facts_html_rows) or "<p class='muted'>No matching AI facts in this folder yet.</p>"
    add_fact_html = ""
    if actor == "owner":
        add_fact_html = (
            f"<details class='fact-add'>"
            f"<summary>+ Add verified fact</summary>"
            f"<form class='fact-add-form' method='post' action='{safe_base_path.rstrip('/')}/facts'>"
            f"<input type='hidden' name='csrf_token' value='{html.escape(facts_csrf, quote=True)}'>"
            f"<input type='hidden' name='action' value='add'>"
            f"<input type='hidden' name='next' value='{html.escape(current_page_url, quote=True)}'>"
            f"<label class='form-label' for='fact-scope'>Scope</label>"
            f"<select id='fact-scope' name='scope'>{upload_scope_options}</select>"
            f"<label class='form-label' for='fact-subject'>Topic slug (updates replace old fact)</label>"
            f"<input id='fact-subject' type='text' name='subject' placeholder='e.g. preferred-editor'>"
            f"<label class='form-label' for='fact-category'>Category</label>"
            f"<select id='fact-category' name='category'>{category_options}</select>"
            f"<label class='form-label' for='fact-statement'>Verified statement</label>"
            f"<textarea id='fact-statement' name='fact' rows='2' placeholder='Clear, self-contained fact to share across agents' required></textarea>"
            f"<button type='submit'>Save Fact</button>"
            f"</form></details>"
        )

    search_banner_html = ""
    if search_query.strip():
        search_banner_html = (
            f"<div class='search-banner'>"
            f"<span>Showing <strong>{len(notes)}</strong> page(s) and <strong>{len(all_facts)}</strong> fact(s) for "
            f"<code>{html.escape(search_query.strip())}</code></span>"
            f"<a href='{safe_base_path}?scope={urllib.parse.quote(scope_filter)}'>Clear search</a>"
            f"</div>"
        )

    if active_note_meta:
        reader_body_html = (
            search_banner_html
            + breadcrumbs_html
            + f"<div class='doc-meta-bar'><span class='badge scope-badge'>{html.escape(str(active_note_meta['scope']))}</span>"
            + f"<span>📄 <code>{html.escape(str(active_note_meta['path']))}</code></span>"
            + f"<span>· Updated {html.escape(str(active_note_meta['updated_at'])[:10])} by <strong>{html.escape(str(active_note_meta['updated_by']))}</strong></span>"
            + f"{active_download_btn}</div>"
            + note_html
            + connected_html
        )
    elif search_query.strip():
        reader_body_html = (
            search_banner_html
            + "<div class='empty-state'><h2>No pages matched that search</h2>"
            + "<p class='muted'>Try fewer keywords, switch to Entire Vault on the left, or check matching AI Memory Facts on the right.</p></div>"
        )
    elif notes:
        reader_body_html = (
            "<div class='empty-state'><h2>Select a page from the folder tree</h2>"
            "<p class='muted'>Browse folders on the left, search notes and facts above, or upload a <code>.md</code>, <code>.pdf</code>, or <code>.docx</code> document.</p></div>"
        )
    else:
        reader_body_html = (
            "<div class='empty-state'>"
            "<h2>Your memory vault is ready</h2>"
            "<p>Notes, uploaded PDFs/DOCX files, and verified AI facts appear here so you and your coding/chat assistants stay in sync.</p>"
            "<ul>"
            "<li>Use <strong>Upload</strong> in the top bar to index your first <code>.md</code>, <code>.pdf</code>, or <code>.docx</code> file.</li>"
            "<li>Open <a href='/apps'>Connected apps</a> for your MCP URL and 1-command laptop login.</li>"
            "<li>Add or retire shared facts directly in the <strong>AI Memory Facts</strong> panel on the right.</li>"
            "</ul></div>"
        )

    reader_checked = "checked" if active_note_meta else ""
    notes_checked = "" if active_note_meta else "checked"
    facts_open_attr = " open" if search_query.strip() else ""
    writable_tooltip = html.escape("Writable folders: " + ", ".join(writable_scopes_for(actor)), quote=True)

    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html.escape(dashboard_title)} · Vault &amp; Memory Hub</title>
  <style>
    html {{ scroll-behavior: smooth; }}
    :root {{
      --header-h: 54px;
      --bg: #f8fafc;
      --canvas: #ffffff;
      --panel: #f1f5f9;
      --panel-hover: #e2e8f0;
      --header-bg: #ffffff;
      --border: #e2e8f0;
      --border-strong: #cbd5e1;
      --text: #0f172a;
      --text-body: #1e293b;
      --muted: #475569;
      --accent: #0052cc;
      --accent-soft: #e0f2fe;
      --accent-border: #93c5fd;
      --green: #15803d;
      --green-bg: #dcfce7;
      --amber: #b45309;
      --amber-bg: #fef3c7;
      --red: #b91c1c;
      --red-bg: #fee2e2;
      --code-inline-bg: #f1f5f9;
      --code-inline-fg: #0f172a;
      --pre-bg: #0f172a;
      --pre-fg: #f8fafc;
      --quote-bg: #f0f7ff;
      --shadow: 0 2px 6px rgba(15, 23, 42, 0.06);
    }}
    #theme-dark:checked ~ .app-shell {{
      --bg: #0b1120;
      --canvas: #0f172a;
      --panel: #1e293b;
      --panel-hover: #334155;
      --header-bg: #020617;
      --border: #1e293b;
      --border-strong: #334155;
      --text: #f8fafc;
      --text-body: #e2e8f0;
      --muted: #cbd5e1;
      --accent: #38bdf8;
      --accent-soft: rgba(56, 189, 248, 0.14);
      --accent-border: #0284c7;
      --green: #4ade80;
      --green-bg: rgba(74, 222, 128, 0.16);
      --amber: #fbbf24;
      --amber-bg: rgba(251, 191, 36, 0.16);
      --red: #f87171;
      --red-bg: rgba(248, 113, 113, 0.16);
      --code-inline-bg: #1e293b;
      --code-inline-fg: #38bdf8;
      --pre-bg: #020617;
      --pre-fg: #f1f5f9;
      --quote-bg: rgba(56, 189, 248, 0.08);
      --shadow: 0 2px 8px rgba(0, 0, 0, 0.35);
    }}
    * {{ box-sizing: border-box; }}
    ::selection {{ background: var(--accent-soft); color: var(--accent); }}
    :focus-visible {{ outline: 2px solid var(--accent); outline-offset: 2px; }}
    body {{ margin: 0; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Inter, sans-serif; background: var(--bg); color: var(--text); line-height: 1.65; overflow-x: hidden; caret-color: var(--accent); }}
    .app-shell {{ min-height: 100vh; background: var(--bg); color: var(--text); width: 100%; max-width: 100vw; overflow-x: clip; }}
    .theme-checkbox, .mview-radio {{ position: fixed; top: 0; left: 0; width: 0; height: 0; opacity: 0; pointer-events: none; margin: 0; }}
    header {{ min-height: var(--header-h); padding: 8px 20px; background: var(--header-bg); border-bottom: 1px solid var(--border); display: flex; flex-wrap: nowrap; gap: 12px; align-items: center; justify-content: space-between; position: sticky; top: 0; z-index: 30; }}
    .brand-wrap {{ display: flex; align-items: center; gap: 10px; flex-shrink: 0; }}
    .brand {{ font-weight: 700; font-size: 0.98rem; color: var(--accent); letter-spacing: -0.01em; text-decoration: none; white-space: nowrap; }}
    .search-form {{ display: flex; gap: 6px; flex: 1 1 380px; max-width: 480px; min-width: 0; align-items: center; }}
    .search-form input[type="search"] {{ width: 100%; min-width: 0; background: var(--bg); color: var(--text); border: 1px solid var(--border-strong); border-radius: 6px; padding: 6px 12px; font-size: 0.85rem; }}
    .search-form input[type="search"]:focus {{ outline: 2px solid var(--accent); border-color: transparent; }}
    .search-form button, .upload-form button, .fact-add-form button {{ background: var(--accent); color: #ffffff; border: none; border-radius: 6px; padding: 6px 12px; font-weight: 600; cursor: pointer; font-size: 0.82rem; white-space: nowrap; flex-shrink: 0; }}
    #theme-dark:checked ~ .app-shell .search-form button, #theme-dark:checked ~ .app-shell .upload-form button, #theme-dark:checked ~ .app-shell .fact-add-form button {{ color: #020617; }}
    .clear-search {{ font-size: 0.78rem; color: var(--muted); text-decoration: none; padding: 4px 6px; white-space: nowrap; }}
    .header-right {{ display: flex; align-items: center; gap: 8px; flex-shrink: 0; }}
    .upload-box {{ position: relative; }}
    .upload-box summary {{ list-style: none; cursor: pointer; padding: 5px 10px; border-radius: 6px; border: 1px solid var(--border-strong); background: var(--canvas); color: var(--text-body); font-size: 0.8rem; font-weight: 600; white-space: nowrap; user-select: none; }}
    .upload-box summary::-webkit-details-marker {{ display: none; }}
    .upload-box[open] > summary {{ border-color: var(--accent); color: var(--accent); background: var(--accent-soft); }}
    .upload-box[open] > summary::before {{ content: " "; position: fixed; top: 0; right: 0; bottom: 0; left: 0; z-index: 45; display: block; cursor: default; background: transparent; }}
    .upload-box:not([open]) .upload-form {{ display: none; }}
    .upload-form {{ position: absolute; right: 0; top: calc(100% + 6px); z-index: 50; width: 310px; max-width: calc(100vw - 28px); padding: 14px; background: var(--canvas); border: 1px solid var(--border-strong); border-radius: 12px; box-shadow: 0 10px 25px rgba(15,23,42,0.18); display: flex; flex-direction: column; gap: 6px; }}
    .form-label {{ font-size: 0.75rem; font-weight: 600; color: var(--muted); margin-top: 2px; }}
    .upload-form select, .upload-form input[type="text"], .upload-form input[type="file"], .fact-add-form select, .fact-add-form input[type="text"], .fact-add-form textarea {{ background: var(--bg); color: var(--text); border: 1px solid var(--border-strong); border-radius: 6px; padding: 6px 8px; font-size: 0.82rem; width: 100%; font-family: inherit; }}
    .theme-toggle {{ cursor: pointer; font-size: 0.79rem; font-weight: 600; padding: 5px 10px; border-radius: 6px; border: 1px solid var(--border-strong); background: var(--panel); color: var(--text); user-select: none; white-space: nowrap; }}
    .theme-toggle:hover {{ border-color: var(--accent); color: var(--accent); }}
    .actor-tag {{ font-size: 0.78rem; background: var(--panel); padding: 4px 10px; border-radius: 6px; border: 1px solid var(--border); color: var(--muted); white-space: nowrap; }}
    .actor-tag strong {{ color: var(--text); }}
    .actor-link {{ color: inherit; font-weight: 600; text-decoration: none; }}
    .actor-link:hover {{ color: var(--accent); text-decoration: underline; }}
    .signout-link {{ color: var(--red); text-decoration: none; font-weight: 600; }}
    .signout-link:hover {{ text-decoration: underline; }}
    .dl-btn {{ display: inline-block; padding: 3px 10px; border-radius: 6px; background: var(--accent-soft); color: var(--accent); border: 1px solid var(--accent-border); text-decoration: none; font-weight: 600; font-size: 0.78rem; }}
    .mobile-tabs {{ display: none; }}
    .layout {{ display: grid; grid-template-columns: 290px minmax(0, 1fr) 280px; width: 100%; min-height: calc(100vh - var(--header-h)); align-items: start; }}
    .sidebar {{ padding: 14px 12px 28px 14px; border-right: 1px solid var(--border); background: var(--bg); height: calc(100vh - var(--header-h)); overflow-y: auto; position: sticky; top: var(--header-h); text-align: left; }}
    .sidebar-section-label {{ font-size: 0.74rem; font-weight: 700; text-transform: uppercase; letter-spacing: 0.05em; color: var(--muted); padding: 2px 8px 6px; text-align: left; }}
    .scope-strip {{ display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 5px; margin-bottom: 14px; padding-bottom: 12px; border-bottom: 1px solid var(--border); }}
    .pill {{ display: flex; align-items: center; justify-content: flex-start; gap: 5px; text-decoration: none; color: var(--text-body); background: var(--panel); padding: 5px 9px; border-radius: 6px; font-size: 0.78rem; font-weight: 500; border: 1px solid var(--border); text-align: left; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; transition: background-color 0.15s ease, color 0.15s ease; }}
    .pill:hover {{ background: var(--panel-hover); color: var(--accent); }}
    .pill.active {{ color: #ffffff; background: var(--accent); border-color: var(--accent); font-weight: 600; }}
    #theme-dark:checked ~ .app-shell .pill.active {{ color: #020617; }}
    .quick-links {{ margin-bottom: 14px; padding-bottom: 12px; border-bottom: 1px solid var(--border); display: flex; flex-direction: column; gap: 2px; text-align: left; }}
    .quick-link {{ display: block; padding: 5px 9px; border-radius: 6px; font-size: 0.82rem; font-weight: 500; color: var(--text-body); text-decoration: none; text-align: left; }}
    .quick-link:hover {{ background: var(--panel-hover); color: var(--accent); }}
    .quick-link.active-note {{ background: var(--accent-soft); color: var(--accent); font-weight: 600; }}
    .tree-group {{ margin-bottom: 3px; border-radius: 6px; text-align: left; }}
    .tree-summary {{ list-style: none; cursor: pointer; display: flex; align-items: center; justify-content: flex-start; gap: 6px; padding: 6px 8px; border-radius: 6px; font-size: 0.82rem; font-weight: 600; color: var(--text); user-select: none; text-align: left; }}
    .tree-summary::-webkit-details-marker {{ display: none; }}
    .tree-summary:hover {{ background: var(--panel-hover); }}
    .tree-folder-name {{ flex: 1 1 auto; display: flex; align-items: center; justify-content: flex-start; gap: 5px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; min-width: 0; text-align: left; }}
    .tree-group > .tree-summary::before {{ content: "▸"; font-size: 0.76rem; color: var(--muted); flex-shrink: 0; }}
    .tree-group[open] > .tree-summary::before {{ content: "▾"; color: var(--accent); }}
    .tree-count {{ font-size: 0.74rem; font-weight: 600; color: var(--muted); background: var(--panel); padding: 1px 6px; border-radius: 999px; border: 1px solid var(--border); flex-shrink: 0; margin-left: auto; font-variant-numeric: tabular-nums; }}
    .note-list {{ list-style: none; padding: 2px 0 6px 10px; margin: 0 0 0 9px; border-left: 1px solid var(--border-strong); display: flex; flex-direction: column; gap: 2px; text-align: left; }}
    .tree-item {{ display: flex; align-items: baseline; justify-content: flex-start; gap: 6px; padding: 4px 8px; border-radius: 6px; text-decoration: none; color: var(--text-body); font-size: 0.81rem; line-height: 1.35; text-align: left; }}
    .tree-item:hover {{ background: var(--panel-hover); color: var(--accent); }}
    .tree-item.active-note {{ background: var(--accent-soft); color: var(--accent); font-weight: 600; border: 1px solid var(--accent-border); }}
    .tree-icon {{ font-size: 0.78rem; flex-shrink: 0; }}
    .tree-title {{ overflow-wrap: anywhere; text-align: left; }}
    .tree-sub {{ font-size: 0.72rem; font-weight: 700; padding: 1px 5px; border-radius: 4px; background: var(--panel); color: var(--muted); border: 1px solid var(--border); }}
    .reader-wrap {{ padding: 24px 28px 60px; min-width: 0; display: flex; justify-content: center; }}
    .reader {{ background: var(--canvas); border: 1px solid var(--border); border-radius: 12px; padding: 32px 42px; max-width: 860px; width: 100%; min-width: 0; overflow-wrap: break-word; word-break: break-word; color: var(--text-body); font-size: 1rem; line-height: 1.72; }}
    .search-banner {{ display: flex; align-items: center; justify-content: space-between; gap: 10px; padding: 8px 12px; margin-bottom: 16px; border-radius: 8px; background: var(--accent-soft); border: 1px solid var(--accent-border); font-size: 0.83rem; color: var(--text); }}
    .search-banner a {{ color: var(--accent); font-weight: 600; text-decoration: none; white-space: nowrap; }}
    .search-banner a:hover {{ text-decoration: underline; }}
    .empty-state {{ padding: 8px 0; }}
    .breadcrumbs {{ display: flex; flex-wrap: wrap; align-items: center; gap: 6px; font-size: 0.81rem; color: var(--muted); margin-bottom: 8px; }}
    .breadcrumbs a {{ color: var(--muted); text-decoration: none; font-weight: 500; text-underline-offset: 3px; }}
    .breadcrumbs a:hover {{ color: var(--accent); text-decoration: underline; }}
    .crumb-sep {{ color: var(--border-strong); }}
    .crumb-current {{ color: var(--text); font-weight: 600; }}
    .doc-meta-bar {{ display: flex; flex-wrap: wrap; gap: 8px; align-items: center; font-size: 0.78rem; color: var(--muted); padding-bottom: 16px; margin-bottom: 22px; border-bottom: 1px solid var(--border); }}
    .reader h1, .reader h2, .reader h3, .reader h4 {{ color: var(--text); font-weight: 700; line-height: 1.28; letter-spacing: -0.02em; scroll-margin-top: 70px; text-wrap: balance; }}
    .reader h1 {{ font-size: 2rem; margin: 0 0 0.65em; }}
    .reader h2 {{ font-size: 1.48rem; margin-top: 1.8em; margin-bottom: 0.55em; padding-bottom: 6px; border-bottom: 1px solid var(--border); }}
    .reader h3 {{ font-size: 1.15rem; margin-top: 1.45em; margin-bottom: 0.45em; }}
    .reader h4 {{ font-size: 0.96rem; margin-top: 1.2em; margin-bottom: 0.4em; color: var(--muted); text-transform: uppercase; letter-spacing: 0.04em; }}
    .reader p {{ margin: 0 0 1.05em; max-width: 72ch; }}
    .reader ul, .reader ol {{ margin: 0 0 1.15em; padding-left: 1.5em; max-width: 72ch; }}
    .reader li {{ margin-bottom: 0.38em; }}
    .reader hr {{ border: none; border-top: 1px solid var(--border); margin: 1.8em 0; }}
    code {{ font-family: "JetBrains Mono", ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; background: var(--code-inline-bg); color: var(--code-inline-fg); padding: 2px 6px; border-radius: 5px; font-size: 0.86em; border: 1px solid var(--border); word-break: break-word; }}
    .code-block {{ margin: 14px 0 18px; border-radius: 8px; overflow: hidden; border: 1px solid var(--border-strong); background: var(--pre-bg); }}
    .code-lang {{ background: rgba(255,255,255,0.06); color: #cbd5e1; font-size: 0.74rem; font-family: ui-monospace, monospace; text-transform: uppercase; letter-spacing: 0.06em; padding: 6px 14px; border-bottom: 1px solid rgba(255,255,255,0.08); }}
    pre {{ background: var(--pre-bg); color: var(--pre-fg); margin: 0; padding: 14px 16px; overflow-x: auto; -webkit-overflow-scrolling: touch; max-width: 100%; line-height: 1.55; font-size: 0.86rem; }}
    pre code {{ word-break: normal; padding: 0; background: transparent; color: inherit; border: none; font-size: inherit; }}
    blockquote {{ margin: 16px 0; padding: 12px 16px; border: 1px solid var(--accent-border); background: var(--quote-bg); border-radius: 8px; }}
    blockquote p:last-child {{ margin-bottom: 0; }}
    .table-wrap {{ width: 100%; overflow-x: auto; -webkit-overflow-scrolling: touch; margin: 16px 0 20px; }}
    table {{ width: 100%; border-collapse: collapse; font-size: 0.88rem; background: var(--canvas); border: 1px solid var(--border); font-variant-numeric: tabular-nums; }}
    th, td {{ border: 1px solid var(--border); padding: 10px 14px; text-align: left; vertical-align: top; overflow-wrap: break-word; }}
    th {{ background: var(--panel); color: var(--text); font-weight: 600; }}
    a.wikilink, a.ext-link {{ color: var(--accent); text-decoration: none; font-weight: 500; border-bottom: 1px solid var(--accent-border); text-underline-offset: 3px; }}
    a.wikilink:hover, a.ext-link:hover {{ background: var(--accent-soft); }}
    .connected-section {{ margin-top: 32px; padding-top: 18px; border-top: 1px solid var(--border); }}
    .connected-section .connected-title {{ font-size: 1.25rem; margin: 0 0 12px; border: none; padding: 0; }}
    .connected-grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(220px, 1fr)); gap: 10px; margin-top: 10px; }}
    .conn-card {{ display: flex; flex-direction: column; gap: 3px; padding: 10px 12px; border-radius: 12px; border: 1px solid var(--border); background: var(--bg); text-decoration: none; color: var(--text); font-size: 0.84rem; transition: border-color 0.15s ease; }}
    .conn-card:hover {{ border-color: var(--accent); background: var(--accent-soft); }}
    .facts-col {{ padding: 16px 14px 28px 12px; border-left: 1px solid var(--border); background: var(--bg); height: calc(100vh - var(--header-h)); overflow-y: auto; position: sticky; top: var(--header-h); }}
    .toc-nav {{ padding-bottom: 14px; margin-bottom: 14px; border-bottom: 1px solid var(--border); display: flex; flex-direction: column; gap: 3px; }}
    .toc-header {{ font-size: 0.74rem; font-weight: 700; text-transform: uppercase; letter-spacing: 0.05em; color: var(--muted); margin-bottom: 5px; }}
    .toc-link {{ display: block; text-decoration: none; color: var(--muted); font-size: 0.8rem; line-height: 1.35; padding: 4px 8px; border-left: 1px solid var(--border-strong); border-radius: 0 4px 4px 0; }}
    .toc-link:hover {{ color: var(--accent); border-left-color: var(--accent); background: var(--panel); }}
    .toc-h3 {{ padding-left: 16px; font-size: 0.77rem; }}
    .facts-drawer summary {{ cursor: pointer; font-size: 0.8rem; font-weight: 700; color: var(--text); padding: 7px 10px; border-radius: 6px; background: var(--panel); border: 1px solid var(--border); list-style: none; display: flex; align-items: center; justify-content: space-between; }}
    .facts-drawer summary::-webkit-details-marker {{ display: none; }}
    .facts-drawer-body {{ margin-top: 10px; }}
    .facts-summary-line {{ margin: 0 0 8px; font-size: 0.78rem; color: var(--muted); }}
    .fact-add {{ margin: 0 0 10px; }}
    .fact-add > summary {{ font-size: 0.78rem; font-weight: 600; color: var(--accent); background: var(--accent-soft); border-color: var(--accent-border); padding: 6px 10px; }}
    .fact-add-form {{ display: flex; flex-direction: column; gap: 6px; margin-top: 8px; padding: 10px; border-radius: 8px; background: var(--canvas); border: 1px solid var(--border-strong); }}
    .muted {{ color: var(--muted); font-size: 0.79rem; }}
    .fact-card {{ padding: 10px 12px; border-radius: 12px; border: 1px solid var(--border); background: var(--canvas); margin-bottom: 8px; font-size: 0.82rem; overflow-wrap: break-word; }}
    .fact-card.superseded {{ opacity: 0.78; }}
    .fact-head {{ display: flex; align-items: flex-start; justify-content: space-between; gap: 6px; }}
    .fact-badges {{ display: flex; flex-wrap: wrap; gap: 4px; align-items: center; }}
    .fact-retire-form {{ margin: 0; flex-shrink: 0; }}
    .fact-retire-btn {{ background: transparent; color: var(--muted); border: 1px solid var(--border-strong); border-radius: 5px; padding: 2px 7px; font-size: 0.72rem; font-weight: 600; cursor: pointer; }}
    .fact-retire-btn:hover {{ color: var(--red); border-color: var(--red); background: var(--red-bg); }}
    .fact-text {{ margin-top: 5px; color: var(--text-body); }}
    .fact-reason {{ margin-top: 4px; font-size: 0.75rem; color: var(--muted); }}
    .badge {{ display: inline-block; padding: 2px 6px; border-radius: 4px; font-size: 0.72rem; font-weight: 700; text-transform: uppercase; }}
    .valid-badge {{ background: var(--green-bg); color: var(--green); }}
    .invalid-badge {{ background: var(--red-bg); color: var(--red); }}
    .cat-weakness {{ background: var(--red-bg); color: var(--red); }}
    .cat-strength, .cat-progress {{ background: var(--green-bg); color: var(--green); }}
    .cat-decision, .cat-preference {{ background: var(--amber-bg); color: var(--amber); }}
    .scope-badge {{ background: var(--accent-soft); color: var(--accent); }}
    .fact-meta {{ margin-top: 4px; font-size: 0.74rem; color: var(--muted); font-variant-numeric: tabular-nums; }}
    @media (max-width: 1120px) {{
      header {{ flex-wrap: wrap; padding: 8px 14px; gap: 8px; position: static; }}
      .mobile-tabs {{ display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); background: var(--canvas); border-bottom: 1px solid var(--border); position: sticky; top: 0; z-index: 25; }}
      .mtab {{ text-align: center; padding: 10px 6px; font-size: 0.83rem; font-weight: 600; color: var(--muted); cursor: pointer; border-bottom: 2px solid transparent; user-select: none; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }}
      .layout {{ display: block; min-height: auto; }}
      .sidebar, .reader-wrap, .facts-col {{ display: none; border: none; height: auto; max-height: none; position: static; width: 100%; }}
      #tab-reader:checked ~ .app-shell .layout .reader-wrap {{ display: block; }}
      #tab-notes:checked ~ .app-shell .layout .sidebar {{ display: block; }}
      #tab-facts:checked ~ .app-shell .layout .facts-col {{ display: block; }}
      #tab-reader:checked ~ .app-shell .mobile-tabs .mtab-reader,
      #tab-notes:checked ~ .app-shell .mobile-tabs .mtab-notes,
      #tab-facts:checked ~ .app-shell .mobile-tabs .mtab-facts {{
        color: var(--accent); border-bottom-color: var(--accent); background: var(--accent-soft);
      }}
    }}
    @media (max-width: 768px) {{
      header {{ padding: 8px 10px; gap: 6px; }}
      .brand {{ font-size: 0.88rem; }}
      .brand-long, .actor-name {{ display: none; }}
      .header-right {{ gap: 5px; }}
      .upload-box summary, .theme-toggle, .actor-tag {{ padding: 4px 8px; font-size: 0.75rem; }}
      .search-form {{ order: 3; flex: 1 1 100%; max-width: 100%; }}
      .search-form input[type="search"] {{ font-size: 16px; padding: 6px 10px; }}
      .upload-form {{ position: fixed; left: 12px; right: 12px; top: 96px; width: auto; max-width: none; }}
      .reader-wrap {{ padding: 10px 8px 36px; }}
      .reader {{ padding: 18px 14px; border-radius: 10px; }}
      .sidebar, .facts-col {{ padding: 12px; }}
      .reader h1 {{ font-size: 1.38rem; }}
      .reader h2 {{ font-size: 1.16rem; }}
      .reader h3 {{ font-size: 1.02rem; }}
      table {{ font-size: 0.8rem; }}
      th, td {{ padding: 6px 7px; }}
      pre {{ padding: 12px; font-size: 0.81rem; }}
    }}
  </style>
</head>
<body>
  <input type="checkbox" id="theme-dark" class="theme-checkbox">
  <input type="radio" name="mview" id="tab-reader" class="mview-radio" {reader_checked}>
  <input type="radio" name="mview" id="tab-notes" class="mview-radio" {notes_checked}>
  <input type="radio" name="mview" id="tab-facts" class="mview-radio">
  <div class="app-shell">
    <header>
      <div class="brand-wrap">
        <a class="brand" href="{safe_base_path}?scope=" title="Vyn Unified Obsidian Vault &amp; Cross-Agent Memory">📘 {html.escape(dashboard_title)}<span class="brand-long"> Vault</span></a>
      </div>
      <form class="search-form" method="get" action="{safe_base_path}">
        <input type="hidden" name="scope" value="{html.escape(scope_filter)}">
        <input type="search" name="q" value="{html.escape(search_query)}" aria-label="Search notes and facts" placeholder="Search notes, topics, facts...">
        <button type="submit">Search</button>
        {f'<a class="clear-search" href="{safe_base_path}?scope={urllib.parse.quote(scope_filter)}" aria-label="Clear search">✕</a>' if search_query else ''}
      </form>
      <div class="header-right">
        <details class="upload-box">
          <summary>📤 Upload</summary>
          <form class="upload-form" method="post" action="{safe_base_path.rstrip('/')}/upload" enctype="multipart/form-data">
            <input type="hidden" name="csrf_token" value="{html.escape(upload_csrf, quote=True)}">
            <label class="form-label" for="upload-scope">Folder</label>
            <select id="upload-scope" name="scope">{upload_scope_options}</select>
            <label class="form-label" for="upload-file">File (.md, .pdf, .docx, .txt)</label>
            <input id="upload-file" type="file" name="file" accept=".pdf,.docx,.md,.txt" required>
            <label class="form-label" for="upload-title">Title (optional)</label>
            <input id="upload-title" type="text" name="title" placeholder="Uses filename if blank">
            <button type="submit">Upload &amp; Index</button>
          </form>
        </details>
        <label for="theme-dark" class="theme-toggle" title="Switch between Light and Dark mode">🌓 Theme</label>
        <div class="actor-tag" title="{writable_tooltip}"><span class="actor-name"><strong>{html.escape(actor)}</strong> · </span><a class="actor-link" href="/apps">Apps</a> · <a class="signout-link" href="/logout">Sign Out</a></div>
      </div>
    </header>
    <nav class="mobile-tabs" aria-label="Mobile view switcher">
      <label for="tab-reader" class="mtab mtab-reader">📖 Read</label>
      <label for="tab-notes" class="mtab mtab-notes">📁 Folders ({len(notes)})</label>
      <label for="tab-facts" class="mtab mtab-facts">📑 Outline &amp; Facts</label>
    </nav>
    <div class="layout">
      <aside class="sidebar" aria-label="Folder navigation">
        <div class="sidebar-section-label">📁 Root Folders</div>
        <div class="scope-strip">{scope_pills}</div>
        {quick_links_html}
        <div class="sidebar-section-label">🗂️ Folder Tree ({len(notes)} pages)</div>
        {notes_tree_html}
      </aside>
      <div class="reader-wrap">
        <main class="reader">
          {reader_body_html}
        </main>
      </div>
      <aside class="facts-col" aria-label="Page outline and AI facts">
        {toc_html}
        <details class="facts-drawer"{facts_open_attr}>
          <summary><span>⚡ AI Memory Facts</span><span class="tree-count">{active_fact_count}</span></summary>
          <div class="facts-drawer-body">
            <p class="facts-summary-line"><strong>{active_fact_count}</strong> active · {retired_fact_count} history — shared across all connected agents.</p>
            {add_fact_html}
            {facts_block}
          </div>
        </details>
      </aside>
    </div>
  </div>
</body>
</html>"""


def build_openapi_schema(server_url: str) -> dict[str, object]:
    """OpenAPI 3.1.0 schema for ChatGPT Custom GPT Actions."""
    return {
        "openapi": "3.1.0",
        "info": {
            "title": "Vyn Unified Cross-Agent Memory & Obsidian Vault API",
            "version": "1.2.0",
            "description": (
                "Complete shared memory and Obsidian vault API across ChatGPT, Claude, Hermes (and its profiles), "
                f"and Antigravity. Every agent can read all scopes ({', '.join(READABLE_SCOPES)}). "
                f"Each agent can write to {', '.join(OPEN_SCOPES)}, and its own 'agents/<self>' scope."
            ),
        },
        "servers": [{"url": server_url}],
        "paths": {
            "/api/v1/briefing": {
                "get": {
                    "operationId": "memoryBriefing",
                    "summary": "Get the complete cross-agent memory briefing, active valid facts, invalidated/superseded history, and vault notes index.",
                    "parameters": [
                        {"name": "scope", "in": "query", "required": False, "schema": {"type": "string", "default": DEFAULT_SCOPE}},
                        {"name": "project", "in": "query", "required": False, "schema": {"type": "string"}},
                    ],
                    "responses": {"200": {"description": "Current memory briefing"}},
                }
            },
            "/api/v1/search": {
                "get": {
                    "operationId": "memorySearch",
                    "summary": "Search across AI-to-AI temporal facts (valid/invalid/all), inline observations, and Obsidian Markdown/PDF/DOCX documents.",
                    "parameters": [
                        {"name": "query", "in": "query", "required": False, "schema": {"type": "string"}},
                        {"name": "scope", "in": "query", "required": False, "schema": {"type": "string"}},
                        {"name": "category", "in": "query", "required": False, "schema": {"type": "string"}},
                        {"name": "validity", "in": "query", "required": False, "schema": {"type": "string", "enum": ["valid", "invalid", "all"], "default": "valid"}},
                        {"name": "include_history", "in": "query", "required": False, "schema": {"type": "boolean", "default": False}},
                    ],
                    "responses": {"200": {"description": "Matching facts, inline observations, and notes"}},
                }
            },
            "/api/v1/fact-check": {
                "get": {
                    "operationId": "memoryCheckFacts",
                    "summary": "Fact-check a claim or topic against active facts, retired/superseded history, and related vault notes before saving new memory.",
                    "parameters": [
                        {"name": "statement", "in": "query", "required": False, "schema": {"type": "string"}},
                        {"name": "scope", "in": "query", "required": False, "schema": {"type": "string"}},
                        {"name": "subject", "in": "query", "required": False, "schema": {"type": "string"}},
                        {"name": "limit", "in": "query", "required": False, "schema": {"type": "integer", "default": 8}},
                    ],
                    "responses": {"200": {"description": "Matching active facts, retired history, related notes, and guidance"}},
                }
            },
            "/api/v1/context": {
                "get": {
                    "operationId": "memoryBuildContext",
                    "summary": "Build multi-hop graph & temporal context around a note or topic (1-2 hops of [[wikilinks]], inline observations, and valid/invalid facts).",
                    "parameters": [
                        {"name": "target", "in": "query", "required": True, "schema": {"type": "string"}},
                        {"name": "depth", "in": "query", "required": False, "schema": {"type": "integer", "default": 1}},
                    ],
                    "responses": {"200": {"description": "Multi-hop graph and temporal context"}},
                }
            },
            "/api/v1/note": {
                "get": {
                    "operationId": "memoryReadNote",
                    "summary": "Read a full Markdown, PDF, or DOCX document from the Obsidian vault and its 1-hop [[wikilink]] graph context.",
                    "parameters": [
                        {"name": "path", "in": "query", "required": True, "schema": {"type": "string"}},
                    ],
                    "responses": {"200": {"description": "Document content and graph links"}},
                },
                "post": {
                    "operationId": "memoryWriteNote",
                    "summary": "Create, replace, append, or update a section of a Markdown document in the Obsidian vault.",
                    "requestBody": {
                        "required": True,
                        "content": {
                            "application/json": {
                                "schema": {
                                    "type": "object",
                                    "required": ["path", "content"],
                                    "properties": {
                                        "path": {"type": "string"},
                                        "content": {"type": "string"},
                                        "title": {"type": "string"},
                                        "scope": {"type": "string"},
                                        "summary": {"type": "string"},
                                        "tags": {"type": "array", "items": {"type": "string"}},
                                        "mode": {"type": "string", "enum": ["replace", "append", "section"], "default": "replace"},
                                        "section": {"type": "string"},
                                    },
                                }
                            }
                        },
                    },
                    "responses": {"200": {"description": "Saved note metadata"}},
                },
            },
            "/api/v1/upload": {
                "post": {
                    "operationId": "memoryUploadDocument",
                    "summary": "Upload and index a binary .pdf or .docx document (or .md/.txt file) into the Obsidian vault using Base64 content.",
                    "requestBody": {
                        "required": True,
                        "content": {
                            "application/json": {
                                "schema": {
                                    "type": "object",
                                    "required": ["filename", "base64_content"],
                                    "properties": {
                                        "filename": {"type": "string"},
                                        "base64_content": {"type": "string"},
                                        "scope": {"type": "string", "default": DEFAULT_SCOPE},
                                        "title": {"type": "string"},
                                        "summary": {"type": "string"},
                                        "tags": {"type": "array", "items": {"type": "string"}},
                                    },
                                }
                            }
                        },
                    },
                    "responses": {"200": {"description": "Uploaded document metadata"}},
                }
            },
            "/api/v1/remember": {
                "post": {
                    "operationId": "memoryRememberFact",
                    "summary": "Save or update an atomic AI-to-AI temporal fact (automatically marks older state on the same subject as superseded/invalid and flags potential_conflicts).",
                    "requestBody": {
                        "required": True,
                        "content": {
                            "application/json": {
                                "schema": {
                                    "type": "object",
                                    "required": ["fact"],
                                    "properties": {
                                        "fact": {"type": "string"},
                                        "scope": {"type": "string", "default": DEFAULT_SCOPE},
                                        "subject": {"type": "string"},
                                        "category": {"type": "string", "enum": list(VALID_CATEGORIES), "default": "fact"},
                                        "supersedes_id": {"type": "integer", "default": 0},
                                    },
                                }
                            }
                        },
                    },
                    "responses": {"200": {"description": "Saved fact"}},
                }
            },
        },
    }


# ── HTTP / MCP / SSE / OAuth 2.1 Server ───────────────────────────────────

SSE_SESSIONS: dict[str, tuple[str, "queue.Queue[str | None]"]] = {}
SSE_LOCK = threading.Lock()
MAX_SSE_SESSIONS = 32
MAX_JSON_BODY_BYTES = 512 * 1024
MAX_FORM_BODY_BYTES = 64 * 1024
MAX_OAUTH_CODES = 256
MAX_OAUTH_TOKENS = 512
MAX_WEB_AUTH_STATES = 256
MAX_DEVICE_CODES = 256
PKCE_CHALLENGE_RE = re.compile(r"^[A-Za-z0-9_-]{43,128}$")
PKCE_VERIFIER_RE = re.compile(r"^[A-Za-z0-9._~-]{32,128}$")
# Human pages that accept the owner's browser cookie; API/MCP routes never do.
BROWSER_ROUTES = ("/", "/oauth/authorize", "/logout", "/download", "/device", "/apps")
# Roles a device login can be granted (Hermes runs on the server with its own token).
DEVICE_ROLES = {"claude": "Claude (Claude Code)", "chatgpt": "ChatGPT (Codex)", "antigravity": "Antigravity"}
USER_CODE_ALPHABET = "BCDFGHJKLMNPQRSTVWXZ"  # no vowels or look-alikes, so codes never spell words
MAX_PENDING_DEVICE_CODES = 20
MAX_PENDING_DEVICE_CODES_PER_IP = 5
DEVICE_TOKEN_TTL = 86400 * 365
DASHBOARD_CSP = (
    "default-src 'none'; "
    "style-src 'unsafe-inline'; "
    "img-src 'self' data:; "
    "form-action 'self'; "
    "frame-ancestors 'none'; "
    "base-uri 'none'"
)
# OAuth 2.1 form submissions redirect (302) to the validated external redirect_uri
# (e.g. https://chatgpt.com, https://claude.ai, or http://127.0.0.1:<port>/callback).
# Chrome CSP3 checks form-action against 302 redirect targets, so form-action 'self'
# must not be set on /oauth/authorize.
OAUTH_CSP = (
    "default-src 'none'; "
    "style-src 'unsafe-inline'; "
    "img-src 'self' data:; "
    "frame-ancestors 'none'; "
    "base-uri 'none'"
)

AUTH_FAILURES: dict[str, list[float]] = {}
AUTH_FAILURES_LOCK = threading.Lock()
MAX_AUTH_FAILURES_PER_WINDOW = 10
AUTH_FAILURE_WINDOW_SECONDS = 300.0
MAX_TRACKED_AUTH_IPS = 4096


def _client_ip(headers: object, client_address: tuple[str, int] | None) -> str:
    getter = getattr(headers, "get", None)
    # Only a Cloudflare tunnel sets this header reliably; anyone else could forge it to dodge rate limits.
    if callable(getter) and os.environ.get("MEMORY_BEHIND_CLOUDFLARE") == "1":
        cf_ip = (getter("CF-Connecting-IP") or "").strip()
        if cf_ip:
            return cf_ip
    if client_address and client_address[0]:
        return str(client_address[0])
    return "unknown"


def _is_rate_limited(ip: str) -> bool:
    now_ts = time.time()
    with AUTH_FAILURES_LOCK:
        attempts = [t for t in AUTH_FAILURES.get(ip, []) if now_ts - t < AUTH_FAILURE_WINDOW_SECONDS]
        if attempts:
            AUTH_FAILURES[ip] = attempts
        else:
            AUTH_FAILURES.pop(ip, None)
        return len(attempts) >= MAX_AUTH_FAILURES_PER_WINDOW


def _record_auth_failure(ip: str) -> None:
    now_ts = time.time()
    with AUTH_FAILURES_LOCK:
        if len(AUTH_FAILURES) >= MAX_TRACKED_AUTH_IPS:
            for tracked_ip in list(AUTH_FAILURES.keys()):
                live = [t for t in AUTH_FAILURES.get(tracked_ip, []) if now_ts - t < AUTH_FAILURE_WINDOW_SECONDS]
                if live:
                    AUTH_FAILURES[tracked_ip] = live
                else:
                    AUTH_FAILURES.pop(tracked_ip, None)
            if len(AUTH_FAILURES) >= MAX_TRACKED_AUTH_IPS:
                oldest_ip = next(iter(AUTH_FAILURES))
                AUTH_FAILURES.pop(oldest_ip, None)
        attempts = [t for t in AUTH_FAILURES.get(ip, []) if now_ts - t < AUTH_FAILURE_WINDOW_SECONDS]
        attempts.append(now_ts)
        AUTH_FAILURES[ip] = attempts


def _clear_auth_failures(ip: str) -> None:
    with AUTH_FAILURES_LOCK:
        AUTH_FAILURES.pop(ip, None)


def _sanitize_next_path(raw_next: str | None, default: str = f"/?scope={DEFAULT_SCOPE}") -> str:
    candidate = (raw_next or "").strip()
    if (
        not candidate
        or not candidate.startswith("/")
        or candidate.startswith("//")
        or "\\" in candidate
        or any(ord(ch) < 32 or ord(ch) == 127 for ch in candidate)
    ):
        return default
    parsed = urllib.parse.urlsplit(candidate)
    if parsed.scheme or parsed.netloc:
        return default
    return candidate


def _sse_actor_matches(caller_actor: str, sess_actor: str) -> bool:
    if caller_actor == sess_actor:
        return True
    if sess_actor.startswith("hermes/") and caller_actor == "hermes":
        return True
    if sess_actor == "hermes" and caller_actor.startswith("hermes/"):
        return True
    return False


def exchange_omni_handoff(code: str) -> dict[str, object]:
    """Exchange a one-time Omni /hub/signin handoff code for the authenticated member record."""
    api_key = os.environ.get("OMNI_MEMORY_KEY", "").strip() or OMNI_MEMORY_KEY
    internal_url = (os.environ.get("OMNI_INTERNAL_URL", "") or OMNI_INTERNAL_URL).rstrip("/")
    if not api_key:
        raise MemoryError("Omni SSO is not configured on this server (missing OMNI_MEMORY_KEY).")
    payload = json.dumps({"code": code}).encode("utf-8")
    req = urllib.request.Request(
        f"{internal_url}/api/v1/hub/exchange",
        data=payload,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
            "Accept": "application/json",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=10.0) as resp:
            raw = resp.read().decode("utf-8", errors="replace")
            data = json.loads(raw) if raw else {}
    except urllib.error.HTTPError as exc:
        if exc.code == 401:
            raise MemoryError("Sign-in code expired or already used. Please sign in again.") from exc
        raise MemoryError(f"Omni SSO verification failed (HTTP {exc.code}).") from exc
    except Exception as exc:
        raise MemoryError("Could not reach Omni SSO service.") from exc
    if not isinstance(data, dict) or not data.get("email"):
        raise MemoryError("Invalid response from Omni SSO service.")
    return data


def _mint_web_session(conn: sqlite3.Connection, email: str) -> str:
    sess_tok = "vms_" + secrets.token_urlsafe(32)
    now_ts = time.time()
    with DB_LOCK:
        _prune_oauth_tables(conn)
        conn.execute(
            "INSERT INTO web_sessions(token_hash, email, created_at, expires_at) VALUES (?, ?, ?, ?)",
            (hashlib.sha256(sess_tok.encode()).hexdigest(), email, now_ts, now_ts + 86400 * 30),
        )
        conn.commit()
    return sess_tok


def _session_cookie_header(token_value: str, max_age: int = 2592000) -> str:
    safe_tok = urllib.parse.quote(token_value, safe="")
    if PUBLIC_URL.lower().startswith("https://"):
        return f"__Host-vyn_memory_token={safe_tok}; Path=/; Secure; HttpOnly; SameSite=Lax; Max-Age={max_age}"
    return f"vyn_memory_token={safe_tok}; Path=/; HttpOnly; SameSite=Lax; Max-Age={max_age}"


def _state_cookie_header(state_value: str, max_age: int = 900) -> str:
    safe_st = urllib.parse.quote(state_value, safe="")
    if PUBLIC_URL.lower().startswith("https://"):
        return f"__Host-vyn_memory_state={safe_st}; Path=/; Secure; HttpOnly; SameSite=Lax; Max-Age={max_age}"
    return f"vyn_memory_state={safe_st}; Path=/; HttpOnly; SameSite=Lax; Max-Age={max_age}"


def _omni_configured() -> bool:
    return bool((os.environ.get("OMNI_PUBLIC_URL", "") or OMNI_PUBLIC_URL).strip())


CARD_CSS = """body{background:#0f172a;color:#f8fafc;font-family:system-ui,-apple-system,sans-serif;display:flex;justify-content:center;padding:40px 16px;margin:0}
.card{background:#1e293b;padding:24px 20px;border-radius:12px;border:1px solid #334155;max-width:var(--w);width:100%;box-sizing:border-box}
h2{margin:0 0 12px;font-size:1.3rem}
p,td,li{color:#cbd5e1;font-size:14px;line-height:1.5}
.muted{color:#94a3b8;font-size:13px}
.err-box{color:#fecaca;background:#450a0a;padding:10px 12px;border-radius:6px;border:1px solid #991b1b;font-size:14px}
.code{font:600 1.6rem/1.2 ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:.12em;margin:4px 0 16px}
label{display:block;color:#cbd5e1;font-size:13px;font-weight:600;margin-top:8px}
input,select,button,.cta-btn{width:100%;padding:11px;margin:6px 0;border-radius:6px;font-size:16px;box-sizing:border-box}
input,select{border:1px solid #475569;background:#020617;color:#f8fafc}
button,.cta-btn{background:#38bdf8;color:#020617;border:none;font-weight:700;cursor:pointer;display:block;text-align:center;text-decoration:none}
button.secondary{background:#334155;color:#f8fafc;border:1px solid #475569;font-weight:600}
td button{width:auto;margin:0;padding:6px 12px;font-size:13px}
button:focus-visible,select:focus-visible,input:focus-visible,a:focus-visible,summary:focus-visible{outline:2px solid #38bdf8;outline-offset:2px}
a{color:#38bdf8;text-underline-offset:3px}
code{color:#e2e8f0;font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:0.9em}
pre{background:#020617;color:#f8fafc;border:1px solid #334155;border-radius:8px;padding:10px 12px;overflow-x:auto;font-size:13px;line-height:1.5}
details{margin:14px 0;border-top:1px solid #334155;padding-top:12px}
summary{color:#cbd5e1;font-size:13px;font-weight:600;cursor:pointer}
::selection{background:#38bdf8;color:#020617}
table{width:100%;border-collapse:collapse;font-variant-numeric:tabular-nums;margin:8px 0 16px}
th{text-align:left;color:#94a3b8;font-size:12px;font-weight:600;padding:8px 6px;border-bottom:1px solid #334155}
td{padding:10px 6px;border-bottom:1px solid #263449;vertical-align:top}
@media (max-width:640px){thead{display:none}tr{display:block;padding:10px 0;border-bottom:1px solid #334155}td{display:block;border:0;padding:2px 0}}"""


def render_card_page(title: str, body: str, width: int = 430) -> str:
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(title)} · Vyn Memory</title><style>{CARD_CSS}</style>
</head><body><main class="card" style="--w:{width}px"><h2>{html.escape(title)}</h2>{body}</main></body></html>"""


def _device_label(info: dict[str, object]) -> str:
    """'Codex · user@laptop · Linux 6.8' from what `memory.py login` reports (untrusted, so cleaned and capped)."""
    def part(key: str) -> str:
        return re.sub(r"[^\w .@()+/-]", "", str(info.get(key) or ""))[:60].strip()
    host, user = part("host") or "unknown device", part("user")
    return " · ".join(x for x in (part("app") or "Unknown app", f"{user}@{host}" if user else host, part("os")) if x)


def _device_role_hint(label: str) -> str:
    app = label.split(" · ")[0].lower()
    if "codex" in app or "chatgpt" in app:
        return "chatgpt"
    return "antigravity" if "antigravity" in app or "gemini" in app else "claude"


def render_device_lookup_page(error_msg: str = "") -> str:
    err_html = f'<p class="err-box">{html.escape(error_msg)}</p>' if error_msg else ""
    body = f"""<p>Enter the 8-letter code shown in your terminal after running <code>memory.py login</code>.</p>
{err_html}
<form method="get" action="/device">
<label for="device-code">Device code</label>
<input id="device-code" type="text" name="code" placeholder="BCDF-GHJK" autocomplete="off" required>
<button type="submit">Continue</button>
</form>
<p class="muted"><a href="/apps">Connected apps</a> · <a href="/">Back to the vault</a></p>"""
    return render_card_page("Approve device login", body)


def render_device_page(row: sqlite3.Row, *, session_token: str = "") -> str:
    options = "".join(
        f'<option value="{r}"{" selected" if r == row["role_hint"] else ""}>{label}</option>'
        for r, label in DEVICE_ROLES.items()
    )
    code = html.escape(str(row["user_code"]), quote=True)
    csrf = html.escape(_mint_upload_csrf(purpose="device", session_token=session_token), quote=True)
    body = f"""<p>A device is asking for its own memory token.</p>
<p><strong>{html.escape(str(row["label"]))}</strong><br><span class="muted">from {html.escape(str(row["ip"]))}</span></p>
<p class="muted">Approve only if you just ran <code>memory.py login</code> and your terminal shows this code:</p>
<div class="code">{code}</div>
<form method="post" action="/device">
<input type="hidden" name="code" value="{code}">
<input type="hidden" name="csrf_token" value="{csrf}">
<label for="role">Act as</label>
<select id="role" name="role">{options}</select>
<button name="decision" value="approve">Approve</button>
<button class="secondary" name="decision" value="deny">Deny</button>
</form>"""
    return render_card_page("Approve device login", body)


def render_apps_page(conn: sqlite3.Connection, *, session_token: str = "") -> str:
    def when(ts: float) -> str:
        return datetime.fromtimestamp(ts, LOCAL_TZ).strftime("%d %b %Y, %H:%M") if ts else "–"

    csrf = html.escape(_mint_upload_csrf(purpose="apps", session_token=session_token), quote=True)

    def row_html(name: str, kind: str, acts_as: str, added: float, used: float, rev_kind: str, rowid: int) -> str:
        return (
            f'<tr><td><strong>{html.escape(name)}</strong><br><span class="muted">{kind}</span></td>'
            f"<td>{html.escape(acts_as)}</td><td>{when(added)}</td><td>{when(used)}</td>"
            f'<td><form method="post" action="/apps"><input type="hidden" name="csrf_token" value="{csrf}">'
            f'<input type="hidden" name="kind" value="{rev_kind}"><input type="hidden" name="id" value="{rowid}">'
            f'<button class="secondary" aria-label="Revoke {html.escape(name, quote=True)}">Revoke</button></form></td></tr>'
        )

    with DB_LOCK:
        _prune_oauth_tables(conn)
        conn.commit()
        tokens = conn.execute("SELECT rowid, * FROM oauth_tokens ORDER BY MAX(last_used, created_at) DESC").fetchall()
        sessions = conn.execute("SELECT rowid, * FROM web_sessions ORDER BY created_at DESC").fetchall()
    rows = [
        row_html(
            str(t["label"] or t["client_id"]),
            "Device login" if t["client_id"] == "device" else "Connector (OAuth)",
            str(t["actor"]), t["created_at"], t["last_used"], "token", t["rowid"],
        )
        for t in tokens
        if oauth_parent_valid(str(t["parent"]), str(t["actor"]))
    ] + [
        row_html(
            "Owner token sign-in" if str(w["email"]).startswith("owner@token:") else str(w["email"]),
            "Browser session", "owner", w["created_at"], 0, "session", w["rowid"],
        )
        for w in sessions
        if owner_email_ok(str(w["email"]))
    ]
    roles = ", ".join(sorted(r for r in configured_tokens() if r != "owner")) or "none"
    mcp_url = html.escape(f"{PUBLIC_URL}/mcp")
    pub_url = html.escape(PUBLIC_URL)
    body = (
        '<p class="muted">Everything that can reach your memory now. Revoke ends access at once; '
        "a device can log in again with <code>memory.py login</code>.</p>"
        "<table><thead><tr><th>App</th><th>Acts as</th><th>Added</th><th>Last used</th><th></th></tr></thead>"
        f'<tbody>{"".join(rows) or "<tr><td colspan=5>Nothing connected yet.</td></tr>"}</tbody></table>'
        "<details>"
        "<summary>Connect a new app, MCP client, or laptop</summary>"
        f"<p><strong>Claude / ChatGPT (MCP Connector):</strong> add <code>{mcp_url}</code> as a remote MCP server and sign in when prompted.</p>"
        f"<p><strong>Laptop CLI (Claude Code, Codex, Antigravity):</strong> run this once, then approve the code at <a href='/device'>/device</a>:</p>"
        f"<pre>python3 memory.py login {pub_url}</pre>"
        "</details>"
        f'<p class="muted">The server also has role tokens for: {html.escape(roles)}. '
        "To revoke one, change it in the server's env file and restart.</p>"
        '<p><a href="/">Back to the vault</a> · <a href="/device">Approve a device code</a></p>'
    )
    return render_card_page("Connected apps", body, width=880)


def render_login_page(next_path: str = f"/?scope={DEFAULT_SCOPE}", error_msg: str = "") -> str:
    safe_next = _sanitize_next_path(next_path)
    err_html = f'<p class="err-box">{html.escape(error_msg)}</p>' if error_msg else ""
    token_form = (
        '<form method="post" action="/login">'
        f'<input type="hidden" name="next" value="{html.escape(safe_next, quote=True)}">'
        '<label for="owner-token">Owner token (<code>MEMORY_OWNER_TOKEN</code>)</label>'
        '<input id="owner-token" type="password" name="token" placeholder="Paste MEMORY_OWNER_TOKEN" autocomplete="current-password" required>'
        '<button type="submit">Sign In with Token</button>'
        "</form>"
    )
    if _omni_configured():
        omni_start_href = f"/auth/start?next={urllib.parse.quote(safe_next, safe='')}"
        body = (
            "<p>Sign in with your <strong>Omni</strong> owner account (email OTP / active Omni session):</p>"
            f"{err_html}"
            f'<a class="cta-btn" href="{html.escape(omni_start_href, quote=True)}">🔐 Sign in with Omni (Owner Email)</a>'
            "<details>"
            "<summary>Fallback: sign in with MEMORY_OWNER_TOKEN</summary>"
            f"{token_form}"
            "</details>"
        )
    else:
        body = (
            "<p>Enter your <code>MEMORY_OWNER_TOKEN</code> from your server env file to open the vault.</p>"
            f"{err_html}"
            f"{token_form}"
        )
    return render_card_page("Sign In to Vyn Memory", body)


def validate_oauth_redirect_uri(uri: str) -> str:
    """Validate OAuth 2.1 redirect_uri: require HTTPS or loopback HTTP, no fragments/credentials/CRLF."""
    cleaned = (uri or "").strip()
    if not cleaned or len(cleaned) > 1024 or any(ch in cleaned for ch in ("\r", "\n", "\x00")):
        raise MemoryError("Invalid or missing redirect_uri")
    parsed = urllib.parse.urlsplit(cleaned)
    if parsed.fragment or parsed.username or parsed.password or not parsed.hostname:
        raise MemoryError("redirect_uri must not contain fragments or credentials")
    scheme = parsed.scheme.lower()
    host = parsed.hostname.lower()
    if scheme == "https" and host in OAUTH_REDIRECT_HOSTS:
        return cleaned
    if scheme == "http" and host in ("127.0.0.1", "localhost", "::1"):
        return cleaned
    raise MemoryError(
        "redirect_uri must be an https callback on an allowed connector host (MEMORY_OAUTH_REDIRECT_HOSTS) "
        "or a local loopback http://127.0.0.1 / http://localhost address"
    )


def _default_oauth_role(redirect_uri: str, query: dict[str, list[str]]) -> str:
    explicit = (query.get("role") or [""])[0].strip().lower()
    if explicit in ("chatgpt", "claude", "antigravity", "hermes"):
        return explicit
    low_uri = (redirect_uri or "").lower()
    if "chatgpt.com" in low_uri or "openai.com" in low_uri:
        return "chatgpt"
    return "claude"


def _prune_oauth_tables(conn: sqlite3.Connection) -> None:
    now_ts = time.time()
    conn.execute("DELETE FROM oauth_codes WHERE expires_at < ?", (now_ts,))
    conn.execute("DELETE FROM oauth_tokens WHERE expires_at < ?", (now_ts,))
    conn.execute("DELETE FROM web_auth_states WHERE expires_at < ?", (now_ts,))
    conn.execute("DELETE FROM web_sessions WHERE expires_at < ?", (now_ts,))
    conn.execute("DELETE FROM device_codes WHERE expires_at < ?", (now_ts,))
    code_count = int(conn.execute("SELECT COUNT(*) FROM oauth_codes").fetchone()[0])
    if code_count >= MAX_OAUTH_CODES:
        conn.execute(
            """
            DELETE FROM oauth_codes WHERE code_hash IN (
                SELECT code_hash FROM oauth_codes ORDER BY expires_at ASC LIMIT ?
            )
            """,
            (code_count - MAX_OAUTH_CODES + 1,),
        )
    tok_count = int(conn.execute("SELECT COUNT(*) FROM oauth_tokens").fetchone()[0])
    if tok_count >= MAX_OAUTH_TOKENS:
        conn.execute(
            """
            DELETE FROM oauth_tokens WHERE token_hash IN (
                SELECT token_hash FROM oauth_tokens ORDER BY created_at ASC LIMIT ?
            )
            """,
            (tok_count - MAX_OAUTH_TOKENS + 1,),
        )
    state_count = int(conn.execute("SELECT COUNT(*) FROM web_auth_states").fetchone()[0])
    if state_count >= MAX_WEB_AUTH_STATES:
        conn.execute(
            """
            DELETE FROM web_auth_states WHERE state_hash IN (
                SELECT state_hash FROM web_auth_states ORDER BY expires_at ASC LIMIT ?
            )
            """,
            (state_count - MAX_WEB_AUTH_STATES + 1,),
        )
    dev_count = int(conn.execute("SELECT COUNT(*) FROM device_codes").fetchone()[0])
    if dev_count >= MAX_DEVICE_CODES:
        conn.execute(
            """
            DELETE FROM device_codes WHERE device_hash IN (
                SELECT device_hash FROM device_codes ORDER BY expires_at ASC LIMIT ?
            )
            """,
            (dev_count - MAX_DEVICE_CODES + 1,),
        )


def _parse_multipart_upload(raw_body: bytes, content_type: str) -> tuple[dict[str, str], str, bytes]:
    """Parse multipart/form-data body using pure stdlib bytes splitting (Python 3.12+ / 3.14 safe)."""
    m_bound = re.search(r'boundary=(?:"([^"]+)"|([^;\s]+))', content_type or "", flags=re.IGNORECASE)
    if not m_bound:
        raise MemoryError("Missing multipart/form-data boundary")
    boundary_str = m_bound.group(1) or m_bound.group(2)
    boundary = ("--" + boundary_str).encode("utf-8")
    fields: dict[str, str] = {}
    filename = ""
    file_bytes = b""

    for part in raw_body.split(boundary)[1:]:
        if part.startswith(b"--"):
            break
        if part.startswith(b"\r\n"):
            part = part[2:]
        elif part.startswith(b"\n"):
            part = part[1:]
        if b"\r\n\r\n" in part:
            hdr_bytes, body = part.split(b"\r\n\r\n", 1)
            if body.endswith(b"\r\n"):
                body = body[:-2]
        elif b"\n\n" in part:
            hdr_bytes, body = part.split(b"\n\n", 1)
            if body.endswith(b"\n"):
                body = body[:-1]
        else:
            continue
        hdr_text = hdr_bytes.decode("utf-8", errors="replace")
        m_name = re.search(r'\bname="([^"]+)"', hdr_text)
        if not m_name:
            continue
        field_name = m_name.group(1)
        m_file = re.search(r'\bfilename="([^"]*)"', hdr_text)
        if m_file is not None:
            filename = Path(m_file.group(1)).name
            file_bytes = body
        else:
            fields[field_name] = body.decode("utf-8", errors="replace").strip()

    if not filename or not file_bytes:
        raise MemoryError("No file provided in multipart upload")
    return fields, filename, file_bytes


class MemoryHTTPHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    timeout = 30.0

    def log_message(self, fmt: str, *args: object) -> None:
        return

    def end_headers(self) -> None:
        # A POST answered before its body was read (401, 429, ...) must not keep the connection:
        # the unread body would be parsed as the next request line (claude.ai got a 501 from that).
        if self.command == "POST" and not getattr(self, "_body_read", False):
            self.close_connection = True
            self.send_header("Connection", "close")
        super().end_headers()

    def client_ip(self) -> str:
        return _client_ip(self.headers, getattr(self, "client_address", None))

    def send_json(
        self,
        status: int,
        payload: object,
        extra_headers: dict[str, str] | None = None,
        *,
        cors: bool = True,
    ) -> None:
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        if cors:
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header(
                "Access-Control-Allow-Headers",
                "Authorization, Content-Type, X-API-Key, X-Hermes-Subagent, Mcp-Session-Id, MCP-Protocol-Version",
            )
            self.send_header("Access-Control-Allow-Methods", "GET, POST, DELETE, OPTIONS")
        if extra_headers:
            for k, v in extra_headers.items():
                self.send_header(k, v)
        self.end_headers()
        if getattr(self, "command", "GET") != "HEAD":
            self.wfile.write(body)

    def send_html(
        self,
        status: int,
        html_text: str,
        extra_headers: dict[str, str] | None = None,
        *,
        csp: str = DASHBOARD_CSP,
    ) -> None:
        body = html_text.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "same-origin")
        self.send_header("Content-Security-Policy", csp)
        if extra_headers:
            for k, v in extra_headers.items():
                self.send_header(k, v)
        self.end_headers()
        if getattr(self, "command", "GET") != "HEAD":
            self.wfile.write(body)

    def _extract_cookie_tokens(self) -> list[str]:
        raw_headers = self.headers.get_all("Cookie") if hasattr(self.headers, "get_all") else None
        if not raw_headers:
            single = self.headers.get("Cookie", "")
            raw_headers = [single] if single else []
        if not raw_headers:
            return []

        host_tokens: list[str] = []
        plain_tokens: list[str] = []
        for raw_cookie in raw_headers:
            for part in raw_cookie.split(";"):
                if "=" not in part:
                    continue
                k, v = part.split("=", 1)
                k = k.strip()
                v = urllib.parse.unquote(v.strip().strip('"'))
                if not v:
                    continue
                if k == "__Host-vyn_memory_token" and v not in host_tokens:
                    host_tokens.append(v)
                elif k == "vyn_memory_token" and v not in plain_tokens:
                    plain_tokens.append(v)
            try:
                c = SimpleCookie()
                c.load(raw_cookie)
                if "__Host-vyn_memory_token" in c:
                    val = urllib.parse.unquote(c["__Host-vyn_memory_token"].value.strip())
                    if val and val not in host_tokens:
                        host_tokens.append(val)
                if "vyn_memory_token" in c:
                    val = urllib.parse.unquote(c["vyn_memory_token"].value.strip())
                    if val and val not in plain_tokens:
                        plain_tokens.append(val)
            except Exception:
                pass
        return host_tokens + [t for t in plain_tokens if t not in host_tokens]

    def _extract_state_cookie(self) -> str:
        raw_headers = self.headers.get_all("Cookie") if hasattr(self.headers, "get_all") else None
        if not raw_headers:
            single = self.headers.get("Cookie", "")
            raw_headers = [single] if single else []
        for raw_cookie in raw_headers:
            for target_key in ("__Host-vyn_memory_state", "vyn_memory_state"):
                for part in raw_cookie.split(";"):
                    if "=" not in part:
                        continue
                    k, v = part.split("=", 1)
                    if k.strip() == target_key:
                        val = urllib.parse.unquote(v.strip().strip('"'))
                        if val:
                            return val
            try:
                c = SimpleCookie()
                c.load(raw_cookie)
                if "__Host-vyn_memory_state" in c:
                    return urllib.parse.unquote(c["__Host-vyn_memory_state"].value)
                if "vyn_memory_state" in c:
                    return urllib.parse.unquote(c["vyn_memory_state"].value)
            except Exception:
                pass
        return ""

    def _is_same_origin_browser_post(self) -> bool:
        sec_site = (self.headers.get("Sec-Fetch-Site") or "").strip().lower()
        if sec_site and sec_site not in ("same-origin", "none"):
            return False
        origin_hdr = (self.headers.get("Origin") or "").strip().rstrip("/").lower()
        if origin_hdr == "null":
            return sec_site == "same-origin"
        if not origin_hdr:
            return sec_site in ("", "same-origin", "none")
        pub_origin = PUBLIC_URL.rstrip("/").lower()
        if origin_hdr == pub_origin:
            return True
        host_hdr = (self.headers.get("Host") or "").split(",")[0].strip().lower()
        if host_hdr and origin_hdr in (f"https://{host_hdr}", f"http://{host_hdr}"):
            return True
        return False

    def parse_route_and_auth(self, *, allow_cookie: bool = False) -> tuple[str, dict[str, list[str]], str | None]:
        """Return (route, query, actor). Tokens come only from the Authorization / X-API-Key headers, never the URL
        (URLs end up in logs and browser history). Browser cookies count only when allow_cookie=True on the human
        pages in BROWSER_ROUTES, never on API/MCP routes."""
        parsed = urllib.parse.urlsplit(self.path)
        query = urllib.parse.parse_qs(parsed.query)
        raw_path = parsed.path or "/"
        if raw_path.startswith("/s/"):
            exc = MemoryError(f"Token URLs (/s/<token>/...) were removed. Connect to {PUBLIC_URL}/mcp and sign in, "
                              "or send the token in an Authorization: Bearer header.")
            exc.status = 410
            raise exc

        auth_hdr = self.headers.get("Authorization", "").strip()
        bearer = auth_hdr[7:].strip() if auth_hdr.lower().startswith("bearer ") else ""
        api_key = self.headers.get("X-API-Key", "").strip()
        subagent = (
            self.headers.get("X-Hermes-Subagent", "").strip()
            or (query.get("subagent") or [""])[0].strip()
        )
        cookie_tokens = self._extract_cookie_tokens() if allow_cookie and raw_path in BROWSER_ROUTES else []

        provided_any = False
        for candidate in (bearer, api_key, *cookie_tokens):
            if not candidate:
                continue
            provided_any = True
            actor = resolve_actor_from_token(candidate, self.server.db, subagent=subagent)  # type: ignore[attr-defined]
            if actor:
                return raw_path, query, actor
        if provided_any:
            _record_auth_failure(self.client_ip())
        return raw_path, query, None

    def _owner_cookie_pair(self) -> tuple[str, str] | None:
        """Return (cookie_token, email) for the active owner browser session, if any."""
        for tok in self._extract_cookie_tokens():
            email = web_session_email(self.server.db, tok)  # type: ignore[attr-defined]
            if email is None and resolve_actor_from_token(tok) == "owner":
                email = owner_session_email()
            if email:
                return tok, email
        return None

    def owner_cookie_token(self) -> str:
        pair = self._owner_cookie_pair()
        return pair[0] if pair else ""

    def owner_cookie_email(self) -> str | None:
        """Email of the owner browser session in this request's cookies, if any."""
        pair = self._owner_cookie_pair()
        return pair[1] if pair else None

    def read_owner_form(self, *, purpose: str = "upload") -> tuple[dict[str, list[str]], str] | None:
        """Form fields and approving email of a same-origin, session-bound CSRF-checked owner POST; otherwise sends 403."""
        try:
            form = urllib.parse.parse_qs(self.read_bounded_body(MAX_FORM_BODY_BYTES).decode("utf-8", errors="replace"))
        except MemoryError as exc:
            self.send_json(exc.status, {"error": str(exc)}, cors=False)
            return None
        pair = self._owner_cookie_pair()
        tok, email = pair if pair else ("", None)
        if (
            self._is_same_origin_browser_post()
            and email
            and _verify_upload_csrf((form.get("csrf_token") or [""])[0], purpose=purpose, session_token=tok)
        ):
            return form, email
        _record_auth_failure(self.client_ip())
        self.send_html(403, render_card_page("Not allowed", "<p>Sign in again and retry from the page.</p>"))
        return None

    def require_auth(self, actor: str | None) -> bool:
        if actor:
            return True
        resource_meta = f"{PUBLIC_URL}/.well-known/oauth-protected-resource"
        self.send_json(
            401,
            {"error": "Unauthorized; send a Bearer token or complete OAuth."},
            extra_headers={
                "WWW-Authenticate": f'Bearer resource_metadata="{resource_meta}"',
            },
        )
        return False

    def read_bounded_body(self, max_bytes: int) -> bytes:
        if self.headers.get("Transfer-Encoding"):
            self.close_connection = True
            raise MemoryLengthRequiredError(
                "Transfer-Encoding is not supported; provide a valid Content-Length header"
            )
        raw_len = (self.headers.get("Content-Length") or "0").strip()
        try:
            length = int(raw_len)
        except ValueError as exc:
            self.close_connection = True
            raise MemoryError("Invalid Content-Length header") from exc
        if length < 0:
            self.close_connection = True
            raise MemoryError("Invalid Content-Length header")
        if length == 0:
            self._body_read = True
            return b""
        if length > max_bytes:
            self.close_connection = True
            raise MemoryPayloadTooLargeError(f"Request body exceeds maximum size of {max_bytes} bytes")
        self._body_read = True
        return self.rfile.read(length)

    def read_json_body(self, max_bytes: int = MAX_JSON_BODY_BYTES) -> dict[str, object] | list[object]:
        raw = self.read_bounded_body(max_bytes)
        if not raw:
            return {}
        try:
            return json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise MemoryError("Invalid JSON request body") from exc

    def do_OPTIONS(self) -> None:
        self.send_json(200, {"ok": True})

    def do_DELETE(self) -> None:
        self.send_json(200, {"ok": True})

    def do_HEAD(self) -> None:
        self.do_GET()

    def do_GET(self) -> None:
        conn: sqlite3.Connection = self.server.db  # type: ignore[attr-defined]
        ip = self.client_ip()
        if _is_rate_limited(ip):
            self.send_json(429, {"error": "Too many failed authentication attempts; try again in 5 minutes."})
            return
        try:
            route, query, actor = self.parse_route_and_auth(allow_cookie=True)
        except MemoryError as exc:
            self.send_json(exc.status, {"error": str(exc)})
            return

        if route == "/health":
            self.send_json(200, {"status": "ok", "service": "vyn-memory"})
            return

        if route == "/login":
            next_p = (query.get("next") or [f"/?scope={DEFAULT_SCOPE}"])[0]
            self.send_html(200, render_login_page(next_path=next_p))
            return

        if route == "/auth/start":
            omni_pub = (os.environ.get("OMNI_PUBLIC_URL", "") or OMNI_PUBLIC_URL).rstrip("/")
            if not omni_pub:
                self.send_html(404, render_login_page(error_msg="Omni sign-in is not configured; use the owner token."))
                return
            next_p = (query.get("next") or [f"/?scope={DEFAULT_SCOPE}"])[0].strip()
            safe_next = _sanitize_next_path(next_p)
            state = "memory_" + secrets.token_urlsafe(24)
            now_ts = time.time()
            with DB_LOCK:
                _prune_oauth_tables(conn)
                conn.execute(
                    "INSERT INTO web_auth_states(state_hash, next_path, expires_at) VALUES (?, ?, ?)",
                    (hashlib.sha256(state.encode()).hexdigest(), safe_next, now_ts + 900),
                )
                conn.commit()
            target = f"{omni_pub}/hub/signin?{urllib.parse.urlencode({'state': state})}"
            self.send_response(303)
            self.send_header("Location", target)
            self.send_header("Set-Cookie", _state_cookie_header(state, max_age=900))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            return

        if route == "/auth/callback":
            code = (query.get("code") or [""])[0].strip()
            state = (query.get("state") or [""])[0].strip()
            cookie_state = self._extract_state_cookie()
            if not code or not state.startswith("memory_") or not cookie_state or not hmac.compare_digest(state, cookie_state):
                _record_auth_failure(ip)
                self.send_html(
                    400,
                    render_login_page(error_msg="Invalid or expired sign-in state. Please start sign-in again."),
                )
                return
            state_hash = hashlib.sha256(state.encode()).hexdigest()
            with DB_LOCK:
                _prune_oauth_tables(conn)
                st_row = conn.execute(
                    "SELECT next_path, expires_at FROM web_auth_states WHERE state_hash = ?",
                    (state_hash,),
                ).fetchone()
                conn.execute("DELETE FROM web_auth_states WHERE state_hash = ?", (state_hash,))
                conn.commit()
            if not st_row or st_row["expires_at"] < time.time():
                _record_auth_failure(ip)
                self.send_html(
                    400,
                    render_login_page(error_msg="Sign-in session expired. Please try again."),
                )
                return
            next_path = _sanitize_next_path(str(st_row["next_path"] or f"/?scope={DEFAULT_SCOPE}"))
            try:
                person = exchange_omni_handoff(code)
            except MemoryError as exc:
                _record_auth_failure(ip)
                self.send_html(401, render_login_page(next_path=next_path, error_msg=str(exc)))
                return
            email = str(person.get("email") or "").strip().lower()
            is_admin = bool(person.get("is_admin"))
            admins = allowed_admin_emails()
            if not email or not is_admin or email not in admins:
                _record_auth_failure(ip)
                self.send_html(
                    403,
                    render_login_page(
                        next_path=next_path,
                        error_msg="Access denied: only the owner account is authorized for Vyn Memory.",
                    ),
                )
                return
            _clear_auth_failures(ip)
            sess_tok = _mint_web_session(conn, email)
            self.send_response(303)
            self.send_header("Location", next_path)
            self.send_header("Set-Cookie", _session_cookie_header(sess_tok, max_age=2592000))
            self.send_header("Set-Cookie", _state_cookie_header("", max_age=0))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            return

        if route == "/logout":
            sec_site = (self.headers.get("Sec-Fetch-Site") or "").strip().lower()
            purpose = (self.headers.get("Purpose") or self.headers.get("Sec-Purpose") or "").strip().lower()
            if (sec_site and sec_site not in ("same-origin", "none")) or "prefetch" in purpose or "prerender" in purpose:
                self.send_html(
                    400,
                    render_login_page(error_msg="Cross-site or prerendered sign-out request ignored."),
                )
                return
            cookie_tokens = [t for t in self._extract_cookie_tokens() if t.startswith("vms_")]
            if cookie_tokens:
                with DB_LOCK:
                    for existing_tok in cookie_tokens:
                        conn.execute(
                            "DELETE FROM web_sessions WHERE token_hash = ?",
                            (hashlib.sha256(existing_tok.encode()).hexdigest(),),
                        )
                    conn.commit()
            clear_cookie = _session_cookie_header("", max_age=0)
            self.send_html(
                200,
                render_login_page(error_msg="Signed out. Your browser session has been revoked and cleared."),
                extra_headers={"Set-Cookie": clear_cookie},
            )
            return

        if route == "/.well-known/oauth-protected-resource":
            self.send_json(
                200,
                {
                    "resource": f"{PUBLIC_URL}/mcp",
                    "authorization_servers": [PUBLIC_URL],
                    "bearer_methods_supported": ["header"],
                },
            )
            return

        if route in ("/.well-known/oauth-authorization-server", "/.well-known/openid-configuration"):
            base_u = PUBLIC_URL
            self.send_json(
                200,
                {
                    "issuer": base_u,
                    "authorization_endpoint": f"{base_u}/oauth/authorize",
                    "token_endpoint": f"{base_u}/oauth/token",
                    "registration_endpoint": f"{base_u}/oauth/register",
                    "response_types_supported": ["code"],
                    "grant_types_supported": ["authorization_code", "refresh_token"],
                    "token_endpoint_auth_methods_supported": ["none", "client_secret_post", "client_secret_basic"],
                    "code_challenge_methods_supported": ["S256"],
                },
            )
            return

        if route == "/oauth/authorize":
            client_id = (query.get("client_id") or ["mcp-client"])[0].strip()
            raw_redirect_uri = (query.get("redirect_uri") or [""])[0].strip()
            state = (query.get("state") or [""])[0].strip()
            code_challenge = (query.get("code_challenge") or [""])[0].strip()
            code_challenge_method = (query.get("code_challenge_method") or ["S256"])[0].strip()
            resource = (query.get("resource") or [""])[0].strip()
            try:
                redirect_uri = validate_oauth_redirect_uri(raw_redirect_uri)
                if code_challenge_method != "S256" or not PKCE_CHALLENGE_RE.match(code_challenge):
                    raise MemoryError("OAuth 2.1 PKCE S256 code_challenge is required")
            except MemoryError as exc:
                self.send_json(exc.status, {"error": "invalid_request", "error_description": str(exc)})
                return
            default_role = _default_oauth_role(redirect_uri, query)
            if actor == "owner":
                oauth_csrf = _mint_upload_csrf(purpose="oauth", session_token=self.owner_cookie_token())
                role_options = "".join(
                    f'<option value="{r}" {"selected" if r == default_role else ""}>{label}</option>'
                    for r, label in (
                        ("claude", "Claude (claude.ai / Claude Desktop / iOS)"),
                        ("chatgpt", "ChatGPT (chatgpt.com / Developer Mode MCP)"),
                        ("antigravity", "Antigravity IDE"),
                        ("hermes", "Hermes Agent"),
                    )
                )
                session_label = "Omni Owner Session" if _omni_configured() else "Owner Session"
                auth_body_html = (
                    f'<p>✅ Signed in via <strong>{session_label}</strong>. Select the AI agent scope to grant this connector:</p>'
                    '<input type="hidden" name="omni_session" value="1">'
                    f'<input type="hidden" name="csrf_token" value="{html.escape(oauth_csrf, quote=True)}">'
                    '<label for="oauth-role">Agent role</label>'
                    f'<select id="oauth-role" name="role">{role_options}</select>'
                    '<button type="submit">Approve Access</button>'
                )
            else:
                parsed_cur = urllib.parse.urlsplit(self.path)
                cur_oauth_target = "/oauth/authorize" + (f"?{parsed_cur.query}" if parsed_cur.query else "")
                if _omni_configured():
                    signin_href = f"/auth/start?next={urllib.parse.quote(cur_oauth_target, safe='')}"
                    signin_label = "🔐 Sign in with Omni to Approve Access"
                    signin_intro = "Sign in with your <strong>Omni</strong> owner account to approve this MCP connector:"
                else:
                    signin_href = f"/login?next={urllib.parse.quote(cur_oauth_target, safe='')}"
                    signin_label = "Sign in as Owner to Approve Access"
                    signin_intro = "Sign in as the vault owner to approve this MCP connector, or paste an agent token below:"
                auth_body_html = (
                    f"<p>{signin_intro}</p>"
                    f'<a class="cta-btn" href="{html.escape(signin_href, quote=True)}">{signin_label}</a>'
                    "<details>"
                    "<summary>Or paste an agent token directly</summary>"
                    '<label for="oauth-agent-token">Agent token</label>'
                    '<input id="oauth-agent-token" type="password" name="token" placeholder="Paste MEMORY_CHATGPT_TOKEN or MEMORY_CLAUDE_TOKEN">'
                    '<button class="secondary" type="submit">Approve with Token</button>'
                    "</details>"
                )
            oauth_body = (
                f'<p>Access will be sent to <strong>{html.escape(urllib.parse.urlsplit(redirect_uri).hostname or "", quote=True)}</strong> '
                f'(client <code>{html.escape(client_id, quote=True)}</code>). Approve only if you started this connection there.</p>'
                '<form method="post" action="/oauth/authorize">'
                f'<input type="hidden" name="client_id" value="{html.escape(client_id, quote=True)}">'
                f'<input type="hidden" name="redirect_uri" value="{html.escape(redirect_uri, quote=True)}">'
                f'<input type="hidden" name="state" value="{html.escape(state, quote=True)}">'
                f'<input type="hidden" name="code_challenge" value="{html.escape(code_challenge, quote=True)}">'
                '<input type="hidden" name="code_challenge_method" value="S256">'
                f'<input type="hidden" name="resource" value="{html.escape(resource, quote=True)}">'
                f"{auth_body_html}"
                "</form>"
            )
            self.send_html(200, render_card_page("Authorize Vyn Memory", oauth_body), csp=OAUTH_CSP)
            return

        if route in ("/device", "/apps"):
            if actor != "owner":
                self.send_html(401, render_login_page(next_path=self.path))
                return
            sess_tok = self.owner_cookie_token()
            if route == "/apps":
                self.send_html(200, render_apps_page(conn, session_token=sess_tok))
                return
            req_code = (query.get("code") or [""])[0].strip().upper()
            if not req_code:
                self.send_html(200, render_device_lookup_page())
                return
            with DB_LOCK:
                row = conn.execute(
                    "SELECT * FROM device_codes WHERE user_code = ? AND actor = '' AND expires_at > ?",
                    (req_code, time.time()),
                ).fetchone()
            if row:
                self.send_html(200, render_device_page(row, session_token=sess_tok))
            else:
                self.send_html(
                    404,
                    render_device_lookup_page(
                        error_msg="Login code not found, expired, or already answered. Check your terminal or run memory.py login again."
                    ),
                )
            return

        if route == "/openapi.json":  # public: only the API shape, so ChatGPT Actions can import it
            self.send_json(200, build_openapi_schema(PUBLIC_URL))
            return

        if route == "/" and actor is None and "text/html" in self.headers.get("Accept", ""):
            parsed_req = urllib.parse.urlsplit(self.path)
            next_target = "/" + (f"?{parsed_req.query}" if parsed_req.query else f"?scope={DEFAULT_SCOPE}")
            self.send_html(401, render_login_page(next_path=next_target))
            return

        if not self.require_auth(actor):
            return
        assert actor is not None

        if route == "/download":
            if actor != "owner":
                self.send_json(403, {"error": "Only the owner session can download original binary vault files."}, cors=False)
                return
            rel = (query.get("path") or [""])[0].strip().lstrip("/")
            if not rel or rel.split("/")[0].lower() == "personal":
                self.send_json(403, {"error": "Invalid or forbidden vault path"}, cors=False)
                return
            try:
                full = assert_safe_vault_path(VAULT_DIR / rel)
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)}, cors=False)
                return
            if not full.is_file() or not full.name.lower().endswith(SUPPORTED_VAULT_EXTENSIONS):
                self.send_json(404, {"error": "Vault document not found"}, cors=False)
                return
            try:
                data_bytes = read_vault_file(rel)[0]
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)}, cors=False)
                return
            low_name = full.name.lower()
            safe_fname = re.sub(r"[^a-zA-Z0-9._-]", "_", full.name)
            if low_name.endswith(".pdf"):
                ctype = "application/pdf"
                disp = f'inline; filename="{safe_fname}"'
            elif low_name.endswith(".docx"):
                ctype = "application/vnd.openxmlformats-officedocument.wordprocessingml.document"
                disp = f'attachment; filename="{safe_fname}"'
            else:
                ctype = "text/markdown; charset=utf-8"
                disp = f'inline; filename="{safe_fname}"'
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data_bytes)))
            self.send_header("Content-Disposition", disp)
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Content-Security-Policy", "default-src 'none'; sandbox")
            self.send_header("X-Frame-Options", "DENY")
            self.end_headers()
            if getattr(self, "command", "GET") != "HEAD":
                self.wfile.write(data_bytes)
            return

        if route == "/api/v1/briefing":
            try:
                project = (query.get("project") or [""])[0]
                scope = (query.get("scope") or [""])[0]
                self.send_json(200, op_briefing(conn, actor, scope=scope, project=project))
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)})
            return

        if route == "/api/v1/search":
            try:
                q = (query.get("query") or query.get("q") or [""])[0]
                scope = (query.get("scope") or [""])[0]
                cat = (query.get("category") or [""])[0]
                val = (query.get("validity") or [""])[0]
                inc = (query.get("include_history") or ["false"])[0].lower() in ("1", "true", "yes")
                self.send_json(200, op_search(conn, query=q, scope=scope, category=cat, include_history=inc, validity=val))
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)})
            return

        if route == "/api/v1/fact-check":
            try:
                stmt = (query.get("statement") or query.get("q") or [""])[0]
                scope = (query.get("scope") or [""])[0]
                subj = (query.get("subject") or [""])[0]
                lim = _safe_int((query.get("limit") or ["8"])[0], "limit", default=8)
                self.send_json(200, op_check_facts(conn, statement=stmt, scope=scope, subject=subj, limit=lim))
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)})
            return

        if route == "/api/v1/context":
            try:
                target = (query.get("target") or query.get("path") or [""])[0]
                depth = _safe_int((query.get("depth") or ["1"])[0], "depth", default=1)
                self.send_json(200, op_build_context(conn, target=target, depth=depth))
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)})
            return

        if route == "/api/v1/notes":
            try:
                scope = (query.get("scope") or [""])[0]
                self.send_json(200, op_list_notes(conn, scope=scope))
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)})
            return

        if route == "/api/v1/note":
            try:
                note_path = (query.get("path") or [""])[0]
                self.send_json(200, op_read_note(conn, note_path))
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)})
            return

        if route == "/sse":
            session_id = secrets.token_hex(16)
            q_chan: queue.Queue[str | None] = queue.Queue(maxsize=64)
            with SSE_LOCK:
                if len(SSE_SESSIONS) >= MAX_SSE_SESSIONS:
                    self.send_json(429, {"error": "Too many active SSE sessions"})
                    return
                SSE_SESSIONS[session_id] = (actor, q_chan)
            msg_endpoint = f"/messages?session_id={session_id}"
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-cache")
            self.send_header("Connection", "keep-alive")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.end_headers()
            try:
                self.wfile.write(f"event: endpoint\ndata: {msg_endpoint}\n\n".encode("utf-8"))
                self.wfile.flush()
                while True:
                    try:
                        item = q_chan.get(timeout=15.0)
                        if item is None:
                            break
                        self.wfile.write(f"event: message\ndata: {item}\n\n".encode("utf-8"))
                        self.wfile.flush()
                    except queue.Empty:
                        self.wfile.write(b": keepalive\n\n")
                        self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError, TimeoutError, OSError):
                pass
            finally:
                with SSE_LOCK:
                    SSE_SESSIONS.pop(session_id, None)
            return

        if route == "/mcp":
            self.send_json(
                200,
                {
                    "name": "vyn-memory",
                    "version": "1.3.0",
                    "actor": actor,
                    "writable_scopes": writable_scopes_for(actor),
                    "transport": "streamable-http",
                },
            )
            return

        if route == "/":
            if actor != "owner":
                self.send_json(
                    403,
                    {
                        "error": "Agent tokens are restricted to MCP/API endpoints; sign in at /login to view the human HTML dashboard.",
                    },
                    cors=False,
                )
                return
            page = render_dashboard_page(
                conn,
                actor,
                selected_note=(query.get("note") or [""])[0],
                scope_filter=(query.get("scope") or [""])[0],
                search_query=(query.get("q") or [""])[0],
                session_token=self.owner_cookie_token(),
            )
            self.send_html(200, page)
            return

        self.send_json(404, {"error": f"Unknown route: {route}"})

    def do_POST(self) -> None:
        self._body_read = False
        conn: sqlite3.Connection = self.server.db  # type: ignore[attr-defined]
        ip = self.client_ip()
        if _is_rate_limited(ip):
            self.send_json(429, {"error": "Too many failed authentication attempts; try again in 5 minutes."})
            return
        try:
            route, query, actor = self.parse_route_and_auth(allow_cookie=False)
        except MemoryError as exc:
            self.send_json(exc.status, {"error": str(exc)})
            return

        if route == "/upload":
            same_origin_ok = self._is_same_origin_browser_post()
            upload_actor = actor if actor == "owner" else None
            used_cookie_auth = False
            upload_cookie_tok = ""
            if not upload_actor and same_origin_ok:
                for cand_tok in self._extract_cookie_tokens():
                    if resolve_actor_from_token(cand_tok, conn) == "owner":
                        upload_actor = "owner"
                        used_cookie_auth = True
                        upload_cookie_tok = cand_tok
                        break
            if upload_actor != "owner":
                _record_auth_failure(ip)
                self.send_json(401, {"error": "Owner authentication required to upload files via browser."}, cors=False)
                return
            try:
                raw_mp = self.read_bounded_body(MAX_UPLOAD_BODY_BYTES)
                fields, fname, fbytes = _parse_multipart_upload(raw_mp, self.headers.get("Content-Type", ""))
                if used_cookie_auth and not _verify_upload_csrf(
                    fields.get("csrf_token", ""),
                    purpose="upload",
                    session_token=upload_cookie_tok,
                ):
                    _record_auth_failure(ip)
                    self.send_json(403, {"error": "Invalid or expired upload CSRF token. Reload the page and try again."}, cors=False)
                    return
                res = op_upload_document(
                    conn,
                    "owner",
                    filename=fname,
                    raw_bytes=fbytes,
                    scope=fields.get("scope", DEFAULT_SCOPE),
                    title=fields.get("title", ""),
                    summary=fields.get("summary", ""),
                )
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)}, cors=False)
                return
            dest = f"/?scope={urllib.parse.quote(str(res['scope']))}&note={urllib.parse.quote(str(res['path']))}"
            self.send_response(303)
            self.send_header("Location", dest)
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            return

        if route == "/facts":
            owner = self.read_owner_form(purpose="facts")
            if not owner:
                return
            form = owner[0]
            action = (form.get("action") or [""])[0].strip().lower()
            next_p = _sanitize_next_path((form.get("next") or [""])[0], default="/")
            try:
                if action == "add":
                    op_remember_fact(
                        conn,
                        "owner",
                        fact=(form.get("fact") or [""])[0],
                        scope=(form.get("scope") or [DEFAULT_SCOPE])[0],
                        subject=(form.get("subject") or [""])[0],
                        category=(form.get("category") or ["fact"])[0],
                    )
                elif action == "forget":
                    fid = _safe_int((form.get("fact_id") or ["0"])[0], "fact_id", default=0)
                    op_forget_fact(
                        conn,
                        "owner",
                        fact_id=fid,
                        reason=(form.get("reason") or ["Retired by owner in web UI"])[0],
                    )
                else:
                    raise MemoryError("Invalid fact action")
            except MemoryError as exc:
                self.send_html(
                    exc.status,
                    render_card_page(
                        "Could not update fact",
                        f'<p class="err-box">{html.escape(str(exc))}</p><p><a href="{html.escape(next_p, quote=True)}">Back to the vault</a></p>',
                    ),
                )
                return
            self.send_response(303)
            self.send_header("Location", next_p)
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            return

        if route == "/login":
            if not self._is_same_origin_browser_post():
                _record_auth_failure(ip)
                self.send_json(403, {"error": "Cross-origin sign-in form submissions are forbidden."}, cors=False)
                return
            try:
                raw_form = self.read_bounded_body(MAX_FORM_BODY_BYTES).decode("utf-8", errors="replace")
                form = urllib.parse.parse_qs(raw_form)
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)}, cors=False)
                return
            submitted_token = (form.get("token") or [""])[0].strip()
            next_p = _sanitize_next_path((form.get("next") or [f"/?scope={DEFAULT_SCOPE}"])[0])
            resolved = resolve_actor_from_token(submitted_token, conn)
            if resolved != "owner":
                _record_auth_failure(ip)
                msg = (
                    "Only MEMORY_OWNER_TOKEN can sign into the human browser dashboard (agent tokens are for MCP/API only)."
                    if resolved
                    else "Invalid MEMORY_OWNER_TOKEN. Check your server env file and try again."
                )
                self.send_html(401, render_login_page(next_path=next_p, error_msg=msg))
                return
            _clear_auth_failures(ip)
            sess_tok = _mint_web_session(conn, owner_session_email())
            self.send_response(303)
            self.send_header("Location", next_p)
            self.send_header("Set-Cookie", _session_cookie_header(sess_tok, max_age=2592000))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            return

        if route == "/oauth/register":
            try:
                body = self.read_json_body()
                data = body if isinstance(body, dict) else {}
                raw_uris = data.get("redirect_uris")
                validated_uris = [
                    validate_oauth_redirect_uri(str(u))
                    for u in (raw_uris if isinstance(raw_uris, list) else [])
                ]
            except MemoryError as exc:
                self.send_json(exc.status, {"error": "invalid_client_metadata", "error_description": str(exc)})
                return
            cid = f"vyn-mcp-{secrets.token_hex(8)}"
            self.send_json(
                201,
                {
                    "client_id": cid,
                    "client_name": str(data.get("client_name") or "MCP Client")[:128],
                    "redirect_uris": validated_uris,
                    "grant_types": ["authorization_code", "refresh_token"],
                    "response_types": ["code"],
                    "token_endpoint_auth_method": "none",
                },
            )
            return

        if route == "/oauth/authorize":
            try:
                raw_form = self.read_bounded_body(MAX_FORM_BODY_BYTES).decode("utf-8", errors="replace")
                form = urllib.parse.parse_qs(raw_form)
                redirect_uri = validate_oauth_redirect_uri((form.get("redirect_uri") or [""])[0])
                code_challenge = (form.get("code_challenge") or [""])[0].strip()
                code_challenge_method = (form.get("code_challenge_method") or ["S256"])[0].strip()
                if code_challenge_method != "S256" or not PKCE_CHALLENGE_RE.match(code_challenge):
                    raise MemoryError("OAuth 2.1 PKCE S256 code_challenge is required")
            except MemoryError as exc:
                self.send_json(exc.status, {"error": "invalid_request", "error_description": str(exc)})
                return

            submitted_token = (form.get("token") or [""])[0].strip()
            resolved: str | None = None
            parent = ""
            if submitted_token:
                # Role tokens only (no db: sessions and OAuth tokens are not accepted here), and never the owner's:
                # the owner approves through the owner session below, so owner credentials never become OAuth tokens.
                resolved = resolve_actor_from_token(submitted_token)
                if resolved == "owner":
                    resolved = None
                parent = "role:" + hashlib.sha256(submitted_token.encode()).hexdigest()
            elif (form.get("omni_session") or [""])[0].strip() == "1":
                same_origin_ok = self._is_same_origin_browser_post()
                pair = self._owner_cookie_pair()
                sess_tok, email = pair if pair else ("", None)
                csrf_ok = bool(email) and _verify_upload_csrf(
                    (form.get("csrf_token") or [""])[0],
                    purpose="oauth",
                    session_token=sess_tok,
                )
                parent = "email:" + (email or "")
                selected_role = (form.get("role") or ["claude"])[0].strip().lower()
                if (
                    same_origin_ok
                    and csrf_ok
                    and email
                    and selected_role in ("chatgpt", "claude", "antigravity", "hermes")
                ):
                    resolved = selected_role
            if not resolved:
                _record_auth_failure(ip)
                self.send_html(401, render_card_page("Unauthorized", "<p>Sign in as owner or provide a valid agent token.</p>"), csp=OAUTH_CSP)
                return
            _clear_auth_failures(ip)
            state = (form.get("state") or [""])[0]
            client_id = (form.get("client_id") or ["mcp-client"])[0].strip()
            resource = (form.get("resource") or [""])[0].strip()
            code = secrets.token_urlsafe(32)
            with DB_LOCK:
                _prune_oauth_tables(conn)
                conn.execute(
                    """
                    INSERT INTO oauth_codes(code_hash, actor, client_id, redirect_uri, code_challenge, resource, parent, expires_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        hashlib.sha256(code.encode()).hexdigest(),
                        resolved,
                        client_id,
                        redirect_uri,
                        code_challenge,
                        resource,
                        parent,
                        time.time() + 300,
                    ),
                )
                conn.commit()
            sep = "&" if "?" in redirect_uri else "?"
            loc = f"{redirect_uri}{sep}code={urllib.parse.quote(code, safe='')}"
            if state:
                loc += f"&state={urllib.parse.quote(state, safe='')}"
            self.send_response(302)
            self.send_header("Location", loc)
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            return

        if route == "/oauth/token":
            try:
                raw_body = self.read_bounded_body(MAX_FORM_BODY_BYTES).decode("utf-8", errors="replace")
                if "application/json" in self.headers.get("Content-Type", ""):
                    try:
                        parsed_body = json.loads(raw_body or "{}")
                    except json.JSONDecodeError as exc:
                        raise MemoryError("Invalid JSON body") from exc
                    if not isinstance(parsed_body, dict):
                        raise MemoryError("Invalid JSON body")
                    form = {k: [str(v)] for k, v in parsed_body.items()}
                else:
                    form = urllib.parse.parse_qs(raw_body)
            except MemoryError as exc:
                self.send_json(exc.status, {"error": "invalid_request", "error_description": str(exc)})
                return

            grant_type = (form.get("grant_type") or ["authorization_code"])[0].strip()
            req_client_id = (form.get("client_id") or [""])[0].strip()

            if grant_type == "refresh_token":
                raw_refresh = (form.get("refresh_token") or [""])[0].strip()
                if not raw_refresh:
                    self.send_json(400, {"error": "invalid_grant", "error_description": "Missing refresh_token"})
                    return
                refresh_hash = hashlib.sha256(raw_refresh.encode()).hexdigest()
                with DB_LOCK:
                    _prune_oauth_tables(conn)
                    tok_row = conn.execute(
                        "SELECT * FROM oauth_tokens WHERE refresh_hash = ?",
                        (refresh_hash,),
                    ).fetchone()
                    if (
                        not tok_row
                        or tok_row["expires_at"] < time.time()
                        or not oauth_parent_valid(str(tok_row["parent"]), str(tok_row["actor"]))
                    ):
                        self.send_json(400, {"error": "invalid_grant"})
                        return
                    if req_client_id and tok_row["client_id"] and req_client_id != tok_row["client_id"]:
                        self.send_json(400, {"error": "invalid_grant", "error_description": "client_id mismatch"})
                        return
                    conn.execute("DELETE FROM oauth_tokens WHERE token_hash = ?", (tok_row["token_hash"],))
                    access_token = secrets.token_urlsafe(32)
                    new_refresh = "vmr_" + secrets.token_urlsafe(32)
                    now_ts = time.time()
                    conn.execute(
                        """
                        INSERT INTO oauth_tokens(token_hash, refresh_hash, actor, client_id, resource, parent, label, last_used, created_at, expires_at)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                        """,
                        (
                            hashlib.sha256(access_token.encode()).hexdigest(),
                            hashlib.sha256(new_refresh.encode()).hexdigest(),
                            tok_row["actor"],
                            tok_row["client_id"],
                            tok_row["resource"],
                            tok_row["parent"],
                            tok_row["label"],
                            now_ts,
                            tok_row["created_at"],
                            now_ts + 86400 * 365,
                        ),
                    )
                    conn.commit()
                self.send_json(
                    200,
                    {
                        "access_token": access_token,
                        "refresh_token": new_refresh,
                        "token_type": "Bearer",
                        "expires_in": 86400 * 365,
                    },
                )
                return

            code = (form.get("code") or [""])[0].strip()
            verifier = (form.get("code_verifier") or [""])[0].strip()
            req_redirect_uri = (form.get("redirect_uri") or [""])[0].strip()
            if not code or not PKCE_VERIFIER_RE.match(verifier):
                self.send_json(400, {"error": "invalid_grant", "error_description": "Missing code or valid PKCE code_verifier"})
                return
            code_hash = hashlib.sha256(code.encode()).hexdigest()
            with DB_LOCK:
                _prune_oauth_tables(conn)
                row = conn.execute("SELECT * FROM oauth_codes WHERE code_hash = ?", (code_hash,)).fetchone()
                if not row or row["expires_at"] < time.time() or not oauth_parent_valid(str(row["parent"]), str(row["actor"])):
                    self.send_json(400, {"error": "invalid_grant"})
                    return
                conn.execute("DELETE FROM oauth_codes WHERE code_hash = ?", (code_hash,))
                conn.commit()
                if not row["code_challenge"]:
                    self.send_json(400, {"error": "invalid_grant", "error_description": "PKCE challenge required"})
                    return
                if req_client_id and row["client_id"] and req_client_id != row["client_id"]:
                    self.send_json(400, {"error": "invalid_grant", "error_description": "client_id mismatch"})
                    return
                if req_redirect_uri and row["redirect_uri"] and req_redirect_uri != row["redirect_uri"]:
                    self.send_json(400, {"error": "invalid_grant", "error_description": "redirect_uri mismatch"})
                    return
                digest = hashlib.sha256(verifier.encode("ascii")).digest()
                computed = base64.urlsafe_b64encode(digest).rstrip(b"=").decode("ascii")
                if not hmac.compare_digest(computed, str(row["code_challenge"])):
                    self.send_json(400, {"error": "invalid_grant", "error_description": "PKCE mismatch"})
                    return
                access_token = secrets.token_urlsafe(32)
                refresh_token = "vmr_" + secrets.token_urlsafe(32)
                now_ts = time.time()
                conn.execute(
                    """
                    INSERT INTO oauth_tokens(token_hash, refresh_hash, actor, client_id, resource, parent, label, created_at, expires_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        hashlib.sha256(access_token.encode()).hexdigest(),
                        hashlib.sha256(refresh_token.encode()).hexdigest(),
                        row["actor"],
                        row["client_id"],
                        row["resource"],
                        row["parent"],
                        f'{urllib.parse.urlsplit(str(row["redirect_uri"])).hostname} connector',
                        now_ts,
                        now_ts + 86400 * 365,
                    ),
                )
                conn.commit()
            self.send_json(
                200,
                {
                    "access_token": access_token,
                    "refresh_token": refresh_token,
                    "token_type": "Bearer",
                    "expires_in": 86400 * 365,
                },
            )
            return

        if route == "/device/code":  # RFC 8628-style login for a device; the owner approves it at /device
            try:
                body = self.read_json_body()
            except MemoryError as exc:
                self.send_json(exc.status, {"error": "invalid_request", "error_description": str(exc)})
                return
            label = _device_label(body if isinstance(body, dict) else {})
            device_code = secrets.token_urlsafe(32)
            letters = "".join(secrets.choice(USER_CODE_ALPHABET) for _ in range(8))
            user_code = f"{letters[:4]}-{letters[4:]}"
            with DB_LOCK:
                _prune_oauth_tables(conn)
                # ponytail: count only unanswered (actor = '') rows so denied/approved codes free their slot immediately
                total_pending = conn.execute("SELECT COUNT(*) FROM device_codes WHERE actor = ''").fetchone()[0]
                ip_pending = conn.execute("SELECT COUNT(*) FROM device_codes WHERE actor = '' AND ip = ?", (ip,)).fetchone()[0]
                if total_pending >= MAX_PENDING_DEVICE_CODES or ip_pending >= MAX_PENDING_DEVICE_CODES_PER_IP:
                    conn.commit()
                    self.send_json(429, {"error": "slow_down", "error_description": "Too many pending logins; try again later."})
                    return
                conn.execute(
                    "INSERT INTO device_codes(device_hash, user_code, label, role_hint, ip, expires_at) VALUES (?, ?, ?, ?, ?, ?)",
                    (hashlib.sha256(device_code.encode()).hexdigest(), user_code, label, _device_role_hint(label), ip, time.time() + 600),
                )
                conn.commit()
            self.send_json(200, {
                "device_code": device_code,
                "user_code": user_code,
                "verification_uri": f"{PUBLIC_URL}/device",
                "verification_uri_complete": f"{PUBLIC_URL}/device?code={user_code}",
                "expires_in": 600,
                "interval": 5,
            })
            return

        if route == "/device/token":
            try:
                body = self.read_json_body()
            except MemoryError as exc:
                self.send_json(exc.status, {"error": "invalid_request", "error_description": str(exc)})
                return
            device_hash = hashlib.sha256(str((body if isinstance(body, dict) else {}).get("device_code") or "").encode()).hexdigest()
            with DB_LOCK:
                _prune_oauth_tables(conn)
                row = conn.execute("SELECT * FROM device_codes WHERE device_hash = ?", (device_hash,)).fetchone()
                if not row:
                    conn.commit()
                    _record_auth_failure(ip)
                    self.send_json(400, {"error": "expired_token"})
                    return
                if not row["actor"]:
                    conn.commit()
                    self.send_json(400, {"error": "authorization_pending"})
                    return
                conn.execute("DELETE FROM device_codes WHERE device_hash = ?", (device_hash,))
                if row["actor"] == "denied" or not oauth_parent_valid(str(row["parent"]), str(row["actor"])):
                    conn.commit()
                    self.send_json(400, {"error": "access_denied"})
                    return
                token = "vmd_" + secrets.token_urlsafe(32)
                now_ts = time.time()
                conn.execute(
                    """
                    INSERT INTO oauth_tokens(token_hash, actor, client_id, parent, label, last_used, created_at, expires_at)
                    VALUES (?, ?, 'device', ?, ?, ?, ?, ?)
                    """,
                    (hashlib.sha256(token.encode()).hexdigest(), row["actor"], row["parent"], row["label"],
                     now_ts, now_ts, now_ts + DEVICE_TOKEN_TTL),
                )
                conn.commit()
            self.send_json(200, {"access_token": token, "token_type": "Bearer", "actor": row["actor"], "expires_in": DEVICE_TOKEN_TTL})
            return

        if route == "/device":
            owner = self.read_owner_form(purpose="device")
            if not owner:
                return
            form, email = owner
            role = (form.get("role") or [""])[0].strip().lower()
            approve = (form.get("decision") or [""])[0] == "approve" and role in DEVICE_ROLES
            with DB_LOCK:
                cur = conn.execute(
                    "UPDATE device_codes SET actor = ?, parent = ? WHERE user_code = ? AND actor = '' AND expires_at > ?",
                    (role if approve else "denied", "email:" + email, (form.get("code") or [""])[0].strip().upper(), time.time()),
                )
                conn.commit()
            if not cur.rowcount:
                self.send_html(404, render_card_page("Login request not found", "<p>It expired or was already answered.</p>"))
            elif approve:
                self.send_html(200, render_card_page(
                    "Approved",
                    "<p>Go back to your terminal; the login finishes on its own.</p><p><a href=\"/apps\">Connected apps</a></p>",
                ))
            else:
                self.send_html(200, render_card_page("Denied", "<p>That device gets no token.</p>"))
            return

        if route == "/apps":
            owner = self.read_owner_form(purpose="apps")
            if not owner:
                return
            form = owner[0]
            table = {"token": "oauth_tokens", "session": "web_sessions"}.get((form.get("kind") or [""])[0])
            rowid = (form.get("id") or [""])[0]
            if table and rowid.isdigit():
                with DB_LOCK:
                    conn.execute(f"DELETE FROM {table} WHERE rowid = ?", (int(rowid),))
                    conn.commit()
            self.send_response(303)
            self.send_header("Location", "/apps")
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            return

        if not self.require_auth(actor):
            return
        assert actor is not None

        if route == "/messages":
            session_id = (query.get("session_id") or [""])[0]
            with SSE_LOCK:
                sess = SSE_SESSIONS.get(session_id)
            if not sess:
                self.send_json(404, {"error": "SSE session not found"})
                return
            sess_actor, q_chan = sess
            if not _sse_actor_matches(actor, sess_actor):
                self.send_json(403, {"error": "SSE session belongs to a different actor"})
                return
            effective_sess_actor = actor if (sess_actor == "hermes" and actor.startswith("hermes/")) else sess_actor
            try:
                payload = self.read_json_body()
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)})
                return
            if isinstance(payload, dict):
                resp = handle_jsonrpc_message(conn, effective_sess_actor, payload)
                if resp is not None:
                    try:
                        q_chan.put_nowait(json.dumps(resp, ensure_ascii=False))
                    except queue.Full:
                        self.send_json(429, {"error": "SSE session queue full"})
                        return
            self.send_json(202, {"accepted": True})
            return

        if route in ("/mcp", "/sse"):
            try:
                payload = self.read_json_body(MAX_UPLOAD_BODY_BYTES)
            except MemoryError as exc:
                self.send_json(exc.status, {"error": str(exc)})
                return
            if isinstance(payload, list):
                if not payload or len(payload) > 32:
                    self.send_json(400, {"error": "JSON-RPC batch must contain between 1 and 32 messages"})
                    return
                responses = [
                    r for item in payload if isinstance(item, dict)
                    if (r := handle_jsonrpc_message(conn, actor, item)) is not None
                ]
                if not responses:
                    self.send_response(202)
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
                self.send_json(200, responses)
                return
            if isinstance(payload, dict):
                resp = handle_jsonrpc_message(conn, actor, payload)
                if resp is None:
                    self.send_response(202)
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
                self.send_json(200, resp)
                return
            self.send_json(400, {"error": "Invalid JSON-RPC payload"})
            return

        try:
            max_b = MAX_UPLOAD_BODY_BYTES if route == "/api/v1/upload" else MAX_JSON_BODY_BYTES
            body = self.read_json_body(max_b)
            data = body if isinstance(body, dict) else {}
            effective_actor = normalize_actor(actor, str(data.get("subagent") or "")) if data.get("subagent") else actor
            if route == "/api/v1/remember":
                res = op_remember_fact(
                    conn,
                    effective_actor,
                    fact=str(data.get("fact") or ""),
                    scope=str(data.get("scope") or DEFAULT_SCOPE),
                    subject=str(data.get("subject") or ""),
                    category=str(data.get("category") or "fact"),
                    supersedes_id=_safe_int(data.get("supersedes_id"), "supersedes_id", default=0),
                    supersede_subject=bool(data.get("supersede_subject", True)),
                )
                self.send_json(200, res)
                return
            if route == "/api/v1/forget":
                res = op_forget_fact(
                    conn,
                    effective_actor,
                    fact_id=_safe_int(data.get("fact_id"), "fact_id", default=0),
                    reason=str(data.get("reason") or ""),
                    resolution=str(data.get("resolution") or "invalidated"),
                )
                self.send_json(200, res)
                return
            if route == "/api/v1/note":
                raw_tags = data.get("tags")
                tags = [str(x) for x in raw_tags] if isinstance(raw_tags, list) else []
                res = op_write_note(
                    conn,
                    effective_actor,
                    path=str(data.get("path") or ""),
                    content=str(data.get("content") or ""),
                    title=str(data.get("title") or ""),
                    scope=str(data.get("scope") or ""),
                    summary=str(data.get("summary") or ""),
                    tags=tags,
                    mode=str(data.get("mode") or "replace"),
                    section=str(data.get("section") or ""),
                )
                self.send_json(200, res)
                return
            if route == "/api/v1/upload":
                raw_tags = data.get("tags")
                tags = [str(x) for x in raw_tags] if isinstance(raw_tags, list) else []
                res = op_upload_document(
                    conn,
                    effective_actor,
                    filename=str(data.get("filename") or ""),
                    base64_content=str(data.get("base64_content") or ""),
                    scope=str(data.get("scope") or DEFAULT_SCOPE),
                    title=str(data.get("title") or ""),
                    summary=str(data.get("summary") or ""),
                    tags=tags,
                )
                self.send_json(200, res)
                return
        except MemoryError as exc:
            self.send_json(exc.status, {"error": str(exc), "actor": actor})
            return

        self.send_json(404, {"error": f"Unknown POST route: {route}"})


def run_stdio_server(conn: sqlite3.Connection, actor: str) -> int:
    """Run MCP over stdin/stdout (for local Antigravity and Claude Code stdio clients)."""
    for raw_line in sys.stdin:
        line = raw_line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(msg, dict):
            resp = handle_jsonrpc_message(conn, actor, msg)
            if resp is not None:
                sys.stdout.write(json.dumps(resp, ensure_ascii=False) + "\n")
                sys.stdout.flush()
    return 0


def run_self_check(conn: sqlite3.Connection) -> int:
    tokens = configured_tokens()
    missing = [k for r, k in TOKEN_ENV_MAP.items() if r not in tokens]
    if missing:
        print(f"Missing token env vars: {', '.join(missing)}", file=sys.stderr)
        return 1
    seed_initial_scaffold(conn)
    brief = op_briefing(conn, "hermes/upgrade")
    print(
        f"Memory hub OK: {brief['notes_total']} vault notes indexed, "
        f"{len(tokens)} role tokens configured ({', '.join(sorted(tokens))})."
    )
    return 0


def main(argv: list[str]) -> int:
    conn = open_db()
    if "--stdio" in argv:
        actor = os.environ.get("MEMORY_ACTOR", "antigravity").strip().lower()
        sub = os.environ.get("MEMORY_SUBAGENT", "").strip().lower()
        effective = normalize_actor(actor, sub) if sub else actor
        seed_initial_scaffold(conn)
        return run_stdio_server(conn, effective)
    if "check" in argv:
        return run_self_check(conn)

    seed_initial_scaffold(conn)
    server = ThreadingHTTPServer(("0.0.0.0", PORT), MemoryHTTPHandler)
    server.db = conn  # type: ignore[attr-defined]
    print(f"vyn-memory listening on 0.0.0.0:{PORT} (vault={VAULT_DIR}, data={DATA_DIR})", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
