#!/usr/bin/env python3
"""CLI helper for the Vyn Unified Cross-Agent Memory Hub (`vyn-memory`).

Automatically detects the calling Hermes profile (e.g. `default`) from `HERMES_PROFILE` or
`HOME` (`/opt/data/profiles/<subagent>`) and sends `X-Hermes-Subagent: <subagent>`
so each sub-agent writes to its own `agents/<subagent>` scope while reading all scopes.
"""
from __future__ import annotations

import argparse
import base64
import json
import getpass
import os
import platform
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

HOME = Path(os.environ.get("HERMES_HOME") or os.environ.get("HOME") or "/opt/data")
# Not resolve(): a laptop links this folder into ~/.claude/skills and ~/.codex/skills, and the link path tells the apps apart.
SCRIPT_PATH = Path(__file__).absolute()
# Token files: MEMORY_ENV_FILE, else ~/.config/vyn-memory.env (chmod 600), e.g.
#   MEMORY_CLAUDE_TOKEN=...
#   MEMORY_HUB_URL=https://memory.example.com
HOST_MEMORY_ENV_CANDIDATES = tuple(
    Path(p).expanduser()
    for p in (os.environ.get("MEMORY_ENV_FILE", ""), str(Path.home() / ".config" / "vyn-memory.env"))
    if p
)
IS_CONTAINER = (
    Path("/.dockerenv").exists()
    or bool(os.environ.get("HERMES_HOME"))
    or bool(os.environ.get("MEMORY_HERMES_TOKEN"))
)


def _validate_hub_url(raw_url: str) -> str:
    cleaned = (raw_url or "").strip().rstrip("/")
    parsed = urllib.parse.urlsplit(cleaned)
    scheme = parsed.scheme.lower()
    host = (parsed.hostname or "").lower()
    if scheme == "https" and host:
        return cleaned
    if scheme == "http" and host in ("127.0.0.1", "localhost", "::1", "vyn-memory"):
        return cleaned
    raise ValueError(
        f"Refusing insecure MEMORY_HUB_URL {cleaned!r}: use https:// for remote servers "
        "(http:// is allowed only for localhost/127.0.0.1/::1/vyn-memory)."
    )


def detect_hermes_subagent(explicit: str = "") -> str:
    parts = HOME.resolve().parts
    home_prof = ""
    if "profiles" in parts:
        idx = parts.index("profiles")
        if idx + 1 < len(parts):
            home_prof = parts[idx + 1].lower()
    env_prof = (os.environ.get("HERMES_PROFILE") or os.environ.get("MEMORY_SUBAGENT") or "").strip().lower()
    bound_prof = home_prof or env_prof
    req_prof = explicit.strip().lower()
    if bound_prof and req_prof and req_prof != bound_prof:
        raise ValueError(
            f"Sub-agent profile is bound to '{bound_prof}' and cannot be overridden to '{req_prof}'"
        )
    return bound_prof or req_prof or "default"


def _read_key_from_env_file(env_path: Path, key: str) -> str:
    if not env_path.exists():
        return ""
    prefix = f"{key}="
    for line in env_path.read_text(encoding="utf-8", errors="replace").splitlines():
        stripped = line.strip()
        if stripped.startswith(prefix):
            return stripped.split("=", 1)[1].strip().strip("\"'")
    return ""


def _read_host_memory_key(key: str) -> str:
    for candidate in HOST_MEMORY_ENV_CANDIDATES:
        val = _read_key_from_env_file(candidate, key)
        if val:
            return val
    return ""


DEFAULT_URL = (
    os.environ.get("MEMORY_HUB_URL", "").strip()
    or _read_host_memory_key("MEMORY_HUB_URL")
    or ("http://vyn-memory:8770" if IS_CONTAINER else "http://127.0.0.1:8770")
).rstrip("/")


def resolve_token_and_mode() -> tuple[str, bool]:
    env_hermes = os.environ.get("MEMORY_HERMES_TOKEN", "").strip()
    if env_hermes:
        return env_hermes, True
    if IS_CONTAINER:
        for candidate in (HOME / ".env", Path("/opt/data/.env")):
            found = _read_key_from_env_file(candidate, "MEMORY_HERMES_TOKEN")
            if found:
                return found, True
    script_str = str(SCRIPT_PATH)
    actor_env = os.environ.get("MEMORY_ACTOR", "").strip().lower()
    preferred_keys = ["MEMORY_ANTIGRAVITY_TOKEN", "MEMORY_CLAUDE_TOKEN", "MEMORY_CHATGPT_TOKEN"]
    if actor_env == "claude" or "/.claude/" in script_str:
        preferred_keys = ["MEMORY_CLAUDE_TOKEN", "MEMORY_ANTIGRAVITY_TOKEN", "MEMORY_CHATGPT_TOKEN"]
    elif actor_env in ("chatgpt", "codex") or "/.codex/" in script_str:
        preferred_keys = ["MEMORY_CHATGPT_TOKEN", "MEMORY_ANTIGRAVITY_TOKEN", "MEMORY_CLAUDE_TOKEN"]
    for key in preferred_keys:
        val = os.environ.get(key, "").strip() or _read_host_memory_key(key)
        if val:
            return val, False
    raise ValueError("No MEMORY_*_TOKEN found in environment or ~/.config/vyn-memory.env (run 'memory.py login <url>')")


def resolve_token() -> str:
    tok, _ = resolve_token_and_mode()
    return tok


def _send(path: str, data: bytes | None = None, subagent: str = "", auth: bool = True, base_url: str = "") -> dict[str, object]:
    hub_url = _validate_hub_url(base_url or DEFAULT_URL)
    headers = {"User-Agent": "vyn-memory-cli/1", "Content-Type": "application/json; charset=utf-8"}
    if auth:
        tok, is_hermes = resolve_token_and_mode()
        headers["Authorization"] = f"Bearer {tok}"
        if is_hermes:
            headers["X-Hermes-Subagent"] = detect_hermes_subagent(subagent)
    req = urllib.request.Request(f"{hub_url}{path}", data=data, headers=headers, method="POST" if data else "GET")
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        try:
            err = json.loads(body).get("error", body)
        except Exception:
            err = body
        raise ValueError(f"HTTP {exc.code}: {err}") from exc


def api_get(path: str, params: dict[str, object] | None = None, subagent: str = "") -> dict[str, object]:
    clean = {k: str(v) for k, v in (params or {}).items() if v is not None and str(v) != ""}
    return _send(path + ("?" + urllib.parse.urlencode(clean) if clean else ""), subagent=subagent)


def api_post(path: str, payload: dict[str, object], subagent: str = "", auth: bool = True, base_url: str = "") -> dict[str, object]:
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    return _send(path, body, subagent=subagent, auth=auth, base_url=base_url)


def detect_app() -> str:
    actor = os.environ.get("MEMORY_ACTOR", "").strip().lower()
    path = str(SCRIPT_PATH)
    if actor == "claude" or "/.claude/" in path:
        return "Claude Code"
    if actor in ("chatgpt", "codex") or "/.codex/" in path:
        return "Codex"
    if actor == "antigravity" or "/.gemini/" in path:
        return "Antigravity"
    return "memory.py"


def login(url: str = "") -> dict[str, object]:
    """Device login: the owner approves this device in a browser, and its own token lands in the token file."""
    hub_url = _validate_hub_url(url or DEFAULT_URL)
    info = {"app": detect_app(), "user": getpass.getuser(), "host": platform.node(),
            "os": f"{platform.system()} {platform.release()} {platform.machine()}".strip()}
    start = api_post("/device/code", info, auth=False, base_url=hub_url)
    print(f"Open {start['verification_uri_complete']}\nand approve code {start['user_code']} "
          "(it must match the page).", file=sys.stderr, flush=True)
    deadline = time.time() + float(start["expires_in"])
    while time.time() < deadline:
        time.sleep(float(start["interval"]))
        try:
            got = api_post("/device/token", {"device_code": start["device_code"]}, auth=False, base_url=hub_url)
        except ValueError as exc:
            if "authorization_pending" in str(exc):
                continue
            raise
        key = f"MEMORY_{str(got['actor']).upper()}_TOKEN"
        target = HOST_MEMORY_ENV_CANDIDATES[0]
        old = target.read_text(encoding="utf-8").splitlines() if target.exists() else []
        kept = [ln for ln in old if not ln.strip().startswith((f"{key}=", "MEMORY_HUB_URL="))]
        target.parent.mkdir(parents=True, exist_ok=True)
        fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write("\n".join([*kept, f"MEMORY_HUB_URL={hub_url}", f"{key}={got['access_token']}"]) + "\n")
        os.chmod(target, 0o600)
        return {"ok": True, "app": info["app"], "acts_as": got["actor"], "hub_url": hub_url, "saved_to": str(target)}
    raise ValueError("Login was not approved within 10 minutes; run login again.")


def main() -> int:
    parser = argparse.ArgumentParser(description="Vyn Unified Cross-Agent Memory CLI")
    parser.add_argument("--subagent", default="", help="Override Hermes sub-agent name (auto-detected from profile HOME)")
    sub = parser.add_subparsers(dest="command", required=True)

    p_login = sub.add_parser("login", help="Get this device's own token: approve it in the browser, saved to the token file")
    p_login.add_argument("url", nargs="?", default="", help="Optional memory server URL (e.g. https://memory.example.com)")

    p_brief = sub.add_parser("briefing", help="Get unified cross-agent memory briefing")
    p_brief.add_argument("--project", default="")
    p_brief.add_argument("--scope", default="")

    p_search = sub.add_parser("search", help="Search AI facts and Obsidian vault notes")
    p_search.add_argument("query", nargs="?", default="")
    p_search.add_argument("--scope", default="")
    p_search.add_argument("--category", default="")
    p_search.add_argument("--validity", default="valid", choices=["valid", "invalid", "all"])
    p_search.add_argument("--history", action="store_true", help="Include superseded and invalidated facts (same as --validity all)")

    p_check = sub.add_parser("check-fact", help="Fact-check a claim or topic against active facts, history, and vault notes")
    p_check.add_argument("statement", nargs="?", default="", help="Claim or question to verify against memory")
    p_check.add_argument("--scope", default="")
    p_check.add_argument("--subject", default="")
    p_check.add_argument("--limit", type=int, default=8)

    p_rem = sub.add_parser("remember", help="Record an atomic AI-to-AI temporal fact")
    p_rem.add_argument("fact", help="Self-contained fact text")
    p_rem.add_argument("--scope", default="")
    p_rem.add_argument("--subject", default="")
    p_rem.add_argument(
        "--category",
        default="fact",
        choices=["weakness", "strength", "progress", "decision", "preference", "question", "fact"],
    )
    p_rem.add_argument("--supersedes-id", type=int, default=0)
    p_rem.add_argument("--no-supersede-subject", action="store_true")

    p_forget = sub.add_parser("forget", help="Mark an outdated fact as invalidated or superseded")
    p_forget.add_argument("fact_id", type=int)
    p_forget.add_argument("--reason", default="")
    p_forget.add_argument("--resolution", default="invalidated", choices=["invalidated", "superseded"])

    p_list = sub.add_parser("list-notes", help="List indexed Markdown notes in the Obsidian vault")
    p_list.add_argument("--scope", default="")

    p_read = sub.add_parser("read-note", help="Read a Markdown note and its 1-hop [[wikilink]] graph context")
    p_read.add_argument("path")

    p_ctx = sub.add_parser("context", help="Build 1-2 hop graph + temporal fact context around a note or topic")
    p_ctx.add_argument("target")
    p_ctx.add_argument("--depth", type=int, default=1, choices=[1, 2])

    p_write = sub.add_parser("write-note", help="Create or update a Markdown note in the Obsidian vault")
    p_write.add_argument("path")
    p_write.add_argument("--title", default="")
    p_write.add_argument("--scope", default="")
    p_write.add_argument("--summary", default="")
    p_write.add_argument("--tags", default="", help="Comma-separated tags")
    p_write.add_argument("--mode", default="replace", choices=["replace", "append", "section"])
    p_write.add_argument("--section", default="")
    p_write.add_argument("--content", default="", help="Note content (if omitted, reads stdin)")

    p_upload = sub.add_parser("upload", help="Upload and index a .pdf, .docx, or .md file into the Obsidian vault")
    p_upload.add_argument("file_path", help="Local path to .pdf, .docx, .md, or .txt file")
    p_upload.add_argument("--filename", default="", help="Optional target filename or vault path (defaults to basename)")
    p_upload.add_argument("--scope", default="")
    p_upload.add_argument("--title", default="")
    p_upload.add_argument("--summary", default="")
    p_upload.add_argument("--tags", default="", help="Comma-separated tags")

    args = parser.parse_args()
    subagent = args.subagent
    if args.command == "login":
        res = login(args.url)
    elif args.command == "briefing":
        res = api_get("/api/v1/briefing", {"project": args.project, "scope": args.scope}, subagent=subagent)
    elif args.command == "search":
        validity = "all" if args.history else args.validity
        res = api_get(
            "/api/v1/search",
            {
                "query": args.query,
                "scope": args.scope,
                "category": args.category,
                "validity": validity,
                "include_history": "true" if validity == "all" else "false",
            },
            subagent=subagent,
        )
    elif args.command == "check-fact":
        res = api_get(
            "/api/v1/fact-check",
            {
                "statement": args.statement,
                "scope": args.scope,
                "subject": args.subject,
                "limit": args.limit,
            },
            subagent=subagent,
        )
    elif args.command == "remember":
        res = api_post(
            "/api/v1/remember",
            {
                "fact": args.fact,
                "scope": args.scope,
                "subject": args.subject,
                "category": args.category,
                "supersedes_id": args.supersedes_id,
                "supersede_subject": not args.no_supersede_subject,
            },
            subagent=subagent,
        )
    elif args.command == "forget":
        res = api_post(
            "/api/v1/forget",
            {"fact_id": args.fact_id, "reason": args.reason, "resolution": args.resolution},
            subagent=subagent,
        )
    elif args.command == "list-notes":
        res = api_get("/api/v1/notes", {"scope": args.scope}, subagent=subagent)
    elif args.command == "read-note":
        res = api_get("/api/v1/note", {"path": args.path}, subagent=subagent)
    elif args.command == "context":
        res = api_get("/api/v1/context", {"target": args.target, "depth": args.depth}, subagent=subagent)
    elif args.command == "write-note":
        content = args.content if args.content.strip() else sys.stdin.read()
        tags = [t.strip() for t in args.tags.split(",") if t.strip()]
        res = api_post(
            "/api/v1/note",
            {
                "path": args.path,
                "content": content,
                "title": args.title,
                "scope": args.scope,
                "summary": args.summary,
                "tags": tags,
                "mode": args.mode,
                "section": args.section,
            },
            subagent=subagent,
        )
    elif args.command == "upload":
        src = Path(args.file_path).expanduser().resolve()
        if not src.is_file():
            raise ValueError(f"File not found: {src}")
        tags = [t.strip() for t in args.tags.split(",") if t.strip()]
        res = api_post(
            "/api/v1/upload",
            {
                "filename": args.filename.strip() or src.name,
                "base64_content": base64.b64encode(src.read_bytes()).decode("ascii"),
                "scope": args.scope,
                "title": args.title,
                "summary": args.summary,
                "tags": tags,
            },
            subagent=subagent,
        )
    else:
        raise ValueError(f"Unknown command: {args.command}")

    print(json.dumps(res, ensure_ascii=False, separators=(",", ":")))  # compact: agents pay per character
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"vyn-memory error: {exc}", file=sys.stderr)
        raise SystemExit(1)
