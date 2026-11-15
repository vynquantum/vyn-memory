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
import os
import sys
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

HOME = Path(os.environ.get("HERMES_HOME") or os.environ.get("HOME") or "/opt/data")
SCRIPT_PATH = Path(__file__).resolve()
# Token files: MEMORY_ENV_FILE, else ~/.config/vyn-memory.env (chmod 600), e.g.
#   MEMORY_CLAUDE_TOKEN=...
#   MEMORY_HUB_URL=https://memory.example.com
HOST_MEMORY_ENV_CANDIDATES = tuple(
    Path(p).expanduser()
    for p in (os.environ.get("MEMORY_ENV_FILE", ""), str(Path.home() / ".config" / "vyn-memory.env"))
    if p
)
IS_CONTAINER = Path("/opt/data").exists() or bool(os.environ.get("MEMORY_HERMES_TOKEN"))


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
    raise ValueError("No MEMORY_*_TOKEN found in environment or memory.env")


def resolve_token() -> str:
    tok, _ = resolve_token_and_mode()
    return tok


def api_get(path: str, params: dict[str, object] | None = None, subagent: str = "") -> dict[str, object]:
    qs = ""
    if params:
        clean = {k: str(v) for k, v in params.items() if v is not None and str(v) != ""}
        if clean:
            qs = "?" + urllib.parse.urlencode(clean)
    tok, is_hermes = resolve_token_and_mode()
    headers = {"Authorization": f"Bearer {tok}", "User-Agent": "vyn-memory-cli/1"}
    if is_hermes:
        headers["X-Hermes-Subagent"] = detect_hermes_subagent(subagent)
    req = urllib.request.Request(
        f"{DEFAULT_URL}{path}{qs}",
        headers=headers,
        method="GET",
    )
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


def api_post(path: str, payload: dict[str, object], subagent: str = "") -> dict[str, object]:
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    tok, is_hermes = resolve_token_and_mode()
    headers = {
        "User-Agent": "vyn-memory-cli/1",
        "Authorization": f"Bearer {tok}",
        "Content-Type": "application/json; charset=utf-8",
    }
    if is_hermes:
        headers["X-Hermes-Subagent"] = detect_hermes_subagent(subagent)
    req = urllib.request.Request(
        f"{DEFAULT_URL}{path}",
        data=data,
        headers=headers,
        method="POST",
    )
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


def main() -> int:
    parser = argparse.ArgumentParser(description="Vyn Unified Cross-Agent Memory CLI")
    parser.add_argument("--subagent", default="", help="Override Hermes sub-agent name (auto-detected from profile HOME)")
    sub = parser.add_subparsers(dest="command", required=True)

    p_brief = sub.add_parser("briefing", help="Get unified cross-agent memory briefing")
    p_brief.add_argument("--project", default="")
    p_brief.add_argument("--scope", default="")

    p_search = sub.add_parser("search", help="Search AI facts and Obsidian vault study notes")
    p_search.add_argument("query", nargs="?", default="")
    p_search.add_argument("--scope", default="")
    p_search.add_argument("--category", default="")
    p_search.add_argument("--validity", default="valid", choices=["valid", "invalid", "all"])
    p_search.add_argument("--history", action="store_true", help="Include superseded and invalidated facts (same as --validity all)")

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
    if args.command == "briefing":
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
