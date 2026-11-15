# vyn-memory

One shared memory for all your AI agents. Claude, ChatGPT/Codex, Antigravity and
Hermes (with its profiles) read and write the same memory, so what one agent learns
the others can use.

It keeps two things in step:

- **Facts**: short statements in SQLite (`memory.db`, full-text search). A fact is
  valid from when it is saved until it is retired or replaced, and the history stays.
- **Notes**: an Obsidian vault of Markdown, PDF and DOCX files. Notes are indexed for
  search, `- [category] text #tag` lines become searchable observations, and
  `[[links]]` / `- relation [[Note]]` lines become a graph that `context` follows.

One Python file, standard library only (`pypdf` is optional, for PDF text).

## Ways in

| Client | How |
| :--- | :--- |
| Agents that can run commands (Claude Code, Codex, Antigravity, Hermes) | the skill in `skills/vyn-memory/`: `memory.py` calls the REST API |
| Apps that cannot (claude.ai, ChatGPT, phone apps) | MCP connector at `<your address>/mcp` (OAuth 2.1 + PKCE) or `/sse` |
| You, in a browser | the dashboard at `<your address>/` |
| Anything else | REST API under `/api/v1/`, described at `/openapi.json` |

The skill only loads its instructions when a task needs memory, so it costs far fewer
tokens per request than an always-loaded MCP tool list.

## Run it

```sh
export MEMORY_DATA_DIR=./data MEMORY_VAULT_DIR=./vault   # database here; your Obsidian vault there
export MEMORY_OWNER_TOKEN=... MEMORY_CLAUDE_TOKEN=... MEMORY_CHATGPT_TOKEN=... \
       MEMORY_ANTIGRAVITY_TOKEN=... MEMORY_HERMES_TOKEN=...
python3 server.py check   # self-check
python3 server.py         # listens on 0.0.0.0:8770 (MEMORY_PORT)
```

Make each token long and random (`python3 -c "import secrets; print(secrets.token_urlsafe(32))"`)
and keep them in an env file only you can read, never in Git.

| Variable | Meaning |
| :--- | :--- |
| `MEMORY_DATA_DIR`, `MEMORY_VAULT_DIR` | where the database and the vault live |
| `MEMORY_<ROLE>_TOKEN` | one token per role: `OWNER`, `CLAUDE`, `CHATGPT`, `ANTIGRAVITY`, `HERMES` |
| `MEMORY_PUBLIC_URL` | the address clients use (OAuth metadata and links) |
| `MEMORY_SETTINGS` | path to your settings JSON (below) |
| `MEMORY_BEHIND_CLOUDFLARE=1` | trust `CF-Connecting-IP` for rate limiting (only behind a Cloudflare tunnel) |
| `OMNI_PUBLIC_URL`, `OMNI_INTERNAL_URL`, `OMNI_MEMORY_KEY`, `MEMORY_ADMIN_EMAILS` | optional sign-in through an Omni server; only the listed emails get in |

Put it behind HTTPS (a reverse proxy or a tunnel) before you expose it to the internet.

## Settings

Everything specific to you lives in one JSON file named by `MEMORY_SETTINGS`;
[`settings.example.json`](settings.example.json) shows every key. Without it the server
uses plain defaults: `shared`, `projects/<slug>` and `resources/books` are open to every agent.

| Key | What it does |
| :--- | :--- |
| `timezone` | timestamps (IANA name, default `UTC`) |
| `default_scope` | where a fact or upload goes when no scope is given |
| `open_scopes` | scopes every agent may write (`"x/*"` covers `x` and below) |
| `areas`, `nested_scopes` | top folders whose subfolders are scopes, and ones that nest a level deeper |
| `scope_aliases` | shorthands, e.g. `{"acme": "career/company/acme"}` |
| `hermes` | `subagents` (profile names), `aliases`, `extra_write` (more scopes Hermes may write) |
| `briefing_areas` | areas whose facts the briefing lists separately |
| `dashboard` | sidebar groups and rules, scope pills, pinned notes, landing note, upload scopes |

Starter notes for your areas belong in your vault (or a template you copy into it), not in settings.

## Who may do what

- Every agent reads everything except `personal/`, which nothing reaches through the server.
- Agents write only to the open scopes and to their own `agents/<name>` folder; Hermes
  profiles also share `agents/{hermes,decisions,gotchas,playbooks,research}`.
- The owner (owner token, or an Omni sign-in for an email in `MEMORY_ADMIN_EMAILS`) can
  write everywhere and is the only one who can open the dashboard and download files.
- Agent tokens may sit in a URL (`/s/<token>/mcp`) for clients that cannot send headers.
  Treat such URLs like passwords; rotate a token by changing it and restarting.
- Notes render with a strict Content-Security-Policy (no scripts), uploads and request
  bodies have size limits, failed sign-ins are rate limited, and paths cannot leave the vault.

## Use it from another machine

1. Get the skill: `git clone https://github.com/vynquantum/vyn-memory.git ~/vyn-memory`.
2. Link it where your agents look for skills, for example:
   ```sh
   for d in ~/.claude/skills ~/.codex/skills ~/.gemini/skills; do
     mkdir -p "$d" && ln -sfn ~/vyn-memory/skills/vyn-memory "$d/vyn-memory"
   done
   ```
3. Create `~/.config/vyn-memory.env` with your address and that app's token, then `chmod 600` it:
   ```sh
   MEMORY_HUB_URL=https://memory.example.com
   MEMORY_CLAUDE_TOKEN=...
   ```
4. Check: `python3 ~/vyn-memory/skills/vyn-memory/memory.py search test`.

`git -C ~/vyn-memory pull` updates the skill.

## Tests

```sh
python3 -m unittest -q test_memory
```

## License

MIT, see [LICENSE](LICENSE).
