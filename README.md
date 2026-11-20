# vyn-memory

One shared memory for all your AI agents. Claude, ChatGPT/Codex, Antigravity and
Hermes (with its profiles) read and write the same memory, so what one agent learns
the others can use.

It keeps two things in step:

- **Facts**: short statements in SQLite (`memory.db`, full-text search). A fact is
  valid from when it is saved until it is retired or replaced, and the history stays.
  Agents can fact-check claims against active facts, retired history, and notes via
  `memory_check_facts` / `memory.py check-fact`, and `remember` flags `potential_conflicts`.
- **Notes**: an Obsidian vault of Markdown, PDF and DOCX files. Notes are indexed for
  search, `- [category] text #tag` lines become searchable observations, and
  `[[links]]` / `- relation [[Note]]` lines become a graph that `context` follows.

One Python file, standard library only (`pypdf` is optional, for PDF text).

## Ways in

| Client | How |
| :--- | :--- |
| Agents that can run commands (Claude Code, Codex, Antigravity, Hermes) | the skill in `skills/vyn-memory/`: `memory.py` calls the REST API |
| Apps that cannot (claude.ai, ChatGPT, phone apps) | MCP connector at `<your address>/mcp` (OAuth 2.1 + PKCE) or `/sse` |
| You, in a browser | the dashboard at `<your address>/` (browse, search, upload, add/retire AI facts), and **Connected apps** at `/apps` |
| Anything else | REST API under `/api/v1/` (including `/api/v1/fact-check`), described at `/openapi.json` |

The skill only loads its instructions when a task needs memory, so it costs far fewer
tokens per request than an always-loaded MCP tool list.

## Run it (30-second Quick Start)

### Option 1: Docker Compose (zero build, standard library only)

```sh
git clone https://github.com/vynquantum/vyn-memory.git && cd vyn-memory
cp .env.example .env
# Generate fresh random role tokens and append them to .env:
python3 -c 'import secrets; [print(f"MEMORY_{r}_TOKEN={secrets.token_urlsafe(32)}") for r in ("OWNER","CLAUDE","CHATGPT","ANTIGRAVITY","HERMES")]' >> .env
docker compose up -d
```

Open `http://127.0.0.1:8770`, sign in with `MEMORY_OWNER_TOKEN` from `.env`, and click **Apps** for your MCP URL and laptop login command. (Keep `.env` private; `.gitignore` already excludes `.env`, `data/`, `vault/`, and `settings.json`.)

### Option 2: Plain Python (no Docker)

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
| `MEMORY_OAUTH_REDIRECT_HOSTS` | hosts allowed to receive OAuth codes (default `claude.ai,claude.com,chatgpt.com,chat.openai.com`; loopback is always allowed) |
| `OMNI_PUBLIC_URL`, `OMNI_INTERNAL_URL`, `OMNI_MEMORY_KEY`, `MEMORY_ADMIN_EMAILS` | optional sign-in through an Omni server; only the listed emails get in (when unset, `/login` opens directly to the owner-token form) |

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
| `dashboard` | title, sidebar groups and rules, scope pills, pinned notes, landing note, upload scopes |

Starter notes for your areas belong in your vault (or a template you copy into it), not in settings.

## Who may do what

- Every agent reads everything except `personal/`, which nothing reaches through the server.
- Agents write only to the open scopes and to their own `agents/<name>` folder; Hermes
  profiles also share `agents/{hermes,decisions,gotchas,playbooks,research}`.
- The owner (owner token, or an Omni sign-in for an email in `MEMORY_ADMIN_EMAILS`) can
  write everywhere and is the only one who can open the dashboard, add/retire facts from the web UI, and download files.
- Connector logins (OAuth) stay valid only while the credential that approved them does: rotating an
  agent token, or removing an email from `MEMORY_ADMIN_EMAILS`, ends them. Owner credentials cannot be
  turned into OAuth tokens, and browser sessions opened with the owner token end when it changes.
- The vault is read and written through directory file descriptors that never follow a symlink.
- Tokens travel only in the `Authorization` header (or `X-API-Key`), never in a URL, because URLs end up
  in logs and browser history. Old `/s/<token>/...` addresses answer 410.
- Each laptop or app gets its own token through `memory.py login`, labelled with the app, user, device
  and OS that asked for it. **Connected apps** (`/apps`) lists every device login, connector login and
  browser session with when it was added and last used, and revokes any of them at once.
- The role tokens are for apps on the server itself; rotate one by changing it and restarting.
- Notes render with a strict Content-Security-Policy (no scripts), browser forms use session- and
  purpose-bound CSRF tokens, uploads and request bodies have size limits, failed sign-ins and
  device codes are rate limited, and paths cannot leave the vault.

## Use it from another machine

1. Get the skill: `git clone https://github.com/vynquantum/vyn-memory.git ~/vyn-memory`.
2. Link it where your agents look for skills, for example:
   ```sh
   for d in ~/.claude/skills ~/.codex/skills ~/.gemini/skills; do
     mkdir -p "$d" && ln -sfn ~/vyn-memory/skills/vyn-memory "$d/vyn-memory"
   done
   ```
3. Log in once from each app's copy, so the server knows which app it is:
   ```sh
   python3 ~/.claude/skills/vyn-memory/memory.py login https://memory.example.com   # Claude Code
   python3 ~/.codex/skills/vyn-memory/memory.py login https://memory.example.com    # Codex
   ```
   It prints a link and a code. Open the link (or `/device`) on any device where you are signed in as the owner,
   check the code matches, and approve. The token is saved to `~/.config/vyn-memory.env` (mode 600).
4. Check: `python3 ~/.claude/skills/vyn-memory/memory.py search test` or `check-fact "release process"`.

`git -C ~/vyn-memory pull` updates the skill.

## Tests

```sh
python3 -m unittest -q test_memory
```

## License

MIT, see [LICENSE](LICENSE).
