---
name: vyn-memory
description: Shared memory server for every agent (Claude, ChatGPT/Codex, Antigravity, Hermes) - remembered facts plus the Obsidian vault notes. Use it to look up or save anything that should carry across apps and sessions.
---

# Vyn Memory (`vyn-memory`)

Use this skill to read or save anything that should carry across apps and sessions: facts about
the owner's work and preferences, project decisions, and notes in the shared Obsidian vault.

## How it works

`memory.py` (in this folder) is a small client. Every command is an HTTPS call to the memory
server, which keeps the database (`memory.db`, with full-text search) and the vault notes in step.
It never edits files itself, so it works the same from Hermes, the server or a laptop.

- **Address:** `MEMORY_HUB_URL` from the environment or the token file below; otherwise
  `http://vyn-memory:8770` inside Hermes and `http://127.0.0.1:8770` elsewhere.
- **Who you are:** each app has a role token (`claude`, `chatgpt`, `antigravity`, `hermes`).
  Hermes has its token already. Elsewhere, put the token and address in `~/.config/vyn-memory.env`
  (`MEMORY_CLAUDE_TOKEN=...`, `MEMORY_HUB_URL=https://...`) and `chmod 600` it.
  Never print a token or put it on a command line.
- **Phone apps** (claude.ai, ChatGPT) cannot run commands; they use the MCP connector at
  `<server address>/mcp`, which reaches the same server.

## What goes where (scopes)

The server enforces who may write where; reads are open to every agent except `personal/*`.
A server may add its own areas (for example `career/...`); `briefing` lists the scopes you can write.

| Scope | Who can write | Use for |
| :--- | :--- | :--- |
| `projects/<slug>` | all agents | project notes and decisions |
| `shared` | all agents | preferences and facts that apply everywhere |
| `resources/books` | all agents | large reference documents (kept apart so they don't flood searches) |
| `agents/<your-name>` | only you | your own working memory (Hermes: your profile name) |
| `agents/{hermes,decisions,gotchas,playbooks,research}` | any Hermes profile | shared Hermes know-how |
| `business/*`, `daily`, `inbox` | owner (a server may open some to Hermes, e.g. `business/clients`) | read-only for agents |
| `personal/*` | nobody | never reachable through this skill |

Fact categories: `fact`, `decision`, `preference`, `progress`, `strength`, `weakness`, `question`.
Saving a `progress`/`strength`/`weakness` fact with the same `--subject` in the same scope
automatically retires the older one, so history stays without contradictions.

## Commands

`M` below means `python3 <this skill's folder>/memory.py`. In Hermes:
`/opt/hermes/.venv/bin/python /opt/data/skills/vynstack/vyn-memory/memory.py`.

```sh
M briefing --scope projects/<slug>     # start of a session: facts + the 40 newest notes of that scope
M search "<words>" [--scope <scope>] [--validity valid|invalid|all]
M read-note <path.md>                  # one note in full
M context <path-or-subject> --depth 1  # a note plus what links to it, with related facts
M remember --scope <scope> --category <category> --subject <slug> "<one self-contained statement>"
M forget <fact-id> --reason "<why>"    # retire a wrong or outdated fact (kept in history)
M write-note <path.md> --title "<title>" --summary "<one line>" --tags "a,b" --mode replace|append|section < note.md
M upload <file.pdf|.docx|.md> --scope <scope> --title "<title>"
M list-notes [--scope <scope>]         # the whole index; large, prefer search
```

In a note, `- [category] text #tag` lines are indexed as searchable observations, and
`- relation [[Other Note]]` lines become links that `context` follows.

**Keep answers small:** use `search` or `read-note` for specifics; `list-notes` without a scope
returns every note in the vault.

**Installing:** see the server repository's README → "Use it from another machine".
