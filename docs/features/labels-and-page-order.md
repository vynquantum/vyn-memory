# Confluence-Style Labels & Ordered Study Pages

## What it does
- Adds Confluence-like **Labels (Tags)** navigation to the `vyn-memory` web UI and REST API without adding extra containers or breaking live Obsidian vault sync.
- Supports optional integer **`order:`** frontmatter metadata (with `00-`, `master-`, `README.md` pinned to `0`, and numeric filename prefixes like `01-` auto-parsed) so study tracks (e.g. DSA) stay in exact learning order instead of alphabetical order.

## How to use it
- **Web UI (`https://memory.vynquantum.com/`):**
  - Click **Labels** in the top bar (`?scope=career&view=tags`) or open the **Labels** drawer in the left sidebar.
  - Click any label (e.g., **`#dsa`**) to open `?scope=career&tag=dsa`: shows all matching pages in study order, auto-surfaced **Sub-topics** chips (`#bitwise`, `#strings`, `#linked-list`, `#queues`, `#allocators`, `#concurrency`, etc.), and filters the left sidebar tree.
  - Click any page inside a label view to read with a **`← Back to #<tag>`** banner, clickable **Page Labels**, and a **Prev / Next pager** that steps through that label's ordered sequence.
- **REST API:**
  - `GET /api/v1/tags?scope=career` — list labels and page counts.
  - `GET /api/v1/notes?scope=career&tag=dsa` — list notes carrying a label, sorted by `(sort_order, path)`.
  - `POST /api/v1/note` — accepts optional integer `"order"` persisted into YAML frontmatter.

## How it works
- `notes.sort_order` (`INTEGER NOT NULL DEFAULT 1000`) is added via idempotent migration in `ensure_schema_migrations()` and indexed on every vault scan (`sync_vault_notes`) and write (`op_write_note`).
- `_normalize_tag()` and `_note_tags_norm()` normalize frontmatter tags across `op_list_notes`, `op_list_tags`, and `render_dashboard_page`.
- Zero client-side JavaScript required; strict CSP and `impeccable detect` (0 non-advisory warnings across light and dark themes) preserved.

## Where it lives
- `repos/vyn-memory/server.py` (`ensure_schema_migrations`, `_parse_sort_order`, `_normalize_tag`, `op_list_notes`, `op_list_tags`, `render_dashboard_page`, `MemoryHTTPHandler`).
- `repos/vyn-memory/test_memory.py` (`test_confluence_tag_navigation_and_study_order`).
- `dockers/vynstack/memory.json` (`dashboard.pinned` Quick Access entries).

## Still to do
- Optional multi-tag intersection filtering (`?tag=dsa+bitwise`) if ever needed.
