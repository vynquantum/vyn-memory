#!/usr/bin/env python3
"""Unit and integration tests for Vyn Memory (`server.py`)."""
from __future__ import annotations

import base64
import hashlib
import importlib.util
import io
import json
import os
import sys
import tempfile
import threading
import time
import unittest
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from http.server import ThreadingHTTPServer
from pathlib import Path


def _load_server():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location("vyn_memory_server", here / "server.py")
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    sys.modules["vyn_memory_server"] = mod
    spec.loader.exec_module(mod)
    return mod


class TestVynMemory(unittest.TestCase):
    def setUp(self) -> None:
        self.tmpdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tmpdir.name)
        self.data_dir = self.root / "data"
        self.vault_dir = self.root / "vault"
        self.env_patch = {
            "MEMORY_DATA_DIR": str(self.data_dir),
            "MEMORY_VAULT_DIR": str(self.vault_dir),
            "MEMORY_OWNER_TOKEN": "tok-owner-test",
            "MEMORY_HERMES_TOKEN": "tok-hermes-test",
            "MEMORY_CLAUDE_TOKEN": "tok-claude-test",
            "MEMORY_CHATGPT_TOKEN": "tok-chatgpt-test",
            "MEMORY_ANTIGRAVITY_TOKEN": "tok-antigravity-test",
            "MEMORY_PUBLIC_URL": "https://memory.example.com",
            "OMNI_PUBLIC_URL": "https://omni.example.com",
            "MEMORY_ADMIN_EMAILS": "owner@example.com",
            "MEMORY_SETTINGS": str(Path(__file__).resolve().parent / "settings.example.json"),
        }
        self._old_env = {k: os.environ.get(k) for k in self.env_patch}
        os.environ.update(self.env_patch)
        self.srv = _load_server()
        self.conn = self.srv.open_db()
        # Starter notes a deployment ships in its own vault template.
        for rel in ("career/00-Read-Before-Interview.md", "career/company/README.md"):
            (self.vault_dir / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.vault_dir / rel).write_text(f"---\ntitle: {Path(rel).stem}\n---\n\n# {Path(rel).stem}\n\n| Scope | Focus |\n| :--- | :--- |\n| `career/company/acme` | Example |\n", encoding="utf-8")
        self.srv.seed_initial_scaffold(self.conn)

    def tearDown(self) -> None:
        self.conn.close()
        for k, v in self._old_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        self.tmpdir.cleanup()

    def test_scope_normalization_and_hermes_subagent_permissions(self) -> None:
        self.assertEqual(self.srv.normalize_scope(""), "shared")
        self.assertEqual(self.srv.normalize_scope("career"), "career")
        self.assertEqual(self.srv.normalize_scope("interview-prep"), "career")
        self.assertEqual(self.srv.normalize_scope("projects/interview-prep"), "career")
        self.assertEqual(self.srv.normalize_scope("embedded"), "career/embedded")
        self.assertEqual(self.srv.normalize_scope("c"), "career/embedded/c")
        self.assertEqual(self.srv.normalize_scope("linux"), "career/embedded/linux")
        self.assertEqual(self.srv.normalize_scope("os"), "career/embedded/os")
        self.assertEqual(self.srv.normalize_scope("system-design"), "career/embedded/system-design")
        self.assertEqual(self.srv.normalize_scope("career/embedded/rtos-concurrency"), "career/embedded/rtos-concurrency")
        self.assertEqual(self.srv.normalize_scope("company"), "career/company")
        self.assertEqual(self.srv.normalize_scope("companies"), "career/company")
        self.assertEqual(self.srv.normalize_scope("acme"), "career/company/acme")
        self.assertEqual(self.srv.normalize_scope("acmee"), "career/company/acme")
        self.assertEqual(self.srv.normalize_scope("career/companies/acmee"), "career/company/acme")
        self.assertEqual(self.srv.normalize_scope("projects/System Design"), "projects/system-design")
        self.assertEqual(self.srv.normalize_scope("claude"), "agents/claude")
        self.assertEqual(self.srv.normalize_scope("agents/hermes"), "agents/hermes")
        self.assertEqual(self.srv.normalize_scope("main"), "agents/default")
        self.assertEqual(self.srv.normalize_scope("default"), "agents/default")
        self.assertEqual(self.srv.normalize_scope("upgrade"), "agents/upgrade")
        self.assertEqual(self.srv.normalize_scope("hermes/reviewer"), "agents/reviewer")
        self.assertEqual(self.srv.normalize_scope("agents/gotchas"), "agents/gotchas")
        self.assertNotIn("alien-x", self.srv.HERMES_SUBAGENTS)

        # Everyone (including Hermes sub-agents) can write to career/*, shared, and projects/*
        for actor in ("claude", "chatgpt", "hermes", "hermes/default", "hermes/upgrade", "hermes/reviewer", "antigravity", "owner"):
            self.srv.check_write_permission(actor, "shared")
            self.srv.check_write_permission(actor, "career")
            self.srv.check_write_permission(actor, "career/embedded/linux")
            self.srv.check_write_permission(actor, "career/company/acme")
            self.srv.check_write_permission(actor, "projects/vynstack")

        # External AI tools can write ONLY their own agents/<tool> scope
        for actor in ("claude", "chatgpt", "antigravity"):
            self.srv.check_write_permission(actor, f"agents/{actor}")

        # Hermes sub-agents can write their own agents/<subagent> scope AND shared Hermes folders
        self.srv.check_write_permission("hermes/default", "agents/default")
        self.srv.check_write_permission("hermes/upgrade", "agents/upgrade")
        self.srv.check_write_permission("hermes/upgrade", "agents/gotchas")
        self.srv.check_write_permission("hermes/upgrade", "agents/decisions")
        self.srv.check_write_permission("hermes/reviewer", "agents/reviewer")

        # Cross-subagent and cross-agent write is strictly forbidden (403)
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.check_write_permission("hermes/upgrade", "agents/reviewer")
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.check_write_permission("hermes/reviewer", "agents/upgrade")
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.check_write_permission("hermes/upgrade", "agents/claude")
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.check_write_permission("claude", "agents/upgrade")
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.check_write_permission("claude", "agents/gotchas")
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.check_write_permission("chatgpt", "agents/antigravity")
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.check_write_permission("owner", "personal/goals")

    def test_temporal_fact_validity_superseding_and_invalidation(self) -> None:
        # 1. Claude records an interview weakness in career/embedded/system-design -> valid
        f1_res = self.srv.op_remember_fact(
            self.conn,
            "claude",
            scope="career/embedded/system-design",
            category="weakness",
            subject="Consistent Hashing",
            fact="Needs practice on virtual nodes and rebalance bounds.",
            supersede_subject=True,
        )
        f1 = f1_res["fact"]
        self.assertEqual(f1["status"], "active")
        self.assertEqual(f1["validity"], "valid")
        self.assertTrue(f1["is_valid"])

        # 2. ChatGPT later records strength on the same subject -> automatically marks f1 invalid (superseded)
        f2_res = self.srv.op_remember_fact(
            self.conn,
            "chatgpt",
            scope="career/embedded/system-design",
            category="strength",
            subject="Consistent Hashing",
            fact="Mastered virtual nodes, K-log-N ring lookup, and bounded load.",
            supersede_subject=True,
        )
        f2 = f2_res["fact"]
        self.assertEqual(f2["status"], "active")
        self.assertEqual(f2["validity"], "valid")
        self.assertIn(f1["id"], f2_res["superseded_ids"])

        # 3. Search with validity='valid' returns only f2; validity='invalid' returns f1
        valid_only = self.srv.op_search(self.conn, query="Consistent", validity="valid")
        self.assertEqual([x["id"] for x in valid_only["facts"]], [f2["id"]])

        invalid_only = self.srv.op_search(self.conn, query="Consistent", validity="invalid")
        self.assertEqual([x["id"] for x in invalid_only["facts"]], [f1["id"]])
        self.assertFalse(invalid_only["facts"][0]["is_valid"])
        self.assertEqual(invalid_only["facts"][0]["validity"], "invalid")
        self.assertIsNotNone(invalid_only["facts"][0]["invalidated_at"])

        # 4. Hermes sub-agent (upgrade) writes a fact to agents/upgrade and invalidates it with reason
        fu_res = self.srv.op_remember_fact(
            self.conn,
            "hermes/upgrade",
            scope="agents/upgrade",
            category="decision",
            subject="Chrome CDP Port",
            fact="Use port 9222 for local debugging.",
        )
        fu = fu_res["fact"]
        self.assertEqual(fu["scope"], "agents/upgrade")
        self.assertEqual(fu["author"], "hermes/upgrade")

        # Another Hermes sub-agent (reviewer) CANNOT invalidate upgrade's fact
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.op_forget_fact(self.conn, "hermes/reviewer", fact_id=fu["id"], reason="Wrong subagent")

        # Upgrade CAN invalidate its own fact
        inv_res = self.srv.op_forget_fact(
            self.conn,
            "hermes/upgrade",
            fact_id=fu["id"],
            reason="Port changed to 9223",
            resolution="invalidated",
        )
        self.assertEqual(inv_res["status"], "invalidated")
        self.assertEqual(inv_res["validity"], "invalid")
        self.assertFalse(inv_res["fact"]["is_valid"])
        self.assertEqual(inv_res["fact"]["invalidated_reason"], "Port changed to 9223")

    def test_unified_vault_indexing_graph_links_and_personal_exclusion(self) -> None:
        # 1. Existing Obsidian vault files (e.g. agents/gotchas/, business/) are indexed, while personal/ is skipped
        gotcha_file = self.vault_dir / "agents/gotchas/docker-dns-timeout.md"
        gotcha_file.parent.mkdir(parents=True, exist_ok=True)
        gotcha_file.write_text(
            "---\ntype: gotcha\nsymptom: Container DNS lookup hangs\nagent: upgrade\n---\n\n# Docker DNS Timeout\n\nCheck `/etc/resolv.conf`.\n",
            encoding="utf-8",
        )
        personal_file = self.vault_dir / "personal/goals/private-goal.md"
        personal_file.parent.mkdir(parents=True, exist_ok=True)
        personal_file.write_text("# Strictly Private Goal\n\nSecret personal note.\n", encoding="utf-8")

        search_gotcha = self.srv.op_search(self.conn, query="resolv")
        self.assertTrue(any("agents/gotchas/docker-dns-timeout.md" == n["path"] for n in search_gotcha["notes"]))

        search_personal = self.srv.op_search(self.conn, query="Strictly Private")
        self.assertEqual(len(search_personal["notes"]), 0)
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.op_read_note(self.conn, "personal/goals/private-goal.md")

        # 2. Create a study note with Basic-Memory-style inline observations, relations, and [[wikilink]]
        self.srv.op_write_note(
            self.conn,
            "antigravity",
            path="career/embedded/system-design/System-Design-Notes.md",
            title="System Design Notes",
            content=(
                "## Observations\n\n"
                "- [weakness] Forgot bounded-load consistent hashing tradeoff #caching #ring\n"
                "- [decision] Always clarify read:write ratio in first 2 minutes #framework\n\n"
                "## Relations\n\n"
                "- part_of [[00-Read-Before-Interview]]\n"
                "- relates_to [[agents/gotchas/docker-dns-timeout]]\n"
            ),
            mode="replace",
            tags=["interview", "system-design"],
        )

        note = self.srv.op_read_note(self.conn, "career/embedded/system-design/System-Design-Notes.md")
        self.assertEqual(note["scope"], "career/embedded/system-design")
        self.assertIn("00-read-before-interview", note["outgoing_links"])
        self.assertTrue(any(r["relation"] == "part_of" for r in note["relations"]))
        self.assertEqual(len(note["observations"]), 2)
        self.assertEqual(note["observations"][0]["category"], "weakness")
        self.assertIn("caching", note["observations"][0]["tags"])

        # 1-hop connected note summary includes both linked notes
        connected_paths = [c["path"] for c in note["connected_notes"]]
        self.assertIn("career/00-Read-Before-Interview.md", connected_paths)
        self.assertIn("agents/gotchas/docker-dns-timeout.md", connected_paths)

        # 3. Search inline observations by category and query
        obs_search = self.srv.op_search(self.conn, query="bounded-load", category="weakness")
        self.assertEqual(len(obs_search["observations"]), 1)
        self.assertEqual(obs_search["observations"][0]["source_path"], "career/embedded/system-design/System-Design-Notes.md")

        # 4. Multi-hop context builder (op_build_context)
        ctx = self.srv.op_build_context(self.conn, "career/embedded/system-design/System-Design-Notes.md", depth=1)
        self.assertEqual(ctx["root_note"]["path"], "career/embedded/system-design/System-Design-Notes.md")
        self.assertEqual(len(ctx["connected_notes"]), 2)
        self.assertGreaterEqual(len(ctx["inline_observations"]), 2)

        # 5. Confluence-style knowledge base, TOC outline, breadcrumbs & human-readable math assertions
        dash_html = self.srv.render_dashboard_page(
            self.conn,
            "owner",
            selected_note="career/company/README.md",
            scope_filter="career",
        )
        self.assertIn('class="mobile-tabs"', dash_html)
        self.assertIn('id="tab-reader"', dash_html)
        self.assertIn('class="scope-strip"', dash_html)
        self.assertIn('class="table-wrap"', dash_html)
        self.assertIn('class="tree-group"', dash_html)
        self.assertIn('class="toc-nav"', dash_html)
        self.assertIn('class="breadcrumbs"', dash_html)

        md_rendered = self.srv.render_markdown_html(
            "# Power Budgets\n\n## Sleep Modes\n\nCompare ($\\mu$A sleep vs wall power) and $2^{16}$ with $\\approx 130\\text{ us}$.\n\n1. First step\n2. Second step\n"
        )
        self.assertIn("(µA sleep vs wall power)", md_rendered)
        self.assertNotIn("\\mu", md_rendered)
        self.assertIn("2¹⁶", md_rendered)
        self.assertIn("≈ 130 us", md_rendered)
        self.assertIn("<ol>", md_rendered)
        self.assertIn('id="sec-2-sleep-modes"', md_rendered)
        toc = self.srv.extract_toc_headings("# Power Budgets\n\n## Sleep Modes\n\n### Deep Sleep\n")
        self.assertEqual(len(toc), 2)
        self.assertEqual(toc[0]["id"], "sec-2-sleep-modes")
        self.assertEqual(toc[1]["id"], "sec-3-deep-sleep")

    def test_http_mcp_subagent_header_and_oauth(self) -> None:
        httpd = ThreadingHTTPServer(("127.0.0.1", 0), self.srv.MemoryHTTPHandler)
        httpd.db = self.conn  # type: ignore[attr-defined]
        port = httpd.server_address[1]
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        base = f"http://127.0.0.1:{port}"
        try:
            # 1. Hermes sub-agent header refines actor to hermes/upgrade
            req_upg = urllib.request.Request(
                f"{base}/api/v1/briefing",
                headers={
                    "Authorization": "Bearer tok-hermes-test",
                    "X-Hermes-Subagent": "upgrade",
                },
            )
            with urllib.request.urlopen(req_upg) as resp:
                brief = json.loads(resp.read().decode())
                self.assertEqual(brief["authenticated_actor"], "hermes/upgrade")
                self.assertIn("agents/upgrade", brief["permissions"]["writable_scopes"])

            # 2. Hermes sub-agent upgrade trying to write to agents/reviewer over HTTP returns 403
            bad_write = urllib.request.Request(
                f"{base}/api/v1/remember",
                data=json.dumps({
                    "scope": "agents/reviewer",
                    "fact": "Should be rejected",
                }).encode(),
                headers={
                    "Authorization": "Bearer tok-hermes-test",
                    "X-Hermes-Subagent": "upgrade",
                    "Content-Type": "application/json",
                },
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(bad_write)
            self.assertEqual(ctx.exception.code, 403)
            ctx.exception.close()

            # 3. MCP Streamable HTTP with a Bearer header
            mcp_url = f"{base}/mcp"
            call_ok = urllib.request.Request(
                mcp_url,
                data=json.dumps({
                    "jsonrpc": "2.0",
                    "id": 2,
                    "method": "tools/call",
                    "params": {
                        "name": "memory_remember_fact",
                        "arguments": {
                            "scope": "agents/claude",
                            "category": "progress",
                            "subject": "Mock Session #1",
                            "fact": "Completed 45-minute distributed cache design.",
                        },
                    },
                }).encode(),
                headers={"Content-Type": "application/json", "Authorization": "Bearer tok-claude-test"},
                method="POST",
            )
            with urllib.request.urlopen(call_ok) as resp:
                res_ok = json.loads(resp.read().decode())
                self.assertFalse(res_ok["result"]["isError"])

            # 4. OAuth 2.1 + PKCE flow
            verifier = "test-pkce-verifier-string-1234567890"
            challenge = base64.urlsafe_b64encode(hashlib.sha256(verifier.encode()).digest()).decode().rstrip("=")
            auth_form = urllib.parse.urlencode({
                "client_id": "claude-web",
                "redirect_uri": "https://claude.ai/api/mcp/auth_callback",
                "state": "xyz123",
                "code_challenge": challenge,
                "code_challenge_method": "S256",
                "token": "tok-claude-test",
            }).encode()

            class NoRedirect(urllib.request.HTTPRedirectHandler):
                def redirect_request(self, req, fp, code, msg, headers, newurl):
                    return None

            opener = urllib.request.build_opener(NoRedirect)
            auth_req = urllib.request.Request(f"{base}/oauth/authorize", data=auth_form, method="POST")
            try:
                opener.open(auth_req)
                self.fail("Expected 302 redirect")
            except urllib.error.HTTPError as e:
                self.assertEqual(e.code, 302)
                loc = e.headers["Location"]
                e.close()
            parsed_loc = urllib.parse.urlparse(loc)
            qs = urllib.parse.parse_qs(parsed_loc.query)
            code = qs["code"][0]

            token_form = urllib.parse.urlencode({
                "grant_type": "authorization_code",
                "code": code,
                "code_verifier": verifier,
            }).encode()
            tok_req = urllib.request.Request(f"{base}/oauth/token", data=token_form, method="POST")
            with urllib.request.urlopen(tok_req) as resp:
                tok_data = json.loads(resp.read().decode())
                access_token = tok_data["access_token"]

            rest_req = urllib.request.Request(
                f"{base}/api/v1/briefing?scope=agents/claude",
                headers={"Authorization": f"Bearer {access_token}"},
            )
            with urllib.request.urlopen(rest_req) as resp:
                brief = json.loads(resp.read().decode())
                self.assertEqual(brief["authenticated_actor"], "claude")
                self.assertEqual(len(brief["agent_specific_facts"]["agents/claude"]), 1)
        finally:
            httpd.shutdown()
            httpd.server_close()

    def test_security_audit_hardening(self) -> None:
        # 1. Sub-agent privilege override blocked & bare 'hermes' blocked from agents/<subagent>
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.normalize_actor("hermes/upgrade", "reviewer")
        self.assertFalse(self.srv.can_write("hermes", "agents/reviewer"))
        self.assertTrue(self.srv.can_write("hermes", "agents/hermes"))
        self.assertTrue(self.srv.can_write("hermes", "agents/gotchas"))

        # 2. Symlink escape to personal/ or outside vault rejected by sync, read, and write
        personal_dir = self.vault_dir / "personal"
        personal_dir.mkdir(parents=True, exist_ok=True)
        secret_file = personal_dir / "private.md"
        secret_file.write_text("# Top Secret Personal Note\n", encoding="utf-8")

        shared_dir = self.vault_dir / "shared"
        shared_dir.mkdir(parents=True, exist_ok=True)
        symlink_note = shared_dir / "leak.md"
        symlink_note.symlink_to(secret_file)

        self.srv.sync_vault_notes(self.conn)
        indexed_paths = [n["path"] for n in self.srv.op_list_notes(self.conn)["notes"]]
        self.assertNotIn("shared/leak.md", indexed_paths)

        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.op_write_note(
                self.conn,
                "claude",
                path="shared/leak.md",
                content="Attempted overwrite via symlink",
            )
        self.assertEqual(secret_file.read_text(encoding="utf-8"), "# Top Secret Personal Note\n")
        symlink_note.unlink()

        # 3. Frontmatter scope spoofing ignored; scope derived from canonical vault directory
        biz_dir = self.vault_dir / "business"
        biz_dir.mkdir(parents=True, exist_ok=True)
        spoof_file = biz_dir / "spoofed.md"
        spoof_file.write_text(
            "---\ntitle: Spoofed\nscope: shared\n---\n\n# Spoofed Scope\n",
            encoding="utf-8",
        )
        self.srv.sync_vault_notes(self.conn)
        spoof_meta = self.srv.op_read_note(self.conn, "business/spoofed.md")
        self.assertEqual(spoof_meta["scope"], "business")

        # 4. HTTP-level security checks (XSS, Cookie CSRF isolation, OAuth open redirect & PKCE, 413 body limit)
        httpd = ThreadingHTTPServer(("127.0.0.1", 0), self.srv.MemoryHTTPHandler)
        httpd.db = self.conn  # type: ignore[attr-defined]
        port = httpd.server_address[1]
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        base = f"http://127.0.0.1:{port}"
        try:
            # 4a. Owner dashboard carries CSP and framing headers
            dash_req = urllib.request.Request(f"{base}/", headers={"Cookie": "__Host-vyn_memory_token=tok-owner-test"})
            with urllib.request.urlopen(dash_req) as resp:
                html_body = resp.read().decode()
                csp = resp.headers.get("Content-Security-Policy", "")
                self.assertIn("default-src 'none'", csp)
                self.assertEqual(resp.headers.get("X-Frame-Options"), "DENY")
                self.assertEqual(resp.headers.get("X-Content-Type-Options"), "nosniff")
                self.assertIn('action="/"', html_body)
                self.assertIn('href="/apps"', html_body)

            # 4b. Token URLs are gone: /s/<token>/... answers 410 even with a valid token, ?token= is ignored
            for path in ("/s/tok-owner-test/", "/s/tok-claude-test/mcp"):
                with self.assertRaises(urllib.error.HTTPError) as ctx:
                    urllib.request.urlopen(urllib.request.Request(f"{base}{path}"))
                self.assertEqual(ctx.exception.code, 410)
                ctx.exception.close()
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(urllib.request.Request(f"{base}/api/v1/briefing?token=tok-claude-test"))
            self.assertEqual(ctx.exception.code, 401)
            ctx.exception.close()

            # 4c. Ambient browser cookie is rejected on POST /api/v1/remember and GET /api/v1/briefing (CSRF protection)
            csrf_post = urllib.request.Request(
                f"{base}/api/v1/remember",
                data=json.dumps({"scope": "shared", "fact": "CSRF attempt"}).encode(),
                headers={
                    "Cookie": "__Host-vyn_memory_token=tok-owner-test",
                    "Content-Type": "application/json",
                },
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(csrf_post)
            self.assertEqual(ctx.exception.code, 401)
            ctx.exception.close()

            csrf_get_api = urllib.request.Request(
                f"{base}/api/v1/briefing",
                headers={"Cookie": "__Host-vyn_memory_token=tok-owner-test"},
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(csrf_get_api)
            self.assertEqual(ctx.exception.code, 401)
            ctx.exception.close()

            # 4d. Sub-agent override via JSON body when X-Hermes-Subagent is set returns 403
            override_req = urllib.request.Request(
                f"{base}/api/v1/remember",
                data=json.dumps({
                    "subagent": "reviewer",
                    "scope": "agents/reviewer",
                    "fact": "Attempted horizontal sub-agent override",
                }).encode(),
                headers={
                    "Authorization": "Bearer tok-hermes-test",
                    "X-Hermes-Subagent": "upgrade",
                    "Content-Type": "application/json",
                },
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(override_req)
            self.assertEqual(ctx.exception.code, 403)
            ctx.exception.close()

            # 4e. OAuth authorize CSP omits form-action 'self' so Chrome allows 302 redirects to redirect_uri
            valid_challenge = base64.urlsafe_b64encode(hashlib.sha256(b"x" * 43).digest()).decode().rstrip("=")
            oauth_get_ok = urllib.request.Request(
                f"{base}/oauth/authorize?client_id=vyn-mcp-test&redirect_uri={urllib.parse.quote('http://127.0.0.1:59631/callback/abc', safe='')}&code_challenge={valid_challenge}&code_challenge_method=S256"
            )
            with urllib.request.urlopen(oauth_get_ok) as resp:
                oauth_csp = resp.headers.get("Content-Security-Policy", "")
                self.assertIn("default-src 'none'", oauth_csp)
                self.assertNotIn("form-action 'self'", oauth_csp)

            class NoRedirectLocal(urllib.request.HTTPRedirectHandler):
                def redirect_request(self, req, fp, code, msg, headers, newurl):
                    return None

            no_redir_opener = urllib.request.build_opener(NoRedirectLocal)

            # 4g. POST /login sets __Host- cookie and redirects to /?scope=career; agent tokens get 403 on GET /
            login_req = urllib.request.Request(
                f"{base}/login",
                data=urllib.parse.urlencode({"token": "tok-owner-test", "next": "/?scope=career"}).encode(),
                method="POST",
            )
            try:
                no_redir_opener.open(login_req)
                self.fail("Expected 303 redirect on /login")
            except urllib.error.HTTPError as e:
                self.assertEqual(e.code, 303)
                self.assertEqual(e.headers.get("Location"), "/?scope=career")
                self.assertIn("__Host-vyn_memory_token=", e.headers.get("Set-Cookie", ""))
                e.close()

            agent_dash_req = urllib.request.Request(
                f"{base}/",
                headers={"Cookie": "__Host-vyn_memory_token=tok-chatgpt-test"},
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(agent_dash_req)
            self.assertEqual(ctx.exception.code, 403)
            ctx.exception.close()

            # 4h. OAuth open redirect (non-HTTPS / non-loopback or javascript:) and missing PKCE rejected with 400
            bad_oauth_get = urllib.request.Request(
                f"{base}/oauth/authorize?client_id=x&redirect_uri=http://evil.example.com/cb&code_challenge=abc"
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(bad_oauth_get)
            self.assertEqual(ctx.exception.code, 400)
            ctx.exception.close()

            no_pkce_post = urllib.request.Request(
                f"{base}/oauth/authorize",
                data=urllib.parse.urlencode({
                    "client_id": "claude-web",
                    "redirect_uri": "https://claude.ai/api/mcp/auth_callback",
                    "token": "tok-claude-test",
                }).encode(),
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(no_pkce_post)
            self.assertEqual(ctx.exception.code, 400)
            ctx.exception.close()

            # 4i. Pre-auth oversized Content-Length rejected with 413 before reading body
            import http.client
            conn_http = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
            conn_http.putrequest("POST", "/oauth/token")
            conn_http.putheader("Content-Type", "application/x-www-form-urlencoded")
            conn_http.putheader("Content-Length", str(10 * 1024 * 1024))
            conn_http.endheaders()
            resp_413 = conn_http.getresponse()
            self.assertEqual(resp_413.status, 413)
            resp_413.read()
            conn_http.close()

            # 4j. claude.ai's sequence on one connection: a POST refused before its body is read
            # closes the connection, so the next request is not parsed from the leftover body (was 501)
            init = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}})
            conn_ka = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
            conn_ka.request("POST", "/s/old-token/mcp", init, {"Content-Type": "application/json"})
            resp_410 = conn_ka.getresponse()
            resp_410.read()
            self.assertEqual(resp_410.status, 410)
            self.assertEqual(resp_410.getheader("Connection"), "close")
            conn_ka.request("POST", "/mcp", init, {"Content-Type": "application/json", "Authorization": "Bearer tok-claude-test"})
            resp_ok = conn_ka.getresponse()
            resp_ok.read()
            self.assertEqual(resp_ok.status, 200)
            conn_ka.close()

            # 4j. Per-IP brute-force rate limiting returns 429 after MAX_AUTH_FAILURES_PER_WINDOW failed attempts
            self.srv._clear_auth_failures("127.0.0.1")
            for _ in range(self.srv.MAX_AUTH_FAILURES_PER_WINDOW):
                bad_tok_req = urllib.request.Request(
                    f"{base}/api/v1/briefing",
                    headers={"Authorization": "Bearer wrong-token-guess"},
                )
                with self.assertRaises(urllib.error.HTTPError) as ctx:
                    urllib.request.urlopen(bad_tok_req)
                self.assertEqual(ctx.exception.code, 401)
                ctx.exception.close()
            rate_limited_req = urllib.request.Request(
                f"{base}/api/v1/briefing",
                headers={"Authorization": "Bearer tok-owner-test"},
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(rate_limited_req)
            self.assertEqual(ctx.exception.code, 429)
            ctx.exception.close()
            self.srv._clear_auth_failures("127.0.0.1")
        finally:
            httpd.shutdown()
            httpd.server_close()

    def test_public_deployment_defaults(self) -> None:
        # An Omni session counts as owner only for an email listed in MEMORY_ADMIN_EMAILS.
        sess = self.srv._mint_web_session(self.conn, "owner@example.com")
        self.assertEqual(self.srv.resolve_actor_from_token(sess, self.conn), "owner")
        os.environ["MEMORY_ADMIN_EMAILS"] = ""
        self.srv.MEMORY_ADMIN_EMAILS = set()
        self.assertIsNone(self.srv.resolve_actor_from_token(sess, self.conn))
        # CF-Connecting-IP is trusted only behind Cloudflare.
        hdrs = {"CF-Connecting-IP": "203.0.113.9"}
        self.assertEqual(self.srv._client_ip(hdrs, ("10.0.0.2", 1)), "10.0.0.2")
        os.environ["MEMORY_BEHIND_CLOUDFLARE"] = "1"
        try:
            self.assertEqual(self.srv._client_ip(hdrs, ("10.0.0.2", 1)), "203.0.113.9")
        finally:
            os.environ.pop("MEMORY_BEHIND_CLOUDFLARE")
        # Aliases can never route a path into personal/.
        self.srv.SCOPE_ALIASES["secret"] = "personal"
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.normalize_note_path("secret/x.md")
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.normalize_scope("secret")

    def test_security_audit_run2_regressions(self) -> None:
        import io, time, zipfile
        srv = self.srv
        # PDF fallback stays linear on unterminated streams and backslash runs.
        start = time.monotonic()
        srv._extract_pdf_text_stdlib(b"%PDF-1.4\n" + b"stream\n" * 8000)
        srv._extract_pdf_text_stdlib(b"%PDF-1.4\nstream\nBT [" + b"\\" * 40 + b"\nendstream\n")
        self.assertLess(time.monotonic() - start, 1.0)
        # OAuth codes only go to allowed connector hosts or loopback.
        self.assertTrue(srv.validate_oauth_redirect_uri("https://claude.ai/api/mcp/auth_callback"))
        self.assertTrue(srv.validate_oauth_redirect_uri("http://127.0.0.1:9/cb"))
        with self.assertRaises(srv.MemoryError):
            srv.validate_oauth_redirect_uri("https://attacker.example.net/cb")
        # A UTF-16 DOCX cannot smuggle a DTD past the guard.
        xml = ('<?xml version="1.0" encoding="UTF-16"?><!DOCTYPE d [<!ENTITY e "AAAAAAAAAA">]>'
               '<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">'
               "<w:body><w:p><w:r><w:t>&e;&e;</w:t></w:r></w:p></w:body></w:document>").encode("utf-16")
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w") as zf:
            zf.writestr("word/document.xml", xml)
        _, body = srv.extract_docx_markdown(Path("x.docx"), buf.getvalue())
        self.assertIn("DTD declarations are not permitted", body)
        # Owner-token browser sessions end when the owner token changes.
        sess = srv._mint_web_session(self.conn, srv.owner_session_email())
        self.assertEqual(srv.resolve_actor_from_token(sess, self.conn), "owner")
        os.environ["MEMORY_OWNER_TOKEN"] = "tok-owner-rotated"
        try:
            self.assertIsNone(srv.resolve_actor_from_token(sess, self.conn))
        finally:
            os.environ["MEMORY_OWNER_TOKEN"] = "tok-owner-test"
        # OAuth tokens live only as long as the credential that approved them.
        parent = "role:" + hashlib.sha256(b"tok-claude-test").hexdigest()
        self.assertTrue(srv.oauth_parent_valid(parent, "claude"))
        os.environ["MEMORY_CLAUDE_TOKEN"] = "tok-claude-rotated"
        try:
            self.assertFalse(srv.oauth_parent_valid(parent, "claude"))
        finally:
            os.environ["MEMORY_CLAUDE_TOKEN"] = "tok-claude-test"
        self.assertTrue(srv.oauth_parent_valid("email:owner@example.com", "claude"))
        self.assertFalse(srv.oauth_parent_valid("email:gone@example.com", "claude"))
        self.assertFalse(srv.oauth_parent_valid("", "owner"))
        # Vault reads never follow a symlink, even one swapped in after the directory walk.
        (self.vault_dir / "shared").mkdir(parents=True, exist_ok=True)
        os.symlink("/etc/hostname", self.vault_dir / "shared" / "link.md")
        with self.assertRaises(srv.MemoryPermissionError):
            srv.read_vault_file("shared/link.md")
        # Writes walk directories without following symlinks too.
        outside = self.root / "outside"
        outside.mkdir()
        os.symlink(outside, self.vault_dir / "shared" / "linkdir")
        with self.assertRaises(srv.MemoryPermissionError):
            srv._vault_dir_fd(["shared", "linkdir"], create=True)
        self.assertEqual(list(outside.iterdir()), [])

    def test_device_login_and_connected_apps(self) -> None:
        httpd = ThreadingHTTPServer(("127.0.0.1", 0), self.srv.MemoryHTTPHandler)
        httpd.db = self.conn  # type: ignore[attr-defined]
        port = httpd.server_address[1]
        threading.Thread(target=httpd.serve_forever, daemon=True).start()
        base = f"http://127.0.0.1:{port}"
        owner = {"Cookie": "__Host-vyn_memory_token=tok-owner-test", "Origin": base}

        def call(path: str, data: object = None, headers: dict[str, str] | None = None) -> tuple[int, str]:
            body = None if data is None else (
                urllib.parse.urlencode(data).encode() if "Cookie" in (headers or {}) else json.dumps(data).encode()
            )
            req = urllib.request.Request(f"{base}{path}", data=body, headers=headers or {})
            try:
                with urllib.request.urlopen(req) as resp:
                    return resp.status, resp.read().decode()
            except urllib.error.HTTPError as exc:
                with exc:
                    return exc.code, exc.read().decode()

        try:
            _, raw = call("/device/code", {"app": "Codex<script>", "user": "veera", "host": "laptop", "os": "Linux 6.8"})
            start = json.loads(raw)
            code, dev = start["user_code"], start["device_code"]
            self.assertEqual(call("/device/token", {"device_code": dev})[1], '{"error": "authorization_pending"}')
            # The approval page needs the owner, shows who is asking, and escapes what the device sent.
            self.assertEqual(call(f"/device?code={code}")[0], 401)
            status, page = call(f"/device?code={code}", headers=owner)
            self.assertEqual(status, 200)
            self.assertIn("Codexscript · veera@laptop · Linux 6.8", page)
            self.assertIn('<option value="chatgpt" selected>', page)
            csrf = page.split('name="csrf_token" value="')[1].split('"')[0]
            # No CSRF token, or another site's Origin: refused.
            self.assertEqual(call("/device", {"code": code, "role": "chatgpt", "decision": "approve"}, owner)[0], 403)
            self.assertEqual(call("/device", {"code": code, "role": "chatgpt", "decision": "approve", "csrf_token": csrf},
                                  {**owner, "Origin": "https://evil.example"})[0], 403)
            self.srv._clear_auth_failures("127.0.0.1")
            self.assertEqual(call("/device", {"code": code, "role": "chatgpt", "decision": "approve", "csrf_token": csrf}, owner)[0], 200)
            got = json.loads(call("/device/token", {"device_code": dev})[1])
            self.assertEqual(got["actor"], "chatgpt")
            tok = got["access_token"]
            self.assertEqual(call("/device/token", {"device_code": dev})[0], 400)  # one token per approval
            auth = {"Authorization": f"Bearer {tok}"}
            self.assertEqual(json.loads(call("/api/v1/briefing", headers=auth)[1])["authenticated_actor"], "chatgpt")
            # Connected apps lists the device and revokes it.
            apps = call("/apps", headers=owner)[1]
            self.assertIn("veera@laptop", apps)
            row_id = apps.split('name="kind" value="token"><input type="hidden" name="id" value="')[1].split('"')[0]
            csrf = apps.split('name="csrf_token" value="')[1].split('"')[0]

            class NoRedirect(urllib.request.HTTPRedirectHandler):
                def redirect_request(self, req, fp, code, msg, headers, newurl):
                    return None

            req = urllib.request.Request(f"{base}/apps", data=urllib.parse.urlencode(
                {"kind": "token", "id": row_id, "csrf_token": csrf}).encode(), headers=owner)
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.build_opener(NoRedirect).open(req)
            self.assertEqual(ctx.exception.code, 303)
            ctx.exception.close()
            self.assertEqual(call("/api/v1/briefing", headers=auth)[0], 401)
            # A denied request gets no token; /apps CSRF token cannot be reused on /device (purpose-scoped).
            start = json.loads(call("/device/code", {"app": "Claude Code"})[1])
            self.assertEqual(call("/device", {"code": start["user_code"], "role": "claude", "decision": "deny", "csrf_token": csrf}, owner)[0], 403)
            deny_page = call(f"/device?code={start['user_code']}", headers=owner)[1]
            device_csrf = deny_page.split('name="csrf_token" value="')[1].split('"')[0]
            call("/device", {"code": start["user_code"], "role": "claude", "decision": "deny", "csrf_token": device_csrf}, owner)
            self.assertEqual(json.loads(call("/device/token", {"device_code": start["device_code"]})[1])["error"], "access_denied")
        finally:
            self.srv._clear_auth_failures("127.0.0.1")
            httpd.shutdown()
            httpd.server_close()

    def test_omni_sso_login_oauth_session_and_refresh_token(self) -> None:
        os.environ["MEMORY_ADMIN_EMAILS"] = "owner@example.com"
        httpd = ThreadingHTTPServer(("127.0.0.1", 0), self.srv.MemoryHTTPHandler)
        httpd.db = self.conn  # type: ignore[attr-defined]
        port = httpd.server_address[1]
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        base = f"http://127.0.0.1:{port}"

        class NoRedirect(urllib.request.HTTPRedirectHandler):
            def redirect_request(self, req, fp, code, msg, headers, newurl):
                return None

        no_redir = urllib.request.build_opener(NoRedirect)
        orig_exchange = self.srv.exchange_omni_handoff
        try:
            # 1. Start Omni SSO flow -> 303 redirect to omni.example.com/hub/signin?state=memory_...
            try:
                no_redir.open(f"{base}/auth/start?next=%2F%3Fscope%3Dcareer")
                self.fail("Expected 303 redirect from /auth/start")
            except urllib.error.HTTPError as e:
                self.assertEqual(e.code, 303)
                loc = e.headers.get("Location", "")
                set_cookie = e.headers.get("Set-Cookie", "")
                e.close()
            self.assertIn("/hub/signin?state=memory_", loc)
            state_val = urllib.parse.parse_qs(urllib.parse.urlsplit(loc).query)["state"][0]
            self.assertIn(state_val, set_cookie)

            # 2. Non-admin member returned by Omni is rejected with 403
            self.srv.exchange_omni_handoff = lambda code: {
                "email": "member@example.com",
                "is_admin": False,
                "active_access": True,
            }
            cb_nonadmin = urllib.request.Request(
                f"{base}/auth/callback?code=code-member&state={state_val}",
                headers={"Cookie": f"__Host-vyn_memory_state={state_val}"},
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                no_redir.open(cb_nonadmin)
            self.assertEqual(ctx.exception.code, 403)
            ctx.exception.close()

            # 3. Start again and complete callback as owner@example.com (is_admin=True)
            try:
                no_redir.open(f"{base}/auth/start?next=%2F%3Fscope%3Dcareer")
                self.fail("Expected 303 redirect from /auth/start")
            except urllib.error.HTTPError as e:
                loc2 = e.headers.get("Location", "")
                e.close()
            state2 = urllib.parse.parse_qs(urllib.parse.urlsplit(loc2).query)["state"][0]
            self.srv.exchange_omni_handoff = lambda code: {
                "email": "owner@example.com",
                "is_admin": True,
                "active_access": False,
            }
            cb_owner = urllib.request.Request(
                f"{base}/auth/callback?code=code-owner&state={state2}",
                headers={"Cookie": f"__Host-vyn_memory_state={state2}"},
            )
            try:
                no_redir.open(cb_owner)
                self.fail("Expected 303 redirect from /auth/callback")
            except urllib.error.HTTPError as e:
                self.assertEqual(e.code, 303)
                self.assertEqual(e.headers.get("Location"), "/?scope=career")
                cookies = e.headers.get_all("Set-Cookie") or []
                e.close()
            sess_cookie_hdr = next(c for c in cookies if "vyn_memory_token=vms_" in c)
            sess_tok = sess_cookie_hdr.split("vyn_memory_token=", 1)[1].split(";", 1)[0]
            self.assertTrue(sess_tok.startswith("vms_"))

            # 4. Owner session cookie grants access to GET / dashboard
            dash_req = urllib.request.Request(
                f"{base}/?scope=career",
                headers={"Cookie": f"__Host-vyn_memory_token={sess_tok}", "Accept": "text/html"},
            )
            with urllib.request.urlopen(dash_req) as resp:
                self.assertEqual(resp.status, 200)
                self.assertIn("Vyn Unified Obsidian Vault", resp.read().decode())

            # 5. One-click OAuth 2.1 approval using Omni session cookie (omni_session=1, role=chatgpt)
            import re as _re
            verifier = "omni-pkce-verifier-string-1234567890-abcdef"
            challenge = base64.urlsafe_b64encode(hashlib.sha256(verifier.encode()).digest()).decode().rstrip("=")
            oauth_get = urllib.request.Request(
                f"{base}/oauth/authorize?response_type=code&client_id=chatgpt-web"
                f"&redirect_uri={urllib.parse.quote('https://chatgpt.com/connector_platform_oauth_redirect', safe='')}"
                f"&state=st99&code_challenge={challenge}&code_challenge_method=S256",
                headers={"Cookie": f"__Host-vyn_memory_token={sess_tok}"},
            )
            with urllib.request.urlopen(oauth_get) as resp:
                html_oauth = resp.read().decode()
                self.assertIn("Omni Owner Session", html_oauth)
                self.assertIn('value="chatgpt" selected', html_oauth)
            m_csrf = _re.search(r'name="csrf_token"\s+value="([^"]+)"', html_oauth)
            self.assertIsNotNone(m_csrf)
            oauth_csrf = m_csrf.group(1) if m_csrf else ""

            # 5a. OAuth omni_session=1 without csrf_token or from Sec-Fetch-Site: same-site is rejected with 401
            oauth_no_csrf = urllib.request.Request(
                f"{base}/oauth/authorize",
                data=urllib.parse.urlencode({
                    "client_id": "chatgpt-web",
                    "redirect_uri": "https://chatgpt.com/connector_platform_oauth_redirect",
                    "state": "st99",
                    "code_challenge": challenge,
                    "code_challenge_method": "S256",
                    "omni_session": "1",
                    "role": "chatgpt",
                }).encode(),
                headers={
                    "Cookie": f"__Host-vyn_memory_token={sess_tok}",
                    "Sec-Fetch-Site": "same-origin",
                },
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_nc:
                no_redir.open(oauth_no_csrf)
            self.assertEqual(ctx_nc.exception.code, 401)
            ctx_nc.exception.close()

            oauth_same_site = urllib.request.Request(
                f"{base}/oauth/authorize",
                data=urllib.parse.urlencode({
                    "client_id": "chatgpt-web",
                    "redirect_uri": "https://chatgpt.com/connector_platform_oauth_redirect",
                    "state": "st99",
                    "code_challenge": challenge,
                    "code_challenge_method": "S256",
                    "omni_session": "1",
                    "csrf_token": oauth_csrf,
                    "role": "chatgpt",
                }).encode(),
                headers={
                    "Cookie": f"__Host-vyn_memory_token={sess_tok}",
                    "Sec-Fetch-Site": "same-site",
                },
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_ss:
                no_redir.open(oauth_same_site)
            self.assertEqual(ctx_ss.exception.code, 401)
            ctx_ss.exception.close()

            self.srv._clear_auth_failures("127.0.0.1")
            oauth_post = urllib.request.Request(
                f"{base}/oauth/authorize",
                data=urllib.parse.urlencode({
                    "client_id": "chatgpt-web",
                    "redirect_uri": "https://chatgpt.com/connector_platform_oauth_redirect",
                    "state": "st99",
                    "code_challenge": challenge,
                    "code_challenge_method": "S256",
                    "omni_session": "1",
                    "csrf_token": oauth_csrf,
                    "role": "chatgpt",
                }).encode(),
                headers={
                    "Cookie": f"__Host-vyn_memory_token={sess_tok}",
                    "Sec-Fetch-Site": "same-origin",
                },
                method="POST",
            )
            try:
                no_redir.open(oauth_post)
                self.fail("Expected 302 redirect on OAuth approval")
            except urllib.error.HTTPError as e:
                self.assertEqual(e.code, 302)
                oauth_loc = e.headers.get("Location", "")
                e.close()
            oauth_code = urllib.parse.parse_qs(urllib.parse.urlsplit(oauth_loc).query)["code"][0]

            # 6. Exchange authorization_code -> access_token + refresh_token, then rotate via grant_type=refresh_token
            tok_req = urllib.request.Request(
                f"{base}/oauth/token",
                data=urllib.parse.urlencode({
                    "grant_type": "authorization_code",
                    "code": oauth_code,
                    "code_verifier": verifier,
                    "client_id": "chatgpt-web",
                }).encode(),
                method="POST",
            )
            with urllib.request.urlopen(tok_req) as resp:
                tok_res = json.loads(resp.read().decode())
            access_1 = tok_res["access_token"]
            refresh_1 = tok_res["refresh_token"]
            self.assertEqual(self.srv.resolve_actor_from_token(access_1, self.conn), "chatgpt")

            refresh_req = urllib.request.Request(
                f"{base}/oauth/token",
                data=urllib.parse.urlencode({
                    "grant_type": "refresh_token",
                    "refresh_token": refresh_1,
                    "client_id": "chatgpt-web",
                }).encode(),
                method="POST",
            )
            with urllib.request.urlopen(refresh_req) as resp:
                ref_res = json.loads(resp.read().decode())
            access_2 = ref_res["access_token"]
            self.assertNotEqual(access_1, access_2)
            self.assertIsNone(self.srv.resolve_actor_from_token(access_1, self.conn))
            self.assertEqual(self.srv.resolve_actor_from_token(access_2, self.conn), "chatgpt")

            # 6b. Revoking email from MEMORY_ADMIN_EMAILS immediately invalidates active web_sessions for that email
            os.environ["MEMORY_ADMIN_EMAILS"] = "other-admin@example.com"
            self.assertIsNone(self.srv.resolve_actor_from_token(sess_tok, self.conn))
            os.environ["MEMORY_ADMIN_EMAILS"] = "owner@example.com"
            self.assertEqual(self.srv.resolve_actor_from_token(sess_tok, self.conn), "owner")

            # 7. Cross-site or prefetch GET /logout is ignored (400) without revoking session; same-origin GET /logout revokes it
            cross_logout = urllib.request.Request(
                f"{base}/logout",
                headers={
                    "Cookie": f"__Host-vyn_memory_token={sess_tok}",
                    "Sec-Fetch-Site": "cross-site",
                },
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_cl:
                urllib.request.urlopen(cross_logout)
            self.assertEqual(ctx_cl.exception.code, 400)
            ctx_cl.exception.close()
            self.assertEqual(self.srv.resolve_actor_from_token(sess_tok, self.conn), "owner")

            logout_req = urllib.request.Request(
                f"{base}/logout",
                headers={"Cookie": f"__Host-vyn_memory_token={sess_tok}"},
            )
            with urllib.request.urlopen(logout_req) as resp:
                self.assertEqual(resp.status, 200)
            self.assertIsNone(self.srv.resolve_actor_from_token(sess_tok, self.conn))
        finally:
            self.srv.exchange_omni_handoff = orig_exchange
            httpd.shutdown()
            httpd.server_close()

    def test_pdf_and_docx_indexing_upload_and_download(self) -> None:
        import io
        import zipfile
        import zlib

        # 1. Build a valid .docx archive in memory (Heading1 + paragraph + table)
        docx_buf = io.BytesIO()
        doc_xml = (
            '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">'
            "<w:body>"
            '<w:p><w:pPr><w:pStyle w:val="Heading1"/></w:pPr><w:r><w:t>Sample Resume 2026</w:t></w:r></w:p>'
            "<w:p><w:r><w:t>Example engineer working on storage drivers.</w:t></w:r></w:p>"
            "<w:tbl>"
            "<w:tr><w:tc><w:p><w:r><w:t>Company</w:t></w:r></w:p></w:tc><w:tc><w:p><w:r><w:t>Domain</w:t></w:r></w:p></w:tc></w:tr>"
            "<w:tr><w:tc><w:p><w:r><w:t>Example Corp</w:t></w:r></w:p></w:tc><w:tc><w:p><w:r><w:t>BSP &amp; IOMMU</w:t></w:r></w:p></w:tc></w:tr>"
            "</w:tbl>"
            "</w:body></w:document>"
        )
        with zipfile.ZipFile(docx_buf, "w", zipfile.ZIP_DEFLATED) as zf:
            zf.writestr("word/document.xml", doc_xml)
        docx_bytes = docx_buf.getvalue()

        # 2. Build a valid .pdf with a FlateDecode content stream
        stream_raw = b"BT /F1 12 Tf 72 720 Td (Linux Kernel XylographyDMA77 Coherency Textbook) Tj ET"
        stream_compressed = zlib.compress(stream_raw)
        pdf_bytes = (
            b"%PDF-1.4\n"
            b"1 0 obj << /Type /Catalog /Pages 2 0 R >> endobj\n"
            b"2 0 obj << /Type /Pages /Kids [3 0 R] /Count 1 >> endobj\n"
            b"3 0 obj << /Type /Page /Parent 2 0 R /Contents 4 0 R >> endobj\n"
            b"4 0 obj << /Length " + str(len(stream_compressed)).encode() + b" /Filter /FlateDecode >>\nstream\n"
            + stream_compressed
            + b"\nendstream\nendobj\n%%EOF\n"
        )

        # Drop the PDF directly into vault/resources/books/ and verify auto-sync + scope isolation
        books_dir = self.vault_dir / "resources/books"
        books_dir.mkdir(parents=True, exist_ok=True)
        (books_dir / "linux-dma-book.pdf").write_bytes(pdf_bytes)

        career_search = self.srv.op_search(self.conn, query="XylographyDMA77", scope="career")
        self.assertEqual(len(career_search["notes"]), 0)

        books_search = self.srv.op_search(self.conn, query="XylographyDMA77", scope="resources/books")
        self.assertEqual(len(books_search["notes"]), 1)
        self.assertEqual(books_search["notes"][0]["path"], "resources/books/linux-dma-book.pdf")

        pdf_note = self.srv.op_read_note(self.conn, "resources/books/linux-dma-book.pdf")
        self.assertIn("Linux Kernel XylographyDMA77 Coherency Textbook", pdf_note["content"])

        # 3. Upload .docx via POST /api/v1/upload (Base64) and verify table + text extraction
        httpd = ThreadingHTTPServer(("127.0.0.1", 0), self.srv.MemoryHTTPHandler)
        httpd.db = self.conn  # type: ignore[attr-defined]
        port = httpd.server_address[1]
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        base = f"http://127.0.0.1:{port}"
        try:
            up_req = urllib.request.Request(
                f"{base}/api/v1/upload",
                data=json.dumps({
                    "filename": "Sample-Resume-2026.docx",
                    "base64_content": base64.b64encode(docx_bytes).decode("ascii"),
                    "scope": "career",
                    "title": "Sample Resume 2026 (DOCX)",
                    "tags": ["resume", "docx"],
                }).encode("utf-8"),
                headers={
                    "Authorization": "Bearer tok-chatgpt-test",
                    "Content-Type": "application/json",
                },
                method="POST",
            )
            with urllib.request.urlopen(up_req) as resp:
                up_res = json.loads(resp.read().decode())
            self.assertEqual(up_res["status"], "uploaded")
            self.assertEqual(up_res["path"], "career/Sample-Resume-2026.docx")
            self.assertEqual(up_res["scope"], "career")

            docx_note = self.srv.op_read_note(self.conn, "career/Sample-Resume-2026.docx")
            self.assertIn("Example engineer working on storage drivers", docx_note["content"])
            self.assertIn("| Example Corp | BSP & IOMMU |", docx_note["content"])

            # 4. Browser multipart/form-data POST /upload and GET /download with owner session cookie + session-bound CSRF token
            sess_tok = self.srv._mint_web_session(self.conn, "owner@example.com")
            csrf_tok = self.srv._mint_upload_csrf(purpose="upload", session_token=sess_tok)
            boundary = "----VynTestBoundary987654"
            mp_body = (
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="csrf_token"\r\n\r\n'
                f"{csrf_tok}\r\n"
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="scope"\r\n\r\n'
                "career/embedded/linux\r\n"
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="title"\r\n\r\n'
                "Browser Uploaded PDF\r\n"
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="file"; filename="kernel-slides.pdf"\r\n'
                "Content-Type: application/pdf\r\n\r\n"
            ).encode("utf-8") + pdf_bytes + f"\r\n--{boundary}--\r\n".encode("utf-8")

            class NoRedirect(urllib.request.HTTPRedirectHandler):
                def redirect_request(self, req, fp, code, msg, headers, newurl):
                    return None

            no_redir = urllib.request.build_opener(NoRedirect)
            mp_req = urllib.request.Request(
                f"{base}/upload",
                data=mp_body,
                headers={
                    "Cookie": f"cf_clearance=weird[val]; vyn_memory_token=stale-old-token; __Host-vyn_memory_token={sess_tok}",
                    "Origin": "null",
                    "Sec-Fetch-Site": "same-origin",
                    "Content-Type": f"multipart/form-data; boundary={boundary}",
                },
                method="POST",
            )
            try:
                no_redir.open(mp_req)
                self.fail("Expected 303 redirect after browser upload")
            except urllib.error.HTTPError as e:
                loc_val = e.headers.get("Location", "")
                e.close()
                self.assertEqual(e.code, 303)
                self.assertIn("note=career/embedded/linux/kernel-slides.pdf", loc_val)

            # 4a. Cookie-authenticated POST /upload WITHOUT csrf_token is rejected with 403
            mp_no_csrf = (
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="scope"\r\n\r\n'
                "career/embedded/linux\r\n"
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="file"; filename="no-csrf.md"\r\n'
                "Content-Type: text/markdown\r\n\r\n"
                "# Missing CSRF\n"
                f"\r\n--{boundary}--\r\n"
            ).encode("utf-8")
            mp_no_csrf_req = urllib.request.Request(
                f"{base}/upload",
                data=mp_no_csrf,
                headers={
                    "Cookie": f"__Host-vyn_memory_token={sess_tok}",
                    "Sec-Fetch-Site": "same-origin",
                    "Content-Type": f"multipart/form-data; boundary={boundary}",
                },
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_nc2:
                no_redir.open(mp_no_csrf_req)
            self.assertEqual(ctx_nc2.exception.code, 403)
            ctx_nc2.exception.close()

            # 4b. Unauthenticated or logged-out POST /upload is rejected with 401 before reading body even if csrf_token is present
            mp_csrf_body = (
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="csrf_token"\r\n\r\n'
                f"{csrf_tok}\r\n"
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="scope"\r\n\r\n'
                "career/embedded/linux\r\n"
                f"--{boundary}\r\n"
                'Content-Disposition: form-data; name="file"; filename="csrf-uploaded.md"\r\n'
                "Content-Type: text/markdown\r\n\r\n"
                "# Uploaded without session cookie\n"
                f"\r\n--{boundary}--\r\n"
            ).encode("utf-8")
            mp_csrf_req = urllib.request.Request(
                f"{base}/upload",
                data=mp_csrf_body,
                headers={
                    "Origin": "null",
                    "Sec-Fetch-Site": "same-origin",
                    "Content-Type": f"multipart/form-data; boundary={boundary}",
                },
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                no_redir.open(mp_csrf_req)
            self.assertEqual(ctx.exception.code, 401)
            ctx.exception.close()

            # 4c. Cross-origin or spoofed X-Forwarded-Host POST /upload is rejected with 401 even if session cookie is present
            cross_req = urllib.request.Request(
                f"{base}/upload",
                data=mp_body,
                headers={
                    "Cookie": f"__Host-vyn_memory_token={sess_tok}",
                    "Origin": "https://evil.example.com",
                    "X-Forwarded-Host": "evil.example.com",
                    "Content-Type": f"multipart/form-data; boundary={boundary}",
                },
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                no_redir.open(cross_req)
            self.assertEqual(ctx.exception.code, 401)
            ctx.exception.close()
            self.srv._clear_auth_failures("127.0.0.1")

            # 4d. Verify GET /download returns the exact original PDF bytes + sandbox CSP & X-Frame-Options for owner
            dl_req = urllib.request.Request(
                f"{base}/download?path=career/embedded/linux/kernel-slides.pdf",
                headers={"Cookie": f"__Host-vyn_memory_token={sess_tok}"},
            )
            with urllib.request.urlopen(dl_req) as resp:
                self.assertEqual(resp.status, 200)
                self.assertEqual(resp.headers.get("Content-Type"), "application/pdf")
                self.assertEqual(resp.headers.get("Content-Security-Policy"), "default-src 'none'; sandbox")
                self.assertEqual(resp.headers.get("X-Frame-Options"), "DENY")
                self.assertEqual(resp.read(), pdf_bytes)

            # Verify SQL LIKE wildcard in op_read_note does not enumerate vault paths
            with self.assertRaises(self.srv.MemoryError) as ctx_wild:
                self.srv.op_read_note(self.conn, "%.md")
            self.assertIn("not found", str(ctx_wild.exception))
            self.assertNotIn("Ambiguous note name", str(ctx_wild.exception))

            # 4e. Spoofed PDF/DOCX without magic bytes are rejected, and _extract_pdf_text_stdlib bounds decompression
            with self.assertRaises(self.srv.MemoryError):
                self.srv.op_upload_document(
                    self.conn,
                    "chatgpt",
                    filename="spoofed.pdf",
                    raw_bytes=b"<html><script>alert(1)</script></html>",
                    scope="career",
                )
            with self.assertRaises(self.srv.MemoryError):
                self.srv.op_upload_document(
                    self.conn,
                    "chatgpt",
                    filename="spoofed.docx",
                    raw_bytes=b"not-a-zip-archive",
                    scope="career",
                )
            big_stream = zlib.compress(b"BT (" + (b"A" * (6 * 1024 * 1024)) + b") Tj ET", level=9)
            bounded_out = self.srv._extract_pdf_text_stdlib(
                b"%PDF-1.4\n1 0 obj\n<<>>\nstream\n" + big_stream + b"\nendstream\nendobj\n%%EOF",
                max_chars=50_000,
            )
            self.assertLessEqual(len(bounded_out), 50_000)

            # 4f. Unscoped op_search excludes resources/books, while explicit scope="resources/books" includes it, and agents can upload to resources/books
            unscoped_book_hit = self.srv.op_search(self.conn, query="XylographyDMA77", scope="")
            unscoped_paths = [n["path"] for n in unscoped_book_hit["notes"]]
            self.assertNotIn("resources/books/linux-dma-book.pdf", unscoped_paths)
            scoped_book_hit = self.srv.op_search(self.conn, query="XylographyDMA77", scope="resources/books")
            self.assertEqual(len(scoped_book_hit["notes"]), 1)
            self.assertEqual(scoped_book_hit["notes"][0]["path"], "resources/books/linux-dma-book.pdf")
            agent_book_up = self.srv.op_upload_document(
                self.conn,
                "chatgpt",
                filename="agent-book.pdf",
                raw_bytes=pdf_bytes,
                scope="resources/books",
            )
            self.assertEqual(agent_book_up["scope"], "resources/books")

            # Verify non-owner token is rejected with 403 on GET /download
            dl_agent = urllib.request.Request(
                f"{base}/download?path=career/embedded/linux/kernel-slides.pdf",
                headers={"Authorization": "Bearer tok-claude-test"},
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(dl_agent)
            self.assertEqual(ctx.exception.code, 403)
            ctx.exception.close()

            # 4g. POST /messages requires authentication (401) and matching SSE session actor (403)
            import queue as _queue
            with self.srv.SSE_LOCK:
                self.srv.SSE_SESSIONS["test-sse-1"] = ("claude", _queue.Queue(maxsize=8))
            try:
                unauth_msg = urllib.request.Request(
                    f"{base}/messages?session_id=test-sse-1",
                    data=b'{"jsonrpc":"2.0","id":1,"method":"ping"}',
                    headers={"Content-Type": "application/json"},
                    method="POST",
                )
                with self.assertRaises(urllib.error.HTTPError) as ctx_um:
                    urllib.request.urlopen(unauth_msg)
                self.assertEqual(ctx_um.exception.code, 401)
                ctx_um.exception.close()
                self.srv._clear_auth_failures("127.0.0.1")

                mismatch_msg = urllib.request.Request(
                    f"{base}/messages?session_id=test-sse-1",
                    data=b'{"jsonrpc":"2.0","id":1,"method":"ping"}',
                    headers={
                        "Authorization": "Bearer tok-chatgpt-test",
                        "Content-Type": "application/json",
                    },
                    method="POST",
                )
                with self.assertRaises(urllib.error.HTTPError) as ctx_mm:
                    urllib.request.urlopen(mismatch_msg)
                self.assertEqual(ctx_mm.exception.code, 403)
                ctx_mm.exception.close()

                ok_msg = urllib.request.Request(
                    f"{base}/messages?session_id=test-sse-1",
                    data=b'{"jsonrpc":"2.0","id":1,"method":"ping"}',
                    headers={
                        "Authorization": "Bearer tok-claude-test",
                        "Content-Type": "application/json",
                    },
                    method="POST",
                )
                with urllib.request.urlopen(ok_msg) as resp_om:
                    self.assertEqual(resp_om.status, 202)
            finally:
                with self.srv.SSE_LOCK:
                    self.srv.SSE_SESSIONS.pop("test-sse-1", None)

            # 4h. Backslash open-redirect next=/\evil.example.com sanitized to /?scope=career, Transfer-Encoding rejected with 411, and non-int depth rejected with 400
            self.assertEqual(self.srv._sanitize_next_path("/\\evil.example.com"), "/?scope=career")
            self.assertEqual(self.srv._sanitize_next_path("//evil.example.com"), "/?scope=career")
            self.assertEqual(self.srv._sanitize_next_path("/?scope=career&note=test.md"), "/?scope=career&note=test.md")

            import http.client as _hc
            conn_te = _hc.HTTPConnection("127.0.0.1", port, timeout=5)
            conn_te.putrequest("POST", "/oauth/register")
            conn_te.putheader("Transfer-Encoding", "chunked")
            conn_te.endheaders()
            resp_411 = conn_te.getresponse()
            self.assertEqual(resp_411.status, 411)
            resp_411.read()
            conn_te.close()

            bad_depth_req = urllib.request.Request(
                f"{base}/api/v1/context?target=career/00-Read-Before-Interview.md&depth=not-an-int",
                headers={"Authorization": "Bearer tok-claude-test"},
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_bd:
                urllib.request.urlopen(bad_depth_req)
            self.assertEqual(ctx_bd.exception.code, 400)
            ctx_bd.exception.close()
        finally:
            httpd.shutdown()
            httpd.server_close()

    def test_security_audit_run3_regressions(self) -> None:
        # 1. render_markdown_html never injects <em>/<strong>/<del>/<code> inside <a href="..."> attributes
        rendered = self.srv.render_markdown_html(
            "[a](https://example.com/*x) and [b](https://example.com/*y)\n[c](https://example.com/`code`)"
        )
        self.assertIn('href="https://example.com/*x"', rendered)
        self.assertIn('href="https://example.com/*y"', rendered)
        self.assertIn('href="https://example.com/code"', rendered)
        self.assertNotIn("href=\"https://example.com/<em>", rendered)
        self.assertNotIn("href=\"https://example.com/<code>", rendered)

        # 2. extract_pdf_markdown pypdf branch slices single-page text to max_chars
        import types
        fake_pypdf = types.ModuleType("pypdf")
        class _FakePage:
            def extract_text(self):
                return "A" * 600_000
        class _FakeReader:
            def __init__(self, _stream):
                self.metadata = None
                self.pages = [_FakePage()]
        fake_pypdf.PdfReader = _FakeReader
        old_pypdf = sys.modules.get("pypdf")
        sys.modules["pypdf"] = fake_pypdf
        try:
            _, body_md = self.srv.extract_pdf_markdown(Path("huge.pdf"), b"%PDF-1.4\n%%EOF", max_chars=50_000)
            self.assertLessEqual(len(body_md), 51_000)
            self.assertIn("Indexed first 1 of 1 pages (50,000 chars)", body_md)
        finally:
            if old_pypdf is None:
                sys.modules.pop("pypdf", None)
            else:
                sys.modules["pypdf"] = old_pypdf

        # 3. HTTP GET error handling (403/400 instead of RemoteDisconnected), MCP batch limit (<=32), and /device deny slot release
        httpd = ThreadingHTTPServer(("127.0.0.1", 0), self.srv.MemoryHTTPHandler)
        httpd.db = self.conn  # type: ignore[attr-defined]
        port = httpd.server_address[1]
        threading.Thread(target=httpd.serve_forever, daemon=True).start()
        base = f"http://127.0.0.1:{port}"
        try:
            for p_403 in ("/api/v1/search?scope=personal", "/api/v1/notes?scope=personal", "/api/v1/briefing?scope=personal"):
                req_403 = urllib.request.Request(f"{base}{p_403}", headers={"Authorization": "Bearer tok-claude-test"})
                with self.assertRaises(urllib.error.HTTPError) as ctx_403:
                    urllib.request.urlopen(req_403)
                self.assertEqual(ctx_403.exception.code, 403)
                ctx_403.exception.close()

            req_400 = urllib.request.Request(f"{base}/api/v1/notes?scope=agents/invalid", headers={"Authorization": "Bearer tok-claude-test"})
            with self.assertRaises(urllib.error.HTTPError) as ctx_400:
                urllib.request.urlopen(req_400)
            self.assertEqual(ctx_400.exception.code, 400)
            ctx_400.exception.close()

            # Oversized JSON-RPC batch (>32) is rejected with 400
            big_batch = json.dumps([{"jsonrpc": "2.0", "id": i, "method": "ping"} for i in range(33)]).encode()
            req_batch = urllib.request.Request(
                f"{base}/mcp",
                data=big_batch,
                headers={"Authorization": "Bearer tok-claude-test", "Content-Type": "application/json"},
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_b:
                urllib.request.urlopen(req_batch)
            self.assertEqual(ctx_b.exception.code, 400)
            ctx_b.exception.close()

            # Per-IP pending device_code cap prevents a single IP from exhausting global slots,
            # and denying a pending device_code immediately frees its pending slot
            codes = []
            for i in range(self.srv.MAX_PENDING_DEVICE_CODES_PER_IP):
                r_dc = urllib.request.Request(
                    f"{base}/device/code",
                    data=json.dumps({"app": "Codex", "host": f"h{i}"}).encode(),
                    headers={"Content-Type": "application/json"},
                    method="POST",
                )
                with urllib.request.urlopen(r_dc) as resp:
                    codes.append(json.loads(resp.read().decode()))
            # Next request from the same IP is throttled with 429
            r_dc_over = urllib.request.Request(
                f"{base}/device/code",
                data=b'{"app":"Codex"}',
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_over:
                urllib.request.urlopen(r_dc_over)
            self.assertEqual(ctx_over.exception.code, 429)
            ctx_over.exception.close()

            sess = self.srv._mint_web_session(self.conn, self.srv.owner_session_email())
            csrf = self.srv._mint_upload_csrf(purpose="device", session_token=sess)
            deny_req = urllib.request.Request(
                f"{base}/device",
                data=urllib.parse.urlencode({"code": codes[0]["user_code"], "csrf_token": csrf, "role": "chatgpt", "decision": "deny"}).encode(),
                headers={
                    "Cookie": f"__Host-vyn_memory_token={sess}",
                    "Sec-Fetch-Site": "same-origin",
                    "Content-Type": "application/x-www-form-urlencoded",
                },
                method="POST",
            )
            with urllib.request.urlopen(deny_req) as resp:
                self.assertEqual(resp.status, 200)
            r_dc_freed = urllib.request.Request(
                f"{base}/device/code",
                data=b'{"app":"Codex"}',
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(r_dc_freed) as resp_freed:
                self.assertEqual(resp_freed.status, 200)
        finally:
            self.srv._clear_auth_failures("127.0.0.1")
            httpd.shutdown()
            httpd.server_close()

    def test_fact_checking_and_web_fact_management(self) -> None:
        # 1. op_remember_fact flags potential_conflicts for other active facts in the same scope
        f1 = self.srv.op_remember_fact(
            self.conn,
            "claude",
            fact="Production deploys use blue-green cutover on Tuesdays.",
            scope="shared",
            subject="deploy-cadence",
            category="decision",
        )
        self.assertEqual(f1["potential_conflicts"], [])

        f2 = self.srv.op_remember_fact(
            self.conn,
            "chatgpt",
            fact="Production deploys happen on Fridays after QA freeze.",
            scope="shared",
            subject="release-window",
            category="decision",
        )
        self.assertTrue(any(c["id"] == f1["fact"]["id"] for c in f2["potential_conflicts"]))

        # Superseding deploy-cadence moves f1 into history
        f3 = self.srv.op_remember_fact(
            self.conn,
            "claude",
            fact="Production deploys use rolling updates on Wednesdays.",
            scope="shared",
            subject="deploy-cadence",
            category="decision",
        )
        self.assertIn(f1["fact"]["id"], f3["superseded_ids"])

        # 2. op_check_facts returns active matches, retired history, related notes, and guidance
        self.srv.op_write_note(
            self.conn,
            "claude",
            path="shared/deploy-runbook.md",
            content="# Deploy Runbook\n\nProduction deploys run via rolling updates on Wednesdays.\n",
            scope="shared",
        )
        chk = self.srv.op_check_facts(self.conn, statement="Production deploys on Tuesdays", scope="shared", subject="deploy-cadence")
        self.assertTrue(any(f["id"] == f3["fact"]["id"] for f in chk["matching_active_facts"]))
        self.assertTrue(any(f["id"] == f1["fact"]["id"] for f in chk["matching_history_facts"]))
        self.assertTrue(any(n["path"] == "shared/deploy-runbook.md" for n in chk["related_notes"]))
        self.assertIn("active fact(s)", chk["guidance"])

        # 3. MCP memory_check_facts tool + REST /api/v1/fact-check + OpenAPI + Web UI POST /facts + /device lookup
        httpd = ThreadingHTTPServer(("127.0.0.1", 0), self.srv.MemoryHTTPHandler)
        httpd.db = self.conn  # type: ignore[attr-defined]
        port = httpd.server_address[1]
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        base = f"http://127.0.0.1:{port}"
        try:
            # OpenAPI includes /api/v1/fact-check
            with urllib.request.urlopen(f"{base}/openapi.json") as resp:
                oa = json.loads(resp.read().decode())
            self.assertIn("/api/v1/fact-check", oa["paths"])

            # REST GET /api/v1/fact-check
            fc_req = urllib.request.Request(
                f"{base}/api/v1/fact-check?statement=Production+deploys&scope=shared",
                headers={"Authorization": "Bearer tok-claude-test"},
            )
            with urllib.request.urlopen(fc_req) as resp:
                fc_data = json.loads(resp.read().decode())
            self.assertGreaterEqual(len(fc_data["matching_active_facts"]), 1)

            # MCP tools/call memory_check_facts
            mcp_req = urllib.request.Request(
                f"{base}/mcp",
                data=json.dumps({
                    "jsonrpc": "2.0",
                    "id": 91,
                    "method": "tools/call",
                    "params": {
                        "name": "memory_check_facts",
                        "arguments": {"statement": "Production deploys", "scope": "shared", "subject": "deploy-cadence"},
                    },
                }).encode("utf-8"),
                headers={"Authorization": "Bearer tok-claude-test", "Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(mcp_req) as resp:
                mcp_res = json.loads(resp.read().decode())
            self.assertFalse(mcp_res["result"]["isError"])
            tool_payload = json.loads(mcp_res["result"]["content"][0]["text"])
            self.assertTrue(any(f["id"] == f3["fact"]["id"] for f in tool_payload["matching_active_facts"]))

            # Owner Web UI: GET /device without ?code= renders lookup form (200) instead of 404
            sess_tok = self.srv._mint_web_session(self.conn, self.srv.owner_session_email())
            owner_hdrs = {"Cookie": f"__Host-vyn_memory_token={sess_tok}", "Sec-Fetch-Site": "same-origin"}
            with urllib.request.urlopen(urllib.request.Request(f"{base}/device", headers=owner_hdrs)) as resp:
                self.assertEqual(resp.status, 200)
                dev_lookup = resp.read().decode()
            self.assertIn('name="code"', dev_lookup)

            # GET /apps shows connect guide
            with urllib.request.urlopen(urllib.request.Request(f"{base}/apps", headers=owner_hdrs)) as resp:
                apps_html = resp.read().decode()
            self.assertIn("memory.py login", apps_html)
            self.assertIn("/mcp", apps_html)

            # Owner Web UI POST /facts (add + retire) with session-bound purpose="facts" CSRF
            class NoRedirect(urllib.request.HTTPRedirectHandler):
                def redirect_request(self, req, fp, code, msg, headers, newurl):
                    return None

            no_redir = urllib.request.build_opener(NoRedirect)
            bad_csrf = self.srv._mint_upload_csrf(purpose="upload", session_token=sess_tok)
            bad_fact_req = urllib.request.Request(
                f"{base}/facts",
                data=urllib.parse.urlencode({
                    "csrf_token": bad_csrf,
                    "action": "add",
                    "scope": "shared",
                    "subject": "ui-fact",
                    "fact": "Should be rejected due to wrong CSRF purpose.",
                }).encode("utf-8"),
                headers={**owner_hdrs, "Content-Type": "application/x-www-form-urlencoded"},
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_bad:
                no_redir.open(bad_fact_req)
            self.assertEqual(ctx_bad.exception.code, 403)
            ctx_bad.exception.close()

            facts_csrf = self.srv._mint_upload_csrf(purpose="facts", session_token=sess_tok)
            add_fact_req = urllib.request.Request(
                f"{base}/facts",
                data=urllib.parse.urlencode({
                    "csrf_token": facts_csrf,
                    "action": "add",
                    "scope": "shared",
                    "subject": "ui-fact",
                    "category": "decision",
                    "fact": "Added directly from owner web UI.",
                    "next": "/?scope=shared",
                }).encode("utf-8"),
                headers={**owner_hdrs, "Content-Type": "application/x-www-form-urlencoded"},
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_add:
                no_redir.open(add_fact_req)
            self.assertEqual(ctx_add.exception.code, 303)
            ctx_add.exception.close()

            found_ui = self.srv.op_check_facts(self.conn, subject="ui-fact", scope="shared")
            self.assertEqual(len(found_ui["matching_active_facts"]), 1)
            ui_fact_id = found_ui["matching_active_facts"][0]["id"]

            retire_req = urllib.request.Request(
                f"{base}/facts",
                data=urllib.parse.urlencode({
                    "csrf_token": facts_csrf,
                    "action": "forget",
                    "fact_id": str(ui_fact_id),
                    "reason": "Superseded during review",
                    "next": "/?scope=shared",
                }).encode("utf-8"),
                headers={**owner_hdrs, "Content-Type": "application/x-www-form-urlencoded"},
                method="POST",
            )
            with self.assertRaises(urllib.error.HTTPError) as ctx_ret:
                no_redir.open(retire_req)
            self.assertEqual(ctx_ret.exception.code, 303)
            ctx_ret.exception.close()

            after_retire = self.srv.op_check_facts(self.conn, subject="ui-fact", scope="shared")
            self.assertEqual(after_retire["matching_active_facts"], [])
            self.assertEqual(len(after_retire["matching_history_facts"]), 1)
            self.assertEqual(after_retire["matching_history_facts"][0]["invalidated_reason"], "Superseded during review")
        finally:
            self.srv._clear_auth_failures("127.0.0.1")
            httpd.shutdown()
            httpd.server_close()

    def test_security_hardening_followup(self) -> None:
        # 1. CSRF tokens reject cross-purpose, cross-session, and future timestamps
        tok_a = self.srv._mint_upload_csrf(purpose="upload", session_token="sess-A")
        self.assertTrue(self.srv._verify_upload_csrf(tok_a, purpose="upload", session_token="sess-A"))
        self.assertFalse(self.srv._verify_upload_csrf(tok_a, purpose="device", session_token="sess-A"))
        self.assertFalse(self.srv._verify_upload_csrf(tok_a, purpose="upload", session_token="sess-B"))
        future_tok = self.srv._mint_upload_csrf(now_ts=time.time() + 3600, purpose="upload", session_token="sess-A")
        self.assertFalse(self.srv._verify_upload_csrf(future_tok, purpose="upload", session_token="sess-A"))

        # 2. normalize_scope is idempotent and owner can write daily/inbox
        for raw in ("shared", "projects/alpha", "career", "career/embedded/linux", "agents/claude", "daily", "inbox"):
            once = self.srv.normalize_scope(raw)
            self.assertEqual(self.srv.normalize_scope(once), once)
        self.assertIn("daily", self.srv.writable_scopes_for("owner"))
        self.assertIn("inbox", self.srv.writable_scopes_for("owner"))

        # 3. Cross-agent writes are denied, and explicit_scope cannot place a note in a nested child scope denied to the actor
        with self.assertRaises(self.srv.MemoryPermissionError):
            self.srv.op_write_note(
                self.conn,
                "claude",
                path="agents/chatgpt/sneaky.md",
                content="# Sneaky\n",
            )
        orig_extra = self.srv.HERMES_EXTRA_WRITE
        try:
            self.srv.HERMES_EXTRA_WRITE = (*orig_extra, "business")
            with self.assertRaises(self.srv.MemoryPermissionError):
                self.srv.op_write_note(
                    self.conn,
                    "hermes",
                    path="secret/file.md",
                    content="# Secret\n",
                    scope="business",
                )
        finally:
            self.srv.HERMES_EXTRA_WRITE = orig_extra

        # 4. DOCX ZIP entry count cap rejects oversized central directories
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w") as zf:
            zf.writestr("word/document.xml", "<w:document xmlns:w='http://schemas.openxmlformats.org/wordprocessingml/2006/main'><w:body><w:p><w:r><w:t>ok</w:t></w:r></w:p></w:body></w:document>")
            for i in range(6):
                zf.writestr(f"extra/{i}.txt", "x")
        orig_cap = self.srv.MAX_DOCX_ZIP_ENTRIES
        try:
            self.srv.MAX_DOCX_ZIP_ENTRIES = 5
            with self.assertRaises(self.srv.MemoryError):
                self.srv.op_upload_document(self.conn, "claude", filename="many.docx", raw_bytes=buf.getvalue(), scope="shared")
        finally:
            self.srv.MAX_DOCX_ZIP_ENTRIES = orig_cap

        # 5. render_login_page adapts when OMNI_PUBLIC_URL is unset, and /auth/start does not pollute web_auth_states
        old_omni_env = os.environ.pop("OMNI_PUBLIC_URL", None)
        old_omni_mod = self.srv.OMNI_PUBLIC_URL
        try:
            self.srv.OMNI_PUBLIC_URL = ""
            login_no_omni = self.srv.render_login_page()
            self.assertNotIn("Sign in with Omni", login_no_omni)
            self.assertIn('id="owner-token"', login_no_omni)

            httpd = ThreadingHTTPServer(("127.0.0.1", 0), self.srv.MemoryHTTPHandler)
            httpd.db = self.conn  # type: ignore[attr-defined]
            port = httpd.server_address[1]
            thread = threading.Thread(target=httpd.serve_forever, daemon=True)
            thread.start()
            base = f"http://127.0.0.1:{port}"
            try:
                before_states = self.conn.execute("SELECT COUNT(*) FROM web_auth_states").fetchone()[0]
                with self.assertRaises(urllib.error.HTTPError) as ctx_s:
                    urllib.request.urlopen(f"{base}/auth/start")
                self.assertEqual(ctx_s.exception.code, 404)
                ctx_s.exception.close()
                after_states = self.conn.execute("SELECT COUNT(*) FROM web_auth_states").fetchone()[0]
                self.assertEqual(before_states, after_states)

                # Origin: null without Sec-Fetch-Site is rejected on cookie-authenticated POST /upload
                sess = self.srv._mint_web_session(self.conn, self.srv.owner_session_email())
                csrf = self.srv._mint_upload_csrf(purpose="upload", session_token=sess)
                bnd = "----NullOriginTest"
                body = (
                    f"--{bnd}\r\nContent-Disposition: form-data; name=\"csrf_token\"\r\n\r\n{csrf}\r\n"
                    f"--{bnd}\r\nContent-Disposition: form-data; name=\"file\"; filename=\"a.md\"\r\n\r\n# Hi\r\n--{bnd}--\r\n"
                ).encode()
                req_null = urllib.request.Request(
                    f"{base}/upload",
                    data=body,
                    headers={
                        "Cookie": f"__Host-vyn_memory_token={sess}",
                        "Origin": "null",
                        "Content-Type": f"multipart/form-data; boundary={bnd}",
                    },
                    method="POST",
                )
                with self.assertRaises(urllib.error.HTTPError) as ctx_null:
                    urllib.request.urlopen(req_null)
                self.assertEqual(ctx_null.exception.code, 401)
                self.assertIsNone(ctx_null.exception.headers.get("Access-Control-Allow-Origin"))
                ctx_null.exception.close()
            finally:
                self.srv._clear_auth_failures("127.0.0.1")
                httpd.shutdown()
                httpd.server_close()
        finally:
            self.srv.OMNI_PUBLIC_URL = old_omni_mod
            if old_omni_env is not None:
                os.environ["OMNI_PUBLIC_URL"] = old_omni_env

        # 6. CLI memory.py rejects remote http:// URLs while allowing https:// and loopback http://
        cli_spec = importlib.util.spec_from_file_location(
            "vyn_memory_cli_test",
            Path(__file__).resolve().parent / "skills" / "vyn-memory" / "memory.py",
        )
        assert cli_spec and cli_spec.loader
        cli_mod = importlib.util.module_from_spec(cli_spec)
        cli_spec.loader.exec_module(cli_mod)
        self.assertEqual(cli_mod._validate_hub_url("https://memory.example.com/"), "https://memory.example.com")
        self.assertEqual(cli_mod._validate_hub_url("http://127.0.0.1:8770"), "http://127.0.0.1:8770")
        self.assertEqual(cli_mod._validate_hub_url("http://vyn-memory:8770"), "http://vyn-memory:8770")
        with self.assertRaises(ValueError):
            cli_mod._validate_hub_url("http://memory.example.com")

    def test_web_ui_search_topics_and_traversal(self) -> None:
        # 1. Humanized README title uses parent folder name
        self.assertEqual(self.srv._humanize_note_title("README", "agents/decisions/README.md"), "Decisions — Overview")
        self.assertEqual(self.srv._humanize_note_title("", "career/embedded/c/README.md"), "C — Overview")

        # 2. Populate sibling notes in one topic + a verified fact
        self.srv.op_write_note(
            self.conn,
            "claude",
            path="projects/alpha/00-overview.md",
            content="# Alpha Overview\n\nDMA ring buffer design for Alpha.\n",
            scope="projects/alpha",
        )
        self.srv.op_write_note(
            self.conn,
            "claude",
            path="projects/alpha/01-ring-buffer.md",
            content="# Ring Buffer Deep Dive\n\nCache coherency and DMA descriptors.\n",
            scope="projects/alpha",
        )
        self.srv.op_write_note(
            self.conn,
            "claude",
            path="projects/alpha/02-testing.md",
            content="# Testing Plan\n\nHardware loopback tests.\n",
            scope="projects/alpha",
        )
        self.srv.op_remember_fact(
            self.conn,
            "claude",
            fact="Alpha uses 64-byte aligned DMA descriptors.",
            scope="projects/alpha",
            subject="dma-align",
            category="decision",
        )

        # 3. Search view renders highlighted <mark> snippets, matching facts, and scope chips
        search_html = self.srv.render_dashboard_page(self.conn, "owner", search_query="DMA", session_token="s1")
        self.assertIn("Matching Verified Facts", search_html)
        self.assertIn("Matching Pages", search_html)
        self.assertIn("<mark>DMA</mark>", search_html)
        self.assertIn("filter-chip", search_html)

        # Opening a search hit preserves back-to-results link
        hit_html = self.srv.render_dashboard_page(
            self.conn,
            "owner",
            selected_note="projects/alpha/01-ring-buffer.md",
            search_query="DMA",
            session_token="s1",
        )
        self.assertIn("← Back to", hit_html)

        # 4. Topic Explorer view renders Recently Updated + Browse by Topic cards
        topics_html = self.srv.render_dashboard_page(self.conn, "owner", view="topics", session_token="s1")
        self.assertIn("Recently Updated", topics_html)
        self.assertIn("Browse by Topic", topics_html)
        self.assertIn("topic-card", topics_html)

        # 5. Reader renders Previous / Next page traversal bar & reading time
        mid_html = self.srv.render_dashboard_page(
            self.conn,
            "owner",
            selected_note="projects/alpha/01-ring-buffer.md",
            scope_filter="projects",
            session_token="s1",
        )
        self.assertIn("pager-nav", mid_html)
        self.assertIn("← Previous", mid_html)
        self.assertIn("Next →", mid_html)
        self.assertIn("min read", mid_html)

        # 6. Upstream 30-second self-starter files exist and match server.py contract
        repo_root = Path(__file__).resolve().parent
        compose_text = (repo_root / "docker-compose.yml").read_text(encoding="utf-8")
        env_ex_text = (repo_root / ".env.example").read_text(encoding="utf-8")
        self.assertIn("/app/server.py", compose_text)
        self.assertIn("/health", compose_text)
        self.assertIn("MEMORY_OWNER_TOKEN=", env_ex_text)


if __name__ == "__main__":
    unittest.main()
