# Cloudflare Origin Security Hardening

## What it does
Hardens `vyn-memory` when exposed publicly behind a Cloudflare Tunnel (`MEMORY_BEHIND_CLOUDFLARE=1`, `PUBLIC_URL=https://...`) while keeping internal Docker and loopback HTTP calls (`http://vyn-memory:8770`, `http://127.0.0.1:8770`) working with zero redirect loops:
- **HTTPS redirect (`308 Permanent Redirect`):** Plaintext HTTP requests arriving through Cloudflare (`X-Forwarded-Proto: http` or `CF-Visitor: {"scheme":"http"}`) on `GET`, `HEAD`, or `POST` are redirected to the sanitized path on `PUBLIC_URL` (`_sanitize_next_path` prevents open redirects).
- **HSTS:** Emits `Strict-Transport-Security: max-age=31536000; includeSubDomains` on HTTPS responses behind Cloudflare.
- **Browser isolation headers on HTML pages:** Emits `Permissions-Policy: camera=(), microphone=(), geolocation=(), payment=(), usb=()` on all HTML responses, and `Cross-Origin-Opener-Policy: same-origin` on dashboard/login/apps/device pages (preserving OAuth popup flows on `/oauth/authorize`).
- **Validated client IP & bounded tag input:** Validates `CF-Connecting-IP` with `ipaddress.ip_address()` before trusting it for auth rate limiting and caps `_normalize_tag()` to 64 characters.

## How to use it
Enabled automatically when `MEMORY_BEHIND_CLOUDFLARE=1` and `PUBLIC_URL` starts with `https://` (the default in `dockers/vynstack/docker-compose.yml`). Reconcile and verify with `./dockers/vynstack/vyn memory-setup`.

## How it works
- `_cloudflare_scheme(headers)` checks `X-Forwarded-Proto` (first hop of comma-separated values) and falls back to `CF-Visitor` JSON, returning `"http"`, `"https"`, or `""`; internal container/loopback requests return `""` and are served directly without redirect or HSTS.
- `MemoryHTTPHandler._maybe_redirect_to_https()` runs at the top of `do_GET` and `do_POST` (and `do_HEAD` via `do_GET`) before routing, redirecting via `self.redirect(..., status=308)` when the scheme is `"http"`.
- `MemoryHTTPHandler.end_headers()` emits HSTS only when `_is_https_public()` and the Cloudflare scheme is `"https"` (never over plaintext internal HTTP).
- `MemoryHTTPHandler.send_html()` sets `Permissions-Policy` and `Cross-Origin-Opener-Policy: same-origin` alongside strict CSP, `X-Frame-Options: DENY`, `X-Content-Type-Options: nosniff`, and `Referrer-Policy: same-origin`, while omitting `COOP` on `/oauth/authorize` and `/login?next=/oauth/authorize...` to preserve OAuth popup `window.opener`.

## Where it lives
- `repos/vyn-memory/server.py` (`_is_https_public`, `_behind_cloudflare`, `_cloudflare_scheme`, `_client_ip`, `_normalize_tag`, `MemoryHTTPHandler._maybe_redirect_to_https`, `MemoryHTTPHandler.end_headers`, `MemoryHTTPHandler.send_html`).
- `repos/vyn-memory/test_memory.py` (`test_cloudflare_security_hardening`).

## Still to do
- Optional: enable Cloudflare edge "Always Use HTTPS" and HSTS in the Cloudflare dashboard as defense-in-depth (origin already enforces both).
