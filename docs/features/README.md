# Feature docs — `vyn-memory`

| Feature | Doc | Summary |
|---|---|---|
| Confluence-style Labels & Ordered Study Pages | [labels-and-page-order.md](labels-and-page-order.md) | Tag/label navigation (`?view=tags`, `?tag=<tag>`, clickable labels on pages, sub-topic chips, tag-scoped Prev/Next pager), `GET /api/v1/tags`, `GET /api/v1/notes?tag=`, and frontmatter `order:` sorting. |
| Cloudflare Origin Security Hardening | [cloudflare-security.md](cloudflare-security.md) | Origin HTTPS `308` redirect behind Cloudflare, HSTS, `Permissions-Policy`, `Cross-Origin-Opener-Policy`, `CF-Connecting-IP` validation, and bounded tag normalization. |
