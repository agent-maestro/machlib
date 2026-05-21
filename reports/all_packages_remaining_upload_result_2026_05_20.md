# All Packages Remaining Upload Result - 2026-05-20

Upload session status: `PARTIAL_FAILED`

## Uploaded Packages
- 1. `claim-boundary` `0.0.0.dev0`
- 2. `eml-records` `0.0.0.dev0`
- 3. `review-branch-packet` `0.0.0.dev0`

## Skipped Packages
- `eml-harness`
- `hybrid-trace-eml`

Failed package: `machlib-workbench`
Failure stage: `twine_upload_http_429_too_many_requests`

PyPI returned HTTP 429 during `machlib-workbench` upload. Public PyPI JSON does
not show `machlib-workbench 0.0.0.dev0`, so it is not recorded as uploaded. The
batch stopped before `eml-harness` and `hybrid-trace-eml`.

Excluded packages: `zero-mathlib-checker`, `machlib`.

Token written to file: `false`
Token printed: `true`
Token printed note: the token value appeared in a local subprocess traceback
after the failed Twine command. The token value is not included in this report
and was not written to committed files.
Token committed: `false`
Token unset after upload: `true`
User revoke token required: `true`
