# All Packages Remaining Upload Continuation Plan - 2026-05-20

## Already Uploaded

- `zero-mathlib-checker` `0.0.0.dev0`
- `claim-boundary` `0.0.0.dev0`
- `eml-records` `0.0.0.dev0`
- `review-branch-packet` `0.0.0.dev0`

## Remaining Ready, Not Uploaded

- `machlib-workbench` `0.0.0.dev0`
- `eml-harness` `0.0.0.dev0`
- `hybrid-trace-eml` `0.0.0.dev0`

## Blocked, Not Uploaded

- `machlib`: broad package-boundary/API/license/public-copy review remains
  incomplete.

## Failure

`machlib-workbench` stopped during Twine upload with PyPI HTTP 429 Too Many
Requests. Public PyPI JSON does not show `machlib-workbench`, so it is not
recorded as uploaded.

## Continuation Rule

- Do not retry immediately.
- Wait before the next upload session.
- Use one new temporary token only after explicit approval.
- Upload remaining packages one at a time.
- Verify version-specific JSON first.
- If project-level JSON lags, retry/backoff before deciding failure.
- Stop on the first true failure.

## Token Hygiene

- Prior token must be revoked/deleted.
- No token is currently handled.
- No token is stored.
- No token value is present in reports.
- The prior token value appeared in local subprocess traceback output and was
  not written to repository files.
