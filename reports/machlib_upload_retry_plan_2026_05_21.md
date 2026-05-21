# MachLib Upload Retry Plan

Package: `machlib`
Version: `0.0.1`

Prior failure: `PYPI_HTTP_429_TOO_MANY_REQUESTS`.

MachLib should not be retried immediately. A future retry must wait for a
cooldown, then use a new explicit human approval and a fresh temporary PyPI
token. The retry should upload only `machlib 0.0.1`, verify version-specific
PyPI JSON, unset the token after completion or failure, and stop on the first
true failure.

Current gate:

- retry_allowed_now: `false`
- retry_requires_cooldown: `true`
- retry_requires_new_token: `true`
- retry_requires_explicit_human_approval: `true`
- upload_allowed_now: `false`
- token_handling_now: `false`
- publish_performed: `false`

Next approval phrase:

`Approve one-token PyPI retry upload for machlib 0.0.1 only. I will provide a new temporary token now.`
