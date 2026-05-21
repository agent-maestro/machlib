# MachLib API Review

Status: `API_OK_FOR_PRE_ALPHA_RELEASE`.

The initial API is intentionally small:

- `machlib.summary.package_summary()`
- `machlib.summary.toolchain()`
- `machlib.boundaries.boundary_lines()`
- CLI commands: `info`, `boundaries`, and `toolchain`

The CLI is read-only and non-mutating. It does not run broad repository scans by
default and does not deploy, upload, push, publish, or call APIs.
