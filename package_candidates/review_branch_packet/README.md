# review-branch-packet

`review-branch-packet` is a local draft package candidate for building private review branch packets from read-only git state.

Status:
- Local draft only.
- No PyPI release performed.
- No PyPI package name availability check performed.
- No PyPI token handling performed.
- No package publish performed.
- No release artifacts created.
- Not release-ready and not upload-ready.

## Install From Source

Use a local editable install only inside an isolated development environment:

```bash
python -m pip install -e package_candidates/review_branch_packet
```

This is not a publication instruction and does not upload anything.

## Usage

```bash
review-branch-packet inspect --target review/machlib-function-class-frontier-2026-05-20
review-branch-packet inspect --target review/machlib-function-class-frontier-2026-05-20 --json
review-branch-packet inspect --target review/machlib-function-class-frontier-2026-05-20 --out packet.json
review-branch-packet inspect --target review/machlib-function-class-frontier-2026-05-20 --markdown-out packet.md
PYTHONPATH=package_candidates/review_branch_packet/src python -m review_branch_packet.cli inspect --target review/machlib-function-class-frontier-2026-05-20 --json
```

## Read-Only Git Commands

The package only uses read-only commands:
- `git status --short`
- `git branch --show-current`
- `git remote -v`
- `git log --oneline -N`
- `git ls-remote --heads origin <target>`

It does not run forbidden commands such as `git push`, `git pull`, `git fetch`, `git checkout`, `git merge`, `gh pr create`, deploy commands, upload commands, or package publish commands.

## Packet Contents

The JSON and Markdown packet include:
- branch summary
- remote review branch summary
- latest commits
- working tree status
- validation summary placeholders
- no-go confirmations
- human approval requirements
- recommended next actions

## Limitations

This package does not validate theorem/proof content, does not create pull requests, does not merge, does not deploy, does not push, and does not publish packages. It is a local reviewer packet helper for MachLib/Monogate workflow evidence.
