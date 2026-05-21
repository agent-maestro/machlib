# review-branch-packet

`review-branch-packet` is a local draft package candidate for building private review branch packets from read-only git state. It packages the repeated MachLib private-review inspection workflow into a small CLI and library surface.

Status:
- Local draft only.
- No PyPI release performed.
- No PyPI package name availability check performed.
- No PyPI token handling performed.
- No package publish performed.
- No release artifacts created.
- Not release-ready and not upload-ready.
- Package name availability is unknown and was not checked.

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
review-branch-packet inspect --target review/machlib-function-class-frontier-2026-05-20 --repo . --remote origin --log-limit 20
review-branch-packet inspect --target review/machlib-function-class-frontier-2026-05-20 --include-validation-placeholder
PYTHONPATH=package_candidates/review_branch_packet/src python -m review_branch_packet.cli inspect --target review/machlib-function-class-frontier-2026-05-20 --json
```

The default command prints a Markdown packet. `--json` prints JSON. `--out` writes JSON to a file, and `--markdown-out` writes Markdown to a file.

## Read-Only Git Commands

The package only uses read-only commands:
- `git status --short`
- `git branch --show-current`
- `git remote -v`
- `git log --oneline -N`
- `git ls-remote --heads <remote> <target>`

The command runner is allowlist based. It refuses forbidden commands such as `git push`, `git pull`, `git fetch`, `git checkout`, `git merge`, `git rebase`, `git reset`, `git add`, `git commit`, `gh pr create`, `npm run deploy`, `twine upload`, deploy commands, upload commands, or package publish commands.

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

## JSON Output Example

```json
{
  "packet_id": "review_branch_packet_2026_05_20",
  "target_review_branch": "review/machlib-function-class-frontier-2026-05-20",
  "local_only": true,
  "read_only": true,
  "review_branch_present": true,
  "local_head_sha": "cafebabe",
  "local_head_short": "cafebab",
  "working_tree_clean": true,
  "push_performed": false,
  "github_pr_created": false,
  "merge_performed": false,
  "command_center_deploy_performed": false,
  "package_publish_performed": false,
  "pypi_token_handling_performed": false
}
```

## Markdown Output Example

```markdown
# Review Branch Packet

## Branch Summary
- Current branch: feat/ac-instances
- Local HEAD: cafebab

This packet is not a PR, not a merge, not a deploy, and not a publish.
```

## Relation To Monogate/MachLib

This package candidate is a local helper for MachLib/Monogate private-review preparation. It summarizes branch state and validation placeholders so a human reviewer can inspect a packet before any separately approved push, PR, merge, deploy, upload, or publication task.

## Limitations

This package does not validate theorem/proof content, does not create pull requests, does not merge, does not deploy, does not push, and does not publish packages. It is not a PR creator, not a deploy tool, not a package publisher, and not a release/publication gate by itself. It is a local reviewer packet helper for MachLib/Monogate workflow evidence.
