# review-branch-packet

`review-branch-packet` is a pre-alpha package for building private review branch
packets from read-only git state. It packages the repeated Monogate/MachLib
private-review inspection workflow into a small CLI and library surface.

It is not a PR creator, not a merge tool, not a deploy tool, not a package
publisher, not a theorem prover, not a safety certifier, not production
controller evidence, not a replacement for Mathlib, and not a public
theorem/proof/open-problem claim.

## Status

- Version: `0.0.1`
- Published for early testing.
- Intended for read-only review packet generation.
- Does not push, pull, fetch, merge, deploy, upload, publish, or handle tokens.

## Install

```bash
python -m pip install review-branch-packet
```

For repository development:

```bash
python -m pip install -e package_candidates/review_branch_packet
```

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

The default command prints a Markdown packet. `--json` prints JSON. `--out`
writes JSON to a file, and `--markdown-out` writes Markdown to a file.

## Read-Only Git Commands

The package only uses read-only commands:

- `git status --short`
- `git branch --show-current`
- `git remote -v`
- `git log --oneline -N`
- `git ls-remote --heads <remote> <target>`

The command runner is allowlist based. It refuses forbidden commands such as
`git push`, `git pull`, `git fetch`, `git checkout`, `git merge`, `git rebase`,
`git reset`, `git add`, `git commit`, `gh pr create`, deploy commands, upload
commands, and package publish commands.

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

## Relationship To Monogate/MachLib

This package is a helper for Monogate/MachLib private-review preparation. It
summarizes branch state and validation placeholders so a human reviewer can
inspect a packet before any separately approved push, PR, merge, deploy, upload,
or publication task.

## Limitations

- Does not validate theorem/proof content.
- Does not create pull requests.
- Does not merge, deploy, push, upload, or publish packages.
- Does not manage credentials or tokens.
- Does not replace human review.
