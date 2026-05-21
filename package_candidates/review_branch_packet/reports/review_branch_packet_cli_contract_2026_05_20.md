# review-branch-packet CLI Contract

## CLI Commands

- `review-branch-packet inspect --target <review-branch>`
- `review-branch-packet inspect --target <review-branch> --json`
- `review-branch-packet inspect --target <review-branch> --out packet.json`
- `review-branch-packet inspect --target <review-branch> --markdown-out packet.md`

## Read-Only Git Command Set

- `git status --short`
- `git branch --show-current`
- `git remote -v`
- `git log --oneline -N`
- `git ls-remote --heads origin <target>`

## Forbidden Commands

The CLI must not run `git push`, `git pull`, `git fetch`, `git checkout`, `git merge`, `gh pr create`, deploy commands, upload commands, twine commands, or package publish commands.

## JSON Schema

The JSON packet includes `packet_id`, `target_review_branch`, `generated_at`, `local_only`, `read_only`, `review_branch_present`, `local_head_sha`, `review_branch_sha`, `latest_commits`, `working_tree_clean`, `dirty_files`, `blocked_actions`, `no_go_confirmations`, and `recommended_next_actions`.

## Markdown Packet Sections

The Markdown packet includes branch summary, remote review branch summary, latest commits, working tree status, validation summary placeholders, no-go confirmations, human approval requirements, and recommended next actions.

## Exit Codes

Exit code `0` means the read-only packet was generated. A subprocess or argument failure returns nonzero through normal Python CLI behavior.
