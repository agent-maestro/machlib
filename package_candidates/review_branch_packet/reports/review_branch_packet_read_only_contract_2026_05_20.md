# review-branch-packet Read-Only Contract - 2026-05-20

## Allowed Commands

The package command runner only permits:

- `git status --short`
- `git branch --show-current`
- `git remote -v`
- `git log --oneline -N`
- `git ls-remote --heads <remote> <target>`

## Forbidden Commands

The package refuses:

- `git push`
- `git pull`
- `git fetch`
- `git checkout`
- `git merge`
- `git rebase`
- `git reset`
- `git add`
- `git commit`
- `gh pr create`
- `npm run deploy`
- `twine upload`

## CLI Contract

Supported commands:

- `review-branch-packet inspect --target <branch>`
- `review-branch-packet inspect --target <branch> --json`
- `review-branch-packet inspect --target <branch> --out packet.json`
- `review-branch-packet inspect --target <branch> --markdown-out packet.md`
- `review-branch-packet inspect --target <branch> --repo <path>`
- `review-branch-packet inspect --target <branch> --remote origin`
- `review-branch-packet inspect --target <branch> --log-limit 20`
- `review-branch-packet inspect --target <branch> --include-validation-placeholder`

## Output Contract

JSON output includes branch state, remote review branch state, latest commits, working tree state, dirty files, validation placeholders, blocked actions, no-go confirmations, and default-false action flags.

Markdown output includes branch summary, remote review branch summary, latest commits, working tree state, dirty files when present, validation placeholders, package/PyPI boundary, no-go confirmations, approval requirements, and recommended next actions.

## Exit Codes

Successful read-only inspection exits 0. Forbidden command attempts or unreadable git inspection failures exit nonzero through the CLI error path.
