# Upstream report — Lean4Lean at `v4.26.0` cannot replay `Init.Core`

**Status: DRAFTED, NOT YET FILED.** Filing posts to a third party's public tracker under the project
owner's identity, so it waits for a go-ahead. Everything below is ready to paste.

**Why we care, stated plainly in the report:** the destination configuration (`v4.32.2`) wants this
instrument working. Reporting it with a minimal repro is the cheapest way to make that more likely —
part citizenship, part self-interest, and the report says so rather than pretending otherwise.

The watch (`tools/migration/watch_kernel_support.py`) now reads their issue tracker and will report
this as `NOT FILED` until an issue whose title contains `String.ofList`, `Char.ofNat` or
`unknown constant` appears — matched on the symptom, not on our issue number, so that someone else
reporting it first also counts.

---

## Suggested title

    v4.26.0: `unknown constant 'String.ofList'` replaying Init.Core; SIGSEGV on larger modules

## Body

Building `lean4lean` at any commit pinning `leanprover/lean4:v4.26.0` produces a checker that cannot
replay Lean's own core library, or its own.

**Repro — entirely within this repository, ~5 seconds, no third-party project involved:**

```console
$ git clone https://github.com/digama0/lean4lean ~/lean4lean-v4.26.0
$ cd ~/lean4lean-v4.26.0 && git checkout f37aeab && lake build lean4lean
$ cat lean-toolchain
leanprover/lean4:v4.26.0

$ lake env .lake/build/bin/lean4lean Init.Core
lean4lean found a problem in Init.Core:
at «_aux_Init_Core___macroRules_term_⊇__1»: (kernel) unknown constant 'String.ofList'
# exit 1

$ lake env .lake/build/bin/lean4lean Lean4Lean      # this repo's own library
# exit 139 (SIGSEGV), no output
```

**Affected commits — all three builds that exist at this version:**

| commit | branch | `Init.Core` | a small downstream module |
|---|---|---|---|
| `f37aeab` | master, pins v4.26.0 | `unknown constant 'String.ofList'` | SIGSEGV |
| `6bca7f6` | master, last commit pinning v4.26.0 | `unknown constant 'Nat'` | `unknown constant 'LE.le'` |
| `56d4dc5` | `arena-v4.26.0` | `unknown constant 'String.ofList'` | SIGSEGV |

On a larger library the `6bca7f6` failure mode reports a distinct "problem" for essentially every
module — `Nat`, `Eq`, `Not`, `Prod`, `Unit`, `Ne`, `NeZero`, `LE.le`, `LT.lt`, `HSub.hSub`,
`HMul.hMul`, `Char.ofNat` — while resident memory climbs to ~61 GiB in 50 seconds. We hit that as
four consecutive OOM kills (59.0–90.4 GiB) before diagnosing it.

**Suspected code path, offered as a lead rather than a diagnosis** — we have not confirmed the
mechanism. `Main.lean`'s string-literal special case in `replayConstant`:

```lean
unless (← get).hasStrings do
  if ci.hasStrLit then
    usedConstants := usedConstants.insert ``String.ofList
    usedConstants := usedConstants.insert ``Char.ofNat
    modify ({· with hasStrings := true })
```

`String.ofList` and `Char.ofNat` are exactly the two names this inserts, and `Char.ofNat` is what a
string-literal-heavy module failed on for us. The `hasStrings` latch flips on the first declaration
carrying a string literal, so if that declaration's `replayConstants` does not actually land
`String.ofList` in the environment — e.g. because it is imported rather than new, and so is not in
`remaining` — no later declaration retries, and the kernel meets the literal without it.

**Environment:** Linux aarch64 (NVIDIA GB10), 128 GB, elan-managed `leanprover/lean4:v4.26.0`.
`lean4checker` at the same version replays the same `.olean` tree clean, so the artifacts themselves
are readable.

---

## What this cost us, kept in-house rather than in the report

The four OOM kills were the visible symptom; the expensive part was nearly believing them. An orderly
non-zero exit carrying `unknown constant 'Nat'` is indistinguishable, to a naive classifier, from a
genuine kernel rejection of our environment — and ours classified it as exactly that. Only the OOM
kill stopped the gate from filing `REPLAY_FAIL` against a tree `lean4checker` had passed forty minutes
earlier.

The fix on our side is step **1b** in `tools/axiom_ledger/check_lean4lean_replay.py`: positive
controls (`Init.Core` + one of ours) that must PASS before step 2 is allowed to render any verdict.
Detection cost: ~15 seconds, versus four OOM kills and a morning. See `MIGRATION_LOG.md`, "Newest
substrate: an instrument, scoped to its own environment".
