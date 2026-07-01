# Claim auditor

**Makes "closed" mean closed.** A standing gate that resolves every *prose* claim
("proven", "unconditional", "no `sorryAx`", "dirty-axiom-free", …) against the
**actual `#print axioms` footprint** of the theorem it cites, and fails loud when a
headline outruns its trail.

The narrow `@verify` binding-integrity gate already pins each proof obligation to its
Lean `tree_hash`. This generalizes that idea to **natural language**: the README, the
CHANGELOG, and blog posts make claims about theorems, and those claims can silently
drift away from what the code actually proves — a renamed-not-resolved axiom, a
refactor that reintroduces `sorry`, a headline edited to sound stronger. This gate
catches that.

## What it checks

For each entry in `claims.json`:

1. **Claim drift (B).** The `claim_text` substrings (whitespace-normalized, so
   line-wrapping is fine) must still appear in `source_file`. If the prose moved or
   changed, the registry no longer describes the repo → re-audit.
2. **Axiom drift (A).** `#print axioms theorem` is run for real, and none of the
   entry's `forbid_axioms` may appear in the transitive closure. `#print axioms` is
   the ground truth — the same trail used to verify every close in this repo.

## Run

```bash
cd foundations
python3 tools/claim_audit/claim_audit.py             # audit the registry
python3 tools/claim_audit/claim_audit.py --self-test # + prove the gate goes RED on a canary
python3 tools/claim_audit/claim_audit.py --registry PATH  # audit an alternate registry
```

Exit `0` = every claim's footprint matches its prose. Non-zero = a headline outran its
footprint.

## Why the `--self-test` canary

A gate that never fails on a known violation is decoration (this repo's own rule:
*prove the gate goes red on an injected regression*). `--self-test` injects a
`by sorry` theorem falsely claimed `sorryAx`-free and requires the gate to catch it.
It has also been exercised against the **real** citation-based theorem
`MachLib.Real.pfaffian_zero_count_bound_classical`: claiming *that* one
dirty-axiom-free fails with `FORBIDDEN axiom zero_count_bound_classical present`, and
against a claim whose text was removed from its doc (claim drift) — both go red.

## Adding a claim

When a doc calls a theorem "clean"/"proven"/"unconditional", **register it here**.
Registering is cheap; the gate then guarantees the prose and the proof cannot part
ways without CI turning red. A headline that calls a theorem clean *without* a
registry entry is exactly the anti-pattern this tool exists to discourage.

```jsonc
{
  "id": "short-slug",
  "source_file": "CHANGELOG.md",            // relative to the machlib/ repo root
  "claim_text": ["theorem_name", "the distinctive claim phrase"],
  "module": "MachLib.SomeModule",
  "theorem": "MachLib.SomeModule.the_theorem",
  "forbid_axioms": ["sorryAx", "zero_count_bound_classical"]
}
```

## Scope (honest)

- v0 checks **axiom footprint** and **claim presence**. It does *not* yet parse a
  claim like "unconditional" into a hypothesis-shape check (e.g. "has no
  `terminal_nonzero` binder"); that is a clean future extension.
- The registry is **curated**, not auto-extracted from prose. Requiring a claim to
  name its theorem is deliberate — it kills vague "machine-verified" copy with no
  referent.
