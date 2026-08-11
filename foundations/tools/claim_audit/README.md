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

## What this gate is for: **proof–claim drift**

Traditional proof checking asks *is theorem T valid?* A corpus written with machine
assistance raises a second, independent question: *is claim C licensed by theorem T?*
The motivating failure here had **theorem true, no `sorry`, dependencies clean, CI green,
and the prose still false** — `pid_trajectory_from_bits` elaborated to
`fun … => affine_trajectory_bound …`, mentioning no bit-level object, while the docs called
it the bits→trajectory join. Nothing was logically unsound. The overstatement was
*epistemic*, and every existing gate was blind to it by construction: they all check what a
theorem **rests on**, never whether prose describes the theorem that **exists**.

## The ladder

| Level | Question | Mechanism |
|---|---|---|
| 1 | What does the proof rest on? | axiom footprint (`#print axioms`) |
| 2 | Does the statement name the subject? | `statement_mentions` (syntactic) |
| 3 | …even through a definition? | `statement_mentions_deep` (unfolds) |
| 4 | Does it *conclude* about it, or merely assume it? | `conclusion_mentions` |
| 5 | Is the theorem still as strong as when the prose was written? | `hypotheses_count` |
| 6 | Does the proof actually invoke the other half? | `proof_uses` |
| 7 | Does the prose assert **this relation** between these objects? | **generated, not checked** |

Level 7 is where a substring search stops being able to help. *"Does this sentence assert
relation R between A and B"* is a semantics question, so it is **not answered — it is
deleted**: a claim is a typed record, the licensed sentence is **rendered from** the record,
and the auditor requires that exact sentence in the document. Set membership, decidable.
The relation is therefore **binding, not verified** — the system does not prove an English
concept is equivalent to these checks; it *defines* that claim class to require them.

## The trust boundary, stated plainly

Once level 7 trades semantics for set membership, **all remaining trust sits in two places**:
the sentence **templates** and the **obligation lists**. A template rendering prose stronger
than its obligations warrant is the original overclaim one layer down, wearing a green
checkmark — and no check can catch it, because that is precisely the question level 7 deleted
rather than solved.

So it is not verified. It is made **expensive**. `RELATIONS` and `ENTAILS` are pinned by
`relations.lock.json`; editing a template or an obligation list breaks the pin and **fails the
shipping path** until `--bless-relations` is run deliberately. Extending the relation
vocabulary is a ceremony, for the same reason extending an axiom base is one. Two consequences
worth stating rather than discovering:

- **No implicit hierarchy.** `asymptotic_upper_bound` genuinely implies `pointwise_upper_bound`
  and their obligation lists are identical — and the machinery still refuses it, because the
  pair is not in `ENTAILS`. A declared entailment is additionally checked for
  obligation-monotonicity. Without this, a reader eventually infers an ordering nothing checked.
- **Verbatim only, permanently.** The cost is that flagship prose contains machine-stilted
  sentences, because the sentence *is* the record. Loosening to "paraphrase allowed if adjacent
  to the licensed form" is a one-way door: the moment a paraphrase can stand in, level 7
  degrades back to the judgment call it replaced. Not a tunable.

**A second independent renderer would not help here**, though it is the natural suggestion. Two
renderers over the same table produce the same sentence from the same overclaiming template, so
agreement is guaranteed and says nothing. Correlated failure is real, but the correlation is in
the *table*, not the rendering — which is why the answer is a pin and a ceremony rather than a
duplicate implementation.

## Specimens

Ten canaries, run with `--self-test`; the gate is unvalidated, not passing, without them.
Two are worth singling out because they exist to catch defects that were actually shipped:

- **canary 9** — a *constant-count* obligation swap (`proof_uses` → `statement_mentions`).
  Canary 7 originally asserted `len(objections) == 3`; cardinality is a weak proxy and that
  swap sailed through it. Named by an outside reader.
- **canary 10** — a **true** implication between two relations with **identical** obligations,
  still refused. Built on a true statement on purpose: it shows the refusal is about
  *declaration*, not about correctness.

## Scope (honest)

- The registry is **curated**, not auto-extracted from prose. Requiring a claim to name its
  theorem is deliberate — it kills vague "machine-verified" copy with no referent.
- **Level 3 cannot certify absence.** The deep check unfolds to a budget; finding a constant is
  evidence, not finding one is not. Only the syntactic check is decidable both ways.
- **Composition is not closed yet.** `proof_uses` asks whether one proof invokes another; it does
  not admit *composition rules* the way `RELATIONS` admits relations. Until it does, a chain
  A→B→C licenses nothing about A→C, and no claim in the registry asserts otherwise.
