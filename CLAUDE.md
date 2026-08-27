# CLAUDE.md — MachLib

**What this is.** A Mathlib-free Lean 4 corpus that proves things about EML kernels — the little
functional language Forge compiles to hardware — so that claims about compiled silicon rest on
machine-checked theorems rather than on prose.

## Architecture

Everything of substance is under **`foundations/`** (the repo root is docs, evidence, and site
material). `foundations/MachLib/` holds **1 056 `.lean` files** (740 top-level + 316 in subdirectories) /
**~235 k lines** / **8 231 theorems**, re-exported through the aggregator
**`foundations/MachLib.lean`** — a module not reachable from there is **invisible to
`lake build` and to every gate**, which is the single most common way to ship dead work.
(Counts are `find`/`grep` over `MachLib/`, theorems excluding `Discovered/`; re-derive with the
commands, do not trust the figure. An earlier revision said 5 851 theorems by an unrecorded method —
a number nobody can reproduce is worse than one that names how it was taken.)
**`MachLib/Discovered/` (294 files) is deliberately outside the aggregator**: each file is
self-contained and they cannot be imported together; it is the Forge `@verify(lean)` corpus and has
its own harness, `scripts/closerate.sh`. The numeric
substrate is **`MachLib.Real`**, an *axiomatised* real field (274 `axiom` declarations, every one
disclosed in **`foundations/axiom_ledger.json`**): there is no Mathlib, no `Complex`, and
`Real.log` is **totalised** — `log y = 0` for `y ≤ 0`, which is load-bearing in EML proofs and a
frequent source of surprise. Custom tactics **`mach_ring`** and **`mach_mpoly`** replace `ring`/
`linarith`.

## The axiom count, reconciled (do not re-derive this)

`lake env lean AxiomLedger.lean` reports **243 axioms pinned**. That number decomposes exactly, and
grepping the sources will *not* reproduce it:

```
221  MachLib.*   axioms in the environment after `import MachLib`
 22  Certcom.*   IEEE-754 floor axioms
---
243  = what the ledger pins
```

(Re-derive the split with a `#eval` over `getEnv` partitioning `.axiomInfo` by name prefix — that is
how these two were measured, not by grep.)

A further **15** axioms are present but *not* pinned — they are Lean's own kernel/compiler trust
base, not project axioms: `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `Quot.lcInv`,
`Lean.{ofReduceBool,ofReduceNat,trustCompiler}`, `isScalarObj`, and the `lc*` compiler internals.

**Why grep disagrees:** `grep -c '^ *axiom '` over `MachLib/*.lean` returns **278** (511 including
subdirectories, which the environment mostly does not see). When this was last decomposed by hand the
gap was docstring prose plus axioms in unreachable modules; those two sub-counts are **not**
re-derived here and should not be quoted as current. Use the environment (`getEnv`, `.axiomInfo`), never grep —
this is the same rule as *"axiom-absence claims must be read off `#print axioms`."*

## Where the content comes from

Self-contained. EML semantics live in `MachLib/SinNotInEML.lean` (the `EMLTree` type and `eval`);
the forward-error certifier is documented in `foundations/docs/forward_error_certifier.md`; the
authoritative claim inventory is **`foundations/docs/what_is_proven.md`**.

## How to run the gates

**All seven run from `foundations/`, not the repo root** (this is what CI does):

```bash
cd foundations
lake build                                     # 719 jobs, ~3 s warm
bash scripts/check_aggregator.sh               # every module reachable
bash scripts/check_consistency_model.sh        # flagship closure has an external ℤ-model
bash scripts/check_discovered_compiles.sh 4    # the 294 Forge @verify files still compile (~1 min)
lake env lean AxiomLedger.lean                 # "243 axioms pinned; 57 headline footprints ⊆ trusted"
python3 tools/claim_audit/claim_audit.py       # "all 477 claims resolve against #print axioms"
bash tools/check_obligations.sh                # EMLDepthTameness's open/discharged rows ↔ the corpus
```

`python3 tools/witness_audit.py` is the newest **measurement harness** and is likewise **not** a CI
gate. It reports every registered claim-theorem that takes hypotheses and is referenced nowhere else
in `MachLib/` — i.e. nobody has ever supplied its hypotheses. That is the one signal that was present
and unread when `positive_branch_impossible` was vacuous: it had no caller and no specimen. The
baseline is pinned as a **set** (`tools/witness_baseline.json`, 36 entries), not a count, so the
ratchet turns one way — a new entry fails, a witnessed one must be removed. It carries two convict
specimens of its own. Read its scope note before trusting it: no-caller is not a defect on its own,
and it cannot see vacuity, only drift.

`lake env lean tools/sorry_audit.lean` is useful (`1 sorryAx`, allowlisted) but is **not** a CI gate,
and note its scope: it walks the **environment** after `import MachLib`, so it cannot see
`Discovered/`. Neither is `scripts/closerate.sh`, which is a *measurement* harness (close-rate,
77.1% at the last sweep), not pass/fail. The CI gate set is exactly the seven above
(`.github/workflows/build-time.yml`).

Note what the last two gate, because it is *not* the same thing. The claim auditor pins prose to the
axiom footprint of a theorem that **exists**; it is structurally blind to a claim about a theorem
that does not — including "this obligation is still open". `check_obligations.sh` covers that one
case: it fails if a row says open and the corpus disagrees, or says discharged and the cited theorem
does not conclude the proposition. Neither gate can tell you a claim with no registered theorem
behind it is missing — registration is still a human act.

## Gotchas

- **`lake` from `foundations/`.** From the repo root it silently resolves the wrong toolchain (v4.14).
- **Stale `.olean`s.** `lake env lean Foo.lean` typechecks against *old* dependencies; run
  `lake build MachLib.Foo` first or `#print axioms` will report unknown constants.
- **A new module must be REACHABLE from `MachLib.lean`** or it is never built and never gated.
  Being imported by a sibling is **not** enough — an island of mutually-importing modules is
  unreachable. `check_aggregator.sh` does a real transitive closure (**750 of 1056 reachable**).
- **`open Real` shadows `max`** — write `Nat.max`, and feed `omega` the `Nat.le_max_*` lemmas.
- **`set`, `linarith`, `ring` do not exist here.** Use `mach_ring` / `mach_mpoly`.
- **Keep coefficients symbolic.** `mach_mpoly` times out on `16·P²` and proves `(c·c)·(a·a)` instantly.
- **Deep `rfl` needs `set_option maxRecDepth`** (29 M-node terms check fine at 40 000 000).
- **Axiom-absence claims must be read off `#print axioms`, never a name-grep** — `exp_gt_one_plus_self`
  and `exp_tangent_line_strict` are the same content under two names.
- **`open MachLib.Real` + `open …AerospaceActuatorGuardBandRate (le_min …)` collide.** Both export a
  `le_min`; a bare `apply le_min` is then ambiguous. Qualify it. (This broke 5 `Applications/`
  modules for an unknown length of time — they were in an unreachable island, so no gate saw it.)
- **These order lemmas do NOT exist here**: `lt_or_ge`, `lt_trans`, `lt_irrefl`,
  `mul_lt_mul_of_pos_left`, `le_or_lt`, `add_lt_add_right`. The local idioms are
  `rcases lt_total`, `lt_of_lt_of_le … (le_of_lt …)`, `(ne_of_lt h) rfl`, `mul_lt_mul_pos_left`,
  `add_le_add_wit`, `add_lt_add_left`.
- **A new module needs `open Real`** inside `namespace MachLib`, or `exp`/`log` are unknown.
- **Casing on a tree then applying a lemma with an implicit tree argument leaves a metavariable** —
  pass `(A := EMLTree.const c)` explicitly, or the shape-specific proof term fails to typecheck.
- **Forward references bite**: a theorem is only usable *below* its declaration in the same file.
- **`min` and `abs` do not exist.** Use `two_bound_witness` (`a·b·exp(−a−b)` is positive and strictly
  below both `a` and `b`) rather than hand-rolling a fourth bespoke two-constraint expression.
- **`mach_mpoly` stalls in `Lean.Meta.acLt` when nested `(1+1)` constants must be DISTRIBUTED over
  sums.** Four specimens pin it: nested `64` under pure commutativity is fine (1 s); the same
  constant in a degree-3 identity with subtractions dies (69 s at 4 000 000 heartbeats); the
  identical identity with `natCast` constants **completes in 1.9 s**; so does the flagship numeral
  obligation (2.3 s) that previously exhausted the same budget. So it is the encoding under
  distribution, not degree, not presentation, and not constants per se.
  **First try splitting the call**: keep each binomial product atomic (bind it to a variable) so no
  single call distributes two brackets — a degree-3 identity that died at 4 000 000 heartbeats
  closes as four ~1 s steps that way.
  **Otherwise:** write constants as `natCast N`; `mach_mpoly` then treats each as one atom and
  normalises fine, but cannot do their arithmetic — supply products via
  `rw [← natCast_mul]` (instant, `Nat` literal equality) *before* calling it.
- **`first | … | …` does not backtrack out of errors inside a nested `by` block** — only out of
  tactic failure. A branch whose `mach_mpoly` makes partial progress and then errors is committed
  to, not abandoned. Use explicit per-case bullets when the branches are genuinely different proofs.
- **`OfNat Real` exists only for `0` and `1`.** `(2 : Real)` does not elaborate. Write constants as
  `natCast N` (`NatCastArith`), **never** as `1+1+…`: `mach_mpoly`'s AC matching diverges on unary
  numerals — a degree-2 identity with constants near `1.4·10⁴` exhausted 4 000 000 heartbeats (20×
  the default) without progress. This is the operational form of "keep coefficients symbolic".
- **A theorem whose conclusion is a ledger obligation needs a BINDER, not an arrow.**
  `tools/obligation_ledger_check.py` reads a conclusion as the tail after the last top-level `:`,
  having first stripped binders of the obligation's own type. So `foo : A → B` has tail `A → B` and
  is counted as a **discharger of `A`** — if `A` is a *refuted* row the gate reports a contradiction
  that does not exist, and if `A` is *open* it reports the row as stale. Write `foo (h : A) : B`,
  which strips correctly. (`depth3DecayExp_of_hard` is the worked case; both forms were run against
  the parser before choosing.)
- **A CONDITIONAL THEOREM IS NOT EVIDENCE UNTIL ITS HYPOTHESES ARE INSTANTIATED.** Two hypotheses in
  the `S > 0` pole layer were *unsatisfiable for every `q`*, so the flagship
  `positive_branch_impossible` was vacuously true and proved nothing — and **every gate passed**, for
  weeks. `False → P` is provable, cites no bad axioms, and discharges any obligation. Build a
  **specimen** (`GermClearedSpecimen`) discharging every hypothesis, and ship it with the capstone;
  it then fails to compile if a hypothesis ever becomes unsatisfiable again. Tell-tale before it was
  found: the capstone had **no caller and no specimen anywhere**.
- **Suspect `∀ n` hypotheses at indices nobody consumes.** `∀ r, DerivCoprime q r` was false at
  `r = 0` (`pnsum 0 _ = []`, and everything divides the zero polynomial) while every proof site used
  `r + 1`. If no site applies a hypothesis at index `k`, ask whether it *holds* at `k`.
- **`pderiv` is LENGTH-PRESERVING, so its output always carries a trailing zero** (`pderiv [a,b] =
  [b, 0]`) and is **never `PNormal`**. Any hypothesis asserting canonicity of a `pderiv`/`pnsum`
  image is unsatisfiable. Use `pnorm` first, or a normalisation-invariant lemma — `euclid_lemma'`
  drops `euclid_lemma`'s `PNormal` side condition entirely, since `Pdvd` already sees only `pnorm`.
- **`obtain` on a `GEvEq` entry against `expCoeffs` yields an UNREDUCED application** —
  `a x = (fun C x => bipev C x (exp (S x))) C x` — so `rw [← e]` will not match the beta-reduced
  goal. Bind it through a typed `have e' : a x = bipev C x (exp (S x)) := e x hx`.
- **A gate's own self-test can go stale when the corpus improves.** `obligation_ledger_check.py`'s
  canary 9 is a literal specimen, and its `open` row must name something no theorem can conclude —
  it named live obligations twice and both were discharged the same day, failing the gate because
  work succeeded. `discharged`, `refuted` and `reduced` specimens are stable; `open` is not.

## Counts: the gate is the source, prose is a copy

**No count in prose — a claim total, an axiom total, an open-obligation total, a job count — may be
written from memory or arithmetic-in-the-head. Run the gate, read its number, paste it.** Prose is a
copy of gate output and never authoritative.

This is policy, not advice, and it is empirical: in the 2026-08 arc three separate remembered counts
went into a changelog wrong (`claims 429` for 431, `claims 439` for 438, and an earlier `5 851
theorems` by an unrecorded method that nobody can reproduce). The gates were right every time and
cost about a second each. A wrong count is worse than a missing one, because it reads as measured.

Corollary for the gates themselves: **a check that is silent on success is indistinguishable from a
check that did not run.** Print the figure even when nothing is wrong — `check_obligations.sh` prints
its footprint tally for exactly this reason.

## Status

Lean `v4.32.2`, branch `poly-euclid-spine`. All seven gates green (753 build jobs) at **true exit
codes** — note `gate | tail` reads `tail`'s status, not the gate's. `sorryAx`: 1, allowlisted.
**243 axioms pinned — unchanged across the whole 2026-08 EML arc**, including the `S > 0` repair and
the entire depth/decay programme below. Obligations ledger: **21 rows, 9 open rows, 6 distinct open
obligations** (a reduction cycle and a proved equivalence each carry several rows for one debt).

**The `S > 0` branch was VACUOUS and is now repaired** (`a10b3b5b`, 2026-08-24). Two pole hypotheses
were unsatisfiable for every `q`: `∀ r, DerivCoprime q r` (false at `r = 0`) and
`∀ r, PNormal (pnsum r (pderiv q))` (false at every `r ≥ 1`). The first was weakened to `r + 1`
(proof-neutral); the second was **deleted** — it fed one `euclid_lemma` call and was not merely
unsatisfiable but decorative. `GermClearedSpecimen` now discharges every hypothesis at `q = x`,
`P = 1`, `Q = x`, giving

```
no_proper_cleared_relation_inv_x : ClearsToExp (1/x) fs → GProperRel (log(1/x)) fs → False
```

with **no pole hypotheses assumed**. `pIrred_X` is the corpus's first `PIrred` construction. Read the
changelog's `(ci)` VOID before citing anything about this branch.

**Degree-`d` is closed.** `ClearsToExp` (a class whose members clear, over one common
eventually-non-vanishing denominator, to `expCoeffs` images) discharges all three obligations of
`minimal_expRel_identity_in`; `no_proper_cleared_relation` takes no `hmin`, no `Cs`, no split and no
degree bound. Two findings worth carrying: `gscaleSub` denominators do **not** multiply (the step is
asymmetric — only one factor per product is ever dirty), so no denominator *bound* is needed; and
`EvNonvanish` (non-zero on a tail) is required over "not eventually zero", because germs have zero
divisors and the weak form silently breaks properness.

**Still open.** `SignHardCase` is **discharged** (`signHardCase_holds`, `d7b8d28c`) — this line said
otherwise for weeks; read the ledger, not this paragraph, and if they disagree the ledger is right
because a gate checks it. The six distinct open obligations are: the
`DecayFloor` ⇄ `EmlGermApproach` ⇄ `GrowthEnvelope` cycle (**one** obligation, three rows),
`TowerLowerBound` ⇄ `TowerReducesToSign` (one obligation, two rows, equivalent since `SignHardCase`
fell), `NegativeTranslationGrowingLeft`, `OneQueryDichotomy`, `BoundedGermTranscendence`,
`OneQueryLevelSet`.

Recent arc: **EML characterised** as exactly the `exp`/`log` closure of `ℝ`; then
`s(1/x) ∈ {7,9,11}` proved, `d(1/x)` frozen at `{3,4}`, and a depth- and size-indexed **growth
envelope** built. Start here:
`monogate-research/exploration/inv_x_termination_route_2026_08_06/EML_STATUS.md`, and
`FRONTIER_BRIEF_3.md` for the open questions.

**2026-08-26/27 — the decay programme, `(dk)`–`(dy)`.** Four things a new session should know before
touching it, because each was learned the expensive way:

1. **The induction search is closed, on both sides.** `EMLLadderMeasure`: no `Nat`-valued measure on
   trees that descends to both children can carry it — syntactic (`recipTree` costs two steps while a
   step buys one) or germ-based (`EMLGermApproach` §4: growth does not descend to the *right* child,
   unboundedly). Stated at that width and no wider: lexicographic orders, ordinal ranks and
   non-structural arguments are untouched.
2. **The missing input is named and placed.** `EmlGermApproach` (`EMLGermApproach`) is the obligation
   at its narrowest, equivalent to `DecayFloor`. Its *per-pair* form is a corollary of Hardy (1912);
   **the entire open content is the position of one `∃ k`** — see
   `monogate-research/exploration/germ_approach_literature_2026_08_27/NOTE.md`. **No axiom has been
   spent on it, deliberately.**
3. **The ladder reaches the obligation.** `decayFloor_of_ladderInputs` (`EMLValueGap`): `DecayFloor`
   follows from per-depth `NodeDecayBound` + `LowerEnvBound`, footprint-clean. `decayFloorUpTo_three`
   is proved (the top was depth 2 for the whole arc); depth 4 needs `NodeDecayBound 3`, whose only
   known route is the depth-≤2 cell enumeration that `FRONTIER_BRIEF_3` §4 Q2 measured and
   **rejected**. Do not start it without deciding that a bounded rung is worth it — bounded rungs do
   not move the ledger.
4. **Everything above is pointwise on purpose.** The hypotheses of `NodeDecayBound` and
   `ValueGapBound` are guarded *inside* the `∀ x`. An eventual reading would need `evSign_all` and
   with it the analytic block, across the entire ladder. It also blocks two converses — see `(dx)`,
   `(dy)` — and that is the accepted price.
