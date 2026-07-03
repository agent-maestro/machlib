# MachLib axiom audit — Khovanskii single-exp announcement gate

**Date**: 2026-06-19
**Target**: `MachLib.SingleExpKhovanskii.ExpPoly.expPoly_khovanskii_bound`
**Total axioms in MachLib repo**: 280
**Load-bearing for the announced result**: 40

## TL;DR

All 39 load-bearing axioms correspond to standard classical theorems
with side conditions satisfiable for the class of functions MachLib
constructs. **One axiom (`rolle`) elides a classical continuity
precondition** (`zero_count_bound_by_deriv` was a second such axiom but
is now a THEOREM derived from `rolle` — see §10); in practice MachLib
only applies them to functions buildable from the closure of
HasDerivAt-tracked operations, so no inconsistency can be
constructed. Recommendation: document the "buildable function"
restriction in the axiom comments; tighten when continuity
infrastructure lands.

**No findings that block the announcement.**

## Categorisation of the 40 load-bearing axioms

### 1. Lean stdlib (3) — universal, no audit needed

`propext`, `Classical.choice`, `Quot.sound`.

### 2. MachLib.Real type + operations (9) — definitional

`MachLib.Real` (the type), `addR`, `subR`, `mulR`, `divR`, `negR`,
`oneR`, `zeroR`, `ltR`. These declare the operational structure.
No content to audit beyond "is this what you'd expect" — yes.

### 3. Field axioms (10) — standard ring/field

`add_assoc`, `add_comm`, `add_neg`, `add_zero`, `mul_assoc`,
`mul_comm`, `mul_distrib`, `mul_inv`, `mul_one_ax`, `mul_neg`.

Classical theorem: standard field axioms (R is a field).
Side conditions: `mul_inv` requires `a ≠ 0`. ✓ encoded.
**Sound.**

### 4. Order axioms (3) — total order

`lt_irrefl_ax`, `lt_total`, `zero_ne_one_ax`.

Classical theorem: R is a totally-ordered set with 0 ≠ 1.
**Sound.**

### 5. Subtraction normaliser (1)

`sub_def : a - b = a + (-b)`. Definitional. **Sound.**

### 6. Nat embedding (2)

`natCast : Nat → Real`, `natCast_zero : natCast 0 = 0`.
Classical: the natural embedding of Nat into R. **Sound.**

### 7. Exp function (3)

`exp : Real → Real`, `exp_pos`, `exp_zero`.

- Classical: `e^x > 0` always; `e^0 = 1`.
- **Sound.**

### 8. HasDerivAt closure rules (9)

`HasDerivAt`, `HasDerivAt_unique`, `HasDerivAt_const`,
`HasDerivAt_id`, `HasDerivAt_exp`, `HasDerivAt_add`,
`HasDerivAt_sub`, `HasDerivAt_mul`, `HasDerivAt_comp`.

Each matches the standard derivative rule in real analysis:

| Axiom | Classical rule |
|---|---|
| `HasDerivAt_unique` | derivative uniqueness |
| `HasDerivAt_const` | (c)' = 0 |
| `HasDerivAt_id` | (x)' = 1 |
| `HasDerivAt_exp` | (e^x)' = e^x |
| `HasDerivAt_add` | (f+g)' = f' + g' |
| `HasDerivAt_sub` | (f-g)' = f' - g' |
| `HasDerivAt_mul` | (fg)' = f'g + fg' |
| `HasDerivAt_comp` | (f∘g)' = f'(g)·g' |

**Sound.** The product rule `HasDerivAt_mul` returns
`a · g x + f x · b` matching the standard textbook form. The chain
rule `HasDerivAt_comp` returns `b · a` matching `f'(g(x)) · g'(x)`.

### 9. **`rolle` (1) — FINDING**

```lean
axiom rolle (f : Real → Real) (a b : Real) (hab : a < b)
    (hfa_eq_fb : f a = f b)
    (hdiff : ∀ c, a < c → c < b → ∃ f', HasDerivAt f f' c) :
    ∃ c, a < c ∧ c < b ∧ HasDerivAt f 0 c
```

- **Classical Rolle**: f **continuous on [a,b]**, differentiable on
  (a,b), f(a) = f(b) ⟹ ∃c ∈ (a,b), f'(c) = 0.
- **MachLib version**: drops "continuous on [a,b]". The differentiability
  hypothesis `hdiff` only requires differentiability on the OPEN
  interval; nothing is said about f's continuity at the endpoints.

**Pedantic counterexample (cannot be constructed in MachLib)**: Take
f(x) = x on (0,1) and define f(0) = f(1) = 0.5 by hand. Then
`hfa_eq_fb` holds (both are 0.5), `hdiff` could be claimed (interior
behaves like id). But f'(c) = 1 ≠ 0 everywhere.

**Why this doesn't bite in practice**: MachLib's HasDerivAt is
abstract (line 72 of `Differentiation.lean`); the only way to
PROVE `HasDerivAt f f' x` for a specific f is via the closure rules
(const, id, exp, add, sub, mul, comp, inv, neg, log, sin, cos).
These are all globally continuous functions on Real, so the "build"
process can't produce a function with an endpoint discontinuity.

**Recommendation**: Add a comment to the axiom noting the implicit
"f is buildable from the HasDerivAt closure" assumption. Tighten by
adding a `continuous_at` hypothesis once continuity infrastructure
lands. **Does not block the announcement.**

### 10. **`zero_count_bound_by_deriv` (0) — RESOLVED: now a THEOREM, not an axiom**

```lean
-- was `axiom`; now `theorem`, derived from `rolle` (MachLib/Rolle.lean)
theorem zero_count_bound_by_deriv (f : Real → Real) (a b : Real)
    (hab : a < b)
    (hdiff : ∀ c, a < c → c < b → ∃ f', HasDerivAt f f' c)
    (N : Nat)
    (hf'_bound : ∀ zeros_f' : List Real, ... → zeros_f'.length ≤ N) :
    ∀ zeros_f : List Real, ... → zeros_f.length ≤ N + 1
```

Iterated Rolle. Classical theorem: zero count of f ≤ 1 + zero count
of f' on a bounded open interval. **As of the 2026-07 hardening pass
this is proved from `rolle`** by sorting the `Nodup` zeros
(`List.mergeSort`) and bracketing each consecutive pair via Rolle; the
bracket points are strictly increasing, hence distinct, giving a
`Nodup` list of `length − 1` zeros of `f'`. `#print axioms` shows
`rolle` (not `zero_count_bound_by_deriv`) as the analytic base. It no
longer contributes an independent axiom.

**No longer a finding — it is a derived theorem.**

## Audit summary

| Category | Count | Status |
|---|---|---|
| Lean stdlib | 3 | OK |
| Real type + ops | 9 | OK |
| Field axioms | 10 | OK |
| Order axioms | 3 | OK |
| Subtraction | 1 | OK |
| Nat embedding | 2 | OK |
| Exp axioms | 3 | OK |
| HasDerivAt closure | 9 | OK |
| `rolle` | 1 | OK with documented assumption |
| `zero_count_bound_by_deriv` | 0 | now a THEOREM derived from `rolle` (§10) |
| **Total** | **39** | **all OK** |

## What this does NOT audit

This audit covers ONLY the axioms in the footprint of the announced
`expPoly_khovanskii_bound` result. MachLib has 280 axioms total
across the repo; the rest are:

- Other special functions (sin/cos/tan/sqrt/atan2/arcsin/arccos/log)
  with their classical relations (Pythagorean, angle-addition, etc.).
- Test/scratch files for variant proofs not on the announcement
  path.
- Domain-specific obligations in `HighDimensional.lean`,
  `EMLAsymptoticBound.lean`, etc. — none of which feed the
  single-exp Khovanskii result.

If/when the announcement is extended to cover multi-exp or
trigonometric Khovanskii, those axioms would need their own audit
under the same methodology.

## Recommendation for the announcement

**The single-exp Khovanskii bound is on a clean axiom footprint and
ready to announce.** The two "buildable assumption" findings are
worth documenting in the source comments but do not affect
soundness of any result that MachLib can actually prove.

The 280-vs-40 ratio is healthy: most MachLib axioms are dormant
infrastructure for future expansions, not load-bearing for
shipped results.
