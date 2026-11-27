# The exponential-height route to `EmlGermApproach` and `TowerLowerBound` — UNCONFIRMED

**Status: a reading of the literature, not a theorem of ours.** Nothing here is formalised, and no
specialist has confirmed it. The obligations ledger does not move: `TowerLowerBound` and
`TowerReducesToSign` stay open, and `DecayFloor`, `EmlGermApproach` and `GrowthEnvelope` stay
reduced (one cycle, one open obligation).

**Provenance, 2026-11-16.**
- A muse found the route from an automated read of the first 100 000 of 162 201 characters of the
  arXiv PDF of [KS], a range that covers all of §2, and wrote most of this note.
- The owner saved the PDF.
- An agent re-read §2 from it and checked each statement cited below against the text.
- Neither read the proofs in [KS]. One step, marked ASSEMBLED, is not stated in [KS] in one place.

If the reading is right, the uniformity asked for in
`germ_approach_problem_statement_2026_09_23.md` §2 is not open as mathematics over `ℝ`, and
`TowerLowerBound` follows from the same source. The sharp height (`max(j − 2, 0)`, measured) is not
settled by it.

## Sources

* [KS] T. Kaiser, P. Speissegger, *Analytic continuation of log-exp-analytic germs*,
  arXiv:1708.04496 (v4, 19 October 2018) — https://arxiv.org/pdf/1708.04496
* [vdDMM] L. van den Dries, A. Macintyre, D. Marker, *Logarithmic-exponential series*, APAL 111
  (2001). [KS] Prop. 2.14 uses its Cor. 4.7.
* [MM] D. Marker, C. Miller, *Levelled o-minimal structures* (1997), for `level`.

## What [KS] §2 provides (as read)

`𝓗` is the Hardy field of germs at `+∞` of unary functions definable in `ℝ_an,exp`. `𝓔ₙ ⊆ 𝓗` are the
germs of exponential height at most `n`, and `𝓔 = ⋃ 𝓔ₙ`.

| Statement | Content |
|---|---|
| definition | `eh(f)` for `f ∈ 𝓔` is the least `k` with `f ∈ 𝓔ₖ`; constants have `eh = −∞`, and `eh(x) = 0` |
| Lemma 2.3(2) | `f ∈ 𝓔ₙ` small, `P` a convergent power series ⇒ `P ∘ f ∈ 𝓔ₙ` |
| Cor. 2.5 | each `𝓔ₙ` is a differential subfield of `𝓗` |
| Prop. 2.8 | `f ∈ 𝓔` large ⇒ `eh(exp ∘ f) = eh(f)` if `level(f) < eh(f)`, and `eh(f) + 1` if `level(f) = eh(f)` |
| Lemma 2.13 | `f ∈ 𝓔ₙ`, `f > 0` ⇒ `log ∘ f ∈ 𝓔ₙ₊₁ ∘ log` |
| Prop. 2.14 | `𝓗 = ⋃ₖ 𝓔 ∘ logₖ`; a large `f ∈ 𝓗` of level `k − l` satisfies `exp_k(x^{1/ν}) ∘ log_l ≤ |f| ≤ exp_k(x^ν) ∘ log_l` |
| Lemma 2.15, def. | `eh(g ∘ logₖ) := eh(g) − k` is well defined on `𝓗` |
| Cor. 2.16(1) | `eh(f ∘ exp) = eh(f) + 1`, `eh(f ∘ log) = eh(f) − 1` |
| Cor. 2.16(2) | `f ∈ 𝓗` infinitely increasing ⇒ `level(f) = eh(lm f) ≤ eh(f)` |
| Cor. 2.16(3) | `𝓗_{≤k} = {f ∈ 𝓗 : eh(f) ≤ k}` is a differential subfield of `𝓗` |

The Introduction's example `x + e^{−x}` has level `0` and height `1`, so the inequality in 2.16(2)
can be strict. The Introduction also says, in words, that `exp` of a bounded germ keeps its height.

## The claim: `eh(⟦t⟧) ≤ depth t`

Every `⟦t⟧` is definable in `ℝ_exp` (totalised `L` is definable), so its germ lies in `𝓗` and has
eventually constant sign. The proof is by induction on `t`.

* **Leaves.** `eh(c) = −∞`, `eh(x) = 0`.
* **`exp ∘ a`, `a` large.** Write `a = g ∘ logₖ` with `g ∈ 𝓔`. Then `exp ∘ a = (exp ∘ g) ∘ logₖ`, and
  Prop. 2.8 gives `eh(exp ∘ a) ≤ eh(a) + 1`.
* **`exp ∘ a`, `a` bounded — ASSEMBLED.** `a` has a finite limit `c` (Hardy field). Then
  `exp ∘ a = e^c · P(a − c)` with `P = exp` and `a − c` small, so Lemma 2.3(2) gives
  `eh(exp ∘ a) ≤ eh(a)`, after the same `logₖ` pull-back. This is the recentring that [KS] itself
  uses in the proof of Prop. 2.12(i).
* **`L ∘ b`.** Eventually `0`, or `log ∘ b` with `b > 0`. Lemma 2.13 with Cor. 2.16(1) gives
  `eh(log ∘ b) ≤ eh(b)`.
* **Difference.** Cor. 2.16(3).

So `eh(⟦⟨A,B⟩⟧) ≤ max(eh ⟦A⟧ + 1, eh ⟦B⟧)`, i.e. `eh(⟦t⟧) ≤ ehTree t ≤ depth t`.

## Consequences

Write `T_k = exp_k(x)`. By Prop. 2.14, an infinitely increasing germ of level `≤ j` is eventually
below `T_{j+1}`.

1. **Tower.** If `depth u < n` and `⟦u⟧ = T_n`, then `n = level(T_n) ≤ eh(T_n) ≤ depth u < n`. So
   `TowerLowerBound` holds (and with `ehTree` in place of depth).
2. **Growth.** Depth `≤ j` ⇒ eventually `⟦t⟧ ≤ T_{j+1}`.
3. **Decay.** Depth `≤ j`, germ positive ⇒ `1/⟦t⟧ ∈ 𝓗_{≤j}` (a field) ⇒ `1/⟦t⟧ < T_{j+1}` ⇒
   `⟦t⟧ > exp(−T_j)`. `DecayFloor` at `k = j`.
4. **Approach.** Depth of `A`, `C` at most `j` and `C < exp ∘ A` on a ray ⇒ the gap lies in
   `𝓗_{≤ j+1}` and is positive ⇒ gap `> exp(−T_{j+1})`. `EmlGermApproach` at `k = j + 1`.

## Why the eight closed mechanisms do not apply

Each of the eight mechanisms in §5 of the 2026-09-23 statement concerns a parameter that must
strictly *decrease* along constructor edges. `eh` is never descended on. It is bounded above, edge
by edge, and the floor comes from two facts the closure axioms of `HeightModel` do not have:
`𝓗_{≤k}` is closed under reciprocals, and height bounds level. `zeroModel` satisfies the closure
clauses and neither of those. This is also the answer to that statement's §6 warning that a height
built from closure clauses alone is free and carries no content.

`eh` is germ-invariant. Mechanism 5 shows no germ-invariant parameter can run a *descent*; it does
not say none can bound the floor.

## What this does not give

* **The sharp height.** Measured: `max(j − 2, 0)` for both the decay and approach forms. This
  route gives `j` and `j + 1`. Prop. 2.8 is the likely place the slack sits: `exp` raises height
  only when `level = eh`, and the induction above charges every `exp` edge.
* **Anything inside MachLib.** The reals there are axiomatised and `𝓔ₙ` does not exist. The ledger
  rows stay open until someone formalises the classes or adopts an axiom under the standing policy
  (`EmlGermApproachResearch.md` §8). Exit criterion 2 (external support) would be met; criterion 3
  is unchanged.
* **Any bound on hardware.** `TowerLowerBound` is about exact trees in the pure EML grammar, equal
  to the tower on all of ℝ. A fixed-point kernel approximates, so the bound says nothing about it.
  In float64, `T₆` overflows at every input and `T₅` overflows for `x > −0.4585`. Heights up to 4
  are already theorems (`tower_lower_bound_upto_four`). A certified minimum depth for an ordinary
  function can rest on the exact-depth theorems that already exist, such as
  `x_plus_neg_c_depth_exact_four`, with the same exact-tree caveat.

## What to correct elsewhere if this is confirmed

* `germ_approach_problem_statement_2026_09_23.md`:
  - §2: "Nothing we have found in the literature supplies it".
  - §4: "that it is a function of `j` at all".
  - §5 item 7: "Transseries … are all covered".
  - §6: the second trap.
  - §8: "Differences break the correspondence".
  - §9: the tower bound.
* `EmlGermApproachResearch.md` §7: the same sentence as §8 above.
* The email draft and the MathOverflow post pose the uniformity as open. Do not send them as they
  are. As of 2026-11-16 all three `germ_approach_*` drafts open with a banner pointing here, and
  `EmlGermApproachResearch.md` §7 opens with a pointer.
