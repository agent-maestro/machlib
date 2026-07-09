import MachLib.PfaffianExpRecipClass

/-!
# Feasibility spike — does the reciprocal level fit the `rankRec` growth tolerance?

The `exp_hard` mixed-chain measure descent is blocked at the **reciprocal** level: two prior architectures
(same-depth `chainNMeasureEI` descent, and clear-then-measure) both failed because reciprocal is
depth-changing / denominator-introducing. The one live path (a unified well-founded descent that keeps
reciprocal as a genuine degree-2 Pfaffian variable) hinges on a single quantitative question:

> Under the chain-total-derivative, does a reciprocal level grow its own `degreeY` by a **bounded** amount —
> specifically by ≤ +1, the exact per-step growth the `rankRec`/`descentBound` nested rank already absorbs
> for the exponential tower — or by more (in which case a nested rank cannot tame it)?

This file answers it, as a pure-degree combinatorial fact (no `rolle`, no analytic content — the log-arm
spike’s register). Findings:

* **`degreeY_cTD_growth_general`** — a chain-agnostic `+1` growth engine: if every relation grows `y_i`-degree
  by ≤ +1 over the bare variable, then `chainTotalDeriv` grows `degreeY i` by ≤ +1 on *all* polynomials.
  This is exactly `rankRec`’s admissible-growth hypothesis (`B' ≤ B + 1`).
* **`recip_relation_degreeY`** — a reciprocal relation `G·yᵢ²` grows `degreeY i` by **exactly +1** (2 = 1 + 1):
  it sits on the *boundary* of the tolerance, not past it.
* **`exp_relation_degreeY`** — an exponential relation `G·yᵢ` **preserves** `degreeY i` (+0): strictly inside.
* **`degreeY_cTD_growth_expOrRecip`** — putting it together: for an exp-or-reciprocal chain and any index `i`,
  the `+1` cTD growth holds provided the *higher* relations are `y_i`-tame (`degreeY i ≤ 1` for `l > i`) —
  automatic below and at `i`. That residual (a **bounded** degree condition on higher levels) is the only
  thing standing between the reciprocal level and the `rankRec` tolerance.

**Verdict:** reciprocal is a well-behaved **+1 digit**, not the unbounded blow-up the same-depth/clear routes
feared. The nested-rank (`rankRec`) machinery from the explicit-bound arc is therefore a genuine candidate for
the unified descent — the open crux narrows to controlling higher-level `y_i`-degree (`htame`) and threading
the depth axis, not to taming reciprocal growth itself. `#print axioms` = propext, Classical.choice, Quot.sound.
-/

namespace MachLib.PfaffianRecipGrowthSpike

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianExpRecip

/-- **The chain-agnostic `+1` growth engine.** If every relation grows `y_i`-degree by ≤ +1 over the bare
variable `varY l`, then `chainTotalDeriv` grows `degreeY i` by ≤ +1 on every polynomial. Structural mirror of
`degreeY_chainTotalDeriv_iterExp_growth`, but the per-relation bound is a *hypothesis* rather than baked into
`IterExpChain` — so it applies to any chain, exp / log / reciprocal alike. This is precisely the
admissible-growth condition (`B' ≤ B + 1`) that `rankRec`/`descentBound` absorb. -/
theorem degreeY_cTD_growth_general {n : Nat} (c : PfaffianChain n) (i : Fin n)
    (hrel : ∀ l : Fin n,
        MultiPoly.degreeY i (c.relations l) ≤ MultiPoly.degreeY i (MultiPoly.varY l) + 1) :
    ∀ q : MultiPoly n,
      MultiPoly.degreeY i (chainTotalDeriv c q) ≤ MultiPoly.degreeY i q + 1
  | .const _ => Nat.zero_le _
  | .varX => Nat.zero_le _
  | .varY j => hrel j
  | .add p q => by
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p))
              (MultiPoly.degreeY i (chainTotalDeriv c q))
          ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + 1
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · exact Nat.le_trans (degreeY_cTD_growth_general c i hrel p)
          (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
      · exact Nat.le_trans (degreeY_cTD_growth_general c i hrel q)
          (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
  | .sub p q => by
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p))
              (MultiPoly.degreeY i (chainTotalDeriv c q))
          ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + 1
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · exact Nat.le_trans (degreeY_cTD_growth_general c i hrel p)
          (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
      · exact Nat.le_trans (degreeY_cTD_growth_general c i hrel q)
          (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
  | .mul p q => by
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p) + MultiPoly.degreeY i q)
              (MultiPoly.degreeY i p + MultiPoly.degreeY i (chainTotalDeriv c q))
          ≤ MultiPoly.degreeY i p + MultiPoly.degreeY i q + 1
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · have := degreeY_cTD_growth_general c i hrel p; omega
      · have := degreeY_cTD_growth_general c i hrel q; omega

/-- `degreeY i (varY i) = 1`. -/
theorem degreeY_varY_self {n : Nat} (i : Fin n) : MultiPoly.degreeY i (MultiPoly.varY i) = 1 := by
  show (if i = i then 1 else 0) = 1
  rw [if_pos rfl]

/-- **Reciprocal grows `degreeY i` by exactly +1** — the tight boundary. A reciprocal-type relation
`G·(yᵢ·yᵢ)` with `G` free of `yᵢ` has `degreeY i = 2 = degreeY i (varY i) + 1`. -/
theorem recip_relation_degreeY {n : Nat} (i : Fin n) (G : MultiPoly n)
    (hG : MultiPoly.degreeY i G = 0) :
    MultiPoly.degreeY i (MultiPoly.mul G (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i)))
      = MultiPoly.degreeY i (MultiPoly.varY i) + 1 := by
  show MultiPoly.degreeY i G
      + (MultiPoly.degreeY i (MultiPoly.varY i) + MultiPoly.degreeY i (MultiPoly.varY i))
      = MultiPoly.degreeY i (MultiPoly.varY i) + 1
  rw [hG, degreeY_varY_self]

/-- **Exponential preserves `degreeY i`** (+0) — strictly inside the tolerance. An exponential-type relation
`G·yᵢ` with `G` free of `yᵢ` has `degreeY i = 1 = degreeY i (varY i)`. -/
theorem exp_relation_degreeY {n : Nat} (i : Fin n) (G : MultiPoly n)
    (hG : MultiPoly.degreeY i G = 0) :
    MultiPoly.degreeY i (MultiPoly.mul G (MultiPoly.varY i)) = MultiPoly.degreeY i (MultiPoly.varY i) := by
  show MultiPoly.degreeY i G + MultiPoly.degreeY i (MultiPoly.varY i)
      = MultiPoly.degreeY i (MultiPoly.varY i)
  rw [hG, Nat.zero_add]

/-- Every relation of an exp-or-reciprocal chain grows its OWN `degreeY` by ≤ +1 (exp: +0, recip: +1). -/
theorem relation_self_degreeY_le {n : Nat} (c : PfaffianChain n) (hc : IsExpOrRecipChain c) (i : Fin n) :
    MultiPoly.degreeY i (c.relations i) ≤ MultiPoly.degreeY i (MultiPoly.varY i) + 1 := by
  rcases (hc i).1 with ⟨G, hG, hrel⟩ | ⟨G, hG, hrel⟩
  · rw [hrel, exp_relation_degreeY i G hG]; exact Nat.le_succ _
  · rw [hrel, recip_relation_degreeY i G hG]; exact Nat.le_refl _

/-- **Spike verdict.** For an exp-or-reciprocal chain and ANY index `i`, `chainTotalDeriv` grows `degreeY i`
by ≤ +1 — the exact `rankRec` tolerance — PROVIDED the higher relations are `y_i`-tame (`degreeY i ≤ 1` for
`l > i`). Below `i` this is automatic (triangularity ⇒ `= 0`); at `i` it is `relation_self_degreeY_le`
(exp +0 / recip +1). So the reciprocal level itself never breaches the tolerance; the sole residual for a
nested-rank descent is the bounded higher-level condition `htame`, not reciprocal growth. -/
theorem degreeY_cTD_growth_expOrRecip {n : Nat} (c : PfaffianChain n)
    (hc : IsExpOrRecipChain c) (i : Fin n)
    (htame : ∀ l : Fin n, i.val < l.val → MultiPoly.degreeY i (c.relations l) ≤ 1) :
    ∀ q : MultiPoly n,
      MultiPoly.degreeY i (chainTotalDeriv c q) ≤ MultiPoly.degreeY i q + 1 := by
  refine degreeY_cTD_growth_general c i (fun l => ?_)
  rcases Nat.lt_trichotomy l.val i.val with hlt | heq | hgt
  · -- l < i : triangular ⇒ degreeY i (relations l) = 0
    have h0 : MultiPoly.degreeY i (c.relations l) = 0 := (hc l).2 i hlt
    omega
  · -- l = i : the self-growth bound
    have : l = i := Fin.ext heq
    subst this
    exact relation_self_degreeY_le c hc l
  · -- l > i : y_i-tame higher relation, and varY l is y_i-free (l ≠ i)
    have hne : ¬ i = l := fun he => by have := congrArg Fin.val he; omega
    have hv : MultiPoly.degreeY i (MultiPoly.varY l) = 0 := by
      show (if i = l then 1 else 0) = 0; rw [if_neg hne]
    have := htame l hgt; omega

end MachLib.PfaffianRecipGrowthSpike
