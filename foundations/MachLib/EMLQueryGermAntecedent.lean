import MachLib.EMLQueryGermUniform
import MachLib.PevSignGerm

/-!
# The antecedent, assembled from the three branches

`ratGerm_eventual_sign` splits `u = pev P / pev Q` three ways and each branch now has a
`UniformZeroBoundFrom` producer. This is the case split that joins them.

## Read the scope before the theorem

What this proves is `bipolyNoOscillation_of_ratUniformBounds`'s antecedent, hence
`BipolyNoOscillation`, hence the **div-conditioned** dichotomy
`oneQueryDichotomy_of_ratUniformBounds`.

**It does NOT prove `OneQueryDichotomy`.** That obligation is stated with *no* `DivDenomsOK`
hypothesis and *no* `ctxFrac` non-vanishing hypothesis; the chain here carries both. They are the
"div side conditions along the curve" `EMLZeroBoundRay` names, and they are unaddressed. The ledger
row stays open and the obligations gate will keep saying so.

Saying that first, because "the antecedent is proved" is one short step from "the obligation is
discharged", and the two are separated here by exactly two hypotheses.
-/

namespace MachLib

open Real

/-- **The antecedent, proved.** For every `N`, `P`, `Q` with `pev Q` non-vanishing on a ray and the
germ not eventually zero, there is an interval-independent zero bound.

The three cases are `ratGerm_eventual_sign`'s, and each is a theorem already:

* `u` eventually zero — the germ collapses to a polynomial (`queryGerm_zero_branch_bound`);
* `u > 0` — the `Fbasis` route through `toEML` (`queryGerm_pos_branch_uniform`);
* `u < 0` — totalisation kills the log, so the log-free tree (`queryGerm_neg_branch_uniform`).

The rays are combined as `X + X'` rather than a maximum: both are `≥ 1`, so the sum dominates each,
and the corpus has no `Real.max` lemmas at hand. -/
theorem queryGerm_ratUniformBounds :
    ∀ (N : List (List Real)) (P Q : List Real) (X : Real), 1 ≤ X →
      (∀ x : Real, X ≤ x → pev Q x ≠ 0) →
      ¬ EvZeroF (fun x => bipev N x (Fbasis (pev P x / pev Q x))) →
      ∃ (K : Nat) (R : Real),
        UniformZeroBoundFrom (fun x => bipev N x (Fbasis (pev P x / pev Q x))) R K := by
  intro N P Q X hX1 hQ hne
  have hX0 : (0 : Real) ≤ X := le_trans (le_of_lt zero_lt_one_ax) hX1
  have hrat : RatGerm (fun x => pev P x / pev Q x) :=
    ⟨P, Q, X, hX1, hQ, fun _ _ => rfl⟩
  rcases ratGerm_eventual_sign hrat with hz | ⟨X', hX'1, hposraw⟩ | ⟨X', hX'1, hnegraw⟩
  · exact queryGerm_zero_branch_bound N P Q hz hne
  · -- `obtain` leaves the sign facts unreduced; bind through typed `have`s
    have hpos : ∀ x : Real, X' ≤ x → 0 < pev P x / pev Q x := fun x hx => hposraw x hx
    have hX'0 : (0 : Real) ≤ X' := le_trans (le_of_lt zero_lt_one_ax) hX'1
    have hXle : X ≤ X + X' := by
      have v := add_le_add_wit (le_refl X) hX'0
      have e : X + (0 : Real) = X := by mach_ring
      rw [e] at v; exact v
    have hX'le : X' ≤ X + X' := by
      have v := add_le_add_wit hX0 (le_refl X')
      have e : (0 : Real) + X' = X' := by mach_ring
      rw [e] at v; exact v
    exact ⟨_, X + X', queryGerm_pos_branch_uniform N P Q (X + X') (le_trans hX1 hXle)
      (fun x hx => hQ x (le_trans hXle hx))
      (fun x hx => hpos x (le_trans hX'le hx)) hne⟩
  · have hneg : ∀ x : Real, X' ≤ x → pev P x / pev Q x < 0 := fun x hx => hnegraw x hx
    have hX'0 : (0 : Real) ≤ X' := le_trans (le_of_lt zero_lt_one_ax) hX'1
    have hXle : X ≤ X + X' := by
      have v := add_le_add_wit (le_refl X) hX'0
      have e : X + (0 : Real) = X := by mach_ring
      rw [e] at v; exact v
    have hX'le : X' ≤ X + X' := by
      have v := add_le_add_wit hX0 (le_refl X')
      have e : (0 : Real) + X' = X' := by mach_ring
      rw [e] at v; exact v
    exact ⟨_, X + X', queryGerm_neg_branch_uniform N P Q (X + X') (le_trans hX1 hXle)
      (fun x hx => hQ x (le_trans hXle hx))
      (fun x hx => le_of_lt (hneg x (le_trans hX'le hx))) hne⟩

/-- **`BipolyNoOscillation`, unconditionally.** The bivariate no-oscillation statement is now a
theorem rather than a hypothesis. -/
theorem bipolyNoOscillation_holds : BipolyNoOscillation :=
  bipolyNoOscillation_of_ratUniformBounds queryGerm_ratUniformBounds

/-- **The div-conditioned one-query dichotomy, unconditionally.**

Compare with the obligation, and note the gap precisely:

```
OneQueryDichotomy       ∀ C P Q X, 1 ≤ X → (∀x≥X, pev Q x ≠ 0) → …
this theorem            ∀ C P Q X, 1 ≤ X → (∀x≥X, pev Q x ≠ 0) →
                          (∀x≥X, DivDenomsOK C x …) →
                          (∀x≥X, bipev (ctxFrac C).2 x … ≠ 0) → …
```

**Two extra hypotheses.** They are the div side conditions along the curve, and nothing here
discharges them. This is a strictly weaker statement than the ledger row, and the row stays open. -/
theorem oneQueryDichotomy_divConditioned :
    ∀ (C : FCtx) (P Q : List Real) (X : Real), 1 ≤ X →
      (∀ x : Real, X ≤ x → pev Q x ≠ 0) →
      (∀ x : Real, X ≤ x → DivDenomsOK C x (Fbasis (pev P x / pev Q x))) →
      (∀ x : Real, X ≤ x → bipev (ctxFrac C).2 x (Fbasis (pev P x / pev Q x)) ≠ 0) →
        EvZeroF (fun x => FCtx.eval C x (Fbasis (pev P x / pev Q x)))
        ∨ ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
            FCtx.eval C x (Fbasis (pev P x / pev Q x)) ≠ 0 :=
  oneQueryDichotomy_of_ratUniformBounds queryGerm_ratUniformBounds

end MachLib
