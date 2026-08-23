import MachLib.BipevDcoeffsShape

/-!
# A denominator that is not eventually zero is eventually nonzero

Written **before** the theorem that needs it, per the pattern recorded last commit.

The composition has to produce `EvRel S (dcoeffs QQ D 0 Ms)` from the relation, and
`bipev_dcoeffs_eq_zero_on_tail` needs `S'` at each point of a tail — which needs `Q(x) ≠ 0` there,
since that is what brick three requires to differentiate `P/Q` at all. So the tail on which the
differentiated relation holds is the intersection of "the relation holds" with "`Q` does not vanish",
and the second needs saying.

`pev_dichotomy` gives it in one step: a coefficient list is eventually zero or **eventually
dominates** `c·xᵏ`, and a dominated-below quantity is nonzero. The only content is turning the bound
into a bare nonvanishing, which is `mul_pos` and `powNat_pos`.

This is analytic — the order axioms are what "eventually" means — and correctly outside invariant (7).
-/

namespace MachLib

open Real

/-- **Not eventually zero implies eventually nonzero.** The gap between the two is exactly
`pev_dichotomy`, and this is the form the tail bookkeeping consumes. -/
theorem pev_ne_zero_on_tail {Q : List Real} (hQ : ¬ EvZeroF (pev Q)) :
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → pev Q x ≠ 0 := by
  rcases pev_dichotomy Q with hz | ⟨c, k, X, hc, hX, hd⟩
  · exact absurd hz hQ
  · refine ⟨X, hX, fun x hx hzero => ?_⟩
    have hpos : 0 < abs (pev Q x) :=
      lt_of_lt_of_le
        (mul_pos hc (powNat_pos (lt_of_lt_of_le zero_lt_one_ax (le_trans hX hx)) k)) (hd x hx)
    rw [hzero, abs_of_nonneg (le_refl (0 : Real))] at hpos
    exact lt_irrefl_ax (0 : Real) hpos

/-- Three tails intersect to one: the relation's, the denominator's, and any given bound. -/
theorem three_tails {X₁ X₂ X₃ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) (h₃ : 1 ≤ X₃) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X ∧ X₃ ≤ X := by
  obtain ⟨Y, hY, hY1, hY2⟩ := two_bounds' h₁ h₂
  obtain ⟨Z, hZ, hZY, hZ3⟩ := two_bounds' hY h₃
  exact ⟨Z, hZ, le_trans hY1 hZY, le_trans hY2 hZY, hZ3⟩

/-! ## The differentiated relation holds on a tail

The composition's first real link: from "the relation holds eventually" to "the *cleared
differentiated* relation holds eventually". Everything needed is now in place —
`hasDerivAt_ratFn` for `S'`, `ratFn_deriv_cleared` for `S'·Q² = D`,
`bipev_dcoeffs_eq_zero_on_tail` for the transfer, and `pev_ne_zero_on_tail` for the denominator.

Stated for `S` *literally* `fun y => pev P y · (1/pev Q y)` — the function brick three
differentiates. A germ that merely agrees with it on a tail is handled by
`hasDerivAt_of_agrees_on_tail`, and is deliberately a separate step: mixing the two would hide which
tail each hypothesis is about. -/

/-- **The cleared differentiated relation holds on a tail.** -/
theorem evRel_dcoeffs_ratFn {P Q : List Real} {Ms : List (List Real)}
    (hQ : ¬ EvZeroF (pev Q))
    (hrel : EvRel (fun y => pev P y * (1 / pev Q y)) Ms) :
    EvRel (fun y => pev P y * (1 / pev Q y))
      (dcoeffs (pmul Q Q) (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) 0 Ms) := by
  obtain ⟨Xr, hXr, hr⟩ := hrel
  obtain ⟨Xq, hXq, hq⟩ := pev_ne_zero_on_tail hQ
  obtain ⟨X, hX, hXXr, hXXq⟩ := two_bounds' hXr hXq
  refine ⟨X + 1, le_trans hX (le_of_lt (self_lt_succ X)), fun x hx => ?_⟩
  have hXx : X < x := lt_of_lt_of_le (self_lt_succ X) hx
  have hQx : pev Q x ≠ 0 := hq x (le_trans hXXq (le_of_lt hXx))
  refine bipev_dcoeffs_eq_zero_on_tail (hasDerivAt_ratFn P Q x hQx) hXx
    (ratFn_deriv_cleared P Q x hQx) (fun y hy => ?_)
  exact hr y (le_trans hXXr (le_of_lt hy))

end MachLib
