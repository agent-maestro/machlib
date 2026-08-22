import MachLib.PolyDeriv

/-!
# The power rule, and the characteristic-zero input named once

`(qᵏ)' = k·q^(k−1)·q'` is the last piece of machinery the pole-order count needs. Two choices here
are deliberate.

## The multiple is an iterated sum, not a `natCast`

`pnsum k Z` is `Z + Z + … + Z`, defined by recursion on `k`. Writing the `k` as `natCast k` would
drag `MachLib.Real.natCast` and its arithmetic in, and — worse — would invite the reader to
*discharge* `natCast k ≠ 0`, which is exactly the characteristic-zero step this layer cannot take.
As an iterated sum the coefficient stays inside the field axioms and the char-zero question is
pushed to precisely one place.

## Both characteristic-zero needs collapse into one hypothesis

Working the count on paper, the `qᵏ` term contributes `k·q'` and the requirement is `q ∤ k·q'`. That
single condition covers *both* char-zero facts that looked separate:

* `q' ≠ 0` — false over `𝔽₂` for `q = X²+1`;
* `natCast k ≠ 0` — false over `𝔽₂` for `k = 2`;

because `q ∣ 0` holds trivially, so `q ∤ k·q'` already implies `k·q' ≠ 0`, hence both. So the count
will carry exactly one named input, `¬ Pdvd q (pnsum r (pderiv q))`, rather than two.

For `MachLib.Real` that hypothesis is true and discharging it needs the order axioms
(`natCast_ne_zero` carries the whole ordered base). Everything in this file stays field-only.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Natural-number multiples, as iterated sums -/

/-- `pnsum k Z = Z + Z + … + Z` (`k` times). The coefficient of a power-rule term, kept inside the
field axioms by never mentioning `natCast`. -/
noncomputable def pnsum : Nat → List Real → List Real
  | 0,     _ => []
  | k + 1, Z => padd Z (pnsum k Z)

theorem pnsum_one (Z : List Real) : pnsum 1 Z = Z := by
  show padd Z (pnsum 0 Z) = Z
  show padd Z [] = Z
  rw [padd_nil_right]

/-! ## The power rule -/

/-- **`(q^(k+1))' ≈ q^k · (k+1)·q'`.** Stated at `k+1` so no `k − 1` truncated subtraction appears,
and with the multiple as `pnsum`. -/
theorem peq_pderiv_ppow : ∀ (q : List Real) (k : Nat),
    PEq (pderiv (ppow q (k + 1))) (pmul (ppow q k) (pnsum (k + 1) (pderiv q))) := by
  intro q k
  induction k with
  | zero =>
      show PEq (pderiv (pmul q (ppow q 0))) (pmul (ppow q 0) (pnsum 1 (pderiv q)))
      rw [pnsum_one]
      show PEq (pderiv (pmul q [(1 : Real)])) (pmul [(1 : Real)] (pderiv q))
      rw [pmul_one_right]
      exact (peq_pmul_one_left (pderiv q)).symm
  | succ k ih =>
      show PEq (pderiv (pmul q (ppow q (k + 1))))
        (pmul (ppow q (k + 1)) (padd (pderiv q) (pnsum (k + 1) (pderiv q))))
      refine PEq.trans (peq_pderiv_pmul q (ppow q (k + 1))) ?_
      rw [pmul_padd_right]
      refine peq_padd (peq_pmul_comm (pderiv q) (ppow q (k + 1))) ?_
      refine PEq.trans (peq_pmul (PEq.refl q) ih) ?_
      exact (pmul_assoc_pnorm q (ppow q k) (pnsum (k + 1) (pderiv q))).symm

/-! ## The characteristic-zero input, named

Stated as a definition so the count can take it as a hypothesis and the axiom ledger can show that
nothing in this layer discharges it. Over `𝔽₂` with `q = X² + 1` and `r = 2` it is **false**, which
is precisely why it is a hypothesis and not a theorem. -/

/-- `q` does not divide `r·q'`. True for irreducible `q` over a characteristic-zero field; false
over `𝔽₂`. The single input the pole-order count needs beyond the field axioms. -/
def DerivCoprime (q : List Real) (r : Nat) : Prop := ¬ Pdvd q (pnsum r (pderiv q))

/-- `DerivCoprime` already gives nonvanishing, since everything divides the zero polynomial. -/
theorem pnsum_deriv_ne_zero {q : List Real} {r : Nat} (h : DerivCoprime q r) :
    ¬ PEq (pnsum r (pderiv q)) [] := by
  intro hz
  exact h (Pdvd_of_peq hz Pdvd_zero)

end MachLib
