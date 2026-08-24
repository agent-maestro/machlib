import MachLib.Bipoly
import MachLib.GermExpCoeff

/-!
# Rearranging the identity into a single relation in `e^S`

`minimal_expRel_identity` delivers a germ identity. `all_coeffs_nil_of_relation` consumes a
*relation* — `bipev Rel x (e^(S x)) = 0` on a tail, with `Rel` a list of polynomial coefficients.
This module builds the `Rel`.

The obstruction is that two of the identity's pieces carry **rational** coefficients: `dbipevExp`,
whose coefficients involve `S'`, and the factor `v = S'/S`. Both clear against `P·Q²`:

```
Q²·c'        = bipev (dcoeffs Q² D 0 C) x (e^S)          -- `bipev_cleared_deriv` at j = 0
P·Q²·(S'/S)  = Q·D                                       -- since S = P/Q and D = P'Q − PQ'
```

so `P·Q²` clears the whole identity at once, and the products and sums that remain are `Bipoly`.

## The two hypotheses are the clearing conditions, not the model

`hclear` and `hv` say what `S'` and `v` are *after* clearing — `S'·Q² = D` and
`v·(P·Q²) = Q·D` — rather than that `S` is literally `P/Q`. That keeps this module free of
nonvanishing side conditions: no division is performed here, so none has to be justified here. The
caller, which does know `S = P/Q` on a tail, discharges both.
-/

namespace MachLib

open Real

/-- `bipev_cleared_deriv` at index `0`, where the correction term vanishes. -/
theorem bipev_dcoeffs_zero (Ls : List (List Real)) (QQ D : List Real) (S : Real → Real)
    (S' x : Real) (h : S' * pev QQ x = pev D x) :
    bipev (dcoeffs QQ D 0 Ls) x (exp (S x)) = pev QQ x * dbipevExp Ls S S' x := by
  rw [← bipev_cleared_deriv Ls QQ D S S' x 0 h]
  show pev QQ x * dbipevExp Ls S S' x + 0 * bipev Ls x (exp (S x))
      = pev QQ x * dbipevExp Ls S S' x
  mach_ring

/-- The identity, cleared by `P·Q²` and assembled into one coefficient family. -/
noncomputable def relCoeffs (P Q D : List Real) (m : Nat) (Cd Cd1 : List (List Real)) :
    List (List Real) :=
  bisub (bimul Cd (biadd (biscale P (dcoeffs (pmul Q Q) D 0 Cd1))
                         (biscale (pmul (pnsum (m + 1) [1]) (pmul Q D)) Cd)))
        (bimul (biscale P (dcoeffs (pmul Q Q) D 0 Cd)) Cd1)

/-- **`relCoeffs` evaluates to `P·Q²` times the identity.** So the identity vanishing on a tail makes
`relCoeffs` a relation there, whatever `P` and `Q` do. -/
theorem bipev_relCoeffs {P Q D : List Real} {Cd Cd1 : List (List Real)} {S : Real → Real}
    {S'x vx x : Real} {m : Nat}
    (hclear : S'x * pev (pmul Q Q) x = pev D x)
    (hv : vx * (pev P x * pev (pmul Q Q) x) = pev Q x * pev D x) :
    bipev (relCoeffs P Q D m Cd Cd1) x (exp (S x))
      = pev P x * pev (pmul Q Q) x *
        (bipev Cd x (exp (S x)) *
            (dbipevExp Cd1 S S'x x + vx * (natMul (m + 1) 1 * bipev Cd x (exp (S x))))
          - dbipevExp Cd S S'x x * bipev Cd1 x (exp (S x))) := by
  have hone : pev [(1 : Real)] x = 1 := by show (1 : Real) + x * 0 = 1; mach_ring
  have e3 : pev (pmul (pnsum (m + 1) [1]) (pmul Q D)) x
      = natMul (m + 1) 1 * (pev Q x * pev D x) := by
    rw [pev_pmul, pev_pnsum, hone, pev_pmul]
  show bipev (bisub _ _) x (exp (S x)) = _
  rw [bipev_bisub, bipev_bimul, bipev_biadd, bipev_biscale, bipev_biscale, bipev_bimul,
      bipev_biscale, bipev_dcoeffs_zero Cd1 (pmul Q Q) D S S'x x hclear,
      bipev_dcoeffs_zero Cd (pmul Q Q) D S S'x x hclear, e3, ← hv]
  mach_mpoly [pev P x, pev (pmul Q Q) x, vx, natMul (m + 1) 1,
    bipev Cd x (exp (S x)), bipev Cd1 x (exp (S x)),
    dbipevExp Cd S S'x x, dbipevExp Cd1 S S'x x]

/-! ## Landing it

`all_coeffs_nil_of_relation` wants an `EvRel`. The identity vanishes on a tail and `relCoeffs` is
`P·Q²` times it, so the product vanishes there too — whatever `P` and `Q` happen to do. The three
tails (the two clearing conditions and the identity) intersect once. -/

/-- **The rearrangement is a relation.** This is the input `all_coeffs_nil_of_relation` consumes. -/
theorem evRel_relCoeffs {P Q D : List Real} {Cd Cd1 : List (List Real)}
    {S S' v : Real → Real} {m : Nat}
    (hclear : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → S' x * pev (pmul Q Q) x = pev D x)
    (hv : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      v x * (pev P x * pev (pmul Q Q) x) = pev Q x * pev D x)
    (hG : EvZeroF (fun x =>
      bipev Cd x (exp (S x)) *
          (dbipevExp Cd1 S (S' x) x + v x * (natMul (m + 1) 1 * bipev Cd x (exp (S x))))
        - dbipevExp Cd S (S' x) x * bipev Cd1 x (exp (S x)))) :
    EvRel S (relCoeffs P Q D m Cd Cd1) := by
  obtain ⟨X₁, hX₁, h1⟩ := hclear
  obtain ⟨X₂, hX₂, h2⟩ := hv
  obtain ⟨X₃, hX₃, h3⟩ := hG
  obtain ⟨X, hX, a1, a2, a3⟩ := three_tails hX₁ hX₂ hX₃
  refine ⟨X, hX, fun x hx => ?_⟩
  have hid : bipev Cd x (exp (S x)) *
          (dbipevExp Cd1 S (S' x) x + v x * (natMul (m + 1) 1 * bipev Cd x (exp (S x))))
        - dbipevExp Cd S (S' x) x * bipev Cd1 x (exp (S x)) = 0 := h3 x (le_trans a3 hx)
  rw [bipev_relCoeffs (h1 x (le_trans a1 hx)) (h2 x (le_trans a2 hx)), hid]
  mach_ring

end MachLib
