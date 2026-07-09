import MachLib.ForwardError
import MachLib.ErrorAlgebra
import MachLib.Exp
import MachLib.Log
import MachLib.HyperbolicId

/-!
# certcom Theorem A — T3 step (composite accuracy): composites inherit ULP error from primitives

T2 (`EMLToCRuntime.lean`) discharged the runtime hypothesis in **exact Float**: the composite `mg_*`
ops (`eml`, `sinh`, `cosh`, `tanh`) equal their primitive decompositions bit-for-bit, so they carry no
independent trust *there*. T3 asks the harder, numerical question — are the composites also
**accurate**? Is their rounding error bounded, given only the primitives' accuracy?

This file answers **yes** for the well-conditioned composite `cosh`, in MachLib's own forward-error
model (`FPModel.RoundsW` / `ForwardError.Renc` — the very machinery the certifier uses). Taking the two
primitive facts "float-`exp` rounds exact `exp` within `u`" as hypotheses (the residual T3 trust, now
formal: `RoundsW u · (exp ·)`), the computed `cosh` inherits the standard relative forward-error bound
`((1+u)² − 1)·cosh` — reducing cosh's accuracy to `exp`'s, with **no** independent libm validation of
`cosh` required.

`cosh(x) = ½(eˣ+e⁻ˣ)` is a **sum of positives** — no cancellation — so `Renc`'s relative fold applies
directly. Cancellation-prone composites (`sinh`, `eml`) instead take an **absolute**
operand-magnitude bound; `eml_fwd_reduces_to_primitives` states that honest form: eml's error is
governed by `exp` and `ln`'s errors plus one subtraction rounding. Together they show the composite
trust reduces to the primitive transcendentals at the **error** level too, complementing T2's
exact-level discharge. The residual trust is exactly the primitive `RoundsW` specs — the libm ULP
obligations, the same short list T2 pinned.

sorryAx-free; depends on MachLib.Real's `exp`/`log`/roundoff axioms (`u`, `exp_pos`, `cosh_eq`, …),
which certcom Theorem B grounds in Mathlib. This is the forward-error *half* of the bridge; connecting
it to T2's exact-`Float` layer (a `Float → Real` abstraction) is the remaining open T3 frontier.
-/

-- These forward-error theorems live in `MachLib.Real` (like `FPModel`/`ForwardError`) so `Real`,
-- `RoundsW`, `Renc`, `exp`, `cosh`, `u`, … resolve directly; they are the certcom T3 composite bricks.
namespace MachLib.Real

/-- **cosh's accuracy reduces to exp's.** Given that the float exponentials `flEp`, `flEnx` round the
exact `exp x`, `exp (-x)` within unit roundoff `u`, and their sum rounds within `u`, the computed
`cosh` numerator inherits the standard two-sided relative forward-error bound at exponent 2. No
independent accuracy assumption about `cosh` itself — only about `exp`. -/
theorem cosh_fwd_reduces_to_exp {flEp flEnx flSum : Real} (x : Real)
    (hEp  : RoundsW u flEp  (exp x))
    (hEnx : RoundsW u flEnx (exp (-x)))
    (hSum : RoundsW u flSum (flEp + flEnx)) :
    abs (flSum - (exp x + exp (-x))) ≤ (npow 2 (1 + u) - 1) * (exp x + exp (-x)) := by
  have hex  : (0 : Real) ≤ exp x    := le_of_lt (exp_pos x)
  have henx : (0 : Real) ≤ exp (-x) := le_of_lt (exp_pos (-x))
  have rx  : Renc 1 u flEp  (exp x)    := renc_round u_nonneg u_le_one hex  hEp
  have rnx : Renc 1 u flEnx (exp (-x)) := renc_round u_nonneg u_le_one henx hEnx
  have radd : Renc 2 u flSum (exp x + exp (-x)) :=
    renc_add u_nonneg u_le_one hex henx rx rnx hSum
  exact renc_fwd u_nonneg u_le_one (add_nonneg_ea hex henx) radd

/-- The same bound phrased via `cosh` itself, using `(1+1)·cosh x = eˣ + e⁻ˣ`
(`two_cosh_eq_exp_add`). The exact `·½` that finishes `cosh` is error-free (an IEEE-754 power-of-two
scaling), so the numerator bound IS cosh's forward-error bound. -/
theorem cosh_fwd_bound {flEp flEnx flSum : Real} (x : Real)
    (hEp  : RoundsW u flEp  (exp x))
    (hEnx : RoundsW u flEnx (exp (-x)))
    (hSum : RoundsW u flSum (flEp + flEnx)) :
    abs (flSum - (1 + 1) * cosh x) ≤ (npow 2 (1 + u) - 1) * ((1 + 1) * cosh x) := by
  rw [two_cosh_eq_exp_add]
  exact cosh_fwd_reduces_to_exp x hEp hEnx hSum

/-- **eml's accuracy reduces to exp's and ln's** — the cancellation-regime companion. `eml(x,y) =
exp(x) − ln(y)` can lose all significance when `exp x ≈ ln y`, so the honest bound is **absolute** in
the operand magnitudes, not relative to the (possibly tiny) difference: the error is at most
`u·(2+u)·(|exp x| + |ln y|)`, built from the two primitive roundings plus the subtraction's rounding.
No independent accuracy assumption about `eml` — only about `exp` and `ln`. -/
theorem eml_fwd_reduces_to_primitives {flE flL flEml : Real} (x y : Real)
    (hE   : RoundsW u flE   (exp x))
    (hL   : RoundsW u flL   (log y))
    (hSub : RoundsW u flEml (flE - flL)) :
    abs (flEml - (exp x - log y)) ≤ u * (1 + 1 + u) * (abs (exp x) + abs (log y)) := by
  -- shorthands for the two exact operands
  have hEe : abs (flE - exp x) ≤ u * abs (exp x) := roundsW_abs hE
  have hLl : abs (flL - log y) ≤ u * abs (log y) := roundsW_abs hL
  have hS  : abs (flEml - (flE - flL)) ≤ u * abs (flE - flL) := roundsW_abs hSub
  -- |flE| ≤ (1+u)|exp x|, |flL| ≤ (1+u)|log y|
  have hflE : abs flE ≤ abs (exp x) + u * abs (exp x) := abs_le_add_err hEe
  have hflL : abs flL ≤ abs (log y) + u * abs (log y) := abs_le_add_err hLl
  -- |flE - flL| ≤ |flE| + |flL| ≤ (1+u)(|exp x| + |log y|)
  have hsub_split : abs (flE - flL) ≤ abs flE + abs flL := by
    have h := abs_add flE (-flL)
    have e : flE + -flL = flE - flL := by mach_mpoly [flE, flL]
    rw [e, abs_neg] at h; exact h
  have hEL : abs (flE - flL) ≤ (abs (exp x) + u * abs (exp x)) + (abs (log y) + u * abs (log y)) :=
    le_trans hsub_split (add_le_add_both hflE hflL)
  -- middle term: |(flE - flL) - (exp x - log y)| ≤ u|exp x| + u|log y|
  have hmid_split :
      abs ((flE - flL) - (exp x - log y)) ≤ abs (flE - exp x) + abs (flL - log y) := by
    have h := abs_add (flE - exp x) (-(flL - log y))
    have e : (flE - exp x) + -(flL - log y) = (flE - flL) - (exp x - log y) := by
      mach_mpoly [flE, flL, exp x, log y]
    rw [e, abs_neg] at h; exact h
  have hmid : abs ((flE - flL) - (exp x - log y)) ≤ u * abs (exp x) + u * abs (log y) :=
    le_trans hmid_split (add_le_add_both hEe hLl)
  -- outer triangle: flEml - (exp x - log y) = (flEml - (flE - flL)) + ((flE - flL) - (exp x - log y))
  have houter : abs (flEml - (exp x - log y))
      ≤ abs (flEml - (flE - flL)) + abs ((flE - flL) - (exp x - log y)) := by
    have h := abs_add (flEml - (flE - flL)) ((flE - flL) - (exp x - log y))
    have e : (flEml - (flE - flL)) + ((flE - flL) - (exp x - log y)) = flEml - (exp x - log y) := by
      mach_mpoly [flEml, flE, flL, exp x, log y]
    rw [e] at h; exact h
  -- bound the first term: u·|flE - flL| ≤ u·(1+u)(|exp x| + |log y|)
  have hu : (0 : Real) ≤ u := u_nonneg
  have hfirst : u * abs (flE - flL) ≤ u * ((abs (exp x) + u * abs (exp x)) + (abs (log y) + u * abs (log y))) :=
    mul_le_mul_of_nonneg_left hEL hu
  have hstep1 : abs (flEml - (flE - flL)) ≤ u * ((abs (exp x) + u * abs (exp x)) + (abs (log y) + u * abs (log y))) :=
    le_trans hS hfirst
  -- assemble and simplify
  have hcomb := add_le_add_both hstep1 hmid
  refine le_trans houter (le_trans hcomb (le_of_eq ?_))
  mach_mpoly [u, abs (exp x), abs (log y)]

end MachLib.Real
