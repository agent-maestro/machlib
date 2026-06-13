import MachLib.PfaffianChain
import MachLib.Differentiation
import MachLib.Rolle

/-!
# Constructive Khovanskii — Item 4 reduction substrate (the muse's angle 1)

This file implements the muse-suggested approach to the constructive
Khovanskii chain-step reduction. The key insight, due to the muse
(2026-06-13 review):

  Define an AUXILIARY function `f · exp(-c·y_n)` as a Real → Real
  function (NOT a PfaffianFn — sidestepping the chain extension).
  Use it purely as a Rolle vehicle:

    g := f · exp(-c·y_n)
    zeros(g) = zeros(f)  (since exp ≠ 0)
    g' = exp(-c·y_n) · (f' - c·y_n'·f)
    zeros(g') = zeros(f' - c·y_n'·f)  (since exp ≠ 0)
    By Rolle: zeros(g) ≤ zeros(g') + 1
    ⟹ zeros(f) ≤ zeros(f' - c·y_n'·f) + 1

This avoids ever constructing `exp(-c·y_n)` as a PfaffianFn — the
exp factor is purely a Real → Real auxiliary function used in the
proof of the zero count transfer lemma.

## Item 4 plan via muse's angle 1

  Step 1 (this file): mulNegExp_aux auxiliary + zero-equivalence
                      + HasDerivAt.
  Step 2: PfaffianFn.linearCombination (f' - c·y_n'·g).
  Step 3: Degree-drop claim (explicit c via leading coefficient).
  Step 4: Zero count transfer (combining 1-3).
  Step 5: Iteration to base case (degreeY n = 0 → dropLast + IH).

## What ships in this commit

Step 1 fully constructive. Steps 2-5 follow in subsequent commits.
-/

namespace MachLib
namespace PfaffianChainMod

open Real

/-! ## Real-arithmetic preliminaries

A small helper missing from MachLib: if a ≠ 0 and a·b = 0, then b = 0.
Used to transfer the zero set from `f` to `f · exp(-c·y_n)`. -/

theorem mul_eq_zero_of_factor_ne_zero {a b : Real} (ha : a ≠ 0)
    (hab : a * b = 0) : b = 0 := by
  -- (a * b) * (1/a) = b · 1 = b. So if a*b = 0, then 0 = b · 1 = b.
  have hkey : a * b * (1 / a) = b := by
    rw [mul_comm a b, mul_assoc, mul_inv a ha, mul_one_ax]
  rw [hab, zero_mul] at hkey
  exact hkey.symm

/-! ## The auxiliary function `f · exp(-c · y_n)` (muse Step 1)

This is the Real → Real function used as a Rolle vehicle. It's NOT
a PfaffianFn — we sidestep the chain extension entirely. -/

/-- The auxiliary function `f.eval x · exp(-c · y_n x)`. Used in the
zero count transfer lemma. -/
noncomputable def mulNegExp_aux (f : PfaffianFn) (c : Real)
    (y_n : Real → Real) : Real → Real :=
  fun x => f.eval x * Real.exp (-c * y_n x)

/-- **Same-zero-set lemma**: the auxiliary function has the same zeros
as f, because `exp(-c·y_n x)` is never zero. -/
theorem mulNegExp_aux_zero_iff (f : PfaffianFn) (c : Real)
    (y_n : Real → Real) (x : Real) :
    mulNegExp_aux f c y_n x = 0 ↔ f.eval x = 0 := by
  show f.eval x * Real.exp (-c * y_n x) = 0 ↔ f.eval x = 0
  constructor
  · intro h
    -- exp(-c·y_n x) ≠ 0 (by exp_pos). So if f.eval · exp = 0, then f.eval = 0.
    have hexp_ne : Real.exp (-c * y_n x) ≠ 0 := exp_ne_zero _
    -- f.eval x * exp(...) = 0 + factor exp ≠ 0 ⟹ f.eval x = 0.
    -- Use: rearrange as exp * f = 0 and apply mul_eq_zero_of_factor_ne_zero.
    rw [mul_comm] at h
    exact mul_eq_zero_of_factor_ne_zero hexp_ne h
  · intro h
    rw [h, zero_mul]

/-! ## HasDerivAt for mulNegExp_aux (muse Step 1 continued)

The derivative of `f · exp(-c · y_n)` at x, given chain coherence:

  d/dx (f · exp(-c · y_n)) = f' · exp(-c · y_n) + f · (-c · y_n') · exp(-c · y_n)
                          = exp(-c · y_n) · (f' - c · y_n' · f)

Note: f' here means `f.chainTotalDerivative.eval`, which is the
total derivative including chain contributions. y_n' is
`chain.evals n` differentiated, which by chain coherence equals
`MultiPoly.eval (chain.relations n) x (chain.chainValues x)`. -/

/-- **The HasDerivAt theorem for the auxiliary function (raw product
rule form).** Given chain coherence-derived HasDerivAt's for f and
y_n, the auxiliary function has the natural product-rule derivative.

The derivative shape `f' * E + f * (E * (-c * y_n'))` is the raw
product rule output; consumers can rearrange to the equivalent
factored form `E * (f' - c * y_n' * f)` using ring arithmetic. -/
theorem hasDerivAt_mulNegExp_aux_raw (f : PfaffianFn) (c : Real)
    (y_n : Real → Real) (y_n' : Real) (x : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval x) x)
    (hyn : HasDerivAt y_n y_n' x) :
    HasDerivAt (mulNegExp_aux f c y_n)
               (f.chainTotalDerivative.eval x * Real.exp (-c * y_n x)
                + f.eval x * (Real.exp (-c * y_n x) * (-c * y_n')))
               x := by
  show HasDerivAt (fun x => f.eval x * Real.exp (-c * y_n x))
                  (f.chainTotalDerivative.eval x * Real.exp (-c * y_n x)
                   + f.eval x * (Real.exp (-c * y_n x) * (-c * y_n'))) x
  -- HasDerivAt for (-c * y_n).
  have hneg_c_yn : HasDerivAt (fun x => -c * y_n x) (-c * y_n') x := by
    have hconst : HasDerivAt (fun _ => -c) 0 x := HasDerivAt_const (-c) x
    have hmul := HasDerivAt_mul (fun _ => -c) y_n 0 y_n' x hconst hyn
    have hsimp : 0 * y_n x + -c * y_n' = -c * y_n' := by
      rw [zero_mul, zero_add]
    rw [hsimp] at hmul
    exact hmul
  -- HasDerivAt for exp(-c * y_n).
  have hexp_comp : HasDerivAt (fun x => Real.exp (-c * y_n x))
                              (Real.exp (-c * y_n x) * (-c * y_n')) x := by
    have hexp_at : HasDerivAt Real.exp (Real.exp (-c * y_n x)) (-c * y_n x) :=
      HasDerivAt_exp (-c * y_n x)
    exact HasDerivAt_comp Real.exp (fun x => -c * y_n x) (-c * y_n')
            (Real.exp (-c * y_n x)) x hneg_c_yn hexp_at
  -- Product rule.
  exact HasDerivAt_mul f.eval (fun x => Real.exp (-c * y_n x))
          (f.chainTotalDerivative.eval x)
          (Real.exp (-c * y_n x) * (-c * y_n')) x hf hexp_comp

/-- **Algebraic identity** relating the raw product-rule shape to the
factored form. This is the ring identity that lets us rewrite

  f' * E + f * (E * (-c * y_n'))
    = E * (f' - c * y_n' * f)

where E = exp(-c * y_n x). Pure real-arithmetic algebra. -/
theorem mulNegExp_derivative_factored (f' E f c y_n' : Real) :
    f' * E + f * (E * (-c * y_n')) = E * (f' - c * y_n' * f) := by
  -- mach_ring handles most ring rewrites but leaves a mul_comm residue.
  mach_ring
  -- Residue: f * (E * (c * y_n')) = E * (f * (c * y_n')).
  -- Use mul_comm and assoc.
  rw [← mul_assoc, mul_comm f E, mul_assoc]

end PfaffianChainMod
end MachLib
