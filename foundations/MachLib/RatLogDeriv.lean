import MachLib.BipevRearrange

/-!
# The logarithmic derivative of a rational function, cleared

`BipevRearrange` takes its two clearing conditions as hypotheses and performs no division. This
module discharges them for the case that matters: `S = P/Q` and `v = (log ∘ S)' = S'/S`.

```
S'·Q²        = D                    -- `ratFn_deriv_cleared`, already in the corpus
(S'/S)·P·Q²  = Q·D                  -- here
```

The second follows from the first by one field identity, `(1/(p·(1/q)))·p = q`, and that identity is
where the two nonvanishing hypotheses live. **Both are paid here and neither propagates**: everything
downstream of `BipevRearrange` is division-free.

## Why `S > 0` enters exactly here and nowhere else

`log` is totalised in MachLib (`log y = 0` for `y ≤ 0`), so it is differentiable only where its
argument is positive — `HasDerivAt_log_pos`. That is the *only* place the branch's defining
hypothesis `S > 0` is used, and it is used for differentiability, not for any inequality in the
algebra. Everything after this module is sign-blind.
-/

namespace MachLib

open Real

/-- The derivative value of `S = P/Q`, named so the clearing lemmas can talk about it. -/
noncomputable def ratFnDeriv (P Q : List Real) (x : Real) : Real :=
  pev (pderiv P) x * (1 / pev Q x) + pev P x * (-(pev (pderiv Q) x) / (pev Q x * pev Q x))

/-- The derivative value of `log ∘ S`. -/
noncomputable def ratLogDeriv (P Q : List Real) (x : Real) : Real :=
  1 / (pev P x * (1 / pev Q x)) * ratFnDeriv P Q x

/-- The field identity the clearing turns on: `(1/(p·(1/q)))·p = q`. -/
private theorem inv_ratFn_mul {p q : Real} (hp : p ≠ 0) (hq : q ≠ 0) :
    (1 / (p * (1 / q))) * p = q := by
  have hqi : q * (1 / q) = 1 := mul_inv q hq
  have key : (p * (1 / q)) * q = p := by
    have e : (p * (1 / q)) * q = p * (q * (1 / q)) := by mach_mpoly [p, q, 1 / q]
    rw [e, hqi, mul_one_ax]
  have ht : p * (1 / q) ≠ 0 := by
    intro h
    have h2 : (p * (1 / q)) * q = 0 * q := by rw [h]
    rw [key, show (0 : Real) * q = 0 by mach_ring] at h2
    exact hp h2
  have hti : (p * (1 / q)) * (1 / (p * (1 / q))) = 1 := mul_inv _ ht
  have e2 : (1 / (p * (1 / q))) * p
      = ((p * (1 / q)) * (1 / (p * (1 / q)))) * q := by
    -- `conv_lhs` does not exist here; rewrite through the equation instead
    have step : (1 / (p * (1 / q))) * ((p * (1 / q)) * q)
        = ((p * (1 / q)) * (1 / (p * (1 / q)))) * q := by
      mach_mpoly [1 / (p * (1 / q)), p, 1 / q, q]
    rw [← step, key]
  rw [e2, hti, one_mul_thm]

/-- **`log ∘ S` is differentiable where `S > 0`**, with derivative `(1/S)·S'`. -/
theorem hasDerivAt_ratLog (P Q : List Real) (x : Real) (hQ : pev Q x ≠ 0)
    (hS : 0 < pev P x * (1 / pev Q x)) :
    HasDerivAt (fun y => Real.log (pev P y * (1 / pev Q y))) (ratLogDeriv P Q x) x :=
  HasDerivAt_comp Real.log (fun y => pev P y * (1 / pev Q y))
    (ratFnDeriv P Q x) (1 / (pev P x * (1 / pev Q x))) x
    (hasDerivAt_ratFn P Q x hQ) (HasDerivAt_log_pos _ hS)

/-- **`(S'/S)·P·Q² = Q·D`** — `BipevRearrange`'s second clearing condition, discharged. -/
theorem ratLogDeriv_cleared (P Q : List Real) (x : Real) (hQ : pev Q x ≠ 0) (hP : pev P x ≠ 0) :
    ratLogDeriv P Q x * (pev P x * pev (pmul Q Q) x)
      = pev Q x * pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x := by
  have h1 := inv_ratFn_mul hP hQ
  have h2 : ratFnDeriv P Q x * pev (pmul Q Q) x
      = pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x := ratFn_deriv_cleared P Q x hQ
  show (1 / (pev P x * (1 / pev Q x))) * ratFnDeriv P Q x * (pev P x * pev (pmul Q Q) x) = _
  have e : (1 / (pev P x * (1 / pev Q x))) * ratFnDeriv P Q x * (pev P x * pev (pmul Q Q) x)
      = ((1 / (pev P x * (1 / pev Q x))) * pev P x) * (ratFnDeriv P Q x * pev (pmul Q Q) x) := by
    mach_mpoly [1 / (pev P x * (1 / pev Q x)), ratFnDeriv P Q x, pev P x, pev (pmul Q Q) x]
  rw [e, h1, h2]

/-- **`S'·Q² = D`**, the first clearing condition, restated at `ratFnDeriv`. -/
theorem ratFnDeriv_cleared (P Q : List Real) (x : Real) (hQ : pev Q x ≠ 0) :
    ratFnDeriv P Q x * pev (pmul Q Q) x
      = pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x := ratFn_deriv_cleared P Q x hQ

/-! ## The tail forms `evRel_relCoeffs` consumes -/

theorem ratFnDeriv_cleared_on_tail {P Q : List Real} (hQz : ¬ EvZeroF (pev Q)) :
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      ratFnDeriv P Q x * pev (pmul Q Q) x
        = pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x := by
  obtain ⟨X, hX, hq⟩ := pev_ne_zero_on_tail hQz
  exact ⟨X, hX, fun x hx => ratFnDeriv_cleared P Q x (hq x hx)⟩

theorem ratLogDeriv_cleared_on_tail {P Q : List Real}
    (hQz : ¬ EvZeroF (pev Q)) (hPz : ¬ EvZeroF (pev P)) :
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      ratLogDeriv P Q x * (pev P x * pev (pmul Q Q) x)
        = pev Q x * pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x := by
  obtain ⟨X₁, hX₁, hq⟩ := pev_ne_zero_on_tail hQz
  obtain ⟨X₂, hX₂, hp⟩ := pev_ne_zero_on_tail hPz
  obtain ⟨X, hX, a1, a2⟩ := two_bounds' hX₁ hX₂
  exact ⟨X, hX, fun x hx =>
    ratLogDeriv_cleared P Q x (hq x (le_trans a1 hx)) (hp x (le_trans a2 hx))⟩

end MachLib
