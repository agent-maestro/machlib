import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel
import MachLib.Exp
import MachLib.Trig
import MachLib.TrigLipschitz
import MachLib.ErrorAlgebra

/-!
# The transcendental rule: `exp` forward-error

The `{+,*}` growth algebra (`ErrorAlgebra`) tracks a *relative* error factor
`(1+w)^d`. Transcendentals break that model, and `exp` shows exactly why:

> `exp` converts the **absolute** error of its argument into a **relative**
> factor on its output. If `|x_c − x_e| ≤ E`, then
> `exp(x_c)/exp(x_e) = exp(x_c − x_e) ∈ [exp(−E), exp(E)]`, so the output's
> relative perturbation is `exp(E) − 1 ≈ E` — driven by the *absolute* `E`, not
> a relative input factor.

So a certifier cannot stay in the pure-relative world through an `exp` node: it
must carry an **absolute** argument-error bound `E` into the transcendental,
which converts it to the relative output factor `exp(E)·(1+w)`. That is the
hybrid the full algebra needs; `exp_grow` is its `exp` case, proved here.

`exp_grow`: with absolute argument error `E` and one rounding (`RoundsW w`),
`|fl(exp x_c) − exp x_e| ≤ exp(x_e)·(exp(E)·(1+w) − 1)`.

`sorryAx`-free; builds on `MachLib.Exp` (`exp_add`, `exp_pos`, `exp_monotone`,
`one_add_le_exp`) + the `ErrorAlgebra`/`FPModel` toolkit.
-/

namespace MachLib.Real

/-! fresh-var ring identities used below. -/
theorem et_lower_ring (A B : Real) : (A + B) - (1 + 1) = (B - 1) - (1 - A) := by
  mach_mpoly [A, B]
theorem et_tan_ring (E w : Real) :
    (1 - E) * (1 - w) + (1 + E) * (1 + w) = (1 + 1) + (E * w + E * w) := by
  mach_mpoly [E, w]
theorem et_factor (a b d : Real) :
    a * b * (1 + d) - a = a * (b * (1 + d) - 1) := by mach_mpoly [a, b, d]
theorem et_neg (A : Real) : -(A - 1) = 1 - A := by mach_mpoly [A]
theorem et_split3 (a b c : Real) : a - c = (a - b) + (b - c) := by mach_mpoly [a, b, c]

/-- `1 - A ≤ B - 1` from `2 ≤ A + B`. -/
theorem et_lower {A B : Real} (h : 1 + 1 ≤ A + B) : 1 - A ≤ B - 1 := by
  have h0 : 0 ≤ (A + B) - (1 + 1) := sub_nonneg_of_le h
  rw [et_lower_ring A B] at h0
  exact le_of_sub_nonneg h0

/-- **`exp` forward-error rule.** One rounded `exp` of an argument carrying
absolute error `≤ E` lands within a *relative* factor `exp(E)·(1+w)` of the exact
`exp(x_e)`. The absolute argument error `E` becomes the relative output factor —
the structural reason transcendentals need a hybrid (absolute+relative) algebra. -/
theorem exp_grow {w E xc xe p : Real}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hE : 0 ≤ E)
    (harg : abs (xc - xe) ≤ E)
    (hp : RoundsW w p (exp xc)) :
    abs (p - exp xe) ≤ exp xe * (exp E * (1 + w) - 1) := by
  obtain ⟨δ, hδl, hδu, hpeq⟩ := hp
  -- factor out exp xe
  have hexc : exp xc = exp xe * exp (xc - xe) := by
    rw [← exp_add, show xe + (xc - xe) = xc from by mach_ring]
  have hexe_pos : 0 ≤ exp xe := le_of_lt (exp_pos xe)
  have hfactor : p - exp xe = exp xe * (exp (xc - xe) * (1 + δ) - 1) := by
    rw [hpeq, hexc]; exact et_factor (exp xe) (exp (xc - xe)) δ
  have habs : abs (p - exp xe) = exp xe * abs (exp (xc - xe) * (1 + δ) - 1) := by
    rw [hfactor, abs_mul, abs_of_nonneg hexe_pos]
  rw [habs]
  apply mul_le_mul_of_nonneg_left ?_ hexe_pos
  -- now: |exp(xc-xe)*(1+δ) - 1| ≤ exp E*(1+w) - 1
  -- argument-error and rounding bounds
  have hΔE  : xc - xe ≤ E := le_of_abs_le harg
  have hEΔ  : -E ≤ xc - xe := by
    have h := neg_le_neg (neg_le_of_abs_le harg)
    rwa [show -(-(xc - xe)) = xc - xe from by mach_ring] at h
  have he_up  : exp (xc - xe) ≤ exp E := exp_monotone hΔE
  have he_lo  : exp (-E) ≤ exp (xc - xe) := exp_monotone hEΔ
  have he_nn  : 0 ≤ exp (xc - xe) := le_of_lt (exp_pos _)
  have h1w_nn : 0 ≤ 1 - w := sub_nonneg_of_le hw1
  have hd_up  : 1 + δ ≤ 1 + w := add_le_add_left hδu 1
  have hd_lo  : 1 - w ≤ 1 + δ := by
    have h := add_le_add_left hδl 1
    rwa [show (1 : Real) + (-w) = 1 - w from by mach_ring] at h
  have hd_nn  : 0 ≤ 1 + δ := le_trans h1w_nn hd_lo
  have hEexp_nn : 0 ≤ exp E := le_of_lt (exp_pos E)
  apply abs_le_of
  · -- upper: exp Δ (1+δ) - 1 ≤ exp E (1+w) - 1
    have hprod : exp (xc - xe) * (1 + δ) ≤ exp E * (1 + w) :=
      le_trans (mul_le_mul_of_nonneg_right he_up hd_nn)
               (mul_le_mul_of_nonneg_left hd_up hEexp_nn)
    exact sub_le_sub_right hprod 1
  · -- lower: -(exp Δ(1+δ) - 1) = 1 - exp Δ(1+δ) ≤ exp E(1+w) - 1
    rw [et_neg (exp (xc - xe) * (1 + δ))]
    -- reduce to 2 ≤ exp Δ(1+δ) + exp E(1+w)
    apply et_lower
    -- 2 ≤ (1-E)(1-w) + (1+E)(1+w) ≤ exp(-E)(1-w) + exp E(1+w) ≤ exp Δ(1+δ) + exp E(1+w)
    have ht1 : (1 - E) ≤ exp (-E) := by
      have h := one_add_le_exp (-E)
      rwa [show (1 : Real) + (-E) = 1 - E from by mach_ring] at h
    have ht2 : (1 + E) ≤ exp E := one_add_le_exp E
    have hlo1 : (1 - E) * (1 - w) ≤ exp (-E) * (1 - w) :=
      mul_le_mul_of_nonneg_right ht1 h1w_nn
    have hlo1' : exp (-E) * (1 - w) ≤ exp (xc - xe) * (1 + δ) :=
      le_trans (mul_le_mul_of_nonneg_right he_lo h1w_nn)
               (mul_le_mul_of_nonneg_left hd_lo he_nn)
    have hlo2 : (1 + E) * (1 + w) ≤ exp E * (1 + w) := by
      have h1wnn : 0 ≤ 1 + w := le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hw0)
      exact mul_le_mul_of_nonneg_right ht2 h1wnn
    -- assemble
    have hsum_lo : (1 + 1) + (E * w + E * w)
        ≤ exp (xc - xe) * (1 + δ) + exp E * (1 + w) := by
      have hA : (1 - E) * (1 - w) ≤ exp (xc - xe) * (1 + δ) := le_trans hlo1 hlo1'
      have hsum := add_le_add_both hA hlo2
      rw [et_tan_ring E w] at hsum; exact hsum
    have htwo : (1 : Real) + 1 ≤ (1 + 1) + (E * w + E * w) :=
      le_add_of_nonneg_right (add_nonneg_ea (mul_nonneg hE hw0) (mul_nonneg hE hw0))
    exact le_trans htwo hsum_lo

/-! ## the other transcendental kind: bounded-Lipschitz (`sin`, `cos`)

`exp` *amplifies* — it turns absolute argument error into a relative output
factor. `sin`/`cos` do the opposite: being globally 1-Lipschitz and bounded by 1,
they keep the error **absolute and bounded**. So the transcendental class splits
in two — amplifying (`exp`/`ln`, need the hybrid abs→rel conversion) and
bounded-Lipschitz (`sin`/`cos`, error stays `≤ E + w`). -/

/-- **`sin` forward-error rule.** One rounded `sin` of an argument with absolute
error `≤ E` stays within `E + w` of `sin x_e` — absolute, not amplified, because
`sin` is 1-Lipschitz and `|sin| ≤ 1`. -/
theorem sin_grow {w E xc xe p : Real}
    (hw0 : 0 ≤ w) (harg : abs (xc - xe) ≤ E)
    (hp : RoundsW w p (sin xc)) :
    abs (p - sin xe) ≤ w + E := by
  have hround1 : abs (p - sin xc) ≤ w := by
    have h := mul_le_mul_of_nonneg_left (abs_sin_le_one xc) hw0
    rw [show w * 1 = w from by mach_ring] at h
    exact le_trans (roundsW_abs hp) h
  have hprop : abs (sin xc - sin xe) ≤ E := le_trans (sin_lipschitz xc xe) harg
  rw [et_split3 p (sin xc) (sin xe)]
  exact le_trans (abs_add _ _) (add_le_add_both hround1 hprop)

/-- **`cos` forward-error rule** (same bound, same reason). -/
theorem cos_grow {w E xc xe p : Real}
    (hw0 : 0 ≤ w) (harg : abs (xc - xe) ≤ E)
    (hp : RoundsW w p (cos xc)) :
    abs (p - cos xe) ≤ w + E := by
  have habscos : abs (cos xc) ≤ 1 := by
    apply abs_le_of (cos_le_one xc)
    have h := neg_le_neg (neg_one_le_cos xc)
    rwa [show -(-1 : Real) = 1 from by mach_ring] at h
  have hround1 : abs (p - cos xc) ≤ w := by
    have h := mul_le_mul_of_nonneg_left habscos hw0
    rw [show w * 1 = w from by mach_ring] at h
    exact le_trans (roundsW_abs hp) h
  have hprop : abs (cos xc - cos xe) ≤ E := le_trans (cos_lipschitz xc xe) harg
  rw [et_split3 p (cos xc) (cos xe)]
  exact le_trans (abs_add _ _) (add_le_add_both hround1 hprop)

end MachLib.Real
