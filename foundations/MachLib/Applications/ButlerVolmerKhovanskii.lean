import MachLib.Exp
import MachLib.SingleExpKhovanskii
import MachLib.KhovanskiiReduction

-- @strengthens butler_volmer_zero_at_zero_overpotential

/-!
# Forge kernel application — Butler-Volmer zero-overpotential certification

**Domain:** electrochemistry — battery management systems (BMS),
fuel cells, corrosion engineering, electroplating.
**Safety class:** DO-178C / IEC-61508 / ISO-26262 (kernel level),
with downstream IEC 62133 (lithium battery safety) and DOE H2
program (fuel cell control) applications.

## The kernel (from Forge, `butler_volmer.eml`)

```eml
fn current_density(i₀, α_a, α_c, η, T) -> CurrentDensity
{
  let β = F · η / (R · T)
  i₀ · (exp(α_a · β) - exp(-α_c · β))
}
```

## The verify obligation (was `sorry` in `MachLib/Discovered/butler_volmer.lean`)

```
@verify(lean, theorem = "butler_volmer_zero_at_zero_overpotential")
```

The clinically meaningful statement: `current = 0 ↔ overpotential = 0`.
This is a **zero-count obligation** at the heart of the Khovanskii
framework.

## Why the Khovanskii framework unblocks this

The Butler-Volmer current is structurally a length-2 ExpPoly:

  `i(η) = i₀ · exp(α_a·β(η)) - i₀ · exp(-α_c·β(η))`

The constructive Khovanskii bound for poly-in-(x, e^x) shipped in
`MachLib.SingleExpKhovanskii` provides the general theory. For this
specific obligation, the direct argument via `exp_injective` ships
the unblock.

The Khovanskii connection: the derivative
`i'(η) = i₀·(α_a + α_c)·F/(RT)·exp(α_a·β) + (positive sum)` has zero
count = 0 by the framework (sum of positive exp terms; bounded by 0
zeros via Khovanskii on derivative + exp_pos). Strict monotonicity
then forces exactly one zero of `i` — and direct computation locates
it at η = 0.

This file ships the constructive proof using the direct path. The
Khovanskii framework subsumes the same argument for general length-2
or longer ExpPolys arising in other Forge kernels (pharmacokinetics,
control loops, etc.). -/

namespace MachLib
namespace Forge
namespace ButlerVolmer

open MachLib.Real
open MachLib.PfaffianChainMod (mul_eq_zero_of_factor_ne_zero)

/-! ## Constants (matching the Forge .eml) -/

noncomputable def R_GAS   : Real := 8.314462618
noncomputable def F_FARAD : Real := 96485.33212

/-! ## The Butler-Volmer current density (exactly matches the .eml) -/

noncomputable def current_density
    (i₀ α_a α_c η T : Real) : Real :=
  i₀ * (Real.exp (α_a * (F_FARAD * η / (R_GAS * T)))
        - Real.exp (-α_c * (F_FARAD * η / (R_GAS * T))))

/-! ## The strengthened safety obligation: zero iff η = 0 -/

/-- **Forward direction**: at zero overpotential, the current is zero.

Trivial by computation. Requires `R_GAS · T ≠ 0` to handle the
division. -/
theorem current_zero_when_overpotential_zero
    (i₀ α_a α_c T : Real) (h_RT_ne : R_GAS * T ≠ 0) :
    current_density i₀ α_a α_c 0 T = 0 := by
  show i₀ * (Real.exp (α_a * (F_FARAD * 0 / (R_GAS * T)))
              - Real.exp (-α_c * (F_FARAD * 0 / (R_GAS * T)))) = 0
  rw [show F_FARAD * (0 : Real) = 0 from mul_zero F_FARAD]
  rw [show (0 : Real) / (R_GAS * T) = 0 from by
        rw [div_def 0 (R_GAS * T) h_RT_ne, zero_mul]]
  rw [show α_a * (0 : Real) = 0 from mul_zero α_a]
  rw [show -α_c * (0 : Real) = 0 from mul_zero (-α_c)]
  rw [exp_zero]
  rw [show (1 : Real) - 1 = 0 from sub_self 1]
  rw [mul_zero]

/-- **Reverse direction (safety-critical)**: if the current is zero,
the overpotential must be zero.

**Why this matters**: a BMS / fuel cell controller observing zero
current can conclude zero overpotential — no false equilibrium
detection.

Proof: from `i = 0` and `i₀ > 0`, extract `exp(α_a·β) = exp(-α_c·β)`;
by `exp_injective`, `α_a·β = -α_c·β`; rearrange to `(α_a + α_c)·β = 0`;
with `α_a + α_c > 0`, force `β = 0`; with `F/(RT) ≠ 0`, force `η = 0`. -/
theorem overpotential_zero_when_current_zero
    (i₀ α_a α_c η T : Real)
    (h_i₀_pos : i₀ > 0)
    (h_αa_pos : α_a > 0)
    (h_αc_pos : α_c > 0)
    (h_RT_ne : R_GAS * T ≠ 0)
    (h_F_ne : F_FARAD ≠ 0)
    (h_current_zero : current_density i₀ α_a α_c η T = 0) :
    η = 0 := by
  have h_i₀_ne : i₀ ≠ 0 := ne_of_gt h_i₀_pos
  -- Extract: exp(α_a · β) - exp(-α_c · β) = 0.
  have h_diff_zero :
      Real.exp (α_a * (F_FARAD * η / (R_GAS * T)))
       - Real.exp (-α_c * (F_FARAD * η / (R_GAS * T))) = 0 := by
    have h_mul_eq : i₀ * (Real.exp (α_a * (F_FARAD * η / (R_GAS * T)))
                          - Real.exp (-α_c * (F_FARAD * η / (R_GAS * T)))) = 0 :=
      h_current_zero
    exact mul_eq_zero_of_factor_ne_zero h_i₀_ne h_mul_eq
  -- Extract: exp(α_a·β) = exp(-α_c·β).
  have h_exp_eq : Real.exp (α_a * (F_FARAD * η / (R_GAS * T)))
                = Real.exp (-α_c * (F_FARAD * η / (R_GAS * T))) := by
    have hstep : Real.exp (α_a * (F_FARAD * η / (R_GAS * T)))
            - Real.exp (-α_c * (F_FARAD * η / (R_GAS * T)))
          + Real.exp (-α_c * (F_FARAD * η / (R_GAS * T)))
         = 0 + Real.exp (-α_c * (F_FARAD * η / (R_GAS * T))) := by
      rw [h_diff_zero]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at hstep
    exact hstep
  -- By exp_injective: α_a · β = -α_c · β.
  have h_arg_eq : α_a * (F_FARAD * η / (R_GAS * T))
                = -α_c * (F_FARAD * η / (R_GAS * T)) :=
    exp_injective h_exp_eq
  -- Rearrange to (α_a + α_c) · β = 0.
  have h_β_aux : α_a * (F_FARAD * η / (R_GAS * T))
                + α_c * (F_FARAD * η / (R_GAS * T)) = 0 := by
    have h_eq2 : α_a * (F_FARAD * η / (R_GAS * T))
              = -(α_c * (F_FARAD * η / (R_GAS * T))) := by
      rw [← neg_mul]
      exact h_arg_eq
    rw [h_eq2, neg_add_self]
  have h_sum_pos : α_a + α_c > 0 := by
    have h1 : α_a + 0 < α_a + α_c := add_lt_add_left h_αc_pos α_a
    rw [add_zero] at h1
    exact lt_trans_ax h_αa_pos h1
  have h_sum_ne : α_a + α_c ≠ 0 := ne_of_gt h_sum_pos
  have h_β_zero : F_FARAD * η / (R_GAS * T) = 0 := by
    have h_distrib : (α_a + α_c) * (F_FARAD * η / (R_GAS * T)) = 0 := by
      rw [show (α_a + α_c) * (F_FARAD * η / (R_GAS * T))
            = α_a * (F_FARAD * η / (R_GAS * T))
              + α_c * (F_FARAD * η / (R_GAS * T)) from by
            rw [mul_comm (α_a + α_c) (F_FARAD * η / (R_GAS * T)), mul_distrib,
                mul_comm (F_FARAD * η / (R_GAS * T)) α_a,
                mul_comm (F_FARAD * η / (R_GAS * T)) α_c]]
      exact h_β_aux
    exact mul_eq_zero_of_factor_ne_zero h_sum_ne h_distrib
  -- β = (F · η) / (RT) = 0; with RT ≠ 0, F · η = 0.
  have h_Fη_zero : F_FARAD * η = 0 := by
    rw [div_def (F_FARAD * η) (R_GAS * T) h_RT_ne] at h_β_zero
    -- h_β_zero : F_FARAD * η * (1 / (R_GAS * T)) = 0
    have h_inv_ne : (1 / (R_GAS * T)) ≠ 0 := by
      intro h
      have hinv : R_GAS * T * (1 / (R_GAS * T)) = 1 := mul_inv (R_GAS * T) h_RT_ne
      rw [h, mul_zero] at hinv
      exact zero_ne_one_ax hinv
    -- Commute h_β_zero from `(F·η) * inv = 0` to `inv * (F·η) = 0`.
    rw [mul_comm (F_FARAD * η) (1 / (R_GAS * T))] at h_β_zero
    exact mul_eq_zero_of_factor_ne_zero h_inv_ne h_β_zero
  -- F · η = 0 and F ≠ 0 force η = 0.
  exact mul_eq_zero_of_factor_ne_zero h_F_ne h_Fη_zero

/-! ## The combined iff theorem (the safety-critical contract) -/

/-- **Butler-Volmer current is zero iff overpotential is zero.**

This is the strengthened verify obligation that replaces the
`True` placeholder in `MachLib/Discovered/butler_volmer.lean`. The
clinical/engineering significance:

  * BMS / fuel cell controllers can use `current = 0` as a **reliable
    equilibrium detector** (no false positives possible).
  * Corrosion sensors avoid mis-detecting equilibrium when
    overpotential is in a non-zero spurious state.

This obligation is exactly the kind of zero-count property the
constructive Khovanskii framework was designed for. The proof uses
`exp_injective` from MachLib.Exp + algebraic manipulation; the
Khovanskii framework's `expPoly_khovanskii_bound` would handle the
analogous bound for general length-N ExpPoly kernels (multi-exp
pharmacokinetics, control loops, oscillators). -/
theorem butler_volmer_zero_iff_overpotential_zero
    (i₀ α_a α_c η T : Real)
    (h_i₀_pos : i₀ > 0)
    (h_αa_pos : α_a > 0)
    (h_αc_pos : α_c > 0)
    (h_RT_ne : R_GAS * T ≠ 0)
    (h_F_ne : F_FARAD ≠ 0) :
    current_density i₀ α_a α_c η T = 0 ↔ η = 0 := by
  constructor
  · intro h_zero
    exact overpotential_zero_when_current_zero i₀ α_a α_c η T
            h_i₀_pos h_αa_pos h_αc_pos h_RT_ne h_F_ne h_zero
  · intro h_η_zero
    rw [h_η_zero]
    exact current_zero_when_overpotential_zero i₀ α_a α_c T h_RT_ne

end ButlerVolmer
end Forge
end MachLib
