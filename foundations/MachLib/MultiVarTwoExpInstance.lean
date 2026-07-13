import MachLib.MultiVarTwoExpRolle
import MachLib.Differentiation
import MachLib.EMLTChartKhovanskii

/-!
# A concrete two-exponential count — end-to-end validation (Gate 2d, two-exp T.0/T.1 demo)

Applies the parametrized Khovanskii–Rolle counting (`khovanskii_rolle_count`) to a genuine
two-independent-exponentials system, with an **explicit** parametrization (so no IFT is needed):

  `{ x + y = c,  eˣ − eʸ = 0 }`  in the box, projected to `x`.

Here `f = x + y − c` is a line, exactly parametrized by `y = c − x` (`yc' = −1`), and `g = eˣ − eʸ` has
partials `g_x = eˣ`, `g_y = −eʸ = −e^{c−x}` along the curve. The Jacobian `J = f_x g_y − f_y g_x =
−(eˣ + e^{c−x})` is **never zero** (`exp_pos`), so it has zero zeros (`N = 0`), and the counting gives
`#solutions ≤ 1`. (Indeed exactly one: `x = y = c/2`.) This validates the T.0/T.1 engine end-to-end on a
real two-exponential system, on single-variable `rolle_ct` only — the first two-exponential count in the
library.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real

/-- **`{x+y=c, eˣ=eʸ}` has `≤ 1` solution in any box** — a concrete two-exponential Khovanskii–Rolle count
via `khovanskii_rolle_count` with the explicit line parametrization `y = c − x`. -/
theorem line_meets_exp_eq_le_one (c a b : Real) (hab : a < b) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ exp z - exp (c - z) = 0) →
      zeros.length ≤ 0 + 1 := by
  apply khovanskii_rolle_count
    (fun x => exp x - exp (c - x)) (fun _ => -1)
    (fun _ => 1) (fun _ => 1) (fun x => exp x) (fun x => -exp (c - x)) a b hab
  · -- hGderiv : d/dx (eˣ − e^{c−x}) = eˣ + e^{c−x} = g_x + g_y·yc'
    intro z _ _
    rw [show exp z + -exp (c - z) * -1 = exp z - exp (c - z) * (0 - 1) from by mach_ring]
    exact HasDerivAt_sub Real.exp (fun x => exp (c - x)) (exp z) (exp (c - z) * (0 - 1)) z
      (HasDerivAt_exp z)
      (hasDerivAt_exp_comp (fun x => c - x) (0 - 1) z
        (HasDerivAt_sub (fun _ => c) (fun x => x) 0 1 z (HasDerivAt_const c z) (HasDerivAt_id z)))
  · -- hcurve : f_x + f_y·yc' = 1 + 1·(−1) = 0
    intro z _ _; show (1 : Real) + 1 * (-1) = 0; mach_ring
  · -- hJ_bound : the Jacobian is never zero, so it has 0 zeros
    intro zeros_J _ hJ
    cases zeros_J with
    | nil => exact Nat.le_refl 0
    | cons z rest =>
      exfalso
      obtain ⟨_, _, hjz⟩ := hJ z (List.mem_cons_self z rest)
      have hsum : (0 : Real) < exp z + exp (c - z) := by
        have h1 : exp z + 0 < exp z + exp (c - z) := add_lt_add_left (exp_pos (c - z)) (exp z)
        rw [add_zero] at h1
        exact lt_trans_ax (exp_pos z) h1
      have hS0 : exp z + exp (c - z) = 0 := by
        rw [show exp z + exp (c - z) = -(1 * (-exp (c - z)) - 1 * exp z) from by mach_ring, hjz,
          neg_zero]
      exact lt_irrefl_ax 0 (hS0 ▸ hsum)

end TwoExp
end MultiVarMod
end MachLib
