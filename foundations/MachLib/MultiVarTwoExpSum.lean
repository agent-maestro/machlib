import MachLib.MultiVarTwoExpRolle
import MachLib.Differentiation
import MachLib.EMLTChartKhovanskii

/-!
# Khovanskii base-case toolkit + the `N=1` sum instance (Gate 2d, two-exp)

Two reusable base-case tools for the Khovanskii induction — a **strictly monotone Jacobian has ≤ 1 zero**
(`inj_zeros_le_one` + `injective_of_antitone`) — plus a second concrete two-exponential count that exercises
the recursion where the Jacobian bound is NONtrivial (`N = 1`):

  `{ x + y = c,  eˣ + eʸ = d }`  ≤ 2 solutions.

Here the line `f = x+y−c` is parametrized by `y = c−x`, and the Jacobian `J = f_x g_y − f_y g_x =
e^{c−x} − eˣ` is strictly decreasing (so injective, ≤ 1 zero → `N = 1`), giving `#solutions ≤ 2` — matching
the convexity fact that `eˣ + e^{c−x} = d` has at most two roots. On single-variable `rolle_ct` only.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real

/-- Add two strict inequalities (derived from `add_lt_add_left`, the only additive-order axiom). -/
theorem add_lt_add {a b c d : Real} (h1 : a < b) (h2 : c < d) : a + c < b + d :=
  lt_trans_ax (add_lt_add_left h2 a)
    (by rw [add_comm a d, add_comm b d]; exact add_lt_add_left h1 d)

/-- `a < b → −b < −a`. -/
theorem neg_lt_neg {a b : Real} (h : a < b) : -b < -a := by
  have key := add_lt_add_left h ((-a) + (-b))
  rw [show (-a + -b) + a = -b from by mach_mpoly [a, b],
      show (-a + -b) + b = -a from by mach_mpoly [a, b]] at key
  exact key

/-- **A strictly antitone function is injective.** -/
theorem injective_of_antitone (J : Real → Real) (hanti : ∀ x y, x < y → J y < J x) :
    ∀ x y, J x = J y → x = y := by
  intro x y hxy
  rcases lt_total x y with h | h | h
  · exact absurd hxy (ne_of_gt (hanti x y h))
  · exact h
  · exact absurd hxy.symm (ne_of_gt (hanti y x h))

/-- **An injective function has ≤ 1 zero** in any `Nodup` list (Khovanskii base case for a monotone
Jacobian). -/
theorem inj_zeros_le_one (J : Real → Real) (hinj : ∀ x y, J x = J y → x = y) :
    ∀ zeros : List Real, zeros.Nodup → (∀ z ∈ zeros, J z = 0) → zeros.length ≤ 1
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: rest, hnd, hz => by
      exfalso
      have hxy : x ≠ y := fun h =>
        (List.nodup_cons.mp hnd).1 (List.mem_cons.mpr (Or.inl h))
      exact hxy (hinj x y (by
        rw [hz x (List.mem_cons_self _ _),
          hz y (List.mem_cons_of_mem _ (List.mem_cons_self _ _))]))

/-- The sum-case Jacobian `J(x) = e^{c−x} − eˣ` is strictly decreasing. -/
theorem sumJac_antitone (c : Real) :
    ∀ x1 x2, x1 < x2 → exp (c - x2) - exp x2 < exp (c - x1) - exp x1 := by
  intro x1 x2 h12
  have hA : exp (c - x2) < exp (c - x1) :=
    exp_lt (by rw [sub_def, sub_def]; exact add_lt_add_left (neg_lt_neg h12) c)
  have hB : -exp x2 < -exp x1 := neg_lt_neg (exp_lt h12)
  have h := add_lt_add hA hB
  rw [← sub_def, ← sub_def] at h
  exact h

/-- **`{x+y=c, eˣ+eʸ=d}` has `≤ 2` solutions in any box** — a two-exponential Khovanskii–Rolle count with
`N = 1` (the Jacobian `e^{c−x}−eˣ` is strictly monotone, so has ≤ 1 zero). -/
theorem line_meets_exp_sum_le_two (c d a b : Real) (hab : a < b) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ exp z + exp (c - z) - d = 0) →
      zeros.length ≤ 1 + 1 := by
  apply khovanskii_rolle_count
    (fun x => exp x + exp (c - x) - d) (fun _ => -1)
    (fun _ => 1) (fun _ => 1) (fun x => exp x) (fun x => exp (c - x)) a b hab
  · -- hGderiv : d/dx (eˣ + e^{c−x} − d) = eˣ − e^{c−x} = g_x + g_y·yc'
    intro z _ _
    rw [show exp z + exp (c - z) * -1 = exp z + exp (c - z) * (0 - 1) - 0 from by mach_ring]
    exact HasDerivAt_sub (fun x => exp x + exp (c - x)) (fun _ => d)
      (exp z + exp (c - z) * (0 - 1)) 0 z
      (HasDerivAt_add Real.exp (fun x => exp (c - x)) (exp z) (exp (c - z) * (0 - 1)) z
        (HasDerivAt_exp z)
        (hasDerivAt_exp_comp (fun x => c - x) (0 - 1) z
          (HasDerivAt_sub (fun _ => c) (fun x => x) 0 1 z (HasDerivAt_const c z) (HasDerivAt_id z))))
      (HasDerivAt_const d z)
  · -- hcurve
    intro z _ _; show (1 : Real) + 1 * (-1) = 0; mach_ring
  · -- hJ_bound : the Jacobian is strictly monotone, so ≤ 1 zero
    intro zeros_J hnd hJ
    apply inj_zeros_le_one (fun z => exp (c - z) - exp z)
      (injective_of_antitone _ (sumJac_antitone c)) zeros_J hnd
    intro z hz
    obtain ⟨_, _, hjz⟩ := hJ z hz
    rw [show exp (c - z) - exp z = 1 * exp (c - z) - 1 * exp z from by mach_ring]
    exact hjz

end TwoExp
end MultiVarMod
end MachLib
