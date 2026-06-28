import MachLib.OperatorBasisComplete
import MachLib.AffineContraction

/-!
# The trajectory lift — the certifier's per-evaluation error, over a whole iteration

The operator-basis certifier (`gexpr_sound`) bounds the forward error of **one**
evaluation of a kernel. Real kernels run in loops — controllers, filters, fixed-point
solvers — so the question is the **whole-trajectory** error. The contraction certificate
(`lipschitz_trajectory_bound`) already lifts a *uniform per-step* error `ε` over an
`L`-contraction to `ε · geom L n ≤ ε/(1−L)`. The missing link is supplying that `ε`
*from the certifier*.

`iterated_kernel_trajectory` is that link: it represents the kernel as a state-indexed
expression `g : Real → GExpr` (`(g x).exact = f x`), reads each step's per-evaluation
forward error off `gexpr_fwd_error`, and feeds the **orbit-uniform** bound into the
contraction certificate. The state-dependence of the per-step error — `Ebound` grows
with the input magnitude through `Mbound` — is handled by the caller's `hub` hypothesis:
a single `ε` bounding the certifier's `Ebound` along the (bounded) orbit. That orbit
bound is the one genuinely new obligation a loop adds over a single evaluation.

`scaling_iteration_certified` discharges it end-to-end for a contractive scaling kernel
`x ↦ c·x` (`0 ≤ c < 1` — a discretized decay / damped amplitude): the orbit stays in
`|x| ≤ B`, so the per-step certifier bound is uniformly `≤ w·|c|·B`, and the whole-run
error is `≤ w·|c|·B / (1−c)`. The analytic analogue of the PID capstone's bit-level
lift. `sorryAx`-free; 0 new axioms.
-/

namespace MachLib.Real

/-- **The trajectory lift.** A kernel `f` represented by a state-indexed expression `g`
(`(g x).exact = f x`, `Valid`), iterated with each step a rounded `GExpr` evaluation
(`heval`), has whole-trajectory error `≤ ε · geom L n ≤ ε/(1−L)` — where `L` is `f`'s
Lipschitz constant and `ε` is the certifier's per-evaluation forward error, made
orbit-uniform by `hub` (`(g (xc k)).Ebound w ≤ ε` for every step). Composes
`gexpr_fwd_error` (per evaluation) with `lipschitz_trajectory_bound` (over the run). -/
theorem iterated_kernel_trajectory {w L ε : Real} {f : Real → Real} {g : Real → GExpr}
    {xc xe : Nat → Real}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hL0 : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ x y, abs (f x - f y) ≤ L * abs (x - y))
    (hgexact : ∀ x, (g x).exact = f x)
    (hgvalid : ∀ x, (g x).Valid)
    (heval : ∀ k, GRoundedEval w (g (xc k)) (xc (k + 1)))
    (hub : ∀ k, (g (xc k)).Ebound w ≤ ε)
    (h0 : abs (xc 0 - xe 0) ≤ 0)
    (hexact : ∀ k, xe (k + 1) = f (xe k))
    (n : Nat) :
    abs (xc n - xe n) ≤ ε * geom L n ∧ (1 - L) * (ε * geom L n) ≤ ε := by
  refine lipschitz_trajectory_bound hL0 hε hlip h0 hexact (fun k => ?_) n
  have hfe := gexpr_fwd_error hw0 hw1 (heval k) (hgvalid (xc k))
  rw [hgexact (xc k)] at hfe
  exact le_trans hfe (hub k)

/-- **A contractive scaling kernel, iterated and certified end-to-end.** `x ↦ c·x`
(`0 ≤ c`, computed as one rounded product per step) with the orbit bounded `|xc k| ≤ B`:
the per-step certifier bound is uniformly `w·|c|·B`, so the whole-trajectory error is
`≤ (w·|c|·B) · geom c n`, and `(1−c)·(that) ≤ w·|c|·B` — i.e. `≤ w·|c|·B / (1−c)` for the
entire run when `c < 1`. The orbit bound `hbound` is the single obligation the loop adds. -/
theorem scaling_iteration_certified {w c B : Real} {xc xe : Nat → Real}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc0 : 0 ≤ c) (hB0 : 0 ≤ B)
    (hbound : ∀ k, abs (xc k) ≤ B)
    (heval : ∀ k, GRoundedEval w (.mul (.leaf c) (.leaf (xc k))) (xc (k + 1)))
    (h0 : abs (xc 0 - xe 0) ≤ 0)
    (hexact : ∀ k, xe (k + 1) = c * xe k)
    (n : Nat) :
    abs (xc n - xe n) ≤ (w * (abs c * B)) * geom c n
      ∧ (1 - c) * ((w * (abs c * B)) * geom c n) ≤ w * (abs c * B) := by
  have hlip : ∀ x y, abs (c * x - c * y) ≤ c * abs (x - y) := by
    intro x y
    have he : abs (c * x - c * y) = c * abs (x - y) := by
      rw [show c * x - c * y = c * (x - y) from by mach_ring, abs_mul, abs_of_nonneg hc0]
    exact le_of_eq he
  have hgexact : ∀ x, (GExpr.mul (.leaf c) (.leaf x)).exact = c * x := fun _ => rfl
  have hgvalid : ∀ x, (GExpr.mul (.leaf c) (.leaf x)).Valid := fun _ => ⟨trivial, trivial⟩
  have hub : ∀ k, (GExpr.mul (.leaf c) (.leaf (xc k))).Ebound w ≤ w * (abs c * B) := by
    intro k
    have hcln : (GExpr.mul (.leaf c) (.leaf (xc k))).Ebound w = w * (abs c * abs (xc k)) := by
      simp only [GExpr.Ebound, GExpr.Mbound, mul_zero, add_zero, zero_add]
    rw [hcln]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hbound k) (abs_nonneg c)) hw0
  exact iterated_kernel_trajectory hw0 hw1 hc0
    (mul_nonneg hw0 (mul_nonneg (abs_nonneg c) hB0)) hlip hgexact hgvalid heval hub h0 hexact n

end MachLib.Real
