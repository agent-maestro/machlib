import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel
import MachLib.Iteration

/-!
# Contraction certificate, applied to a real kernel family

`Iteration.contraction_certificate` lifts a per-step error bound to the whole
trajectory *abstractly* (given an error sequence obeying `e(k+1) ≤ L·e k + ε`).
This file discharges that hypothesis for a concrete, ubiquitous kernel family —
**affine maps** `f(x) = c·x + d` — which covers the PID plant (`x' = 0.99x +
0.01u`), exponential smoothing (`x' = (1−α)x + αu`), and the RC low-pass
(`x' = (1−dt/τ)x + …`). All are affine; all contract iff `|c| < 1`.

* `affine_lipschitz` — `|f(x) − f(y)| ≤ c·|x − y|` (for `0 ≤ c`): the map is
  `c`-Lipschitz.
* `affine_trajectory_bound` — for the rounded iteration of an affine map with
  `0 ≤ c ≤ 1` and per-step round-off `≤ ε`, the trajectory error is
  `≤ ε·geom c n` with `(1−c)·bound ≤ ε` — an **unconditional** whole-trajectory
  bound for the actual kernel, no abstract hypothesis left. (`c = 0.99` ⇒ `≤
  100ε` over the whole run.)

`sorryAx`-free.
-/

namespace MachLib.Real

/-- An affine map is `c`-Lipschitz (`0 ≤ c`). -/
theorem affine_lipschitz (c d x y : Real) (hc : 0 ≤ c) :
    abs ((c * x + d) - (c * y + d)) ≤ c * abs (x - y) := by
  apply le_of_eq
  rw [show (c * x + d) - (c * y + d) = c * (x - y) from by mach_mpoly [c, d, x, y], abs_mul,
      abs_of_nonneg hc]

/-- **Affine kernels satisfy the contraction certificate.** The rounded iteration
of `f(x)=c·x+d` (exact orbit `xe`, computed orbit `xc` with per-step round-off
`≤ ε`) has whole-trajectory error `≤ ε·geom c n`, and `(1−c)·bound ≤ ε`. For
`c<1` this is a finite bound for all `n` — Leg A / FixedPoint's per-step result
lifted to the full run for a real kernel family. -/
theorem affine_trajectory_bound {c d ε : Real} {xc xe : Nat → Real}
    (hc0 : 0 ≤ c) (hε : 0 ≤ ε)
    (h0 : abs (xc 0 - xe 0) ≤ 0)
    (hexact : ∀ k, xe (k + 1) = c * xe k + d)
    (hstep : ∀ k, abs (xc (k + 1) - (c * xc k + d)) ≤ ε)
    (n : Nat) :
    abs (xc n - xe n) ≤ ε * geom c n ∧ (1 - c) * (ε * geom c n) ≤ ε := by
  have hrec : ∀ k, (fun n => abs (xc n - xe n)) (k + 1)
      ≤ c * (fun n => abs (xc n - xe n)) k + ε := by
    intro k
    show abs (xc (k + 1) - xe (k + 1)) ≤ c * abs (xc k - xe k) + ε
    rw [hexact k,
        show xc (k + 1) - (c * xe k + d)
          = (xc (k + 1) - (c * xc k + d)) + ((c * xc k + d) - (c * xe k + d))
          from by mach_mpoly [xc (k + 1), c, xc k, d, xe k]]
    exact le_trans (abs_add _ _)
      (le_trans (add_le_add_both (hstep k) (affine_lipschitz c d (xc k) (xe k) hc0))
        (le_of_eq (add_comm ε (c * abs (xc k - xe k)))))
  exact contraction_certificate (fun n => abs (xc n - xe n)) hc0 hε h0 hrec n

/-- **Nonlinear contraction.** The same trajectory bound for *any* map `f` given
only a global Lipschitz hypothesis `|f x − f y| ≤ L·|x − y|` — no affine structure
needed, so it covers nonlinear contractions (a saturating controller, the
logistic map's stable regime, …). `affine_trajectory_bound` is the instance
`f = (c·+d)`, `L = c`. (Local/domain-restricted Lipschitz is the continuation.) -/
theorem lipschitz_trajectory_bound {f : Real → Real} {L ε : Real} {xc xe : Nat → Real}
    (hL0 : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ x y, abs (f x - f y) ≤ L * abs (x - y))
    (h0 : abs (xc 0 - xe 0) ≤ 0)
    (hexact : ∀ k, xe (k + 1) = f (xe k))
    (hstep : ∀ k, abs (xc (k + 1) - f (xc k)) ≤ ε)
    (n : Nat) :
    abs (xc n - xe n) ≤ ε * geom L n ∧ (1 - L) * (ε * geom L n) ≤ ε := by
  have hrec : ∀ k, (fun n => abs (xc n - xe n)) (k + 1)
      ≤ L * (fun n => abs (xc n - xe n)) k + ε := by
    intro k
    show abs (xc (k + 1) - xe (k + 1)) ≤ L * abs (xc k - xe k) + ε
    rw [hexact k,
        show xc (k + 1) - f (xe k)
          = (xc (k + 1) - f (xc k)) + (f (xc k) - f (xe k))
          from by mach_mpoly [xc (k + 1), f (xc k), f (xe k)]]
    exact le_trans (abs_add _ _)
      (le_trans (add_le_add_both (hstep k) (hlip (xc k) (xe k)))
        (le_of_eq (add_comm ε (L * abs (xc k - xe k)))))
  exact contraction_certificate (fun n => abs (xc n - xe n)) hL0 hε h0 hrec n

/-- **Local (domain-restricted) contraction.** `f` need only be Lipschitz on a
domain `D`, provided both orbits stay in `D`. The honest version for maps that
contract only on an invariant region (a basin of attraction) — the local Banach
setting. -/
theorem local_lipschitz_trajectory_bound {f : Real → Real} {L ε : Real}
    {xc xe : Nat → Real} {D : Real → Prop}
    (hL0 : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ x y, D x → D y → abs (f x - f y) ≤ L * abs (x - y))
    (hin : ∀ k, D (xc k) ∧ D (xe k))
    (h0 : abs (xc 0 - xe 0) ≤ 0)
    (hexact : ∀ k, xe (k + 1) = f (xe k))
    (hstep : ∀ k, abs (xc (k + 1) - f (xc k)) ≤ ε)
    (n : Nat) :
    abs (xc n - xe n) ≤ ε * geom L n ∧ (1 - L) * (ε * geom L n) ≤ ε := by
  have hrec : ∀ k, (fun n => abs (xc n - xe n)) (k + 1)
      ≤ L * (fun n => abs (xc n - xe n)) k + ε := by
    intro k
    show abs (xc (k + 1) - xe (k + 1)) ≤ L * abs (xc k - xe k) + ε
    rw [hexact k,
        show xc (k + 1) - f (xe k)
          = (xc (k + 1) - f (xc k)) + (f (xc k) - f (xe k))
          from by mach_mpoly [xc (k + 1), f (xc k), f (xe k)]]
    exact le_trans (abs_add _ _)
      (le_trans (add_le_add_both (hstep k) (hlip (xc k) (xe k) (hin k).1 (hin k).2))
        (le_of_eq (add_comm ε (L * abs (xc k - xe k)))))
  exact contraction_certificate (fun n => abs (xc n - xe n)) hL0 hε h0 hrec n

end MachLib.Real
