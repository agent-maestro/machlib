import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel
import MachLib.ErrorAlgebra
import MachLib.ConditionedError

/-!
# The condition number — when the conditioned bound is tight

`ConditionedError` bounds a mixed-sign kernel's error against the *conditioning
quantity* `Σ|tᵢ|`. Whether that is a useful forward-error guarantee is governed
by the **condition number** `κ = Σ|tᵢ| / |exact|`:

* the conditioned bound is `≈ w·Σ|tᵢ|`, so the *relative* error is `≈ w·κ`;
* `κ ≥ 1` always (`Σ|tᵢ| ≥ |exact|`, `exact_le_sigma` = the triangle inequality);
* `κ = 1` **iff the terms share a sign** (`sigma_eq_exact_nonneg`): then
  `Σ|tᵢ| = |exact|` and the conditioned bound *is* the relative bound — the kernel
  is perfectly conditioned;
* `κ → ∞` near cancellation (`exact → 0` with `Σ|tᵢ|` fixed) — the conditioned
  bound stays true but the *relative* guarantee degrades, honestly.

So the well/ill-conditioned boundary is exactly the sign structure of the terms.
This is the characterisation; proving `κ`-bounds for general kernel families
(where signs are data-dependent) is the open research past it.
-/

namespace MachLib.Real

/-- `|x| = −x` for nonpositive `x` (the `abs_of_nonneg` companion). -/
theorem abs_of_nonpos {x : Real} (h : x ≤ 0) : abs x = -x := by
  unfold abs
  by_cases h0 : 0 ≤ x
  · have hx : x = 0 := le_antisymm h h0
    rw [if_pos h0, hx]; mach_ring
  · rw [if_neg h0]

/-- `κ ≥ 1` always: the conditioning quantity dominates the exact value. (Just
the triangle inequality, named for what it means.) -/
theorem exact_le_sigma (t1 t2 : Real) : abs (t1 + t2) ≤ abs t1 + abs t2 := abs_add t1 t2

/-- **`κ = 1` for same-sign terms.** When both terms are nonneg, `Σ|tᵢ| = |exact|`,
so the conditioned bound `((1+w)^d−1)·Σ|tᵢ|` collapses to the relative bound
`((1+w)^d−1)·|exact|` — perfect conditioning. -/
theorem sigma_eq_exact_nonneg {t1 t2 : Real} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) :
    abs t1 + abs t2 = abs (t1 + t2) := by
  rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg (add_nonneg_ea h1 h2)]

/-- Same, both nonpositive (the other same-sign case). -/
theorem sigma_eq_exact_nonpos {t1 t2 : Real} (h1 : t1 ≤ 0) (h2 : t2 ≤ 0) :
    abs t1 + abs t2 = abs (t1 + t2) := by
  have e1 : abs t1 = -t1 := abs_of_nonpos h1
  have e2 : abs t2 = -t2 := abs_of_nonpos h2
  have e3 : abs (t1 + t2) = -(t1 + t2) := abs_of_nonpos (by
    have h := add_le_add_both h1 h2; rwa [show (0 : Real) + 0 = 0 from by mach_ring] at h)
  rw [e1, e2, e3]; mach_ring

/-- **Well-conditioned ⇒ conditioned bound = relative bound.** For same-sign terms
and any factor `B`, the conditioned target `B·Σ|tᵢ|` equals the relative target
`B·|exact|`. So `prod_diff_fwd`-style bounds on a same-sign dot are genuine
*relative* forward-error guarantees (`κ=1`); only cancellation (`κ>1`) separates
them. -/
theorem cond_is_rel_of_nonneg {t1 t2 B : Real} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) :
    B * (abs t1 + abs t2) = B * abs (t1 + t2) := by
  rw [sigma_eq_exact_nonneg h1 h2]

end MachLib.Real
