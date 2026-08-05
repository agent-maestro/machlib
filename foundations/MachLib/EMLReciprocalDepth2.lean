import MachLib.SinNotInEML
import MachLib.FieldLemmas
import MachLib.SignTactic
import MachLib.EMLAsymptoticClass

/-!
# `K/x` at depth 2: every reaching tree has `K > 1`

**The prior arm proved the floor for ONE family** — `no_exp_eq_log_of_le_one`, the impossibility
`exp a ≠ log K` for `K ≤ 1`. **This closes the depth-2 case for the family that an exhaustive
numerical search found to be the ONLY depth-2 shape reaching `K/x`**
(`monogate-research/exploration/inv_x_reachable_K_2026_08_04/RESULT.md`: 93 distinct `K` at depth 2,
every one from `((c ⊕ x) ⊕ c)`, none `≤ 1`).

**The route is "constrain the destination", not shape enumeration.** Two evaluations at distinct
positive points force the outer constant, and the outer constant forces `K` behind an `exp`.

**What the search contributed:** it did not prove anything. It told us *which shape to constrain* and
*what invariant to look for* — `K = exp(strictly positive)`. That is the search earning its keep as
a direction-finder rather than as evidence.
-/

namespace MachLib
namespace Real

/-- `x · exp(u − log x) = exp u` for `x > 0`. The division-free form of `exp(u − log x) = exp u / x`,
which is what lets the whole argument stay inside the corpus's algebraic idiom. -/
theorem mul_exp_sub_log {u x : Real} (hx : 0 < x) :
    x * exp (u - log x) = exp u := by
  -- DIVISION-FREE on purpose: `exp_sub` would introduce `/`, which `mach_mpoly` does not
  -- normalise and for which this corpus has no cancellation lemma. `exp_add` keeps the whole
  -- argument inside the algebraic idiom the tactics actually support.
  have h1 : exp (log x) * exp (u - log x) = exp u := by
    rw [← exp_add]
    have e : log x + (u - log x) = u := by mach_ring
    rw [e]
  rw [exp_log hx] at h1
  exact h1

/-- **The depth-2 reciprocal family, evaluated.** `eml (eml (const a) var) (const c)` sends `x` to
`exp(exp a)/x − log c`, here in the division-free form `x · eval = exp(exp a) − x · log c`. -/
theorem depth2_eval_scaled (a c x : Real) (hx : 0 < x) :
    x * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x
      = exp (exp a) - x * log c := by
  show x * (exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x) - log c) = _
  show x * (exp (exp a - log x) - log c) = _
  have h : x * (exp (exp a - log x) - log c)
      = x * exp (exp a - log x) - x * log c := by mach_mpoly [x, exp (exp a - log x), log c]
  rw [h, mul_exp_sub_log hx]

/-- **The outer constant is FORCED.** If the tree agrees with `K/x` at two distinct positive points,
`log c = 0` — there is no freedom in the second argument. -/
theorem depth2_forces_log_c_zero {a c K x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x₂ = K) :
    log c = 0 := by
  rw [depth2_eval_scaled a c x₁ h₁] at e₁
  rw [depth2_eval_scaled a c x₂ h₂] at e₂
  -- (exp(exp a) − x₁·L) = (exp(exp a) − x₂·L)  ⟹  (x₂ − x₁)·L = 0
  have h := e₁.trans e₂.symm
  have hsub : (x₂ - x₁) * log c = 0 := by
    have e : (x₂ - x₁) * log c
        = (exp (exp a) - x₁ * log c) - (exp (exp a) - x₂ * log c) := by
      mach_mpoly [x₁, x₂, log c, exp (exp a)]
    rw [e, h]; mach_mpoly [exp (exp a), x₂, log c]
  have hx : x₂ - x₁ ≠ 0 := by
    intro hz
    apply hne
    have e : x₁ = x₂ - (x₂ - x₁) := by mach_ring
    rw [e, hz]; mach_ring
  -- This corpus has `mul_ne_zero` but no `mul_eq_zero`, and no `by_contra` tactic. The
  -- contrapositive plus `Classical.byContradiction` does the same work with what exists.
  exact Classical.byContradiction (fun hL => (mul_ne_zero hx hL) hsub)

/-- **`K > 1`, for every depth-2 tree of this family reaching `K/x`.**

`K = exp(exp a)`, and `exp a > 0`, so `K > 1`. **The floor is not a bound that happens to hold — it
is `exp` being unable to reach `0`.** -/
theorem depth2_K_over_x_gt_one {a c K x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const c)).eval x₂ = K) :
    1 < K := by
  have hL : log c = 0 := depth2_forces_log_c_zero h₁ h₂ hne e₁ e₂
  rw [depth2_eval_scaled a c x₁ h₁, hL] at e₁
  have hK : K = exp (exp a) := by
    rw [← e₁]; mach_mpoly [x₁, exp (exp a)]
  rw [hK]
  exact one_lt_exp (exp_pos a)

end Real
end MachLib
