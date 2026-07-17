import MachLib.BivariateDeriv
import MachLib.TwoExpNonlinearCurveInstance
import MachLib.TwoExpPfaffianRepresentation
import MachLib.KhovanskiiReduction

/-!
# Two independent exponentials in `f` itself — a genuine curve-intersection count (Gate 2d)

`TwoExpNonlinearCurveInstance.lean` built the first non-degenerate curve (`f = eˣ·y − c`), but its
`f_x = eˣ·y` is only linear in `y` — only `f_y` is genuinely transcendental. This file builds a case
where **both** partials are transcendental: `f(x,y) = eʸ − eˣ − c`, `f_x = −eˣ`, `f_y = eʸ`. It then
applies the *full* curve-intersection capstone (`khovanskii_rolle_count_curve_of_represented_jacobian`,
not just a slice bound) against a second curve `g(x,y) = eʸ − x·eˣ`, giving a genuine finite bound on
how many times `{f=0}` and `{g=0}` meet.

**A real scope limit found along the way.** The most natural "two independent exponentials" curve is
`eˣ+eʸ=c`: solving for `y` gives `yc(x) = log(c−eˣ)`, well-defined only for `x < log c` — no real `y`
satisfies the equation once `eˣ ≥ c`. `hasDerivAt_implicit` (`BivariateDeriv.lean`) requires its curve
hypothesis `∀ s : Real, f s (yc s) = 0` to hold for **every** real `s`, not just an interval — so no
total function `yc` can ever discharge it for `eˣ+eʸ=c`. This is a genuine, previously-undocumented
boundary of the IFT bridge: it only reaches curves with a **global** solution branch. `f = eʸ−eˣ−c`
(`c ≥ 0`) routes around this rather than resolving it — `eˣ+c > 0` for every real `x`, so `yc(x) =
log(eˣ+c)` is total — while still keeping `f_y = eʸ` genuinely non-constant, unlike a linear curve.
Whether the branch-curve case (`eˣ+eʸ=c`) admits any treatment is left open; it would need an
interval-localized variant of `hasDerivAt_implicit` that does not currently exist.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce

/-! ## Part 1: the curve `yc(x) = log(eˣ + c)`, total for every `c ≥ 0` -/

/-- The curve: `f(x, sumC_yc c x) = 0`, i.e. `eˣ + c = exp (log (eˣ+c))`. -/
noncomputable def sumC_yc (c z : Real) : Real := log (exp z + c)

/-- `eˣ + c > 0` for every real `x`, given `c ≥ 0` — the fact that makes `sumC_yc` total, unlike
`log (c − eˣ)` for `eˣ+eʸ=c`. -/
theorem sumC_pos (c z : Real) (hc : 0 ≤ c) : 0 < exp z + c := by
  have h := add_pos_of_nonneg_pos hc (exp_pos z)
  rwa [show c + exp z = exp z + c from by mach_ring] at h

theorem sumC_exp_yc (c z : Real) (hc : 0 ≤ c) : exp (sumC_yc c z) = exp z + c :=
  exp_log (sumC_pos c z hc)

/-- `yc' = eˣ/(eˣ+c)` — the direct closed-form derivative, via the log chain rule. -/
theorem hasDerivAt_sumC_yc (c x : Real) (hc : 0 ≤ c) :
    HasDerivAt (fun t => sumC_yc c t) (1 / (exp x + c) * exp x) x := by
  have hsum0 : HasDerivAt (fun t => exp t + c) (exp x + 0) x :=
    HasDerivAt_add (fun t => exp t) (fun _ => c) (exp x) 0 x (HasDerivAt_exp x) (HasDerivAt_const c x)
  have hsum : HasDerivAt (fun t => exp t + c) (exp x) x := by
    rwa [show exp x + 0 = exp x from by mach_ring] at hsum0
  have hlog := HasDerivAt_log_pos (exp x + c) (sumC_pos c x hc)
  exact HasDerivAt_comp Real.log (fun t => exp t + c) (exp x) (1 / (exp x + c)) x hsum hlog

/-- **The curve identity, for ALL real `s`** — total, unlike the branch curve `eˣ+eʸ=c` would give. -/
theorem sumC_curve_id (c s : Real) (hc : 0 ≤ c) :
    exp (sumC_yc c s) - exp s - c = 0 := by
  rw [sumC_exp_yc c s hc]; mach_ring

/-! ## Part 2: `f(a,b) = eᵇ − eᵃ − c` — both `f_x = -eˣ` and `f_y = eʸ` transcendental -/

/-- `f(a,b) = eᵇ - eᵃ - c`. -/
noncomputable def sumC_f (c : Real) : Real → Real → Real := fun a b => exp b - exp a - c

theorem hasDerivAt2_sumC_f (c x y : Real) :
    HasDerivAt2 (sumC_f c) (-exp x) (exp y) x y := by
  have hExpA : HasDerivAt2 (fun a _ => exp a) (exp x * 1) (exp x * 0) x y :=
    HasDerivAt2_scomp exp (exp x) (fun a _ => a) 1 0 x y (HasDerivAt_exp x) (HasDerivAt2_projX x y)
  have hExpB : HasDerivAt2 (fun _ b => exp b) (exp y * 0) (exp y * 1) x y :=
    HasDerivAt2_scomp exp (exp y) (fun _ b => b) 0 1 x y (HasDerivAt_exp y) (HasDerivAt2_projY x y)
  have hSub1 := HasDerivAt2_sub (fun _ b => exp b) (fun a _ => exp a) _ _ _ _ x y hExpB hExpA
  have hSub2 := HasDerivAt2_sub (fun a b => exp b - exp a) (fun _ _ => c) _ _ 0 0 x y hSub1
    (HasDerivAt2_const c x y)
  have e1 : exp y * 0 - exp x * 1 - 0 = -exp x := by mach_ring
  have e2 : exp y * 1 - exp x * 0 - 0 = exp y := by mach_ring
  rw [e1, e2] at hSub2
  exact hSub2

/-! ## Part 3: `g(a,b) = eᵇ − a·eᵃ` — the second curve -/

/-- `g(a,b) = eᵇ - a·eᵃ`. -/
noncomputable def sumC_g : Real → Real → Real := fun a b => exp b - a * exp a

theorem hasDerivAt2_sumC_g (x y : Real) :
    HasDerivAt2 sumC_g (-(exp x + x * exp x)) (exp y) x y := by
  have hExpA : HasDerivAt2 (fun a _ => exp a) (exp x * 1) (exp x * 0) x y :=
    HasDerivAt2_scomp exp (exp x) (fun a _ => a) 1 0 x y (HasDerivAt_exp x) (HasDerivAt2_projX x y)
  have hAxExpA := HasDerivAt2_mul (fun a _ => a) (fun a _ => exp a) 1 0 (exp x * 1) (exp x * 0) x y
    (HasDerivAt2_projX x y) hExpA
  have hExpB : HasDerivAt2 (fun _ b => exp b) (exp y * 0) (exp y * 1) x y :=
    HasDerivAt2_scomp exp (exp y) (fun _ b => b) 0 1 x y (HasDerivAt_exp y) (HasDerivAt2_projY x y)
  have hSub := HasDerivAt2_sub (fun _ b => exp b) (fun a _ => a * exp a) _ _ _ _ x y hExpB hAxExpA
  have e1 : exp y * 0 - (1 * exp x + x * (exp x * 1)) = -(exp x + x * exp x) := by mach_ring
  have e2 : exp y * 1 - (0 * exp x + x * (exp x * 0)) = exp y := by mach_ring
  rw [e1, e2] at hSub
  exact hSub

/-! ## Part 4: the four partials, represented over `nonlinearCurveChain 0`

Reuses `TwoExpNonlinearCurveInstance`'s chain (level `0 = eˣ`, level `1 = e⁻ˣ`, level `2 =
exp(0·e⁻ˣ)`), fixing its unused internal parameter to `0`. Only level `0` is referenced below; the
other two levels come along only to satisfy `PfaffianChain (M+2)`'s minimum-length-2 requirement —
already proven `IsExpChain` + coherent + positive by `TwoExpNonlinearCurveInstance.lean`, reused
here with zero new chain-level proof work. -/

noncomputable def repChain : PfaffianChain 3 := nonlinearCurveChain 0

theorem repPfx_eval (z : Real) :
    (pfaffianChainFn repChain (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))).eval z
      = -exp z := by
  show MultiPoly.eval (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩)) z
    (repChain.chainValues z) = -exp z
  rw [MultiPoly.eval_sub, MultiPoly.eval_const, MultiPoly.eval_varY]
  show (0:Real) - (nonlinearCurveChain 0).evals ⟨0, by omega⟩ z = -exp z
  show (0:Real) - exp z = -exp z
  mach_ring

theorem repPfy_eval (c z : Real) :
    (pfaffianChainFn repChain (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))).eval z
      = exp z + c := by
  show MultiPoly.eval (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c)) z
    (repChain.chainValues z) = exp z + c
  rw [MultiPoly.eval_add, MultiPoly.eval_varY, MultiPoly.eval_const]
  show (nonlinearCurveChain 0).evals ⟨0, by omega⟩ z + c = exp z + c
  show exp z + c = exp z + c
  rfl

theorem repPgx_eval (z : Real) :
    (pfaffianChainFn repChain
      (MultiPoly.sub (MultiPoly.const 0)
        (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩)
          (MultiPoly.mul MultiPoly.varX (MultiPoly.varY ⟨0, by omega⟩))))).eval z
      = -(exp z + z * exp z) := by
  show MultiPoly.eval
    (MultiPoly.sub (MultiPoly.const 0)
      (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩)
        (MultiPoly.mul MultiPoly.varX (MultiPoly.varY ⟨0, by omega⟩)))) z
    (repChain.chainValues z) = -(exp z + z * exp z)
  rw [MultiPoly.eval_sub, MultiPoly.eval_const, MultiPoly.eval_add, MultiPoly.eval_mul,
    MultiPoly.eval_varX, MultiPoly.eval_varY]
  show (0:Real) -
    ((nonlinearCurveChain 0).evals ⟨0, by omega⟩ z + z * (nonlinearCurveChain 0).evals ⟨0, by omega⟩ z)
    = -(exp z + z * exp z)
  show (0:Real) - (exp z + z * exp z) = -(exp z + z * exp z)
  mach_ring

/-! ## Part 5: the capstone — a genuine curve-intersection finiteness bound

Applies `khovanskii_rolle_count_curve_of_represented_jacobian` directly (not a slice bound): the
number of points where `g` vanishes **along the curve `{f=0}`** — i.e. the number of simultaneous
solutions to `{f=0, g=0}` in the strip `(a,b) × ℝ` — is finite. -/

theorem sumC_intersection_finite (c a b : Real) (hc : 0 ≤ c) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn repChain
        (jacobianRepPoly
          (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
          (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))
          (MultiPoly.sub (MultiPoly.const 0)
            (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩)
              (MultiPoly.mul MultiPoly.varX (MultiPoly.varY ⟨0, by omega⟩))))
          (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c)))).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ sumC_g z (sumC_yc c z) = 0) →
      zeros_g.length ≤ N + 1 := by
  refine khovanskii_rolle_count_curve_of_represented_jacobian
    (sumC_f c) sumC_g (fun z => -exp z) (fun z => exp z + c) (fun z => -(exp z + z * exp z))
    (fun z => exp z + c) (sumC_yc c) a b hab
    (fun z _ _ => by
      show HasDerivAt2 (sumC_f c) (-exp z) (exp z + c) z (sumC_yc c z)
      rw [← sumC_exp_yc c z hc]; exact hasDerivAt2_sumC_f c z (sumC_yc c z))
    (fun z _ _ => by
      show HasDerivAt2 sumC_g (-(exp z + z * exp z)) (exp z + c) z (sumC_yc c z)
      rw [← sumC_exp_yc c z hc]; exact hasDerivAt2_sumC_g z (sumC_yc c z))
    (fun z _ _ => ne_of_gt (sumC_pos c z hc))
    (fun s => sumC_curve_id c s hc)
    1 repChain
    (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
    (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))
    (MultiPoly.sub (MultiPoly.const 0)
      (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩)
        (MultiPoly.mul MultiPoly.varX (MultiPoly.varY ⟨0, by omega⟩))))
    (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))
    (nonlinearCurveChain_isExpChain 0) (nonlinearCurveChain_isCoherentOn 0 a b)
    (fun z _ _ i => nonlinearCurveChain_pos 0 z i)
    hne
    (fun z _ _ => repPfx_eval z) (fun z _ _ => repPfy_eval c z)
    (fun z _ _ => repPgx_eval z) (fun z _ _ => repPfy_eval c z)

/-- **The Jacobian's zero set really is exactly `{0}`** for `c ≥ 0` — the general bound above is
protecting against a genuinely finite (here, singleton) set, not a vacuous one. Direct algebraic
confirmation: `x·eˣ·(eˣ+c) = 0 ↔ x = 0`, since `eˣ·(eˣ+c) > 0` always. -/
theorem sumC_jacobian_zero_iff (c x : Real) (hc : 0 ≤ c) :
    x * exp x * (exp x + c) = 0 ↔ x = 0 := by
  have hpos : 0 < exp x * (exp x + c) := mul_pos (exp_pos x) (sumC_pos c x hc)
  constructor
  · intro h
    have h2 : (exp x * (exp x + c)) * x = 0 := by rw [← h]; mach_ring
    exact mul_eq_zero_of_factor_ne_zero (ne_of_gt hpos) h2
  · intro h; rw [h]; mach_ring

end TwoExp
end MultiVarMod
end MachLib
