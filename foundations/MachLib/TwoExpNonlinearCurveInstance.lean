import MachLib.BivariateDeriv
import MachLib.EMLTChartKhovanskii
import MachLib.PfaffianGeneralReduce
import MachLib.PfaffianGeneralBoundUncond

/-!
# A genuinely non-degenerate curve instance (Gate 2d, chain-2 honest test)

`monogate-research/roadmap/multivariate-khovanskii-chainN-scoping.md §7` found that every curve
constructed anywhere in the ~10,700-line chain-2 apparatus is LINEAR (`f = x+y-c`, `f_y = 1` constant) —
including the file that specifically claims to validate the IFT gate "end-to-end ... via the general-curve
pipeline". This file builds the first genuinely non-degenerate instance: `f(x,y) = eˣ·y − c`, where
`f_y = eˣ` is a real, non-constant function of `x` — the case the apparatus was ostensibly built to
handle, but had never been exercised.

**Why this specific `f`:** solving `f=0` for `y` gives `yc(x) = c·e^{−x}`, a genuine (non-linear) closed
form. Computed by hand first (verified against SymPy) before writing any Lean: `yc' = -f_x/f_y` simplifies
to exactly `-yc` — the division cancels cleanly (`f_x = eˣ·y`, `f_y = eˣ`, and `f_x/f_y = y`, evaluated on
the curve). This is NOT automatic for a general `f` (the scoping doc's §6.3 obstruction is real for the
general case); it happens here because `f_y` divides `f_x` exactly. The point of this file is to (1)
confirm `hasDerivAt_implicit`, applied to this genuinely non-linear `f`, actually produces that same value
(validating the general machinery rather than just asserting the closed form), and (2) show the resulting
curve — and its exponential, which is what actually enters a second equation `g` built from `eʸ` — admits
a clean `IsExpChain` representation, directly testing the representability question §6.3/§7 raised.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce

/-! ## Part 1: the curve `yc(x) = c·exp(-x)` and its derivative, both directly and via the IFT bridge -/

/-- `d/dx exp(-x) = -exp(-x)`. -/
theorem hasDerivAt_exp_neg (x : Real) : HasDerivAt (fun t => exp (-t)) (-exp (-x)) x := by
  have hneg : HasDerivAt (fun t : Real => -t) (-1) x := by
    have := HasDerivAt_neg (fun t => t) 1 x (HasDerivAt_id x)
    simpa using this
  have h := hasDerivAt_exp_comp (fun t => -t) (-1) x hneg
  rwa [show exp (-x) * (-1) = -exp (-x) from by mach_ring] at h

/-- The curve `yc(x) = c·exp(-x)`, directly differentiated (full product-rule form). -/
theorem hasDerivAt_yc_raw (c x : Real) :
    HasDerivAt (fun t => c * exp (-t)) (0 * exp (-x) + c * (-exp (-x))) x :=
  HasDerivAt_mul (fun _ => c) (fun t => exp (-t)) 0 (-exp (-x)) x
    (HasDerivAt_const c x) (hasDerivAt_exp_neg x)

/-- **`yc` satisfies `yc' = -yc`** — the exp-type relation, stated directly. -/
theorem hasDerivAt_yc_selfExp (c x : Real) :
    HasDerivAt (fun t => c * exp (-t)) (-(c * exp (-x))) x := by
  have h := hasDerivAt_yc_raw c x
  rwa [show (0:Real) * exp (-x) + c * (-exp (-x)) = -(c * exp (-x)) from by mach_ring] at h

/-! ## Part 2: `f(x,y) = eˣ·y − c` as a genuinely non-linear bivariate function -/

/-- **`f = eˣ·y − c` has joint derivative `(eˣ·y, eˣ)`** — `f_y = eˣ` is NOT a constant, unlike every
prior worked example in this codebase (`f = x+y-c` always gave `f_y = 1`). -/
theorem hasDerivAt2_expMul (c x y : Real) :
    HasDerivAt2 (fun a b => exp a * b - c) (exp x * y) (exp x) x y := by
  have hExpX : HasDerivAt2 (fun a _ => exp a) (exp x * 1) (exp x * 0) x y :=
    HasDerivAt2_scomp exp (exp x) (fun a _ => a) 1 0 x y (HasDerivAt_exp x) (HasDerivAt2_projX x y)
  -- exp(a)*b directly via the mul rule with F=exp(a) (hExpX) and G=b (projY).
  have hMul := HasDerivAt2_mul (fun a _ => exp a) (fun _ b => b)
    (exp x * 1) (exp x * 0) 0 1 x y hExpX (HasDerivAt2_projY x y)
  have hSub := HasDerivAt2_sub (fun a b => exp a * b) (fun _ _ => c) _ _ 0 0 x y hMul
    (HasDerivAt2_const c x y)
  have e1 : exp x * 1 * y + exp x * 0 - 0 = exp x * y := by mach_ring
  have e2 : exp x * 0 * y + exp x * 1 - 0 = exp x := by mach_ring
  rw [e1, e2] at hSub
  exact hSub

/-- **The implicit identity**: `f(s, yc(s)) = 0` for all `s`, i.e. `exp(s)·(c·exp(-s)) − c = 0`. -/
theorem expMul_curve_id (c s : Real) : exp s * (c * exp (-s)) - c = 0 := by
  have h : exp s * exp (-s) = 1 := by
    rw [(exp_add s (-s)).symm]
    rw [show s + -s = 0 from by mach_ring]
    exact exp_zero
  rw [show exp s * (c * exp (-s)) = c * (exp s * exp (-s)) from by mach_ring, h]
  mach_ring

/-- **The IFT bridge, applied to the genuinely non-linear `f`, reproduces the hand-computed `yc'`.**
`hasDerivAt_implicit` derives `yc' = -f_x/f_y`; here that's `-(eˣ·y)/eˣ` evaluated at `y=yc(x)`, which
cancels to `-yc(x)` — confirmed by uniqueness of derivatives (`HasDerivAt_unique`) against the DIRECT
computation `hasDerivAt_yc_selfExp`, not asserted by hand. This is the validation §7 found missing
everywhere else in the codebase: a non-constant `f_y` genuinely exercised end-to-end. -/
theorem expMul_curve_ift_matches_direct (c x : Real) :
    -(exp x * (c * exp (-x))) / exp x = -(c * exp (-x)) := by
  have hfy : exp x ≠ 0 := ne_of_gt (exp_pos x)
  have h2 := hasDerivAt2_expMul c x (c * exp (-x))
  have himplicit := hasDerivAt_implicit (fun a b => exp a * b - c) (exp x * (c * exp (-x))) (exp x)
    (fun t => c * exp (-t)) x h2 hfy (fun s => expMul_curve_id c s)
  have hdirect := hasDerivAt_yc_selfExp c x
  exact HasDerivAt_unique _ _ _ x himplicit hdirect

/-! ## Part 3: the curve's exponential IS `IsExpChain`-representable

The `§6.3`/`§7` obstruction: `IsExpChain` needs each level's coefficient to be POLYNOMIAL in prior
chain elements, but `yc' = -f_x/f_y` is a ratio in general. Here the ratio genuinely cancels (Part 1/2),
landing exactly on `yc' = -yc` — already of the required `G·y` form with `G = -1` (a constant, trivially
polynomial). This section builds the concrete 3-level chain `{eˣ, e⁻ˣ, exp(c·e⁻ˣ)}` and proves it satisfies
`IsExpChain` + coherence + positivity — i.e., for THIS genuinely non-linear system, the representation
question has a constructive YES answer, not just an abstract possibility. -/

/-- The concrete chain: level 0 = `eˣ`, level 1 = `e⁻ˣ`, level 2 = `exp(c·e⁻ˣ)` (`= exp(yc(x))` for
`yc(x) = c·e⁻ˣ` from Part 1). Relations: `y₀' = y₀`, `y₁' = -y₁`, `y₂' = -c·y₁·y₂` (since
`(exp(c·w))' = c·w'·exp(c·w) = c·(-w)·exp(c·w) = -c·w·exp(c·w)`, `w=y₁` — the sign flips through `w'=-w`). -/
noncomputable def nonlinearCurveChain (c : Real) : PfaffianChain 3 :=
  { evals := fun i => match i with
      | ⟨0, _⟩ => fun x => exp x
      | ⟨1, _⟩ => fun x => exp (-x)
      | ⟨2, _⟩ => fun x => exp (c * exp (-x)),
    relations := fun i => match i with
      | ⟨0, _⟩ => MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY ⟨0, by omega⟩)
      | ⟨1, _⟩ => MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY ⟨1, by omega⟩)
      | ⟨2, _⟩ => MultiPoly.mul (MultiPoly.mul (MultiPoly.const (-c)) (MultiPoly.varY ⟨1, by omega⟩))
          (MultiPoly.varY ⟨2, by omega⟩) }

/-- **Coherence**: each level's actual derivative matches its relation, evaluated along the chain. -/
theorem nonlinearCurveChain_isCoherentOn (c a b : Real) :
    (nonlinearCurveChain c).IsCoherentOn a b := by
  intro x _ _ i
  rcases i with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · show HasDerivAt (fun x => exp x)
      (MultiPoly.eval (MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY ⟨0, by omega⟩)) x
        ((nonlinearCurveChain c).chainValues x)) x
    rw [MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY]
    show HasDerivAt (fun x => exp x) (1 * exp x) x
    rw [show (1:Real) * exp x = exp x from by mach_ring]
    exact hasDerivAt_exp_t x
  · show HasDerivAt (fun x => exp (-x))
      (MultiPoly.eval (MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY ⟨1, by omega⟩)) x
        ((nonlinearCurveChain c).chainValues x)) x
    rw [MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY]
    show HasDerivAt (fun x => exp (-x)) ((-1) * exp (-x)) x
    rw [show (-1:Real) * exp (-x) = -exp (-x) from by mach_ring]
    exact hasDerivAt_exp_neg x
  · show HasDerivAt (fun x => exp (c * exp (-x)))
      (MultiPoly.eval
        (MultiPoly.mul (MultiPoly.mul (MultiPoly.const (-c)) (MultiPoly.varY ⟨1, by omega⟩))
          (MultiPoly.varY ⟨2, by omega⟩)) x ((nonlinearCurveChain c).chainValues x)) x
    rw [MultiPoly.eval_mul, MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY,
      MultiPoly.eval_varY]
    show HasDerivAt (fun x => exp (c * exp (-x))) (-c * exp (-x) * exp (c * exp (-x))) x
    have h := hasDerivAt_exp_comp (fun t => c * exp (-t)) (c * (-exp (-x))) x
      (by
        have := hasDerivAt_yc_raw c x
        rwa [show (0:Real) * exp (-x) + c * (-exp (-x)) = c * (-exp (-x)) from by mach_ring] at this)
    rwa [show exp (c * exp (-x)) * (c * (-exp (-x))) = -c * exp (-x) * exp (c * exp (-x))
      from by mach_ring] at h
  · omega

/-- Bulletproof helper: `Fin 3` inequality from a raw `Nat` inequality on `.val`, avoiding `omega`'s
occasional trouble seeing through `0+1`/`0+1+1`-shaped literals inside a `Fin.mk` coercion. -/
theorem fin3_ne_of_val_ne {p q : Fin 3} (h : p.val ≠ q.val) : p ≠ q := fun he => h (by rw [he])

/-- **`IsExpChain`**: each level's relation is `Gᵢ · yᵢ` with `Gᵢ` polynomial in EARLIER chain elements
only (not `yᵢ` itself, not later levels) — the precise "exponential-type" signature, and exactly what
`§6.3` asked whether an implicit curve's exponential could satisfy. Here it does, concretely. -/
theorem nonlinearCurveChain_isExpChain (c : Real) : IsExpChain (nonlinearCurveChain c) := by
  intro i
  rcases i with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · refine ⟨⟨MultiPoly.const 1, MultiPoly.degreeY_const _ 1, rfl⟩, ?_⟩
    intro j hij
    show MultiPoly.degreeY j (MultiPoly.const 1) + MultiPoly.degreeY j (MultiPoly.varY ⟨0, by omega⟩) = 0
    rw [MultiPoly.degreeY_const]
    show 0 + (if j = ⟨0, by omega⟩ then 1 else 0) = 0
    have hn : (0:Nat) < j.val := hij
    rw [if_neg (fin3_ne_of_val_ne (by simpa using Nat.ne_of_gt hn))]
  · refine ⟨⟨MultiPoly.const (-1), MultiPoly.degreeY_const _ (-1), rfl⟩, ?_⟩
    intro j hij
    show MultiPoly.degreeY j (MultiPoly.const (-1)) + MultiPoly.degreeY j (MultiPoly.varY ⟨1, by omega⟩)
      = 0
    rw [MultiPoly.degreeY_const]
    show 0 + (if j = ⟨1, by omega⟩ then 1 else 0) = 0
    have hn : (1:Nat) < j.val := hij
    rw [if_neg (fin3_ne_of_val_ne (by simpa using Nat.ne_of_gt hn))]
  · refine ⟨⟨MultiPoly.mul (MultiPoly.const (-c)) (MultiPoly.varY ⟨1, by omega⟩), ?_, rfl⟩, ?_⟩
    · show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.const (-c))
        + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.varY ⟨1, by omega⟩) = 0
      rw [MultiPoly.degreeY_const]
      show 0 + (if (⟨2, by omega⟩ : Fin 3) = ⟨1, by omega⟩ then 1 else 0) = 0
      rw [if_neg (by decide)]
    · intro j hij
      have hn : (2:Nat) < j.val := hij
      omega
  · omega

/-- **Positivity**: every chain level evaluates positive on all of `ℝ` (each is `exp` of something). -/
theorem nonlinearCurveChain_pos (c : Real) :
    ∀ z, ∀ i : Fin 3, 0 < (nonlinearCurveChain c).evals i z := by
  intro z i
  rcases i with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact exp_pos z
  · exact exp_pos (-z)
  · exact exp_pos (c * exp (-z))
  · omega

/-! ## Part 4: closing the loop — the general bound applies, concretely

`§6.2` found `pfaffian_khovanskii_bound_gen_uncond`: unconditional finiteness for ANY `IsExpChain`-satisfying
chain. Parts 1–3 built exactly such a chain from a genuinely non-degenerate curve. This applies it: `exp
(c·e⁻ˣ) = k` (a level-2 slice of the curve's own exponential) has finitely many solutions on any bounded
interval where it isn't vacuous — not because a bespoke argument for this specific equation exists, but as
a direct instantiation of the fully general theorem. -/

/-- **Concrete finiteness, via the general bound, on the non-degenerate chain.** `exp(c·e⁻ˣ) = k` has
finitely many solutions in `(a,b)`, whenever it doesn't vanish identically there. `M=1` (chain length
`1+2=3`), `p = varY 2 - const k`. -/
theorem nonlinearCurveChain_slice_finite (c k a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (nonlinearCurveChain c)
      (MultiPoly.sub (MultiPoly.varY ⟨2, by omega⟩) (MultiPoly.const k))).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ exp (c * exp (-z)) - k = 0) → zeros.length ≤ N := by
  have h := pfaffian_khovanskii_bound_gen_uncond a b hab 1 (nonlinearCurveChain c)
    (nonlinearCurveChain_isExpChain c) (nonlinearCurveChain_isCoherentOn c a b)
    (fun z hza hzb i => nonlinearCurveChain_pos c z i)
    (MultiPoly.sub (MultiPoly.varY ⟨2, by omega⟩) (MultiPoly.const k)) hne
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
  obtain ⟨hza, hzb, heq⟩ := hz z hzmem
  refine ⟨hza, hzb, ?_⟩
  show MultiPoly.eval (MultiPoly.sub (MultiPoly.varY ⟨2, by omega⟩) (MultiPoly.const k)) z
    ((nonlinearCurveChain c).chainValues z) = 0
  rw [MultiPoly.eval_sub, MultiPoly.eval_varY, MultiPoly.eval_const]
  show (nonlinearCurveChain c).evals ⟨2, by omega⟩ z - k = 0
  show exp (c * exp (-z)) - k = 0
  exact heq

end TwoExp
end MultiVarMod
end MachLib
