import MachLib.BivariateDeriv
import MachLib.TwoExpGlobalSumIntersection
import MachLib.TwoExpPfaffianRepresentationELR
import MachLib.ExpRationalKhovanskii

/-!
# A genuine log-type chain level — bare-`y` dependence, exercising `IsExpLogRecipW`'s real difference

`TwoExpPfaffianRepresentationELR.lean` built the `IsExpLogRecipW` curve-intersection capstone but validated
it only by re-deriving `TwoExpGlobalSumIntersection`'s own `IsExpChain` result through the broader route —
real plumbing validation, but it never needed a log-type level (its `g` only ever touched `exp y`, never
bare `y`). This file builds the case that does: same curve `yc(x) = log(eˣ+c)` (`sumC_yc`, reused from
`TwoExpGlobalSumIntersection.lean`), same `f = eʸ−eˣ−c`, but `g(x,y) = y²` — genuinely bare `y`, forcing
`yc(z)` ITSELF (not `exp(yc(z))`) into the Jacobian.

`yc(z) = log(eᶻ+c)` needs a **log-type** chain level, whose coherence (`w' = v'/v`) needs `1/v` — here
`1/(eᶻ+c)` — chain-representable too, so the chain also needs a genuine **reciprocal-type** level (the
piece `PfaffianExpRecipExample.lean` demonstrated in isolation for the trivial case `1/x`; this generalizes
it to `1/(eᶻ+c)`, a composition, not the identity). Three levels: `y₀=eᶻ` (exp), `y₁=1/(eᶻ+c)` (reciprocal,
witness `v=eᶻ+c`), `y₂=log(eᶻ+c)=yc(z)` (log, relation `y₀·y₁` — top-free, matching `IsExpLogRecipW`'s
"doesn't reference its own variable" shape).

The Jacobian `fx·gy − fy·gx = (−eᶻ)·(2·yc(z)) − (eᶻ+c)·0 = −2·eᶻ·yc(z)` genuinely mixes an exp-type level
(`y₀`) and the log-type level (`y₂`) — the case §10/§11 identified as still open. Closing it here confirms
the `IsExpLogRecipW` capstone does what it was built for, not just that it type-checks.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpLogRecip

/-! ## Part 1: `g(a,b) = b²` — genuinely bare `y`, not `exp y` -/

noncomputable def sumC_g2 : Real → Real → Real := fun a b => b * b

theorem hasDerivAt2_sumC_g2 (x y : Real) : HasDerivAt2 sumC_g2 0 ((1+1) * y) x y := by
  have h := HasDerivAt2_mul (fun _ b => b) (fun _ b => b) 0 1 0 1 x y
    (HasDerivAt2_projY x y) (HasDerivAt2_projY x y)
  have e1 : (0:Real) * y + y * 0 = 0 := by mach_ring
  have e2 : (1:Real) * y + y * 1 = (1+1) * y := by mach_ring
  rw [e1, e2] at h
  exact h

/-! ## Part 2: the reciprocal level `1/(eˣ+c)` -/

/-- `(1/(eˣ+c))' = -eˣ·(1/(eˣ+c))²` — the reciprocal-type relation, generalizing
`PfaffianExpRecipExample.lean`'s `1/x` case to a genuine composition. -/
theorem sumC_recip_hasDerivAt (c x : Real) (hc : 0 ≤ c) :
    HasDerivAt (fun t => 1 / (exp t + c))
      ((0 - exp x) * ((1 / (exp x + c)) * (1 / (exp x + c)))) x := by
  have hHpos : 0 < exp x + c := sumC_pos c x hc
  have hHne : (exp x + c) ≠ 0 := ne_of_gt hHpos
  have hsum0 : HasDerivAt (fun t => exp t + c) (exp x + 0) x :=
    HasDerivAt_add (fun t => exp t) (fun _ => c) (exp x) 0 x (HasDerivAt_exp x) (HasDerivAt_const c x)
  have hsum : HasDerivAt (fun t => exp t + c) (exp x) x := by
    rwa [show exp x + 0 = exp x from by mach_ring] at hsum0
  have h := HasDerivAt_inv (fun t => exp t + c) (exp x) x hHne hsum
  have hne2 : (exp x + c) * (exp x + c) ≠ 0 := ne_of_gt (mul_pos hHpos hHpos)
  have hb : (-(exp x) / ((exp x + c) * (exp x + c)) : Real)
      = (0 - exp x) * ((1 / (exp x + c)) * (1 / (exp x + c))) := by
    rw [one_div_mul_one_div hHpos, ← div_def (0 - exp x) ((exp x + c) * (exp x + c)) hne2]
    congr 1
    mach_ring
  rwa [hb] at h

/-- `(1/(eˣ+c))·(eˣ+c) = 1`. -/
theorem sumC_recip_witness (c x : Real) (hc : 0 ≤ c) :
    (1 / (exp x + c)) * (exp x + c) = 1 := by
  rw [mul_comm]; exact mul_inv (exp x + c) (ne_of_gt (sumC_pos c x hc))

/-! ## Part 3: the chain `{eˣ, 1/(eˣ+c), log(eˣ+c)}` -/

noncomputable def logChain (c : Real) : PfaffianChain 3 :=
  { evals := fun i => match i with
      | ⟨0, _⟩ => fun x => exp x
      | ⟨1, _⟩ => fun x => 1 / (exp x + c)
      | ⟨2, _⟩ => fun x => sumC_yc c x,
    relations := fun i => match i with
      | ⟨0, _⟩ => MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY ⟨0, by omega⟩)
      | ⟨1, _⟩ => MultiPoly.mul (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
          (MultiPoly.mul (MultiPoly.varY ⟨1, by omega⟩) (MultiPoly.varY ⟨1, by omega⟩))
      | ⟨2, _⟩ => MultiPoly.mul (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.varY ⟨1, by omega⟩) }

theorem logChain_isCoherentOn (c a b : Real) (hc : 0 ≤ c) : (logChain c).IsCoherentOn a b := by
  intro x _ _ i
  rcases i with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · show HasDerivAt (fun x => exp x)
      (MultiPoly.eval (MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY ⟨0, by omega⟩)) x
        ((logChain c).chainValues x)) x
    rw [MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY]
    show HasDerivAt (fun x => exp x) (1 * exp x) x
    rw [show (1:Real) * exp x = exp x from by mach_ring]
    exact HasDerivAt_exp x
  · show HasDerivAt (fun x => 1 / (exp x + c))
      (MultiPoly.eval
        (MultiPoly.mul (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
          (MultiPoly.mul (MultiPoly.varY ⟨1, by omega⟩) (MultiPoly.varY ⟨1, by omega⟩))) x
        ((logChain c).chainValues x)) x
    rw [MultiPoly.eval_mul, MultiPoly.eval_sub, MultiPoly.eval_const, MultiPoly.eval_varY,
      MultiPoly.eval_mul, MultiPoly.eval_varY]
    show HasDerivAt (fun x => 1 / (exp x + c))
      ((0 - exp x) * ((1 / (exp x + c)) * (1 / (exp x + c)))) x
    exact sumC_recip_hasDerivAt c x hc
  · show HasDerivAt (fun x => sumC_yc c x)
      (MultiPoly.eval (MultiPoly.mul (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.varY ⟨1, by omega⟩)) x
        ((logChain c).chainValues x)) x
    rw [MultiPoly.eval_mul, MultiPoly.eval_varY, MultiPoly.eval_varY]
    show HasDerivAt (fun x => sumC_yc c x) (exp x * (1 / (exp x + c))) x
    rw [show exp x * (1 / (exp x + c)) = 1 / (exp x + c) * exp x from by mach_ring]
    exact hasDerivAt_sumC_yc c x hc
  · omega

theorem logChain_isExpLogRecipW (c a b : Real) (hc : 0 ≤ c) : IsExpLogRecipW (logChain c) a b := by
  intro i
  rcases i with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · refine ⟨Or.inl ⟨MultiPoly.const 1, MultiPoly.degreeY_const _ 1, rfl⟩, ?_⟩
    intro j hij
    show MultiPoly.degreeY j (MultiPoly.const 1) + MultiPoly.degreeY j (MultiPoly.varY ⟨0, by omega⟩) = 0
    rw [MultiPoly.degreeY_const]
    show 0 + (if j = ⟨0, by omega⟩ then 1 else 0) = 0
    have hn : (0:Nat) < j.val := hij
    rw [if_neg (fin3_ne_of_val_ne (by simpa using Nat.ne_of_gt hn))]
  · refine ⟨Or.inr (Or.inr ⟨MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩),
      MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c), ?_, rfl, ?_, ?_, ?_⟩), ?_⟩
    · show Nat.max (MultiPoly.degreeY (⟨0 + 1, hv⟩ : Fin 3) (MultiPoly.const 0))
        (MultiPoly.degreeY (⟨0 + 1, hv⟩ : Fin 3) (MultiPoly.varY ⟨0, by omega⟩)) = 0
      rw [MultiPoly.degreeY_const]
      show Nat.max 0 (if (⟨0 + 1, hv⟩ : Fin 3) = ⟨0, by omega⟩ then 1 else 0) = 0
      rw [if_neg (fin3_ne_of_val_ne (by simp))]
      rfl
    · intro j hij
      have hn : (0:Nat) < j.val := hij
      show Nat.max (MultiPoly.degreeY j (MultiPoly.varY ⟨0, by omega⟩))
        (MultiPoly.degreeY j (MultiPoly.const c)) = 0
      rw [MultiPoly.degreeY_const]
      show Nat.max (if j = ⟨0, by omega⟩ then 1 else 0) 0 = 0
      rw [if_neg (fin3_ne_of_val_ne (by simpa using Nat.ne_of_gt hn))]
      rfl
    · intro x _ _
      show (logChain c).evals ⟨0 + 1, hv⟩ x
        * MultiPoly.eval (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c)) x
          ((logChain c).chainValues x) = 1
      rw [MultiPoly.eval_add, MultiPoly.eval_varY, MultiPoly.eval_const]
      show (1 / (exp x + c)) * (exp x + c) = 1
      exact sumC_recip_witness c x hc
    · intro x _ _
      show 0 < MultiPoly.eval (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c)) x
        ((logChain c).chainValues x)
      rw [MultiPoly.eval_add, MultiPoly.eval_varY, MultiPoly.eval_const]
      exact sumC_pos c x hc
    · intro j hij
      have hn : (0 + 1 : Nat) < j.val := hij
      show MultiPoly.degreeY j
        (MultiPoly.mul (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
          (MultiPoly.mul (MultiPoly.varY ⟨0 + 1, hv⟩) (MultiPoly.varY ⟨0 + 1, hv⟩))) = 0
      show MultiPoly.degreeY j (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
        + (MultiPoly.degreeY j (MultiPoly.varY ⟨0 + 1, hv⟩)
          + MultiPoly.degreeY j (MultiPoly.varY ⟨0 + 1, hv⟩)) = 0
      have hn0 : (0:Nat) < j.val := by omega
      have hj0 : ¬ (j = (⟨0, by omega⟩ : Fin 3)) := fin3_ne_of_val_ne (by simpa using Nat.ne_of_gt hn0)
      have hj1 : ¬ (j = (⟨0 + 1, hv⟩ : Fin 3)) := fin3_ne_of_val_ne (by simpa using Nat.ne_of_gt hn)
      show Nat.max (MultiPoly.degreeY j (MultiPoly.const 0)) (MultiPoly.degreeY j (MultiPoly.varY ⟨0, by omega⟩))
        + ((if j = ⟨0 + 1, hv⟩ then 1 else 0) + (if j = ⟨0 + 1, hv⟩ then 1 else 0)) = 0
      rw [if_neg hj1, MultiPoly.degreeY_const]
      show Nat.max 0 (if j = ⟨0, by omega⟩ then 1 else 0) + (0 + 0) = 0
      rw [if_neg hj0]
      rfl
  · refine ⟨Or.inr (Or.inl ?_), ?_⟩
    · show MultiPoly.degreeY (⟨0 + 1 + 1, hv⟩ : Fin 3)
        (MultiPoly.mul (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.varY ⟨0 + 1, by omega⟩)) = 0
      show MultiPoly.degreeY (⟨0 + 1 + 1, hv⟩ : Fin 3) (MultiPoly.varY ⟨0, by omega⟩)
        + MultiPoly.degreeY (⟨0 + 1 + 1, hv⟩ : Fin 3) (MultiPoly.varY ⟨0 + 1, by omega⟩) = 0
      show (if (⟨0 + 1 + 1, hv⟩ : Fin 3) = ⟨0, by omega⟩ then 1 else 0)
        + (if (⟨0 + 1 + 1, hv⟩ : Fin 3) = ⟨0 + 1, by omega⟩ then 1 else 0) = 0
      rw [if_neg (fin3_ne_of_val_ne (by simp)), if_neg (fin3_ne_of_val_ne (by simp))]
    · intro j hij
      have hn : (0 + 1 + 1 : Nat) < j.val := hij
      omega
  · omega

theorem logChain_posExceptLog (c a b : Real) (hc : 0 ≤ c) : PosExceptLog (logChain c) a b := by
  intro z _ _ i
  rcases i with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inr (exp_pos z)
  · exact Or.inr (one_div_pos_of_pos (sumC_pos c z hc))
  · left
    show MultiPoly.degreeY (⟨0 + 1 + 1, hv⟩ : Fin 3)
      (MultiPoly.mul (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.varY ⟨0 + 1, by omega⟩)) = 0
    show MultiPoly.degreeY (⟨0 + 1 + 1, hv⟩ : Fin 3) (MultiPoly.varY ⟨0, by omega⟩)
      + MultiPoly.degreeY (⟨0 + 1 + 1, hv⟩ : Fin 3) (MultiPoly.varY ⟨0 + 1, by omega⟩) = 0
    show (if (⟨0 + 1 + 1, hv⟩ : Fin 3) = ⟨0, by omega⟩ then 1 else 0)
      + (if (⟨0 + 1 + 1, hv⟩ : Fin 3) = ⟨0 + 1, by omega⟩ then 1 else 0) = 0
    rw [if_neg (fin3_ne_of_val_ne (by simp)), if_neg (fin3_ne_of_val_ne (by simp))]
  · omega

/-! ## Part 4: analyticity -/

theorem logChain_evals_analytic (c : Real) (hc : 0 ≤ c) (S : RealSet)
    (hS : ∀ x, S x → 0 < exp x + c) :
    ∀ i : Fin 3, IsAnalyticOnReals (fun x => (logChain c).evals i x) S := by
  intro i
  rcases i with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact analytic_exp S
  · have hsumAn : IsAnalyticOnReals (fun x : Real => exp x + c) S :=
      analytic_add (fun x => exp x) (fun _ => c) S (analytic_exp S) (analytic_const c S)
    exact analytic_comp (fun x => 1 / x) (fun x => exp x + c) S (Ioi 0) hsumAn hS
      analytic_one_div_pos
  · have hsumAn : IsAnalyticOnReals (fun x : Real => exp x + c) S :=
      analytic_add (fun x => exp x) (fun _ => c) S (analytic_exp S) (analytic_const c S)
    exact analytic_comp Real.log (fun x => exp x + c) S (Ioi 0) hsumAn hS analytic_log_pos
  · omega

theorem logChain_analytic (c a b : Real) (hc : 0 ≤ c) :
    ∀ r : MultiPoly 3, IsAnalyticOnReals (pfaffianChainFn (logChain c) r).eval (Icc a b) :=
  pfaffianChainFn_eval_analytic (logChain c) (Icc a b)
    (logChain_evals_analytic c hc (Icc a b) (fun x _ => sumC_pos c x hc))

/-! ## Part 5: the capstone — a genuine intersection count needing the log-type level -/

/-- **The bare-`y` case closes.** `f = eʸ−eˣ−c`, `g = y²`: the Jacobian `−2eˣ·yc(x)` genuinely mixes the
exp-type level `y₀` and the log-type level `y₂` — the case that was still open after
`TwoExpPfaffianRepresentationELR.lean`'s validation (which only ever needed `exp(yc(x))`, never `yc(x)`
itself). Closes via the same `IsExpLogRecipW` capstone, on a chain that actually needs its log arm. -/
theorem sumC_g2_intersection_finite (c a b : Real) (hc : 0 ≤ c) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn (logChain c)
        (jacobianRepPoly
          (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
          (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))
          (MultiPoly.const 0)
          (MultiPoly.mul (MultiPoly.const (1+1)) (MultiPoly.varY ⟨2, by omega⟩)))).eval z ≠ 0) :
    ∃ K : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ sumC_g2 z (sumC_yc c z) = 0) →
      zeros_g.length ≤ K + 1 := by
  refine khovanskii_rolle_count_curve_of_represented_jacobian_ELR
    (sumC_f c) sumC_g2 (fun z => -exp z) (fun z => exp z + c) (fun _ => 0)
    (fun z => (1+1) * sumC_yc c z) (sumC_yc c) a b hab
    (fun z _ _ => by
      show HasDerivAt2 (sumC_f c) (-exp z) (exp z + c) z (sumC_yc c z)
      rw [← sumC_exp_yc c z hc]; exact hasDerivAt2_sumC_f c z (sumC_yc c z))
    (fun z _ _ => by
      show HasDerivAt2 sumC_g2 0 ((1+1) * sumC_yc c z) z (sumC_yc c z)
      exact hasDerivAt2_sumC_g2 z (sumC_yc c z))
    (fun z _ _ => ne_of_gt (sumC_pos c z hc))
    (fun s => sumC_curve_id c s hc)
    3 (logChain c)
    (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
    (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))
    (MultiPoly.const 0)
    (MultiPoly.mul (MultiPoly.const (1+1)) (MultiPoly.varY ⟨2, by omega⟩))
    (logChain_isExpLogRecipW c a b hc) (logChain_isCoherentOn c a b hc)
    (logChain_posExceptLog c a b hc) (logChain_analytic c a b hc)
    hne
    (fun z _ _ => by
      show MultiPoly.eval (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩)) z
        ((logChain c).chainValues z) = -exp z
      rw [MultiPoly.eval_sub, MultiPoly.eval_const, MultiPoly.eval_varY]
      show (0:Real) - exp z = -exp z
      mach_ring)
    (fun z _ _ => by
      show MultiPoly.eval (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c)) z
        ((logChain c).chainValues z) = exp z + c
      rw [MultiPoly.eval_add, MultiPoly.eval_varY, MultiPoly.eval_const]
      show (logChain c).evals ⟨0, by omega⟩ z + c = exp z + c
      show exp z + c = exp z + c
      rfl)
    (fun z _ _ => by
      show MultiPoly.eval (MultiPoly.const 0) z ((logChain c).chainValues z) = (0:Real)
      rw [MultiPoly.eval_const])
    (fun z _ _ => by
      show MultiPoly.eval (MultiPoly.mul (MultiPoly.const (1+1)) (MultiPoly.varY ⟨2, by omega⟩)) z
        ((logChain c).chainValues z) = (1+1) * sumC_yc c z
      rw [MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY]
      show (1+1) * (logChain c).evals ⟨2, by omega⟩ z = (1+1) * sumC_yc c z
      show (1+1) * sumC_yc c z = (1+1) * sumC_yc c z
      rfl)

end TwoExp
end MultiVarMod
end MachLib
