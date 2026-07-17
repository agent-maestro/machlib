import MachLib.BivariateDeriv
import MachLib.TwoExpNonlinearCurveInstance
import MachLib.TwoExpGlobalSumIntersection
import MachLib.TwoExpPfaffianRepresentation
import MachLib.TwoExpCurveCount
import MachLib.PfaffianExpLogRecipClass
import MachLib.PfaffianExpHard
import MachLib.PfaffianAnalytic

/-!
# The curve-intersection capstone over `IsExpLogRecipW` chains (Gate 2d, §10 follow-up)

`scoping.md §10` claimed no `jacobian`/`bound_gen`-style theorem exists for `IsExpLogRecipW` chains —
**that claim was wrong**, caught while double-checking it before writing further instances. The exact tool
already exists, just under a different name: `MachLib.PfaffianExpLogRecip.combined_descent_3_of_exp_hard`,
composed with `MachLib.PfaffianExpHard.exp_hard_proof`, gives — for ANY `N`, ANY `c : PfaffianChain N`
satisfying `IsExpLogRecipW c a b` + coherence + `PosExceptLog` + analyticity, and ANY `p : MultiPoly N`
non-vanishing somewhere — `BoundedZeros (pfaffianChainFn c p) a b`. That is the *exact* `IsExpLogRecipW`
analogue of `pfaffian_khovanskii_bound_gen_uncond` (the `IsExpChain`-only tool `TwoExpGlobalSumIntersection`
used), fully unconditional, zero new axioms (it rests on `exp_hard_proof`, itself `rolle`-grounded per its
own docstring — matches [[project_exp_hard_eml_unconditional]]).

This file threads that tool through the SAME wrapper pattern `TwoExpPfaffianRepresentation.lean` used for
`IsExpChain` (`jacobianRepPoly` representability → Jacobian zero bound → `khovanskii_rolle_count_curve`),
giving a genuine `IsExpLogRecipW` curve-intersection capstone. `jacobianRepPoly`/`jacobianRepPoly_eval_eq`
are chain-agnostic (pure `MultiPoly`/`PfaffianChain` algebra, no `IsExpChain` reference) and reused as-is;
`khovanskii_rolle_count_curve` (the outer Rolle-counting step) was already fully generic over an abstract
Jacobian-zero bound `N` — neither needed touching. Only the middle layer (representability → bound) needed
rebuilding against the broader hypothesis class.

Validated in Part 2 by re-deriving `TwoExpGlobalSumIntersection`'s own result through this strictly more
general route (`IsExpChain ⊆ IsExpLogRecipW` via `IsExpChain_imp_ELR`), confirming the new capstone actually
produces a working end-to-end result, not just a type-checking generalization.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpLogRecip

/-! ## Part 1: the generalized capstone -/

/-- **Curve-intersection finiteness over `IsExpLogRecipW` chains** — the `IsExpChain`-only
`khovanskii_rolle_count_curve_of_represented_jacobian` (`TwoExpPfaffianRepresentation.lean`), generalized to
the strictly broader class that also admits log-type and reciprocal-type levels. Same conclusion shape
(bounds how many times `g` vanishes along `{f=0}`); the representability burden (`hexp`, `hpos`, `hAn`) is
correspondingly broader — `PosExceptLog` instead of blanket positivity, plus an explicit analyticity
hypothesis (`IsExpChain`'s route never needed one; `IsExpLogRecipW`'s reciprocal/log arms do). -/
theorem khovanskii_rolle_count_curve_of_represented_jacobian_ELR
    (f g : Real → Real → Real) (fx fy gx gy yc : Real → Real)
    (a b : Real) (hab : a < b)
    (hf2 : ∀ z : Real, a < z → z < b → HasDerivAt2 f (fx z) (fy z) z (yc z))
    (hg2 : ∀ z : Real, a < z → z < b → HasDerivAt2 g (gx z) (gy z) z (yc z))
    (hfy : ∀ z : Real, a < z → z < b → fy z ≠ 0)
    (hid : ∀ s : Real, f s (yc s) = 0)
    (N : Nat) (c : PfaffianChain N)
    (pfx pfy pgx pgy : MultiPoly N)
    (hexp : IsExpLogRecipW c a b)
    (hcoh : c.IsCoherentOn a b)
    (hpos : PosExceptLog c a b)
    (hAn : ∀ r : MultiPoly N, IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b))
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c (jacobianRepPoly pfx pfy pgx pgy)).eval z ≠ 0)
    (hfx : ∀ z, a < z → z < b → (pfaffianChainFn c pfx).eval z = fx z)
    (hfy_rep : ∀ z, a < z → z < b → (pfaffianChainFn c pfy).eval z = fy z)
    (hgx : ∀ z, a < z → z < b → (pfaffianChainFn c pgx).eval z = gx z)
    (hgy : ∀ z, a < z → z < b → (pfaffianChainFn c pgy).eval z = gy z) :
    ∃ K : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ g z (yc z) = 0) →
      zeros_g.length ≤ K + 1 := by
  obtain ⟨K, hK⟩ := combined_descent_3_of_exp_hard a b hab (PfaffianExpHard.exp_hard_proof a b hab)
    N c hexp hcoh hpos hAn (jacobianRepPoly pfx pfy pgx pgy) hne
  refine ⟨K, khovanskii_rolle_count_curve f g fx fy gx gy yc a b hab hf2 hg2 hfy hid K ?_⟩
  intro zeros hnd hz
  exact hK zeros hnd (fun z hzmem => by
    obtain ⟨hza, hzb, hJz⟩ := hz z hzmem
    refine ⟨hza, hzb, ?_⟩
    rw [jacobianRepPoly_eval_eq c pfx pfy pgx pgy fx fy gx gy a b z hza hzb hfx hfy_rep hgx hgy]
    exact hJz)

/-! ## Part 2: validation — re-derive `TwoExpGlobalSumIntersection`'s own result through this strictly
more general route, confirming it actually produces a working end-to-end result. -/

theorem repChain_isExpLogRecipW (a b : Real) : IsExpLogRecipW repChain a b :=
  IsExpChain_imp_ELR repChain a b (nonlinearCurveChain_isExpChain 0)

theorem repChain_posExceptLog (a b : Real) : PosExceptLog repChain a b :=
  fun z _ _ i => Or.inr (nonlinearCurveChain_pos 0 z i)

/-- `-x` is analytic: bridges `analytic_sub`'s `0 - x` shape to literal negation via a value-level
`mach_ring` identity lifted to function equality (`negR`/`subR` are independent axioms here, not
definitionally related, so this bridge is not free). -/
theorem analytic_neg_id (S : RealSet) : IsAnalyticOnReals (fun x : Real => -x) S := by
  have heq : (fun x : Real => (0:Real) - x) = (fun x : Real => -x) := by
    funext x; mach_ring
  rw [← heq]
  exact analytic_sub (fun _ => (0:Real)) (fun x => x) S (analytic_const 0 S) (analytic_id S)

/-- Each level of `repChain` (`= nonlinearCurveChain 0`) is analytic: all three are `exp` composed with an
analytic function of `x`, and `exp` itself is analytic (`analytic_exp`, an already-disclosed axiom — no new
trust). -/
theorem repChain_evals_analytic (S : RealSet) :
    ∀ i : Fin 3, IsAnalyticOnReals (fun x => repChain.evals i x) S := by
  intro i
  rcases i with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact analytic_exp S
  · exact analytic_comp Real.exp (fun x => -x) S (fun _ => True) (analytic_neg_id S)
      (fun _ _ => trivial) (analytic_exp (fun _ => True))
  · have hexpneg : IsAnalyticOnReals (fun x : Real => exp (-x)) S :=
      analytic_comp Real.exp (fun x => -x) S (fun _ => True) (analytic_neg_id S)
        (fun _ _ => trivial) (analytic_exp (fun _ => True))
    have hmul : IsAnalyticOnReals (fun x : Real => (0:Real) * exp (-x)) S :=
      analytic_mul (fun _ => (0:Real)) (fun x => exp (-x)) S (analytic_const 0 S) hexpneg
    exact analytic_comp Real.exp (fun x => 0 * exp (-x)) S (fun _ => True) hmul
      (fun _ _ => trivial) (analytic_exp (fun _ => True))
  · omega

theorem repChain_analytic (a b : Real) :
    ∀ r : MultiPoly 3, IsAnalyticOnReals (pfaffianChainFn repChain r).eval (Icc a b) :=
  pfaffianChainFn_eval_analytic repChain (Icc a b) (repChain_evals_analytic (Icc a b))

/-- **Validation**: `sumC_intersection_finite`'s own conclusion, re-derived through the strictly more
general `IsExpLogRecipW` route instead of `TwoExpGlobalSumIntersection`'s `IsExpChain`-only one. Same `f`,
`g`, chain, and representing polynomials — only the capstone theorem invoked differs. -/
theorem sumC_intersection_finite_ELR (c a b : Real) (hc : 0 ≤ c) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn repChain
        (jacobianRepPoly
          (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
          (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))
          (MultiPoly.sub (MultiPoly.const 0)
            (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩)
              (MultiPoly.mul MultiPoly.varX (MultiPoly.varY ⟨0, by omega⟩))))
          (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c)))).eval z ≠ 0) :
    ∃ K : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ sumC_g z (sumC_yc c z) = 0) →
      zeros_g.length ≤ K + 1 := by
  refine khovanskii_rolle_count_curve_of_represented_jacobian_ELR
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
    3 repChain
    (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.varY ⟨0, by omega⟩))
    (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))
    (MultiPoly.sub (MultiPoly.const 0)
      (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩)
        (MultiPoly.mul MultiPoly.varX (MultiPoly.varY ⟨0, by omega⟩))))
    (MultiPoly.add (MultiPoly.varY ⟨0, by omega⟩) (MultiPoly.const c))
    (repChain_isExpLogRecipW a b) (nonlinearCurveChain_isCoherentOn 0 a b)
    (repChain_posExceptLog a b) (repChain_analytic a b)
    hne
    (fun z _ _ => repPfx_eval z) (fun z _ _ => repPfy_eval c z)
    (fun z _ _ => repPgx_eval z) (fun z _ _ => repPfy_eval c z)

end TwoExp
end MultiVarMod
end MachLib
