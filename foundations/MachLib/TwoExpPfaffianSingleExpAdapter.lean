import MachLib.TwoExpPfaffianReductionWitness
import MachLib.ChainExp2PathC

/-!
# Single-exp SDR adapter for the two-exp Pfaffian bridge

`ChainExp2PathC` contains the completed SingleExp dispatch reducer and a
generic wrapper that delegates non-SingleExp shapes to a caller-supplied
fallback SDR. This file packages that existing reducer as the reducer-only
half of the two-exp Pfaffian SDR frontier.

It does not claim the full exp-chain reducer. It records the already-built
SingleExp island as a reusable `PfaffianExpSDRReducer` component.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce

/-- Package the existing SingleExp dispatch SDR as a two-exp bridge
`PfaffianExpSDRReducer`, with a caller-supplied fallback for all non-SingleExp
shapes. -/
noncomputable def singleExpPfaffianExpSDRReducer_of_fallback
    (fallback : PfaffianFn.StepwiseDecreaseReducer) :
    PfaffianExpSDRReducer :=
  PfaffianExpSDRReducer.of_sdr
    (MachLib.ChainExp2PathC.singleExp_to_generic_sdr
      MachLib.ChainExp2PathC.singleExp_sdr fallback)

/-- Assemble the SingleExp reducer adapter with a supplied terminal-nonzero
component into the full SDR-level solver consumed by the two-exp bridge. -/
noncomputable def singleExpPfaffianExpSDRReductionSolver_of_fallback
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero) :
    PfaffianExpSDRReductionSolver :=
  PfaffianExpSDRReductionSolver.of_parts
    (singleExpPfaffianExpSDRReducer_of_fallback fallback)
    nonzero

/-- The exp-function solver induced by the SingleExp reducer adapter and a
terminal-nonzero component. -/
noncomputable def singleExpPfaffianExpFunctionReductionSolver_of_fallback
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero) :
    PfaffianExpFunctionReductionSolver :=
  pfaffianExpFunctionReductionSolver_of_sdr
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)

/-- The packaged reducer uses exactly the generic SingleExp wrapper from
`ChainExp2PathC`. -/
theorem singleExpPfaffianExpSDRReducer_of_fallback_sdr
    (fallback : PfaffianFn.StepwiseDecreaseReducer) :
    (singleExpPfaffianExpSDRReducer_of_fallback fallback).sdr =
      MachLib.ChainExp2PathC.singleExp_to_generic_sdr
        MachLib.ChainExp2PathC.singleExp_sdr fallback :=
  rfl

/-- The assembled SDR solver uses exactly the SingleExp reducer wrapper on
its reducer side. -/
theorem singleExpPfaffianExpSDRReductionSolver_of_fallback_sdr
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero) :
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).sdr =
      MachLib.ChainExp2PathC.singleExp_to_generic_sdr
        MachLib.ChainExp2PathC.singleExp_sdr fallback :=
  rfl

/-- The assembled SDR solver preserves the supplied terminal-nonzero
component judgmentally. -/
theorem singleExpPfaffianExpSDRReductionSolver_of_fallback_terminal_nonzero
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero) :
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).terminal_nonzero =
      nonzero.terminal_nonzero :=
  rfl

/-- Direct one-variable count using the SingleExp reducer adapter plus a
supplied terminal-nonzero component. -/
theorem pfaffian_function_count_of_singleExp_adapter_bound
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (f : PfaffianFn)
    (hexp : IsExpChain f.chain)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) :
    zeros.length ≤
      (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound f :=
  pfaffian_function_count_of_expSDRReductionSolver_bound
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    f hexp a b hab hcoherent zeros hnd hz

/-- Existential one-variable count using the SingleExp reducer adapter plus a
supplied terminal-nonzero component. -/
theorem pfaffian_function_count_of_singleExp_adapter
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (f : PfaffianFn)
    (hexp : IsExpChain f.chain)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ N :=
  pfaffian_function_count_of_expSDRReductionSolver
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    f hexp a b hab hcoherent

/-- The lower-system solver induced by the SingleExp reducer adapter plus a
supplied terminal-nonzero component. -/
noncomputable def twoExpLowerReductionSolver_of_singleExp_adapter
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero) :
    TwoExpLowerReductionSolver :=
  twoExpLowerReductionSolver_of_expSDRReductionSolver
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)

/-- The SingleExp adapter lower solver exposes the selected Jacobian bound
directly. -/
theorem twoExpLowerReductionSolver_of_singleExp_adapter_jacobianBound
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    ((twoExpLowerReductionSolver_of_singleExp_adapter fallback nonzero).reduce F G A B M c
      yExpr expXExpr expYExpr sep lower).jacobianBound =
      (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
        (pfaffianChainFn lower.jacobian.chain lower.jacobian.poly) := by
  simp [twoExpLowerReductionSolver_of_singleExp_adapter,
    twoExpLowerReductionSolver_of_expSDRReductionSolver,
    twoExpLowerReductionSolver_of_expFunctionSolver,
    twoExpLowerReductionSolver_of_predicateSolver,
    TwoExpLowerReductionWitness.ofPredicateSolver,
    TwoExpLowerReductionWitness.jacobianBound,
    PfaffianPredicateReductionWitness.bound,
    PfaffianPredicateReductionWitness.ofFunctionWitness,
    PfaffianFunctionReductionWitness.bound,
    PfaffianExpSDRReductionSolver.bound,
    pfaffianPredicateReductionSolver_of_expFunctionSolver,
    pfaffianExpFunctionReductionSolver_of_sdr]

/-- The SingleExp adapter lower solver exposes the selected separator bound
directly. -/
theorem twoExpLowerReductionSolver_of_singleExp_adapter_separatorBound
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    ((twoExpLowerReductionSolver_of_singleExp_adapter fallback nonzero).reduce F G A B M c
      yExpr expXExpr expYExpr sep lower).separatorBound =
      (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
        (pfaffianChainFn lower.separator.chain lower.separator.poly) := by
  simp [twoExpLowerReductionSolver_of_singleExp_adapter,
    twoExpLowerReductionSolver_of_expSDRReductionSolver,
    twoExpLowerReductionSolver_of_expFunctionSolver,
    twoExpLowerReductionSolver_of_predicateSolver,
    TwoExpLowerReductionWitness.ofPredicateSolver,
    TwoExpLowerReductionWitness.separatorBound,
    PfaffianPredicateReductionWitness.bound,
    PfaffianPredicateReductionWitness.ofFunctionWitness,
    PfaffianFunctionReductionWitness.bound,
    PfaffianExpSDRReductionSolver.bound,
    pfaffianPredicateReductionSolver_of_expFunctionSolver,
    pfaffianExpFunctionReductionSolver_of_sdr]

/-- Jacobian-side lower count using the SingleExp reducer adapter plus a
supplied terminal-nonzero component. -/
theorem jacobian_count_of_lower_singleExp_adapter_bound
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧
      restrictedJacobianPred F G M c yExpr expXExpr expYExpr z) :
    zeros.length ≤
      (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
        (pfaffianChainFn lower.jacobian.chain lower.jacobian.poly) :=
  jacobian_count_of_lower_expSDRReductionSolver_bound
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower zeros hnd hz

/-- Separator-side lower count using the SingleExp reducer adapter plus a
supplied terminal-nonzero component. -/
theorem separator_count_of_lower_singleExp_adapter_bound
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ sep z) :
    zeros.length ≤
      (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
        (pfaffianChainFn lower.separator.chain lower.separator.poly) :=
  separator_count_of_lower_expSDRReductionSolver_bound
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower zeros hnd hz

/-- A two-exp lower system can be certified using the SingleExp reducer
adapter plus a supplied terminal-nonzero component. -/
theorem descentCertificate_of_lower_singleExp_adapter
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_expSDRReductionSolver
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower

/-- A solved two-exp descent can be certified using the SingleExp reducer
adapter plus a supplied terminal-nonzero component. -/
theorem descentCertificate_of_solved_singleExp_adapter
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_solved_expSDRReductionSolver
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    F G A B M c yExpr expXExpr expYExpr sep solved

/-- Local curve consumer for a solved descent using the SingleExp reducer
adapter plus a supplied terminal-nonzero component. -/
theorem khovanskii_rolle_curve_of_solved_singleExp_adapter_bound
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (yc : Real → Real)
    (a b : Real) (hab : a < b)
    (hsub : ∀ z, a < z → z < b → A < z ∧ z < B)
    (hf2 : ∀ z, a < z → z < b →
      HasDerivAt2 (TwoExpBivarExpr.denote F)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z)
        z (yc z))
    (hg2 : ∀ z, a < z → z < b →
      HasDerivAt2 (TwoExpBivarExpr.denote G)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z)
        z (yc z))
    (hfy_nz : ∀ z, a < z → z < b →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z ≠ 0)
    (hid : ∀ t, TwoExpBivarExpr.denote F t (yc t) = 0)
    (zeros_g : List Real) (hzeros_nd : zeros_g.Nodup)
    (hzeros : ∀ z ∈ zeros_g,
      a < z ∧ z < b ∧ TwoExpBivarExpr.denote G z (yc z) = 0) :
    zeros_g.length ≤
      (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
        (pfaffianChainFn solved.result.lower.jacobian.chain
          solved.result.lower.jacobian.poly) + 1 :=
  khovanskii_rolle_curve_of_solved_expSDRReductionSolver_bound
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    F G A B M c yExpr expXExpr expYExpr sep solved yc a b hab hsub
    hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros

/-- Full global consumer for a solved descent using the SingleExp reducer
adapter plus a supplied terminal-nonzero component. -/
theorem khovanskii_rolle_full_of_solved_singleExp_adapter_bound
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (hd : RepresentedCurveArc) (s : List RepresentedCurveArc)
    (hchain : ChainSep (fun x => A < x ∧ x < B ∧ sep x) hd.rep (s.map (fun arc => arc.rep)))
    (hinside : ∀ arc ∈ (hd :: s), A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : ∀ arc ∈ (hd :: s), arc.zeros.Nodup)
    (hf2 : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 (TwoExpBivarExpr.denote F)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z)
        z (arc.yc z))
    (hg2 : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 (TwoExpBivarExpr.denote G)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z)
        z (arc.yc z))
    (hfy_nz : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z ≠ 0)
    (hid : ∀ arc ∈ (hd :: s), ∀ t, TwoExpBivarExpr.denote F t (arc.yc t) = 0)
    (hzeros : ∀ arc ∈ (hd :: s), ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ TwoExpBivarExpr.denote G z (arc.yc z) = 0) :
    ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤
      ((singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
        (pfaffianChainFn solved.result.lower.separator.chain
          solved.result.lower.separator.poly) + 1) *
        ((singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
          (pfaffianChainFn solved.result.lower.jacobian.chain
            solved.result.lower.jacobian.poly) + 1) :=
  khovanskii_rolle_full_of_solved_expSDRReductionSolver_bound
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    F G A B M c yExpr expXExpr expYExpr sep solved hd s hchain hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a solved descent using the SingleExp reducer
adapter plus a supplied terminal-nonzero component. -/
theorem khovanskii_rolle_single_of_solved_singleExp_adapter_bound
    (fallback : PfaffianFn.StepwiseDecreaseReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (arc : RepresentedCurveArc)
    (hinside : A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : arc.zeros.Nodup)
    (hf2 : ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 (TwoExpBivarExpr.denote F)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z)
        z (arc.yc z))
    (hg2 : ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 (TwoExpBivarExpr.denote G)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z)
        z (arc.yc z))
    (hfy_nz : ∀ z, arc.lo < z → z < arc.hi →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z ≠ 0)
    (hid : ∀ t, TwoExpBivarExpr.denote F t (arc.yc t) = 0)
    (hzeros : ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ TwoExpBivarExpr.denote G z (arc.yc z) = 0) :
    arc.zeros.length ≤
      ((singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
        (pfaffianChainFn solved.result.lower.separator.chain
          solved.result.lower.separator.poly) + 1) *
        ((singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero).bound
          (pfaffianChainFn solved.result.lower.jacobian.chain
            solved.result.lower.jacobian.poly) + 1) :=
  khovanskii_rolle_single_of_solved_expSDRReductionSolver_bound
    (singleExpPfaffianExpSDRReductionSolver_of_fallback fallback nonzero)
    F G A B M c yExpr expXExpr expYExpr sep solved arc hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros

end TwoExp
end MultiVarMod
end MachLib
