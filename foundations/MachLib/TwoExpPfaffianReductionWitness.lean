import MachLib.TwoExpPfaffianDescent
import MachLib.PfaffianFnBound

/-!
# Reduction-witness bridge for two-exp lower systems

`TwoExpPfaffianDescent` uses the unconditional general Pfaffian bound to turn
lower Pfaffian predicate systems into list-count certificates. This file
records the parallel bridge through the older witness-based reduction
machinery: if a lower predicate system carries an explicit Khovanskii
reduction witness to chain length zero, it yields the same list-count shape.

This does not construct the deep witness. It makes the interface precise
for any future proof that produces one.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce

private theorem flatMap_arc_pair_zeros_length (s : List RepresentedCurveArc) :
    ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
      (s.flatMap (fun arc => arc.zeros)).length := by
  induction s with
  | nil => rfl
  | cons arc rest ih =>
      simp [ih]

/-- Exponential-type chains carry the triangularity required by the
Khovanskii reduction bound. -/
theorem isExpChain_isTriangular {N : Nat} (c : PfaffianChain N)
    (hexp : IsExpChain c) :
    c.IsTriangular := by
  intro i j hij
  exact (hexp i).2 j hij

/-- A pure one-variable Pfaffian reduction witness. This is the function-level
core of the remaining Khovanskii descent input, before it is packaged as a
predicate-system count certificate. -/
structure PfaffianFunctionReductionWitness (f : PfaffianFn) where
  target : PfaffianFn
  steps : Nat
  triangular : f.chain.IsTriangular
  iter : f.IsKhovanskiiReducible target steps
  target_chain_zero : target.n = 0
  target_nonzero : ∃ x : Real, target.eval x ≠ 0

/-- The function-level theorem-shaped frontier: every concrete Pfaffian
function should carry a Khovanskii reduction witness to chain length zero.
This isolates the deep Pfaffian-chain descent theorem from the lower
predicate-system bookkeeping used by the two-exp bridge. -/
structure PfaffianFunctionReductionSolver where
  reduce : ∀ f : PfaffianFn, PfaffianFunctionReductionWitness f

/-- The theorem-shaped frontier specialized to the chains the two-exp bridge
actually creates: exponential-type Pfaffian chains. This avoids asking for a
reducer on arbitrary, possibly non-triangular Pfaffian chains. -/
structure PfaffianExpFunctionReductionSolver where
  reduce :
    ∀ (f : PfaffianFn), IsExpChain f.chain →
      PfaffianFunctionReductionWitness f

/-- Reducer-only part of the SDR frontier. This is the constructive
strict-descent input: every positive-chain-length Pfaffian function receives
a lex-decreasing step, packaged as Khovanskii's generic
`StepwiseDecreaseReducer`. -/
structure PfaffianExpSDRReducer where
  sdr : PfaffianFn.StepwiseDecreaseReducer

/-- Package an existing generic stepwise-decrease reducer as the reducer-only
half of the exp-chain SDR frontier. -/
def PfaffianExpSDRReducer.of_sdr
    (sdr : PfaffianFn.StepwiseDecreaseReducer) :
    PfaffianExpSDRReducer :=
  { sdr := sdr }

/-- Terminal nonzero part of the SDR frontier. This is deliberately separated
from the reducer, since it is a different mathematical obligation from
constructing the lex-decreasing descent step. -/
structure PfaffianExpTerminalNonzero where
  terminal_nonzero :
    ∀ (f : PfaffianFn), IsExpChain f.chain →
      ∀ g k, g.n = 0 → f.IsKhovanskiiReducible g k →
        ∃ x : Real, g.eval x ≠ 0

/-- Package a terminal-nonzero theorem as the nonzero-only half of the
exp-chain SDR frontier. -/
def PfaffianExpTerminalNonzero.of_terminal_nonzero
    (terminal_nonzero :
      ∀ (f : PfaffianFn), IsExpChain f.chain →
        ∀ g k, g.n = 0 → f.IsKhovanskiiReducible g k →
          ∃ x : Real, g.eval x ≠ 0) :
    PfaffianExpTerminalNonzero :=
  { terminal_nonzero := terminal_nonzero }

/-- SDR-level theorem package for exponential-type chains. The generic
`StepwiseDecreaseReducer` supplies the iterated Khovanskii reduction witness;
the terminal nonzero clause is kept explicit because it is a separate
mathematical ingredient in the existing SDR capstone. -/
structure PfaffianExpSDRReductionSolver where
  sdr : PfaffianFn.StepwiseDecreaseReducer
  terminal_nonzero :
    ∀ (f : PfaffianFn), IsExpChain f.chain →
      ∀ g k, g.n = 0 → f.IsKhovanskiiReducible g k →
        ∃ x : Real, g.eval x ≠ 0

/-- Assemble the full SDR-level solver from its two independent mathematical
inputs: descent and terminal nonzero. -/
def PfaffianExpSDRReductionSolver.of_parts
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero) :
    PfaffianExpSDRReductionSolver :=
  { sdr := reducer.sdr,
    terminal_nonzero := nonzero.terminal_nonzero }

/-- Extract the reducer-only component from a full SDR-level solver. -/
def PfaffianExpSDRReductionSolver.reducer
    (solver : PfaffianExpSDRReductionSolver) :
    PfaffianExpSDRReducer :=
  { sdr := solver.sdr }

/-- Extract the terminal-nonzero component from a full SDR-level solver. -/
def PfaffianExpSDRReductionSolver.nonzero
    (solver : PfaffianExpSDRReductionSolver) :
    PfaffianExpTerminalNonzero :=
  { terminal_nonzero := solver.terminal_nonzero }

/-- Reassembling the extracted parts is judgmentally the same solver data. -/
theorem PfaffianExpSDRReductionSolver.of_parts_extracted
    (solver : PfaffianExpSDRReductionSolver) :
    PfaffianExpSDRReductionSolver.of_parts solver.reducer solver.nonzero = solver := by
  cases solver
  rfl

/-- The chain-length-zero target selected from the SDR witness extraction. -/
noncomputable def PfaffianExpSDRReductionSolver.target
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn) : PfaffianFn :=
  Classical.choose (PfaffianFn.witness_via_sdr solver.sdr f)

/-- The number of reduction steps selected from the SDR witness extraction. -/
noncomputable def PfaffianExpSDRReductionSolver.steps
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn) : Nat :=
  Classical.choose
    (Classical.choose_spec (PfaffianFn.witness_via_sdr solver.sdr f))

/-- The selected SDR target has chain length zero. -/
theorem PfaffianExpSDRReductionSolver.target_chain_zero
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn) :
    (solver.target f).n = 0 :=
  (Classical.choose_spec
    (Classical.choose_spec (PfaffianFn.witness_via_sdr solver.sdr f))).1

/-- The selected SDR target is reached by an iterated Khovanskii reduction. -/
theorem PfaffianExpSDRReductionSolver.iter
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn) :
    f.IsKhovanskiiReducible (solver.target f) (solver.steps f) :=
  (Classical.choose_spec
    (Classical.choose_spec (PfaffianFn.witness_via_sdr solver.sdr f))).2

/-- The terminal nonzero fact supplied for the selected SDR target. -/
theorem PfaffianExpSDRReductionSolver.target_nonzero
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn)
    (hexp : IsExpChain f.chain) :
    ∃ x : Real, (solver.target f).eval x ≠ 0 :=
  solver.terminal_nonzero f hexp (solver.target f) (solver.steps f)
    (solver.target_chain_zero f) (solver.iter f)

/-- The explicit bound selected by the SDR witness extraction. -/
noncomputable def PfaffianExpSDRReductionSolver.bound
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn) : Nat :=
  MultiPoly.degreeX (solver.target f).poly + solver.steps f

/-- Direct one-variable zero-count bound exposed by an SDR-level exp-chain
solver. This is the function-level consumer underneath the predicate-system
and two-exp bridges. -/
theorem pfaffian_function_count_of_expSDRReductionSolver_bound
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn)
    (hexp : IsExpChain f.chain)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) :
    zeros.length ≤ solver.bound f := by
  unfold PfaffianExpSDRReductionSolver.bound
  exact MachLib.PfaffianFnBound.pfaffian_fn_zero_count_bound
    f a b hab hcoherent (isExpChain_isTriangular f.chain hexp)
    (solver.target f) (solver.steps f) (solver.iter f)
    (solver.target_chain_zero f) (solver.target_nonzero f hexp)
    zeros hnd hz

/-- Existential list-count form of the SDR-level one-variable bound. -/
theorem pfaffian_function_count_of_expSDRReductionSolver
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn)
    (hexp : IsExpChain f.chain)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ N := by
  refine ⟨solver.bound f, ?_⟩
  intro zeros hnd hz
  exact pfaffian_function_count_of_expSDRReductionSolver_bound
    solver f hexp a b hab hcoherent zeros hnd hz

/-- Direct one-variable zero-count bound from the split SDR inputs. -/
theorem pfaffian_function_count_of_expSDR_parts_bound
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (f : PfaffianFn)
    (hexp : IsExpChain f.chain)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) :
    zeros.length ≤
      (PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound f :=
  pfaffian_function_count_of_expSDRReductionSolver_bound
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    f hexp a b hab hcoherent zeros hnd hz

/-- Existential one-variable count from the split SDR inputs. -/
theorem pfaffian_function_count_of_expSDR_parts
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (f : PfaffianFn)
    (hexp : IsExpChain f.chain)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ N :=
  pfaffian_function_count_of_expSDRReductionSolver
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    f hexp a b hab hcoherent

/-- An SDR-level solver for exponential-type chains induces the exp-chain
function reduction solver consumed by the two-exp bridge. -/
noncomputable def pfaffianExpFunctionReductionSolver_of_sdr
    (solver : PfaffianExpSDRReductionSolver) :
    PfaffianExpFunctionReductionSolver :=
  { reduce := fun f hexp => by
      exact
        { target := solver.target f,
          steps := solver.steps f,
          triangular := isExpChain_isTriangular f.chain hexp,
          iter := solver.iter f,
          target_chain_zero := solver.target_chain_zero f,
          target_nonzero := solver.target_nonzero f hexp } }

/-- The explicit zero-count bound carried by a function reduction witness. -/
noncomputable def PfaffianFunctionReductionWitness.bound
    {f : PfaffianFn}
    (wit : PfaffianFunctionReductionWitness f) : Nat :=
  MultiPoly.degreeX wit.target.poly + wit.steps

/-- The exp-function solver induced by an SDR solver exposes exactly the SDR
selected bound. -/
theorem pfaffianExpFunctionReductionSolver_of_sdr_bound
    (solver : PfaffianExpSDRReductionSolver)
    (f : PfaffianFn)
    (hexp : IsExpChain f.chain) :
    ((pfaffianExpFunctionReductionSolver_of_sdr solver).reduce f hexp).bound =
      solver.bound f :=
  rfl

/-- A witness that a concrete lower Pfaffian predicate system reduces, via
the existing Khovanskii reduction machinery, to a chain-length-zero
Pfaffian function. -/
structure PfaffianPredicateReductionWitness
    {A B : Real} {P : Real → Prop}
    (sys : PfaffianPredicateSystem A B P) where
  target : PfaffianFn
  steps : Nat
  triangular : sys.chain.IsTriangular
  iter :
    (pfaffianChainFn sys.chain sys.poly).IsKhovanskiiReducible target steps
  target_chain_zero : target.n = 0
  target_nonzero : ∃ x : Real, target.eval x ≠ 0

/-- Package a pure function-level reduction witness for the Pfaffian function
underlying a predicate system as the predicate-level witness consumed by the
count bridge. -/
def PfaffianPredicateReductionWitness.ofFunctionWitness
    {A B : Real} {P : Real → Prop}
    (sys : PfaffianPredicateSystem A B P)
    (wit : PfaffianFunctionReductionWitness (pfaffianChainFn sys.chain sys.poly)) :
    PfaffianPredicateReductionWitness sys :=
  { target := wit.target,
    steps := wit.steps,
    triangular := wit.triangular,
    iter := wit.iter,
    target_chain_zero := wit.target_chain_zero,
    target_nonzero := wit.target_nonzero }

/-- The theorem-shaped frontier for general one-variable Pfaffian descent:
every concrete lower predicate system should carry an explicit Khovanskii
reduction witness to chain length zero. Proving an inhabitant of this
structure is the remaining deep Pfaffian-chain induction input. -/
structure PfaffianPredicateReductionSolver where
  reduce :
    ∀ {A B : Real} {P : Real → Prop}
      (sys : PfaffianPredicateSystem A B P),
      PfaffianPredicateReductionWitness sys

/-- A uniform function-level reduction solver induces the predicate-level
solver needed by the lower-system bridge. -/
noncomputable def pfaffianPredicateReductionSolver_of_functionSolver
    (solver : PfaffianFunctionReductionSolver) :
    PfaffianPredicateReductionSolver :=
  { reduce := fun sys =>
      PfaffianPredicateReductionWitness.ofFunctionWitness sys
        (solver.reduce (pfaffianChainFn sys.chain sys.poly)) }

/-- A uniform exp-chain function reducer induces the predicate-level solver
needed by the concrete lower systems. -/
noncomputable def pfaffianPredicateReductionSolver_of_expFunctionSolver
    (solver : PfaffianExpFunctionReductionSolver) :
    PfaffianPredicateReductionSolver :=
  { reduce := fun sys =>
      PfaffianPredicateReductionWitness.ofFunctionWitness sys
        (solver.reduce (pfaffianChainFn sys.chain sys.poly) sys.isExp) }

/-- An SDR-level exp-chain solver induces the predicate-level solver needed by
the concrete lower systems. -/
noncomputable def pfaffianPredicateReductionSolver_of_expSDRReductionSolver
    (solver : PfaffianExpSDRReductionSolver) :
    PfaffianPredicateReductionSolver :=
  pfaffianPredicateReductionSolver_of_expFunctionSolver
    (pfaffianExpFunctionReductionSolver_of_sdr solver)

/-- The explicit zero-count bound carried by a predicate reduction witness:
the final one-variable degree plus the number of Rolle-counted reduction
steps. -/
noncomputable def PfaffianPredicateReductionWitness.bound
    {A B : Real} {P : Real → Prop}
    {sys : PfaffianPredicateSystem A B P}
    (wit : PfaffianPredicateReductionWitness sys) : Nat :=
  MultiPoly.degreeX wit.target.poly + wit.steps

/-- The predicate-system adapter preserves the explicit function-witness
bound. -/
theorem PfaffianPredicateReductionWitness.ofFunctionWitness_bound
    {A B : Real} {P : Real → Prop}
    (sys : PfaffianPredicateSystem A B P)
    (wit : PfaffianFunctionReductionWitness (pfaffianChainFn sys.chain sys.poly)) :
    (PfaffianPredicateReductionWitness.ofFunctionWitness sys wit).bound =
      wit.bound :=
  rfl

/-- A lower predicate system with an explicit Khovanskii reduction witness
gets the concrete bound advertised by that witness. -/
theorem count_of_predicate_system_reductionWitness_bound
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : PfaffianPredicateSystem A B P)
    (wit : PfaffianPredicateReductionWitness sys)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ P z) :
    zeros.length ≤ wit.bound := by
  unfold PfaffianPredicateReductionWitness.bound
  exact MachLib.PfaffianFnBound.pfaffian_fn_zero_count_bound
    (pfaffianChainFn sys.chain sys.poly) A B hab sys.coherent wit.triangular
    wit.target wit.steps wit.iter wit.target_chain_zero wit.target_nonzero
    zeros hnd (fun z hzmem => by
      obtain ⟨hza, hzb, hPz⟩ := hz z hzmem
      exact ⟨hza, hzb, sys.predicate_zero z hza hzb hPz⟩)

/-- A lower predicate system with an explicit Khovanskii reduction witness
produces the list-count shape required by the two-exp descent certificate. -/
theorem count_of_predicate_system_reductionWitness
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : PfaffianPredicateSystem A B P)
    (wit : PfaffianPredicateReductionWitness sys) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) → zeros.length ≤ N := by
  refine ⟨wit.bound, ?_⟩
  intro zeros hnd hz
  exact count_of_predicate_system_reductionWitness_bound A B hab P sys wit zeros hnd hz

/-- A function-level reduction solver produces the list-count shape for any
concrete lower predicate system, after the predicate-system adapter has done
the bookkeeping. -/
theorem count_of_predicate_system_functionReductionSolver
    (solver : PfaffianFunctionReductionSolver)
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : PfaffianPredicateSystem A B P) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) → zeros.length ≤ N :=
  count_of_predicate_system_reductionWitness A B hab P sys
    (PfaffianPredicateReductionWitness.ofFunctionWitness sys
      (solver.reduce (pfaffianChainFn sys.chain sys.poly)))

/-- An exp-chain function reduction solver produces the list-count shape for
any concrete lower predicate system. -/
theorem count_of_predicate_system_expFunctionReductionSolver
    (solver : PfaffianExpFunctionReductionSolver)
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : PfaffianPredicateSystem A B P) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) → zeros.length ≤ N :=
  count_of_predicate_system_reductionWitness A B hab P sys
    (PfaffianPredicateReductionWitness.ofFunctionWitness sys
      (solver.reduce (pfaffianChainFn sys.chain sys.poly) sys.isExp))

/-- An SDR-level exp-chain reduction solver produces the list-count shape for
any concrete lower predicate system. -/
theorem count_of_predicate_system_expSDRReductionSolver
    (solver : PfaffianExpSDRReductionSolver)
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : PfaffianPredicateSystem A B P) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) → zeros.length ≤ N :=
  count_of_predicate_system_expFunctionReductionSolver
    (pfaffianExpFunctionReductionSolver_of_sdr solver) A B hab P sys

/-- An SDR-level exp-chain reduction solver gives the explicit selected
bound for any concrete lower predicate system. -/
theorem count_of_predicate_system_expSDRReductionSolver_bound
    (solver : PfaffianExpSDRReductionSolver)
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : PfaffianPredicateSystem A B P)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ P z) :
    zeros.length ≤
      solver.bound (pfaffianChainFn sys.chain sys.poly) := by
  exact pfaffian_function_count_of_expSDRReductionSolver_bound
    solver (pfaffianChainFn sys.chain sys.poly) sys.isExp A B hab sys.coherent
    zeros hnd (fun z hzmem => by
      obtain ⟨hza, hzb, hPz⟩ := hz z hzmem
      exact ⟨hza, hzb, sys.predicate_zero z hza hzb hPz⟩)

/-- Explicit predicate-system count from the split SDR inputs. -/
theorem count_of_predicate_system_expSDR_parts_bound
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : PfaffianPredicateSystem A B P)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ P z) :
    zeros.length ≤
      (PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
        (pfaffianChainFn sys.chain sys.poly) :=
  count_of_predicate_system_expSDRReductionSolver_bound
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    A B hab P sys zeros hnd hz

/-- A uniform predicate reduction solver produces the list-count shape for
any concrete lower predicate system. -/
theorem count_of_predicate_system_reductionSolver
    (solver : PfaffianPredicateReductionSolver)
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : PfaffianPredicateSystem A B P) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) → zeros.length ≤ N :=
  count_of_predicate_system_reductionWitness A B hab P sys (solver.reduce sys)

/-- Reduction witnesses for both lower systems in a two-exp descent step. -/
structure TwoExpLowerReductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) where
  jacobian : PfaffianPredicateReductionWitness lower.jacobian
  separator : PfaffianPredicateReductionWitness lower.separator

/-- A uniform one-variable reduction solver specializes to both lower
systems in a two-exp descent step. -/
def TwoExpLowerReductionWitness.ofPredicateSolver
    (solver : PfaffianPredicateReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower :=
  { jacobian := solver.reduce lower.jacobian,
    separator := solver.reduce lower.separator }

/-- The theorem-shaped frontier specialized to the two-exp lower systems:
given the lower Jacobian and separator predicate systems, produce explicit
reduction witnesses for both. A uniform predicate solver induces this
structure, but specialized solvers can target this smaller surface. -/
structure TwoExpLowerReductionSolver where
  reduce :
    ∀ (F G : TwoExpBivarExpr)
      (A B : Real)
      (M : Nat) (c : PfaffianChain (M + 2))
      (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
      (sep : Real → Prop)
      (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep),
      TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower

/-- A uniform predicate-level solver is a two-exp lower reduction solver. -/
def twoExpLowerReductionSolver_of_predicateSolver
    (solver : PfaffianPredicateReductionSolver) :
    TwoExpLowerReductionSolver :=
  { reduce := fun F G A B M c yExpr expXExpr expYExpr sep lower =>
      TwoExpLowerReductionWitness.ofPredicateSolver solver F G A B M c
        yExpr expXExpr expYExpr sep lower }

/-- A uniform function-level solver is also enough for every two-exp lower
system, via the predicate-system adapter. -/
noncomputable def twoExpLowerReductionSolver_of_functionSolver
    (solver : PfaffianFunctionReductionSolver) :
    TwoExpLowerReductionSolver :=
  twoExpLowerReductionSolver_of_predicateSolver
    (pfaffianPredicateReductionSolver_of_functionSolver solver)

/-- A uniform exp-chain function solver is enough for every two-exp lower
system, because lower predicate systems carry `IsExpChain`. -/
noncomputable def twoExpLowerReductionSolver_of_expFunctionSolver
    (solver : PfaffianExpFunctionReductionSolver) :
    TwoExpLowerReductionSolver :=
  twoExpLowerReductionSolver_of_predicateSolver
    (pfaffianPredicateReductionSolver_of_expFunctionSolver solver)

/-- An SDR-level exp-chain solver is enough for every two-exp lower system. -/
noncomputable def twoExpLowerReductionSolver_of_expSDRReductionSolver
    (solver : PfaffianExpSDRReductionSolver) :
    TwoExpLowerReductionSolver :=
  twoExpLowerReductionSolver_of_expFunctionSolver
    (pfaffianExpFunctionReductionSolver_of_sdr solver)

/-- Split SDR inputs are enough for every two-exp lower system. -/
noncomputable def twoExpLowerReductionSolver_of_expSDR_parts
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero) :
    TwoExpLowerReductionSolver :=
  twoExpLowerReductionSolver_of_expSDRReductionSolver
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)

/-- Explicit Jacobian-side count bound carried by a two-exp lower reduction
witness. -/
noncomputable def TwoExpLowerReductionWitness.jacobianBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    {lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep}
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower) :
    Nat :=
  wit.jacobian.bound

/-- Explicit separator-side count bound carried by a two-exp lower reduction
witness. -/
noncomputable def TwoExpLowerReductionWitness.separatorBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    {lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep}
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower) :
    Nat :=
  wit.separator.bound

/-- The induced two-exp lower solver uses the predicate solver's Jacobian
bound directly. -/
theorem twoExpLowerReductionSolver_of_predicateSolver_jacobianBound
    (solver : PfaffianPredicateReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    ((twoExpLowerReductionSolver_of_predicateSolver solver).reduce F G A B M c
      yExpr expXExpr expYExpr sep lower).jacobianBound =
      (solver.reduce lower.jacobian).bound :=
  rfl

/-- The induced two-exp lower solver uses the predicate solver's separator
bound directly. -/
theorem twoExpLowerReductionSolver_of_predicateSolver_separatorBound
    (solver : PfaffianPredicateReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    ((twoExpLowerReductionSolver_of_predicateSolver solver).reduce F G A B M c
      yExpr expXExpr expYExpr sep lower).separatorBound =
      (solver.reduce lower.separator).bound :=
  rfl

/-- The lower solver induced by split SDR inputs exposes the selected
Jacobian SDR bound directly. -/
theorem twoExpLowerReductionSolver_of_expSDR_parts_jacobianBound
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    ((twoExpLowerReductionSolver_of_expSDR_parts reducer nonzero).reduce F G A B M c
      yExpr expXExpr expYExpr sep lower).jacobianBound =
      (PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
        (pfaffianChainFn lower.jacobian.chain lower.jacobian.poly) := by
  simp [twoExpLowerReductionSolver_of_expSDR_parts,
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

/-- The lower solver induced by split SDR inputs exposes the selected
separator SDR bound directly. -/
theorem twoExpLowerReductionSolver_of_expSDR_parts_separatorBound
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    ((twoExpLowerReductionSolver_of_expSDR_parts reducer nonzero).reduce F G A B M c
      yExpr expXExpr expYExpr sep lower).separatorBound =
      (PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
        (pfaffianChainFn lower.separator.chain lower.separator.poly) := by
  simp [twoExpLowerReductionSolver_of_expSDR_parts,
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

/-- The Jacobian-side list bound with the concrete witness bound exposed. -/
theorem jacobian_count_of_lower_reductionWitness_bound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧
      restrictedJacobianPred F G M c yExpr expXExpr expYExpr z) :
    zeros.length ≤ wit.jacobianBound :=
  count_of_predicate_system_reductionWitness_bound A B hAB
    (restrictedJacobianPred F G M c yExpr expXExpr expYExpr)
    lower.jacobian wit.jacobian zeros hnd hz

/-- The separator-side list bound with the concrete witness bound exposed. -/
theorem separator_count_of_lower_reductionWitness_bound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ sep z) :
    zeros.length ≤ wit.separatorBound :=
  count_of_predicate_system_reductionWitness_bound A B hAB
    sep lower.separator wit.separator zeros hnd hz

/-- The Jacobian-side list bound exposed directly through an SDR-level
exp-chain reduction solver. -/
theorem jacobian_count_of_lower_expSDRReductionSolver_bound
    (solver : PfaffianExpSDRReductionSolver)
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
      solver.bound (pfaffianChainFn lower.jacobian.chain lower.jacobian.poly) :=
  count_of_predicate_system_expSDRReductionSolver_bound solver A B hAB
    (restrictedJacobianPred F G M c yExpr expXExpr expYExpr)
    lower.jacobian zeros hnd hz

/-- The separator-side list bound exposed directly through an SDR-level
exp-chain reduction solver. -/
theorem separator_count_of_lower_expSDRReductionSolver_bound
    (solver : PfaffianExpSDRReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ sep z) :
    zeros.length ≤
      solver.bound (pfaffianChainFn lower.separator.chain lower.separator.poly) :=
  count_of_predicate_system_expSDRReductionSolver_bound solver A B hAB
    sep lower.separator zeros hnd hz

/-- The Jacobian-side list bound exposed directly through split SDR inputs. -/
theorem jacobian_count_of_lower_expSDR_parts_bound
    (reducer : PfaffianExpSDRReducer)
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
      (PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
        (pfaffianChainFn lower.jacobian.chain lower.jacobian.poly) :=
  jacobian_count_of_lower_expSDRReductionSolver_bound
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower zeros hnd hz

/-- The separator-side list bound exposed directly through split SDR inputs. -/
theorem separator_count_of_lower_expSDR_parts_bound
    (reducer : PfaffianExpSDRReducer)
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
      (PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
        (pfaffianChainFn lower.separator.chain lower.separator.poly) :=
  separator_count_of_lower_expSDRReductionSolver_bound
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower zeros hnd hz

/-- A lower system plus explicit reduction witnesses for both of its
components yields the full count-shaped two-exp descent certificate. -/
theorem descentCertificate_of_lower_reductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  { jacobianCount := count_of_predicate_system_reductionWitness A B hAB
      (restrictedJacobianPred F G M c yExpr expXExpr expYExpr)
      lower.jacobian wit.jacobian,
    separatorCount := count_of_predicate_system_reductionWitness A B hAB
      sep lower.separator wit.separator }

/-- A two-exp lower reduction solver turns any constructed lower system into
the count-shaped descent certificate consumed by Khovanskii-Rolle. -/
theorem descentCertificate_of_lower_reductionSolver
    (solver : TwoExpLowerReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_reductionWitness F G A B hAB M c yExpr expXExpr
    expYExpr sep lower
    (solver.reduce F G A B M c yExpr expXExpr expYExpr sep lower)

/-- Predicate-level uniform reduction is enough to certify any two-exp lower
system. -/
theorem descentCertificate_of_lower_predicateReductionSolver
    (solver : PfaffianPredicateReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_reductionSolver
    (twoExpLowerReductionSolver_of_predicateSolver solver)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower

/-- Function-level uniform reduction is enough to certify any two-exp lower
system. -/
theorem descentCertificate_of_lower_functionReductionSolver
    (solver : PfaffianFunctionReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_predicateReductionSolver
    (pfaffianPredicateReductionSolver_of_functionSolver solver)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower

/-- Exp-chain function-level uniform reduction is enough to certify any
two-exp lower system. -/
theorem descentCertificate_of_lower_expFunctionReductionSolver
    (solver : PfaffianExpFunctionReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_predicateReductionSolver
    (pfaffianPredicateReductionSolver_of_expFunctionSolver solver)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower

/-- SDR-level exp-chain reduction is enough to certify any two-exp lower
system. -/
theorem descentCertificate_of_lower_expSDRReductionSolver
    (solver : PfaffianExpSDRReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_expFunctionReductionSolver
    (pfaffianExpFunctionReductionSolver_of_sdr solver)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower

/-- Split SDR inputs are enough to certify any two-exp lower system. -/
theorem descentCertificate_of_lower_expSDR_parts
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_expSDRReductionSolver
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    F G A B hAB M c yExpr expXExpr expYExpr sep lower

/-- A solved descent plus reduction witnesses for its stored lower systems
also yields the count-shaped certificate. This is the witness-based analogue
of `descentCertificate_of_solved_descent`. -/
theorem descentCertificate_of_solved_reductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved.result.lower) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_reductionWitness F G A B solved.problem.interval_nonempty
    M c yExpr expXExpr expYExpr sep solved.result.lower wit

/-- A solved descent plus a two-exp lower reduction solver yields the
count-shaped certificate. This is the solver-shaped analogue of
`descentCertificate_of_solved_reductionWitness`. -/
theorem descentCertificate_of_solved_reductionSolver
    (solver : TwoExpLowerReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_reductionSolver solver F G A B
    solved.problem.interval_nonempty M c yExpr expXExpr expYExpr sep solved.result.lower

/-- A solved descent plus a uniform predicate-level reduction solver yields
the count-shaped certificate. -/
theorem descentCertificate_of_solved_predicateReductionSolver
    (solver : PfaffianPredicateReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_solved_reductionSolver
    (twoExpLowerReductionSolver_of_predicateSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved

/-- A solved descent plus a uniform function-level reduction solver yields
the count-shaped certificate. -/
theorem descentCertificate_of_solved_functionReductionSolver
    (solver : PfaffianFunctionReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_solved_predicateReductionSolver
    (pfaffianPredicateReductionSolver_of_functionSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved

/-- A solved descent plus a uniform exp-chain function reduction solver yields
the count-shaped certificate. -/
theorem descentCertificate_of_solved_expFunctionReductionSolver
    (solver : PfaffianExpFunctionReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_solved_predicateReductionSolver
    (pfaffianPredicateReductionSolver_of_expFunctionSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved

/-- A solved descent plus an SDR-level exp-chain reduction solver yields the
count-shaped certificate. -/
theorem descentCertificate_of_solved_expSDRReductionSolver
    (solver : PfaffianExpSDRReductionSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_solved_expFunctionReductionSolver
    (pfaffianExpFunctionReductionSolver_of_sdr solver)
    F G A B M c yExpr expXExpr expYExpr sep solved

/-- A solved descent plus the split SDR inputs yields the count-shaped
certificate. -/
theorem descentCertificate_of_solved_expSDR_parts
    (reducer : PfaffianExpSDRReducer)
    (nonzero : PfaffianExpTerminalNonzero)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_solved_expSDRReductionSolver
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    F G A B M c yExpr expXExpr expYExpr sep solved

/-- Local curve consumer for a lower system equipped with explicit reduction
witnesses. This is the direct KR endpoint for the witness-based descent path. -/
theorem khovanskii_rolle_curve_of_lower_reductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower)
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
    (hid : ∀ t, TwoExpBivarExpr.denote F t (yc t) = 0) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ TwoExpBivarExpr.denote G z (yc z) = 0) →
      zeros_g.length ≤ N + 1 :=
  khovanskii_rolle_curve_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    (descentCertificate_of_lower_reductionWitness F G A B hAB M c yExpr expXExpr expYExpr
      sep lower wit)
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Full global consumer for a lower system equipped with explicit reduction
witnesses. -/
theorem khovanskii_rolle_full_of_lower_reductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower)
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
    ∃ Ncrit N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    (descentCertificate_of_lower_reductionWitness F G A B hAB M c yExpr expXExpr expYExpr
      sep lower wit)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a lower system equipped with explicit reduction
witnesses. -/
theorem khovanskii_rolle_single_of_lower_reductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower)
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
    ∃ Ncrit N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_single_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    (descentCertificate_of_lower_reductionWitness F G A B hAB M c yExpr expXExpr expYExpr
      sep lower wit)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Local curve consumer with the explicit Jacobian bound carried by the
reduction witness. -/
theorem khovanskii_rolle_curve_of_lower_reductionWitness_bound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower)
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
    zeros_g.length ≤ wit.jacobianBound + 1 := by
  exact khovanskii_rolle_count_curve
    (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G)
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G))
    yc a b hab hf2 hg2 hfy_nz hid wit.jacobianBound
    (fun zeros_J hnd hJlocal =>
      jacobian_count_of_lower_reductionWitness_bound F G A B hAB M c yExpr expXExpr
        expYExpr sep lower wit zeros_J hnd (fun z hzmem => by
          obtain ⟨hza, hzb, hJac⟩ := hJlocal z hzmem
          obtain ⟨hA, hB⟩ := hsub z hza hzb
          exact ⟨hA, hB, hJac⟩))
    zeros_g hzeros_nd hzeros

/-- Full global consumer with the explicit bounds carried by the reduction
witnesses: separator bound for the number of arcs, Jacobian bound per arc. -/
theorem khovanskii_rolle_full_of_lower_reductionWitness_bound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower)
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
      (wit.separatorBound + 1) * (wit.jacobianBound + 1) := by
  have harcRich : ∀ arc ∈ (hd :: s), arc.zeros.length ≤ wit.jacobianBound + 1 := by
    intro arc harcmem
    exact khovanskii_rolle_curve_of_lower_reductionWitness_bound
      F G A B hAB M c yExpr expXExpr expYExpr sep lower wit arc.yc arc.lo arc.hi
      (hinside arc harcmem).2.1
      (fun z hzlo hzhi => by
        exact ⟨lt_trans_ax (hinside arc harcmem).1 hzlo,
          lt_trans_ax hzhi (hinside arc harcmem).2.2⟩)
      (hf2 arc harcmem) (hg2 arc harcmem) (hfy_nz arc harcmem) (hid arc harcmem)
      arc.zeros (hzeros_nd arc harcmem) (hzeros arc harcmem)
  have hchainPairs : ChainSep (fun x => A < x ∧ x < B ∧ sep x) (hd.rep, hd.zeros).1
      ((s.map (fun arc => (arc.rep, arc.zeros))).map (fun pair => pair.1)) := by
    simpa [List.map_map] using hchain
  have hglobal := khovanskii_rolle_full (fun x => A < x ∧ x < B ∧ sep x)
    wit.separatorBound wit.jacobianBound
    (fun ss hnd hss =>
      separator_count_of_lower_reductionWitness_bound F G A B hAB M c yExpr expXExpr
        expYExpr sep lower wit ss hnd (fun x hx => hss x hx))
    (hd.rep, hd.zeros) (s.map (fun arc => (arc.rep, arc.zeros))) hchainPairs ?_
  · have htail :
        ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
          (s.flatMap (fun arc => arc.zeros)).length :=
        flatMap_arc_pair_zeros_length s
    simpa [htail] using hglobal
  · intro pair hpairmem
    cases hpairmem with
    | head =>
        exact harcRich hd (List.mem_cons_self _ _)
    | tail _ hp =>
        obtain ⟨arc, harcmem, hpair⟩ := List.mem_map.mp hp
        cases hpair
        exact harcRich arc (List.mem_cons_of_mem _ harcmem)

/-- Single-arc consumer with the explicit bounds carried by the reduction
witnesses. -/
theorem khovanskii_rolle_single_of_lower_reductionWitness_bound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep lower)
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
    arc.zeros.length ≤ (wit.separatorBound + 1) * (wit.jacobianBound + 1) := by
  have hglobal := khovanskii_rolle_full_of_lower_reductionWitness_bound
    F G A B hAB M c yExpr expXExpr expYExpr sep lower wit arc [] trivial
    (fun a ha => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hinside)
    (fun a ha => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hzeros_nd)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hf2 z hzlo hzhi)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hg2 z hzlo hzhi)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hfy_nz z hzlo hzhi)
    (fun a ha t => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hid t)
    (fun a ha z hzmem => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hzeros z hzmem)
  simpa using hglobal

/-- Local curve consumer for a solved descent whose stored lower systems carry
explicit reduction witnesses. -/
theorem khovanskii_rolle_curve_of_solved_reductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved.result.lower)
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
    (hid : ∀ t, TwoExpBivarExpr.denote F t (yc t) = 0) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ TwoExpBivarExpr.denote G z (yc z) = 0) →
      zeros_g.length ≤ N + 1 :=
  khovanskii_rolle_curve_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    (descentCertificate_of_solved_reductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved wit)
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Full global consumer for a solved descent whose stored lower systems carry
explicit reduction witnesses. -/
theorem khovanskii_rolle_full_of_solved_reductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved.result.lower)
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
    ∃ Ncrit N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    (descentCertificate_of_solved_reductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved wit)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a solved descent whose stored lower systems carry
explicit reduction witnesses. -/
theorem khovanskii_rolle_single_of_solved_reductionWitness
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved.result.lower)
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
    ∃ Ncrit N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_single_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    (descentCertificate_of_solved_reductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved wit)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Local curve consumer for a solved descent with the explicit Jacobian
bound carried by its reduction witness. -/
theorem khovanskii_rolle_curve_of_solved_reductionWitness_bound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved.result.lower)
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
    zeros_g.length ≤ wit.jacobianBound + 1 :=
  khovanskii_rolle_curve_of_lower_reductionWitness_bound
    F G A B solved.problem.interval_nonempty M c yExpr expXExpr expYExpr sep
    solved.result.lower wit yc a b hab hsub hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros

/-- Full global consumer for a solved descent with the explicit bounds
carried by its reduction witnesses. -/
theorem khovanskii_rolle_full_of_solved_reductionWitness_bound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved.result.lower)
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
      (wit.separatorBound + 1) * (wit.jacobianBound + 1) :=
  khovanskii_rolle_full_of_lower_reductionWitness_bound
    F G A B solved.problem.interval_nonempty M c yExpr expXExpr expYExpr sep
    solved.result.lower wit hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a solved descent with the explicit bounds carried
by its reduction witnesses. -/
theorem khovanskii_rolle_single_of_solved_reductionWitness_bound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (wit : TwoExpLowerReductionWitness F G A B M c yExpr expXExpr expYExpr sep
      solved.result.lower)
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
    arc.zeros.length ≤ (wit.separatorBound + 1) * (wit.jacobianBound + 1) :=
  khovanskii_rolle_single_of_lower_reductionWitness_bound
    F G A B solved.problem.interval_nonempty M c yExpr expXExpr expYExpr sep
    solved.result.lower wit arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Local curve consumer for a solved descent plus a two-exp lower reduction
solver, exposing the solver-produced Jacobian bound. -/
theorem khovanskii_rolle_curve_of_solved_reductionSolver_bound
    (solver : TwoExpLowerReductionSolver)
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
      (solver.reduce F G A B M c yExpr expXExpr expYExpr sep solved.result.lower).jacobianBound + 1 :=
  khovanskii_rolle_curve_of_solved_reductionWitness_bound F G A B M c yExpr expXExpr
    expYExpr sep solved
    (solver.reduce F G A B M c yExpr expXExpr expYExpr sep solved.result.lower)
    yc a b hab hsub hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros

/-- Full global consumer for a solved descent plus a two-exp lower reduction
solver, exposing the solver-produced separator and Jacobian bounds. -/
theorem khovanskii_rolle_full_of_solved_reductionSolver_bound
    (solver : TwoExpLowerReductionSolver)
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
      ((solver.reduce F G A B M c yExpr expXExpr expYExpr sep solved.result.lower).separatorBound + 1) *
        ((solver.reduce F G A B M c yExpr expXExpr expYExpr sep solved.result.lower).jacobianBound + 1) :=
  khovanskii_rolle_full_of_solved_reductionWitness_bound F G A B M c yExpr expXExpr
    expYExpr sep solved
    (solver.reduce F G A B M c yExpr expXExpr expYExpr sep solved.result.lower)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a solved descent plus a two-exp lower reduction
solver, exposing the solver-produced separator and Jacobian bounds. -/
theorem khovanskii_rolle_single_of_solved_reductionSolver_bound
    (solver : TwoExpLowerReductionSolver)
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
      ((solver.reduce F G A B M c yExpr expXExpr expYExpr sep solved.result.lower).separatorBound + 1) *
        ((solver.reduce F G A B M c yExpr expXExpr expYExpr sep solved.result.lower).jacobianBound + 1) :=
  khovanskii_rolle_single_of_solved_reductionWitness_bound F G A B M c yExpr expXExpr
    expYExpr sep solved
    (solver.reduce F G A B M c yExpr expXExpr expYExpr sep solved.result.lower)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Local curve consumer for a solved descent plus a uniform predicate-level
reduction solver, exposing the predicate solver's Jacobian bound directly. -/
theorem khovanskii_rolle_curve_of_solved_predicateReductionSolver_bound
    (solver : PfaffianPredicateReductionSolver)
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
    zeros_g.length ≤ (solver.reduce solved.result.lower.jacobian).bound + 1 := by
  have h := khovanskii_rolle_curve_of_solved_reductionSolver_bound
    (twoExpLowerReductionSolver_of_predicateSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved yc a b hab hsub
    hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros
  simpa [twoExpLowerReductionSolver_of_predicateSolver_jacobianBound] using h

/-- Full global consumer for a solved descent plus a uniform predicate-level
reduction solver, exposing the predicate solver's separator and Jacobian
bounds directly. -/
theorem khovanskii_rolle_full_of_solved_predicateReductionSolver_bound
    (solver : PfaffianPredicateReductionSolver)
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
      ((solver.reduce solved.result.lower.separator).bound + 1) *
        ((solver.reduce solved.result.lower.jacobian).bound + 1) := by
  have h := khovanskii_rolle_full_of_solved_reductionSolver_bound
    (twoExpLowerReductionSolver_of_predicateSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved hd s hchain hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros
  simpa [twoExpLowerReductionSolver_of_predicateSolver_jacobianBound,
    twoExpLowerReductionSolver_of_predicateSolver_separatorBound] using h

/-- Single-arc consumer for a solved descent plus a uniform predicate-level
reduction solver, exposing the predicate solver's separator and Jacobian
bounds directly. -/
theorem khovanskii_rolle_single_of_solved_predicateReductionSolver_bound
    (solver : PfaffianPredicateReductionSolver)
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
      ((solver.reduce solved.result.lower.separator).bound + 1) *
        ((solver.reduce solved.result.lower.jacobian).bound + 1) := by
  have h := khovanskii_rolle_single_of_solved_reductionSolver_bound
    (twoExpLowerReductionSolver_of_predicateSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved arc hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros
  simpa [twoExpLowerReductionSolver_of_predicateSolver_jacobianBound,
    twoExpLowerReductionSolver_of_predicateSolver_separatorBound] using h

/-- Local curve consumer for a solved descent plus a uniform function-level
reduction solver, exposing the function solver's Jacobian bound directly. -/
theorem khovanskii_rolle_curve_of_solved_functionReductionSolver_bound
    (solver : PfaffianFunctionReductionSolver)
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
      (solver.reduce (pfaffianChainFn solved.result.lower.jacobian.chain
        solved.result.lower.jacobian.poly)).bound + 1 := by
  have h := khovanskii_rolle_curve_of_solved_predicateReductionSolver_bound
    (pfaffianPredicateReductionSolver_of_functionSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved yc a b hab hsub
    hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros
  simpa [pfaffianPredicateReductionSolver_of_functionSolver,
    PfaffianPredicateReductionWitness.ofFunctionWitness_bound] using h

/-- Full global consumer for a solved descent plus a uniform function-level
reduction solver, exposing the function solver's separator and Jacobian
bounds directly. -/
theorem khovanskii_rolle_full_of_solved_functionReductionSolver_bound
    (solver : PfaffianFunctionReductionSolver)
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
      ((solver.reduce (pfaffianChainFn solved.result.lower.separator.chain
        solved.result.lower.separator.poly)).bound + 1) *
        ((solver.reduce (pfaffianChainFn solved.result.lower.jacobian.chain
          solved.result.lower.jacobian.poly)).bound + 1) := by
  have h := khovanskii_rolle_full_of_solved_predicateReductionSolver_bound
    (pfaffianPredicateReductionSolver_of_functionSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved hd s hchain hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros
  simpa [pfaffianPredicateReductionSolver_of_functionSolver,
    PfaffianPredicateReductionWitness.ofFunctionWitness_bound] using h

/-- Single-arc consumer for a solved descent plus a uniform function-level
reduction solver, exposing the function solver's separator and Jacobian
bounds directly. -/
theorem khovanskii_rolle_single_of_solved_functionReductionSolver_bound
    (solver : PfaffianFunctionReductionSolver)
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
      ((solver.reduce (pfaffianChainFn solved.result.lower.separator.chain
        solved.result.lower.separator.poly)).bound + 1) *
        ((solver.reduce (pfaffianChainFn solved.result.lower.jacobian.chain
          solved.result.lower.jacobian.poly)).bound + 1) := by
  have h := khovanskii_rolle_single_of_solved_predicateReductionSolver_bound
    (pfaffianPredicateReductionSolver_of_functionSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved arc hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros
  simpa [pfaffianPredicateReductionSolver_of_functionSolver,
    PfaffianPredicateReductionWitness.ofFunctionWitness_bound] using h

/-- Local curve consumer for a solved descent plus a uniform exp-chain
function reduction solver, exposing the solver's Jacobian bound directly. -/
theorem khovanskii_rolle_curve_of_solved_expFunctionReductionSolver_bound
    (solver : PfaffianExpFunctionReductionSolver)
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
      (solver.reduce
        (pfaffianChainFn solved.result.lower.jacobian.chain solved.result.lower.jacobian.poly)
        solved.result.lower.jacobian.isExp).bound + 1 := by
  have h := khovanskii_rolle_curve_of_solved_predicateReductionSolver_bound
    (pfaffianPredicateReductionSolver_of_expFunctionSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved yc a b hab hsub
    hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros
  simpa [pfaffianPredicateReductionSolver_of_expFunctionSolver,
    PfaffianPredicateReductionWitness.ofFunctionWitness_bound] using h

/-- Full global consumer for a solved descent plus a uniform exp-chain
function reduction solver, exposing the solver's separator and Jacobian
bounds directly. -/
theorem khovanskii_rolle_full_of_solved_expFunctionReductionSolver_bound
    (solver : PfaffianExpFunctionReductionSolver)
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
      ((solver.reduce
        (pfaffianChainFn solved.result.lower.separator.chain solved.result.lower.separator.poly)
        solved.result.lower.separator.isExp).bound + 1) *
        ((solver.reduce
          (pfaffianChainFn solved.result.lower.jacobian.chain solved.result.lower.jacobian.poly)
          solved.result.lower.jacobian.isExp).bound + 1) := by
  have h := khovanskii_rolle_full_of_solved_predicateReductionSolver_bound
    (pfaffianPredicateReductionSolver_of_expFunctionSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved hd s hchain hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros
  simpa [pfaffianPredicateReductionSolver_of_expFunctionSolver,
    PfaffianPredicateReductionWitness.ofFunctionWitness_bound] using h

/-- Single-arc consumer for a solved descent plus a uniform exp-chain
function reduction solver, exposing the solver's separator and Jacobian
bounds directly. -/
theorem khovanskii_rolle_single_of_solved_expFunctionReductionSolver_bound
    (solver : PfaffianExpFunctionReductionSolver)
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
      ((solver.reduce
        (pfaffianChainFn solved.result.lower.separator.chain solved.result.lower.separator.poly)
        solved.result.lower.separator.isExp).bound + 1) *
        ((solver.reduce
          (pfaffianChainFn solved.result.lower.jacobian.chain solved.result.lower.jacobian.poly)
          solved.result.lower.jacobian.isExp).bound + 1) := by
  have h := khovanskii_rolle_single_of_solved_predicateReductionSolver_bound
    (pfaffianPredicateReductionSolver_of_expFunctionSolver solver)
    F G A B M c yExpr expXExpr expYExpr sep solved arc hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros
  simpa [pfaffianPredicateReductionSolver_of_expFunctionSolver,
    PfaffianPredicateReductionWitness.ofFunctionWitness_bound] using h

/-- Local curve consumer for a solved descent plus an SDR-level exp-chain
reduction solver. -/
theorem khovanskii_rolle_curve_of_solved_expSDRReductionSolver_bound
    (solver : PfaffianExpSDRReductionSolver)
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
      solver.bound
        (pfaffianChainFn solved.result.lower.jacobian.chain
          solved.result.lower.jacobian.poly) + 1 := by
  have h := khovanskii_rolle_curve_of_solved_expFunctionReductionSolver_bound
    (pfaffianExpFunctionReductionSolver_of_sdr solver)
    F G A B M c yExpr expXExpr expYExpr sep solved yc a b hab hsub
    hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros
  simpa [pfaffianExpFunctionReductionSolver_of_sdr_bound] using h

/-- Full global consumer for a solved descent plus an SDR-level exp-chain
reduction solver. -/
theorem khovanskii_rolle_full_of_solved_expSDRReductionSolver_bound
    (solver : PfaffianExpSDRReductionSolver)
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
      (solver.bound
        (pfaffianChainFn solved.result.lower.separator.chain
          solved.result.lower.separator.poly) + 1) *
        (solver.bound
          (pfaffianChainFn solved.result.lower.jacobian.chain
            solved.result.lower.jacobian.poly) + 1) := by
  have h := khovanskii_rolle_full_of_solved_expFunctionReductionSolver_bound
    (pfaffianExpFunctionReductionSolver_of_sdr solver)
    F G A B M c yExpr expXExpr expYExpr sep solved hd s hchain hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros
  simpa [pfaffianExpFunctionReductionSolver_of_sdr_bound] using h

/-- Single-arc consumer for a solved descent plus an SDR-level exp-chain
reduction solver. -/
theorem khovanskii_rolle_single_of_solved_expSDRReductionSolver_bound
    (solver : PfaffianExpSDRReductionSolver)
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
      (solver.bound
        (pfaffianChainFn solved.result.lower.separator.chain
          solved.result.lower.separator.poly) + 1) *
        (solver.bound
          (pfaffianChainFn solved.result.lower.jacobian.chain
            solved.result.lower.jacobian.poly) + 1) := by
  have h := khovanskii_rolle_single_of_solved_expFunctionReductionSolver_bound
    (pfaffianExpFunctionReductionSolver_of_sdr solver)
    F G A B M c yExpr expXExpr expYExpr sep solved arc hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros
  simpa [pfaffianExpFunctionReductionSolver_of_sdr_bound] using h

/-- Local curve consumer for a solved descent plus the split SDR inputs. -/
theorem khovanskii_rolle_curve_of_solved_expSDR_parts_bound
    (reducer : PfaffianExpSDRReducer)
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
      (PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
        (pfaffianChainFn solved.result.lower.jacobian.chain
          solved.result.lower.jacobian.poly) + 1 :=
  khovanskii_rolle_curve_of_solved_expSDRReductionSolver_bound
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    F G A B M c yExpr expXExpr expYExpr sep solved yc a b hab hsub
    hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros

/-- Full global consumer for a solved descent plus the split SDR inputs. -/
theorem khovanskii_rolle_full_of_solved_expSDR_parts_bound
    (reducer : PfaffianExpSDRReducer)
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
      ((PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
        (pfaffianChainFn solved.result.lower.separator.chain
          solved.result.lower.separator.poly) + 1) *
        ((PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
          (pfaffianChainFn solved.result.lower.jacobian.chain
            solved.result.lower.jacobian.poly) + 1) :=
  khovanskii_rolle_full_of_solved_expSDRReductionSolver_bound
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    F G A B M c yExpr expXExpr expYExpr sep solved hd s hchain hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a solved descent plus the split SDR inputs. -/
theorem khovanskii_rolle_single_of_solved_expSDR_parts_bound
    (reducer : PfaffianExpSDRReducer)
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
      ((PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
        (pfaffianChainFn solved.result.lower.separator.chain
          solved.result.lower.separator.poly) + 1) *
        ((PfaffianExpSDRReductionSolver.of_parts reducer nonzero).bound
          (pfaffianChainFn solved.result.lower.jacobian.chain
            solved.result.lower.jacobian.poly) + 1) :=
  khovanskii_rolle_single_of_solved_expSDRReductionSolver_bound
    (PfaffianExpSDRReductionSolver.of_parts reducer nonzero)
    F G A B M c yExpr expXExpr expYExpr sep solved arc hinside hzeros_nd
    hf2 hg2 hfy_nz hid hzeros

end TwoExp
end MultiVarMod
end MachLib
