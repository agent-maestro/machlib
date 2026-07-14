import MachLib.TwoExpPfaffianRepresentation

/-!
# Descent certificates for the two-exponential Khovanskii-Rolle assembly

The bivariate Pfaffian bridge now produces both lower-level counts needed by
the global two-exp engine:

* zeros of the restricted Jacobian;
* separators/critical points, usually restricted `F_y = 0`.

This file names that pair as a certificate. The point is to isolate the
remaining deep mathematical input: a genuine Khovanskii/Pfaffian descent
only has to construct one of these certificates for the next lower system.
Once it does, the already-formalized KR/arc-count machinery consumes it.
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

/-- The restricted Jacobian predicate associated to bivariate syntax and a
chosen one-variable arc representation. -/
def restrictedJacobianPred
    (F G : TwoExpBivarExpr)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) (z : Real) : Prop :=
  PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z *
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z -
    PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z *
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z = 0

/-- Syntactic size of a one-variable Pfaffian representation expression.
This is not the final Khovanskii complexity measure; it is a stable
formula-dependent component that can feed a later rank. -/
def PfaffianRepExpr.complexity {n : Nat} : PfaffianRepExpr n → Nat
  | PfaffianRepExpr.const _ => 1
  | PfaffianRepExpr.varX => 1
  | PfaffianRepExpr.varY _ => 1
  | PfaffianRepExpr.add e₁ e₂ => 1 + complexity e₁ + complexity e₂
  | PfaffianRepExpr.sub e₁ e₂ => 1 + complexity e₁ + complexity e₂
  | PfaffianRepExpr.mul e₁ e₂ => 1 + complexity e₁ + complexity e₂

/-- Syntactic size of a bivariate two-exp expression. This is the source
formula component of the lightweight rank below. -/
def TwoExpBivarExpr.complexity : TwoExpBivarExpr → Nat
  | TwoExpBivarExpr.const _ => 1
  | TwoExpBivarExpr.varX => 1
  | TwoExpBivarExpr.varY => 1
  | TwoExpBivarExpr.expX => 1
  | TwoExpBivarExpr.expY => 1
  | TwoExpBivarExpr.add e₁ e₂ => 1 + complexity e₁ + complexity e₂
  | TwoExpBivarExpr.sub e₁ e₂ => 1 + complexity e₁ + complexity e₂
  | TwoExpBivarExpr.mul e₁ e₂ => 1 + complexity e₁ + complexity e₂

/-- A lightweight, source-tied rank for a bivariate two-exp descent problem.

It combines the arc-chain size, formula sizes, arc-representation sizes, and
the total degrees of the compiled lower witnesses already used by the
current bridge. The leading `succ` makes the rank positive by construction.

This is deliberately a *rank interface*, not the final Khovanskii theorem:
the hard future work is to prove that the true lower systems produced by
Pfaffian descent have strictly smaller rank. -/
noncomputable def twoExpCompiledSourceRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) : Nat :=
  Nat.succ
    (M +
      TwoExpBivarExpr.complexity F +
      TwoExpBivarExpr.complexity G +
      PfaffianRepExpr.complexity yExpr +
      PfaffianRepExpr.complexity expXExpr +
      PfaffianRepExpr.complexity expYExpr +
      MultiPoly.totalDegree
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G) +
      MultiPoly.totalDegree
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F)))

/-- The compiled source rank is always in the positive-rank branch required
by the descent solver contract. -/
theorem twoExpCompiledSourceRank_pos
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) :
    0 < twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr :=
  Nat.succ_pos _

/-- The rank-decrease obligations for the lightweight compiled source rank.

This is intentionally separated from the construction of lower Pfaffian
systems. The future hard descent lemmas should produce this object from a
real complexity argument; examples can use simple witnesses while the
interface settles. -/
structure TwoExpCompiledRankObligation
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) where
  jacobianRank : Nat
  separatorRank : Nat
  jacobian_descends :
    jacobianRank < twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr
  separator_descends :
    separatorRank < twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr

/-- Rank of the restricted Jacobian lower witness used by the current
bivariate bridge: chain parameter plus total degree of the compiled
Jacobian polynomial. -/
noncomputable def twoExpCompiledJacobianChildRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) : Nat :=
  M + MultiPoly.totalDegree
    (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)

/-- Rank of the separator lower witness used by the current bivariate
bridge: chain parameter plus total degree of the compiled restricted
`F_y` polynomial. -/
noncomputable def twoExpCompiledSeparatorChildRank
    (F : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) : Nat :=
  M + MultiPoly.totalDegree
    (PfaffianRepExpr.compilePoly c A B
      (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))

/-- The compiled Jacobian child rank lies below the lightweight compiled
source rank. This is not the deep Khovanskii descent theorem; it verifies
that the direct bridge's lower witness rank is compatible with the current
source-rank bookkeeping. -/
theorem twoExpCompiledJacobianChildRank_lt_source
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) :
    twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr <
      twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr := by
  unfold twoExpCompiledJacobianChildRank twoExpCompiledSourceRank
  omega

/-- The compiled separator child rank lies below the lightweight compiled
source rank. -/
theorem twoExpCompiledSeparatorChildRank_lt_source
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) :
    twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr <
      twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr := by
  unfold twoExpCompiledSeparatorChildRank twoExpCompiledSourceRank
  omega

/-- Rank obligation using the actual compiled lower-witness ranks from the
current bivariate bridge. -/
noncomputable def compiledWitnessRankObligation
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  { jacobianRank := twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr,
    separatorRank := twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr,
    jacobian_descends := twoExpCompiledJacobianChildRank_lt_source
      F G A B M c yExpr expXExpr expYExpr,
    separator_descends := twoExpCompiledSeparatorChildRank_lt_source
      F G A B M c yExpr expXExpr expYExpr }

/-- Trivial child-rank witness for examples whose lower systems are already
constructed directly. It does not prove the future Khovanskii decrease; it
only packages that `0` lies below the positive compiled source rank. -/
def zeroChildCompiledRankObligation
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  { jacobianRank := 0,
    separatorRank := 0,
    jacobian_descends := twoExpCompiledSourceRank_pos F G A B M c yExpr expXExpr expYExpr,
    separator_descends := twoExpCompiledSourceRank_pos F G A B M c yExpr expXExpr expYExpr }

/-- The zero-child compiled-rank obligation assigns rank `0` to the
Jacobian child. -/
theorem zeroChildCompiledRankObligation_jacobianRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) :
    (zeroChildCompiledRankObligation F G A B M c yExpr expXExpr expYExpr).jacobianRank = 0 :=
  rfl

/-- The zero-child compiled-rank obligation assigns rank `0` to the
separator child. -/
theorem zeroChildCompiledRankObligation_separatorRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)) :
    (zeroChildCompiledRankObligation F G A B M c yExpr expXExpr expYExpr).separatorRank = 0 :=
  rfl

/-- A concrete lower-level one-variable Pfaffian predicate system on `(A,B)`.

This is the next layer down from `TwoExpDescentCertificate`: instead of
storing a finished count, it stores the Pfaffian chain/polynomial witness and
the implication from the target predicate to vanishing of that witness. The
general Pfaffian zero-count bridge turns this into a count. -/
structure PfaffianPredicateSystem (A B : Real) (P : Real → Prop) where
  K : Nat
  chain : PfaffianChain (K + 2)
  poly : MultiPoly (K + 2)
  isExp : IsExpChain chain
  coherent : chain.IsCoherentOn A B
  positive : ∀ z, A < z → z < B → ∀ i : Fin (K + 2), 0 < chain.evals i z
  nonzero : ∃ z, A < z ∧ z < B ∧ (pfaffianChainFn chain poly).eval z ≠ 0
  predicate_zero : ∀ z, A < z → z < B → P z → (pfaffianChainFn chain poly).eval z = 0

/-- Lightweight rank of a concrete one-variable lower Pfaffian predicate
system: chain parameter plus total degree of its witness polynomial. -/
noncomputable def PfaffianPredicateSystem.rank {A B : Real} {P : Real → Prop}
    (sys : PfaffianPredicateSystem A B P) : Nat :=
  sys.K + MultiPoly.totalDegree sys.poly

/-- A lower-level Pfaffian predicate system produces the list-count shape
consumed by the two-exp descent certificate. -/
theorem count_of_predicate_system (A B : Real) (hab : A < B)
    (P : Real → Prop) (sys : PfaffianPredicateSystem A B P) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) → zeros.length ≤ N :=
  pfaffian_predicate_count_bridge A B hab sys.K sys.chain sys.poly
    sys.isExp sys.coherent sys.positive sys.nonzero P sys.predicate_zero

/-- The pair of lower-level Pfaffian systems needed for two-exp descent:
one for the restricted Jacobian predicate and one for the separator
predicate. A genuine future Khovanskii descent construction should target
this structure. -/
structure TwoExpLowerSystem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  jacobian :
    PfaffianPredicateSystem A B
      (restrictedJacobianPred F G M c yExpr expXExpr expYExpr)
  separator : PfaffianPredicateSystem A B sep

/-- Rank of the Jacobian lower predicate system. -/
noncomputable def TwoExpLowerSystem.jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (sys : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) : Nat :=
  sys.jacobian.rank

/-- Rank of the separator lower predicate system. -/
noncomputable def TwoExpLowerSystem.separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (sys : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) : Nat :=
  sys.separator.rank

/-- A lower system whose component ranks are the compiled witness ranks
produces the compiled witness rank obligation. This separates the rank
calculation from the concrete construction of the lower systems. -/
noncomputable def compiledWitnessRankObligation_of_lowerSystem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (sys : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      sys.jacobianRank = twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      sys.separatorRank = twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  { jacobianRank := sys.jacobianRank,
    separatorRank := sys.separatorRank,
    jacobian_descends := by
      rw [hJrank]
      exact twoExpCompiledJacobianChildRank_lt_source F G A B M c yExpr expXExpr expYExpr,
    separator_descends := by
      rw [hSrank]
      exact twoExpCompiledSeparatorChildRank_lt_source F G A B M c yExpr expXExpr expYExpr }

/-- A lower system together with the measure-decrease facts expected from a
genuine Khovanskii/Pfaffian descent construction.

The ranks are intentionally abstract `Nat`s. Existing concrete bridge data
can provide trivial witness ranks; the future deep theorem should replace
those with the real complexity measure and strict decrease proofs. -/
structure TwoExpRankedLowerSystem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep
  sourceRank : Nat
  jacobianRank : Nat
  separatorRank : Nat
  jacobian_descends : jacobianRank < sourceRank
  separator_descends : separatorRank < sourceRank

/-- The source problem for one two-exp Pfaffian descent step.

This names the data whose lower systems must be produced: a bivariate
two-exp pair, an arc representation, the Pfaffian witnesses for that
representation, a separator predicate, and the abstract source rank that
future genuine Khovanskii descent will decrease. -/
structure TwoExpDescentProblem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  interval_nonempty : A < B
  isExp : IsExpChain c
  coherent : c.IsCoherentOn A B
  positive : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z
  jacobian_nonzero : ∃ z, A < z ∧ z < B ∧
    (pfaffianChainFn c
      (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0
  separator_nonzero : ∃ z, A < z ∧ z < B ∧
    (pfaffianChainFn c
      (PfaffianRepExpr.compilePoly c A B
        (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0
  separator_zero : ∀ z, A < z → z < B → sep z →
    PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0
  sourceRank : Nat

/-- A solved one-step descent problem: both lower Pfaffian systems are
constructed, and each carries a strict rank decrease from the source
problem. This is the construction-shaped frontier for the future recursive
descent theorem. -/
structure TwoExpDescentResult
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep) where
  lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep
  jacobianRank : Nat
  separatorRank : Nat
  jacobian_descends : jacobianRank < problem.sourceRank
  separator_descends : separatorRank < problem.sourceRank

/-- A solver for the genuinely-open Pfaffian descent step.

This is the theorem-shaped frontier: given any positive-rank source problem,
produce lower Pfaffian systems for the restricted Jacobian and separator,
with both child ranks strictly below the source rank. The current library
can consume such a solver immediately; proving one uniformly is the deep
Khovanskii/Pfaffian descent input. -/
structure TwoExpDescentSolver where
  solve :
    ∀ (F G : TwoExpBivarExpr)
      (A B : Real)
      (M : Nat) (c : PfaffianChain (M + 2))
      (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
      (sep : Real → Prop),
      ∀ problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep,
        0 < problem.sourceRank →
        TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem

/-- A concrete solved source descent, without claiming to solve every
possible source problem. This is the right packaging for examples and
specialized constructions: a source problem, proof that it lies in the
positive-rank branch, and the lower systems with strict rank descent. -/
structure TwoExpSolvedDescent
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep
  positive_rank : 0 < problem.sourceRank
  result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem

/-- A universal descent solver specializes to a concrete solved descent for
any positive-rank source problem. -/
def solvedDescent_of_solver
    (solver : TwoExpDescentSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  { problem := problem,
    positive_rank := hposRank,
    result := solver.solve F G A B M c yExpr expXExpr expYExpr sep problem hposRank }

/-- Build a descent result from an already-constructed lower system whose
own witness-polynomial ranks descend from the source problem. This is the
generic constructor that future descent theorems should feed. -/
noncomputable def descentResult_of_lowerSystem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank : lower.jacobianRank < problem.sourceRank)
    (hSrank : lower.separatorRank < problem.sourceRank) :
    TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem :=
  { lower := lower,
    jacobianRank := lower.jacobianRank,
    separatorRank := lower.separatorRank,
    jacobian_descends := hJrank,
    separator_descends := hSrank }

/-- Build a solved descent from an already-constructed lower system and
rank-decrease proofs. -/
noncomputable def solvedDescent_of_lowerSystem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank : lower.jacobianRank < problem.sourceRank)
    (hSrank : lower.separatorRank < problem.sourceRank) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  { problem := problem,
    positive_rank := hposRank,
    result := descentResult_of_lowerSystem F G A B M c yExpr expXExpr expYExpr sep
      problem lower hJrank hSrank }

/-- The lower-system constructor stores the Jacobian rank of the supplied
lower system. -/
theorem descentResult_of_lowerSystem_jacobianRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank : lower.jacobianRank < problem.sourceRank)
    (hSrank : lower.separatorRank < problem.sourceRank) :
    (descentResult_of_lowerSystem F G A B M c yExpr expXExpr expYExpr sep
      problem lower hJrank hSrank).jacobianRank = lower.jacobianRank :=
  rfl

/-- The lower-system constructor stores the separator rank of the supplied
lower system. -/
theorem descentResult_of_lowerSystem_separatorRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (lower : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank : lower.jacobianRank < problem.sourceRank)
    (hSrank : lower.separatorRank < problem.sourceRank) :
    (descentResult_of_lowerSystem F G A B M c yExpr expXExpr expYExpr sep
      problem lower hJrank hSrank).separatorRank = lower.separatorRank :=
  rfl

/-- Recover the packaged compiled-rank obligation from a descent result whose
source problem uses the compiled source rank. -/
def compiledRankObligation_of_descent_result
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hsource :
      problem.sourceRank = twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr)
    (result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  { jacobianRank := result.jacobianRank,
    separatorRank := result.separatorRank,
    jacobian_descends := by
      rw [← hsource]
      exact result.jacobian_descends,
    separator_descends := by
      rw [← hsource]
      exact result.separator_descends }

/-- Recover the packaged compiled-rank obligation from a solved descent whose
source problem uses the compiled source rank. -/
def compiledRankObligation_of_solved_descent
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (hsource :
      solved.problem.sourceRank =
        twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  compiledRankObligation_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
    solved.problem hsource solved.result

/-- Forget a source-problem/result pair to the older ranked-lower-system
interface. -/
def rankedLowerSystem_of_descent_result
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem) :
    TwoExpRankedLowerSystem F G A B M c yExpr expXExpr expYExpr sep :=
  { lower := result.lower,
    sourceRank := problem.sourceRank,
    jacobianRank := result.jacobianRank,
    separatorRank := result.separatorRank,
    jacobian_descends := result.jacobian_descends,
    separator_descends := result.separator_descends }

/-- The two lower-level counts required by the global two-exp
Khovanskii-Rolle assembly on an outer interval `(A,B)`.

This is deliberately count-shaped, not construction-shaped. A future
Pfaffian descent theorem should produce this from lower-complexity systems;
the existing bivariate Pfaffian representation bridge already produces it
when a concrete restricted chain/polynomial witness is supplied. -/
structure TwoExpDescentCertificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  jacobianCount :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, A < z ∧ z < B ∧
        PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z *
          PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z -
        PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z *
          PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z = 0) →
      zeros_J.length ≤ N
  separatorCount :
    ∃ Ncrit : Nat, ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, A < s ∧ s < B ∧ sep s) → ss.length ≤ Ncrit

/-- A pair of concrete lower-level Pfaffian systems yields the two-exp
descent certificate. This is the formal bridge from “descent produced lower
systems” to “the KR/arc-count engine has its lower counts.” -/
theorem descentCertificate_of_lower_system
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (sys : TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  { jacobianCount := count_of_predicate_system A B hAB
      (restrictedJacobianPred F G M c yExpr expXExpr expYExpr) sys.jacobian,
    separatorCount := count_of_predicate_system A B hAB sep sys.separator }

/-- A ranked lower system also yields the descent certificate; the rank
fields are retained as the proof obligations for the eventual recursive
descent theorem, while this consumer only needs the underlying lower systems. -/
theorem descentCertificate_of_ranked_lower_system
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (sys : TwoExpRankedLowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_system F G A B hAB M c yExpr expXExpr expYExpr sep sys.lower

/-- A solved descent problem yields the count-shaped certificate consumed by
the existing KR/arc-count machinery. -/
theorem descentCertificate_of_descent_result
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_ranked_lower_system F G A B problem.interval_nonempty M c
    yExpr expXExpr expYExpr sep
    (rankedLowerSystem_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
      problem result)

/-- A positive-rank source problem plus a descent solver yields the
count-shaped certificate consumed by the existing KR/arc-count machinery. -/
theorem descentCertificate_of_solver
    (solver : TwoExpDescentSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_descent_result F G A B M c yExpr expXExpr expYExpr sep problem
    (solver.solve F G A B M c yExpr expXExpr expYExpr sep problem hposRank)

/-- A concrete solved descent yields the count-shaped certificate consumed
by the existing KR/arc-count machinery. -/
theorem descentCertificate_of_solved_descent
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
    solved.problem solved.result

/-- The existing bivariate Pfaffian representation data forms a concrete
two-exp lower system: the restricted Jacobian polynomial handles the
Jacobian predicate, and the restricted formal `F_y` polynomial handles the
separator predicate. -/
noncomputable def lowerSystem_of_bivar_pfaffian
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep :=
  { jacobian :=
      { K := M,
        chain := c,
        poly := TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G,
        isExp := hexp,
        coherent := hcoh,
        positive := hpos,
        nonzero := hneJ,
        predicate_zero := by
          intro z hA hB hJ
          unfold restrictedJacobianPred at hJ
          unfold TwoExpBivarExpr.restrictedJacobianPoly
          have hrep := (PfaffianRepExpr.compileJacobian c A B
            (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F)
            (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F)
            (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G)
            (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G)).eval_eq z hA hB
          unfold PfaffianRepExpr.compileJacobianPoly
          rw [hrep]
          exact hJ },
    separator :=
      { K := M,
        chain := c,
        poly := PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F),
        isExp := hexp,
        coherent := hcoh,
        positive := hpos,
        nonzero := hneS,
        predicate_zero := by
          intro z hA hB hsep
          unfold PfaffianRepExpr.compilePoly
          rw [(PfaffianRepExpr.compile c A B
            (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F)).eval_eq z hA hB]
          exact hsep_zero z hA hB hsep } }

/-- The Jacobian component of the direct bivariate lower system has the
compiled Jacobian child rank. -/
theorem lowerSystem_of_bivar_pfaffian_jacobianRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
      hexp hcoh hpos hneJ hneS sep hsep_zero).jacobianRank =
      twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr :=
  rfl

/-- The separator component of the direct bivariate lower system has the
compiled separator child rank. -/
theorem lowerSystem_of_bivar_pfaffian_separatorRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
      hexp hcoh hpos hneJ hneS sep hsep_zero).separatorRank =
      twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr :=
  rfl

/-- The direct bivariate lower system produces the compiled witness rank
obligation via the actual ranks of its lower predicate-system witnesses. -/
noncomputable def compiledWitnessRankObligation_of_bivar_lowerSystem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  compiledWitnessRankObligation_of_lowerSystem F G A B M c yExpr expXExpr expYExpr sep
    (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
      hexp hcoh hpos hneJ hneS sep hsep_zero)
    (lowerSystem_of_bivar_pfaffian_jacobianRank F G A B M c yExpr expXExpr expYExpr
      hexp hcoh hpos hneJ hneS sep hsep_zero)
    (lowerSystem_of_bivar_pfaffian_separatorRank F G A B M c yExpr expXExpr expYExpr
      hexp hcoh hpos hneJ hneS sep hsep_zero)

/-- The same bivariate Pfaffian lower system, annotated with abstract rank
data and strict descent proofs. This is the shape future genuine descent
constructions should target. -/
noncomputable def rankedLowerSystem_of_bivar_pfaffian
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (sourceRank jacobianRank separatorRank : Nat)
    (hJrank : jacobianRank < sourceRank)
    (hSrank : separatorRank < sourceRank) :
    TwoExpRankedLowerSystem F G A B M c yExpr expXExpr expYExpr sep :=
  { lower := lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
      hexp hcoh hpos hneJ hneS sep hsep_zero,
    sourceRank := sourceRank,
    jacobianRank := jacobianRank,
    separatorRank := separatorRank,
    jacobian_descends := hJrank,
    separator_descends := hSrank }

/-- The same bivariate Pfaffian construction, now as a solved descent
problem. The caller supplies the source problem and the child ranks; the
concrete lower systems come from the current representation bridge. -/
noncomputable def descentResult_of_bivar_pfaffian
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (jacobianRank separatorRank : Nat)
    (hJrank : jacobianRank < problem.sourceRank)
    (hSrank : separatorRank < problem.sourceRank) :
    TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem :=
  { lower :=
      lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
        problem.isExp problem.coherent problem.positive
        problem.jacobian_nonzero problem.separator_nonzero sep problem.separator_zero,
    jacobianRank := jacobianRank,
    separatorRank := separatorRank,
    jacobian_descends := hJrank,
    separator_descends := hSrank }

/-- Bivariate Pfaffian descent result whose child ranks are taken from the
actual lower-system witnesses. -/
noncomputable def descentResult_of_bivar_pfaffian_lowerSystemRanks
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
        problem.isExp problem.coherent problem.positive problem.jacobian_nonzero
        problem.separator_nonzero sep problem.separator_zero).jacobianRank < problem.sourceRank)
    (hSrank :
      (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
        problem.isExp problem.coherent problem.positive problem.jacobian_nonzero
        problem.separator_nonzero sep problem.separator_zero).separatorRank < problem.sourceRank) :
    TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem :=
  descentResult_of_lowerSystem F G A B M c yExpr expXExpr expYExpr sep problem
    (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
      problem.isExp problem.coherent problem.positive problem.jacobian_nonzero
      problem.separator_nonzero sep problem.separator_zero)
    hJrank hSrank

/-- Solved bivariate Pfaffian descent whose child ranks are taken from the
actual lower-system witnesses. -/
noncomputable def solvedDescent_of_bivar_pfaffian_lowerSystemRanks
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank :
      (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
        problem.isExp problem.coherent problem.positive problem.jacobian_nonzero
        problem.separator_nonzero sep problem.separator_zero).jacobianRank < problem.sourceRank)
    (hSrank :
      (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
        problem.isExp problem.coherent problem.positive problem.jacobian_nonzero
        problem.separator_nonzero sep problem.separator_zero).separatorRank < problem.sourceRank) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  { problem := problem,
    positive_rank := hposRank,
    result := descentResult_of_bivar_pfaffian_lowerSystemRanks F G A B M c
      yExpr expXExpr expYExpr sep problem hJrank hSrank }

/-- One-shot packaging of the current bivariate Pfaffian bridge as a
concrete solved descent. This is the convenient constructor for examples:
the caller supplies the source witnesses and rank-decrease facts, and gets
the full source/problem/result bundle. -/
noncomputable def solvedDescent_of_bivar_pfaffian
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (sourceRank jacobianRank separatorRank : Nat)
    (hSourceRank : 0 < sourceRank)
    (hJrank : jacobianRank < sourceRank)
    (hSrank : separatorRank < sourceRank) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  let problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep :=
    { interval_nonempty := hAB,
      isExp := hexp,
      coherent := hcoh,
      positive := hpos,
      jacobian_nonzero := hneJ,
      separator_nonzero := hneS,
      separator_zero := hsep_zero,
      sourceRank := sourceRank }
  { problem := problem,
    positive_rank := hSourceRank,
    result := descentResult_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr sep
      problem jacobianRank separatorRank hJrank hSrank }

/-- One-shot bivariate Pfaffian solved descent using the lightweight
compiled source rank as the source rank. The caller still supplies the child
ranks and proves they descend from this computed source rank. -/
noncomputable def solvedDescent_of_bivar_pfaffian_compiledRank
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (jacobianRank separatorRank : Nat)
    (hJrank :
      jacobianRank < twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      separatorRank < twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  solvedDescent_of_bivar_pfaffian F G A B hAB M c yExpr expXExpr expYExpr
    hexp hcoh hpos hneJ hneS sep hsep_zero
    (twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr)
    jacobianRank separatorRank
    (twoExpCompiledSourceRank_pos F G A B M c yExpr expXExpr expYExpr)
    hJrank hSrank

/-- One-shot bivariate Pfaffian solved descent using a packaged compiled-rank
obligation. This is the preferred example-facing constructor because it
separates lower-system witnesses from rank-decrease witnesses. -/
noncomputable def solvedDescent_of_bivar_pfaffian_compiledRank_obligation
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (rankObligation :
      TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  solvedDescent_of_bivar_pfaffian_compiledRank F G A B hAB M c yExpr expXExpr expYExpr
    hexp hcoh hpos hneJ hneS sep hsep_zero
    rankObligation.jacobianRank rankObligation.separatorRank
    rankObligation.jacobian_descends rankObligation.separator_descends

/-- The compiled-rank constructor stores the computed source rank in the
source problem. -/
theorem solvedDescent_of_bivar_pfaffian_compiledRank_sourceRank
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (rankObligation :
      TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr) :
    (solvedDescent_of_bivar_pfaffian_compiledRank_obligation F G A B hAB M c
      yExpr expXExpr expYExpr hexp hcoh hpos hneJ hneS sep hsep_zero
      rankObligation).problem.sourceRank =
      twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr :=
  rfl

/-- Recovering the compiled-rank obligation from the compiled-rank
constructor preserves the child ranks supplied to the constructor. -/
theorem compiledRankObligation_of_bivar_pfaffian_compiledRank_jacobianRank
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (rankObligation :
      TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr) :
    (compiledRankObligation_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
      (solvedDescent_of_bivar_pfaffian_compiledRank_obligation F G A B hAB M c
        yExpr expXExpr expYExpr hexp hcoh hpos hneJ hneS sep hsep_zero rankObligation)
      (solvedDescent_of_bivar_pfaffian_compiledRank_sourceRank F G A B hAB M c
        yExpr expXExpr expYExpr hexp hcoh hpos hneJ hneS sep hsep_zero rankObligation)
      ).jacobianRank = rankObligation.jacobianRank :=
  rfl

/-- Recovering the compiled-rank obligation from the compiled-rank
constructor preserves the separator child rank supplied to the constructor. -/
theorem compiledRankObligation_of_bivar_pfaffian_compiledRank_separatorRank
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (rankObligation :
      TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr) :
    (compiledRankObligation_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
      (solvedDescent_of_bivar_pfaffian_compiledRank_obligation F G A B hAB M c
        yExpr expXExpr expYExpr hexp hcoh hpos hneJ hneS sep hsep_zero rankObligation)
      (solvedDescent_of_bivar_pfaffian_compiledRank_sourceRank F G A B hAB M c
        yExpr expXExpr expYExpr hexp hcoh hpos hneJ hneS sep hsep_zero rankObligation)
      ).separatorRank = rankObligation.separatorRank :=
  rfl

/-- The current bivariate Pfaffian bridge produces a descent certificate.
This packages the two lower-level bridge theorems into the exact contract
that the global KR/arc-count assembly consumes. -/
theorem descentCertificate_of_bivar_pfaffian
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_system F G A B hAB M c yExpr expXExpr expYExpr sep
    (lowerSystem_of_bivar_pfaffian F G A B M c yExpr expXExpr expYExpr
      hexp hcoh hpos hneJ hneS sep hsep_zero)

/-- Local curve consumer for a two-exp descent certificate. Only the
Jacobian-count field is used here; the separator-count field is for global
arc assembly. This isolates the core Khovanskii-Rolle step on one
parametrized curve. -/
theorem khovanskii_rolle_curve_of_descent_certificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (cert : TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
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
      zeros_g.length ≤ N + 1 := by
  obtain ⟨N, hJ⟩ := cert.jacobianCount
  refine ⟨N, ?_⟩
  exact khovanskii_rolle_count_curve
    (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G)
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G))
    yc a b hab hf2 hg2 hfy_nz hid N
    (fun zeros_J hnd hJlocal =>
      hJ zeros_J hnd (fun z hzmem => by
        obtain ⟨hza, hzb, hJac⟩ := hJlocal z hzmem
        obtain ⟨hA, hB⟩ := hsub z hza hzb
        exact ⟨hA, hB, hJac⟩))

/-- A descent certificate drives the full global two-exp assembly. This is
the clean consumer theorem for the remaining deep descent input: once the two
lower-level counts are packaged as a `TwoExpDescentCertificate`, the rest is
formal KR plus the combinatorial arc count. -/
theorem khovanskii_rolle_full_of_descent_certificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (cert : TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
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
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨N, hJ⟩ := cert.jacobianCount
  obtain ⟨Ncrit, hNcrit_interval⟩ := cert.separatorCount
  have harcRich : ∀ arc ∈ (hd :: s), arc.zeros.length ≤ N + 1 := by
    intro arc harcmem
    have hcurve := khovanskii_rolle_count_curve
      (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G)
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G))
      arc.yc arc.lo arc.hi
      (hinside arc harcmem).2.1
      (hf2 arc harcmem) (hg2 arc harcmem) (hfy_nz arc harcmem) (hid arc harcmem)
      N
      (fun zeros_J hnd hJlocal =>
        hJ zeros_J hnd (fun z hzmem => by
          obtain ⟨hzlo, hzhi, hJac⟩ := hJlocal z hzmem
          have hA : A < z := lt_trans_ax (hinside arc harcmem).1 hzlo
          have hB : z < B := lt_trans_ax hzhi (hinside arc harcmem).2.2
          exact ⟨hA, hB, hJac⟩))
    exact hcurve arc.zeros (hzeros_nd arc harcmem) (hzeros arc harcmem)
  refine ⟨Ncrit, N, ?_⟩
  have hchainPairs : ChainSep (fun x => A < x ∧ x < B ∧ sep x) (hd.rep, hd.zeros).1
      ((s.map (fun arc => (arc.rep, arc.zeros))).map (fun pair => pair.1)) := by
    simpa [List.map_map] using hchain
  have hglobal := khovanskii_rolle_full (fun x => A < x ∧ x < B ∧ sep x) Ncrit N
    (fun ss hnd hss => hNcrit_interval ss hnd (fun x hx => hss x hx))
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

/-- A descent certificate can be combined with a sharper externally supplied
separator count. This keeps the certificate's Jacobian-count field, but lets
examples replace the certificate's separator-count field when they know a
better separator bound directly. -/
theorem khovanskii_rolle_full_of_descent_certificate_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (cert : TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
    (Ncrit : Nat)
    (hNcrit_interval : ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, A < s ∧ s < B ∧ sep s) → ss.length ≤ Ncrit)
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
    ∃ N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨N, hJ⟩ := cert.jacobianCount
  have harcRich : ∀ arc ∈ (hd :: s), arc.zeros.length ≤ N + 1 := by
    intro arc harcmem
    have hcurve := khovanskii_rolle_count_curve
      (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G)
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G))
      arc.yc arc.lo arc.hi
      (hinside arc harcmem).2.1
      (hf2 arc harcmem) (hg2 arc harcmem) (hfy_nz arc harcmem) (hid arc harcmem)
      N
      (fun zeros_J hnd hJlocal =>
        hJ zeros_J hnd (fun z hzmem => by
          obtain ⟨hzlo, hzhi, hJac⟩ := hJlocal z hzmem
          have hA : A < z := lt_trans_ax (hinside arc harcmem).1 hzlo
          have hB : z < B := lt_trans_ax hzhi (hinside arc harcmem).2.2
          exact ⟨hA, hB, hJac⟩))
    exact hcurve arc.zeros (hzeros_nd arc harcmem) (hzeros arc harcmem)
  refine ⟨N, ?_⟩
  have hchainPairs : ChainSep (fun x => A < x ∧ x < B ∧ sep x) (hd.rep, hd.zeros).1
      ((s.map (fun arc => (arc.rep, arc.zeros))).map (fun pair => pair.1)) := by
    simpa [List.map_map] using hchain
  have hglobal := khovanskii_rolle_full (fun x => A < x ∧ x < B ∧ sep x) Ncrit N
    (fun ss hnd hss => hNcrit_interval ss hnd (fun x hx => hss x hx))
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

/-- Single-arc consumer for a two-exp descent certificate. This is the
minimal surface a concrete one-arc example needs once the lower-level descent
certificate has been produced. -/
theorem khovanskii_rolle_single_of_descent_certificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (cert : TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
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
    ∃ Ncrit N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨Ncrit, N, hN⟩ := khovanskii_rolle_full_of_descent_certificate
    F G A B M c yExpr expXExpr expYExpr sep cert arc [] trivial
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
  refine ⟨Ncrit, N, ?_⟩
  simpa using hN

/-- Single-arc consumer for a descent certificate with a sharper externally
supplied separator count. -/
theorem khovanskii_rolle_single_of_descent_certificate_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (cert : TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
    (Ncrit : Nat)
    (hNcrit_interval : ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, A < s ∧ s < B ∧ sep s) → ss.length ≤ Ncrit)
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
    ∃ N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨N, hN⟩ := khovanskii_rolle_full_of_descent_certificate_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep cert Ncrit hNcrit_interval arc [] trivial
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
  refine ⟨N, ?_⟩
  simpa using hN

/-- Local curve consumer for a solved descent problem. This is the
construction-shaped version of `khovanskii_rolle_curve_of_descent_certificate`. -/
theorem khovanskii_rolle_curve_of_descent_result
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem)
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
    (descentCertificate_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
      problem result)
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Full global consumer for a solved descent problem. -/
theorem khovanskii_rolle_full_of_descent_result
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem)
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
    (descentCertificate_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
      problem result)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a solved descent problem. -/
theorem khovanskii_rolle_single_of_descent_result
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem)
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
    (descentCertificate_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
      problem result)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Full global consumer for a solved descent result with a sharper
externally supplied separator count. -/
theorem khovanskii_rolle_full_of_descent_result_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem)
    (Ncrit : Nat)
    (hNcrit_interval : ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, A < s ∧ s < B ∧ sep s) → ss.length ≤ Ncrit)
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
    ∃ N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full_of_descent_certificate_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep
    (descentCertificate_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
      problem result)
    Ncrit hNcrit_interval hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a solved descent result with a sharper externally
supplied separator count. -/
theorem khovanskii_rolle_single_of_descent_result_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (result : TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem)
    (Ncrit : Nat)
    (hNcrit_interval : ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, A < s ∧ s < B ∧ sep s) → ss.length ≤ Ncrit)
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
    ∃ N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_single_of_descent_certificate_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep
    (descentCertificate_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
      problem result)
    Ncrit hNcrit_interval arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Local curve consumer for a concrete solved descent. -/
theorem khovanskii_rolle_curve_of_solved_descent
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
    (hid : ∀ t, TwoExpBivarExpr.denote F t (yc t) = 0) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ TwoExpBivarExpr.denote G z (yc z) = 0) →
      zeros_g.length ≤ N + 1 :=
  khovanskii_rolle_curve_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
    solved.problem solved.result yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Full global consumer for a concrete solved descent. -/
theorem khovanskii_rolle_full_of_solved_descent
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
    ∃ Ncrit N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
    solved.problem solved.result hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a concrete solved descent. -/
theorem khovanskii_rolle_single_of_solved_descent
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
    ∃ Ncrit N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_single_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
    solved.problem solved.result arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Full global consumer for a concrete solved descent with a sharper
externally supplied separator count. -/
theorem khovanskii_rolle_full_of_solved_descent_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (Ncrit : Nat)
    (hNcrit_interval : ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, A < s ∧ s < B ∧ sep s) → ss.length ≤ Ncrit)
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
    ∃ N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full_of_descent_result_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep solved.problem solved.result
    Ncrit hNcrit_interval hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a concrete solved descent with a sharper
externally supplied separator count. -/
theorem khovanskii_rolle_single_of_solved_descent_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (solved : TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep)
    (Ncrit : Nat)
    (hNcrit_interval : ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, A < s ∧ s < B ∧ sep s) → ss.length ≤ Ncrit)
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
    ∃ N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_single_of_descent_result_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep solved.problem solved.result
    Ncrit hNcrit_interval arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Local curve consumer for a descent solver. This is the direct plug-in
point for the future uniform Pfaffian descent theorem. -/
theorem khovanskii_rolle_curve_of_descent_solver
    (solver : TwoExpDescentSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
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
  khovanskii_rolle_curve_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
    problem
    (solver.solve F G A B M c yExpr expXExpr expYExpr sep problem hposRank)
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Full global consumer for a descent solver. -/
theorem khovanskii_rolle_full_of_descent_solver
    (solver : TwoExpDescentSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
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
  khovanskii_rolle_full_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
    problem
    (solver.solve F G A B M c yExpr expXExpr expYExpr sep problem hposRank)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer for a descent solver. -/
theorem khovanskii_rolle_single_of_descent_solver
    (solver : TwoExpDescentSolver)
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
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
  khovanskii_rolle_single_of_descent_result F G A B M c yExpr expXExpr expYExpr sep
    problem
    (solver.solve F G A B M c yExpr expXExpr expYExpr sep problem hposRank)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

end TwoExp
end MultiVarMod
end MachLib
