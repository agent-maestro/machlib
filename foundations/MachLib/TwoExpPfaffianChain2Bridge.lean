import MachLib.TwoExpPfaffianDescent
import MachLib.ChainExp2NoZeros
import MachLib.ChainExp2ExplicitTool
import MachLib.PfaffianGeneralBridge

/-!
# Canonical chain-2 predicate bridge

`ChainExp2NoZeros` proves an unconditional finite zero-count theorem for
`chain2Fn p`, i.e. functions over the canonical `IterExpChain 2`. This file
packages that solved island into the predicate-count shape consumed by the
two-exp Pfaffian descent layer.

This is intentionally narrower than the general exp-chain SDR frontier: it
applies only to the canonical chain-2 wrapper `chain2Fn`.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.ChainExp2Bound
open MachLib.ChainExp2NoZeros

private theorem flatMap_arc_pair_zeros_length_chain2 (s : List RepresentedCurveArc) :
    ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
      (s.flatMap (fun arc => arc.zeros)).length := by
  induction s with
  | nil => rfl
  | cons arc rest ih =>
      simp [ih]

/-- A predicate system represented by a polynomial over the canonical
chain-2 function wrapper `chain2Fn`. This is the solved chain-2 analogue of
`PfaffianPredicateSystem`, specialized to `IterExpChain 2`. -/
structure Chain2PredicateSystem (A B : Real) (P : Real → Prop) where
  poly : MultiPoly 2
  nonzero : ∃ z, A < z ∧ z < B ∧ (chain2Fn poly).eval z ≠ 0
  predicate_zero : ∀ z, A < z → z < B → P z → (chain2Fn poly).eval z = 0

/-- Lightweight rank for a canonical chain-2 predicate system. -/
noncomputable def Chain2PredicateSystem.rank {A B : Real} {P : Real → Prop}
    (sys : Chain2PredicateSystem A B P) : Nat :=
  MultiPoly.totalDegree sys.poly

/-- View a canonical chain-2 predicate system as a generic Pfaffian predicate
system over the normalized iterated-exponential chain. The normalized chain
has the same eval functions as `IterExpChain 2`, but its relations are in
the syntactic `IsExpChain` form expected by the generic Pfaffian interface. -/
noncomputable def pfaffianPredicateSystem_of_chain2
    (A B : Real) (P : Real → Prop)
    (sys : Chain2PredicateSystem A B P) :
    PfaffianPredicateSystem A B P :=
  { K := 0,
    chain := IterExpChainNorm 2,
    poly := sys.poly,
    isExp := IterExpChainNorm_isExp 2,
    coherent := IterExpChainNorm_coh 2 A B,
    positive := IterExpChainNorm_pos 2 A B,
    nonzero := by
      simpa [chain2Fn, pfaffianChainFn, IterExpChainNorm] using sys.nonzero,
    predicate_zero := by
      intro z hA hB hP
      simpa [chain2Fn, pfaffianChainFn, IterExpChainNorm] using
        sys.predicate_zero z hA hB hP }

/-- The generic Pfaffian rank of the normalized-chain view agrees with the
lightweight chain-2 rank. -/
theorem pfaffianPredicateSystem_of_chain2_rank
    (A B : Real) (P : Real → Prop)
    (sys : Chain2PredicateSystem A B P) :
    (pfaffianPredicateSystem_of_chain2 A B P sys).rank = sys.rank :=
  by simp [PfaffianPredicateSystem.rank, Chain2PredicateSystem.rank,
    pfaffianPredicateSystem_of_chain2]

/-- Explicit predicate-list bound from the unconditional canonical chain-2
Khovanskii theorem. -/
theorem chain2_predicate_count_bound
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (p : MultiPoly 2)
    (hne : ∃ z, A < z ∧ z < B ∧ (chain2Fn p).eval z ≠ 0)
    (hpred : ∀ z, A < z → z < B → P z → (chain2Fn p).eval z = 0)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ P z) :
    ∃ N : Nat, zeros.length ≤ N := by
  obtain ⟨N, hN⟩ := chain2_khovanskii_bound_unconditional p A B hab hne
  refine ⟨N, hN zeros hnd ?_⟩
  intro z hzmem
  obtain ⟨hza, hzb, hPz⟩ := hz z hzmem
  exact ⟨hza, hzb, hpred z hza hzb hPz⟩

/-- Predicate-count shape from the unconditional canonical chain-2
Khovanskii theorem. -/
theorem chain2_predicate_count
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (p : MultiPoly 2)
    (hne : ∃ z, A < z ∧ z < B ∧ (chain2Fn p).eval z ≠ 0)
    (hpred : ∀ z, A < z → z < B → P z → (chain2Fn p).eval z = 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) → zeros.length ≤ N := by
  obtain ⟨N, hN⟩ := chain2_khovanskii_bound_unconditional p A B hab hne
  refine ⟨N, ?_⟩
  intro zeros hnd hz
  exact hN zeros hnd (fun z hzmem => by
    obtain ⟨hza, hzb, hPz⟩ := hz z hzmem
    exact ⟨hza, hzb, hpred z hza hzb hPz⟩)

/-- Explicit predicate-list bound for a canonical chain-2 predicate system. -/
theorem count_of_chain2_predicate_system_bound
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : Chain2PredicateSystem A B P)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ P z) :
    ∃ N : Nat, zeros.length ≤ N :=
  chain2_predicate_count_bound A B hab P sys.poly sys.nonzero
    sys.predicate_zero zeros hnd hz

/-- Count shape for a canonical chain-2 predicate system. -/
theorem count_of_chain2_predicate_system
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : Chain2PredicateSystem A B P) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) → zeros.length ≤ N :=
  chain2_predicate_count A B hab P sys.poly sys.nonzero sys.predicate_zero

/-- Explicit syntactic predicate-list bound for a canonical chain-2 predicate
system. The bound is `ChainExp2NoZeros.khovBound sys.poly`, computed from
polynomial degrees only. -/
theorem count_of_chain2_predicate_system_khovBound
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : Chain2PredicateSystem A B P)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ P z) :
    zeros.length ≤ ChainExp2NoZeros.khovBound sys.poly := by
  exact chain2_khovanskii_bound_syntactic sys.poly A B hab sys.nonzero zeros hnd
    (fun z hzmem => by
      obtain ⟨hA, hB, hP⟩ := hz z hzmem
      exact ⟨hA, hB, sys.predicate_zero z hA hB hP⟩)

/-- The canonical chain-2 predicate count can be packaged with its explicit
syntactic `ChainExp2NoZeros.khovBound`. -/
theorem count_of_chain2_predicate_system_khovBound_packaged
    (A B : Real) (hab : A < B)
    (P : Real → Prop)
    (sys : Chain2PredicateSystem A B P) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, A < z ∧ z < B ∧ P z) →
      zeros.length ≤ ChainExp2NoZeros.khovBound sys.poly :=
  fun zeros hnd hz =>
    count_of_chain2_predicate_system_khovBound A B hab P sys zeros hnd hz

/-- The pair of canonical chain-2 predicate systems needed for a two-exp
descent certificate: one for the restricted Jacobian predicate and one for
the separator predicate. -/
structure Chain2LowerSystem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  jacobian :
    Chain2PredicateSystem A B
      (restrictedJacobianPred F G M c yExpr expXExpr expYExpr)
  separator : Chain2PredicateSystem A B sep

/-- View a canonical chain-2 lower system as a generic two-exp lower system.
This forgets the sharper chain-2 syntactic bounds, but lets the solved
chain-2 island feed APIs that consume `TwoExpLowerSystem`. -/
noncomputable def lowerSystem_of_chain2_lowerSystem
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep :=
  { jacobian := pfaffianPredicateSystem_of_chain2 A B
      (restrictedJacobianPred F G M c yExpr expXExpr expYExpr)
      lower.jacobian,
    separator := pfaffianPredicateSystem_of_chain2 A B sep lower.separator }

/-- The generic lower-system Jacobian rank agrees with the chain-2
Jacobian rank. -/
theorem lowerSystem_of_chain2_lowerSystem_jacobianRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    (lowerSystem_of_chain2_lowerSystem F G A B M c yExpr expXExpr expYExpr sep
      lower).jacobianRank = lower.jacobian.rank :=
  by simp [TwoExpLowerSystem.jacobianRank, lowerSystem_of_chain2_lowerSystem,
    pfaffianPredicateSystem_of_chain2_rank]

/-- The generic lower-system separator rank agrees with the chain-2
separator rank. -/
theorem lowerSystem_of_chain2_lowerSystem_separatorRank
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    (lowerSystem_of_chain2_lowerSystem F G A B M c yExpr expXExpr expYExpr sep
      lower).separatorRank = lower.separator.rank :=
  by simp [TwoExpLowerSystem.separatorRank, lowerSystem_of_chain2_lowerSystem,
    pfaffianPredicateSystem_of_chain2_rank]

/-- Rank pair for a canonical chain-2 lower system. -/
noncomputable def Chain2LowerSystem.rankPair
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    Nat × Nat :=
  (lower.jacobian.rank, lower.separator.rank)

/-- The explicit syntactic bounds carried by a canonical chain-2 lower
system: separator/critical count first, Jacobian count second. -/
noncomputable def Chain2LowerSystem.khovBoundPair
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    Nat × Nat :=
  (ChainExp2NoZeros.khovBound lower.separator.poly,
    ChainExp2NoZeros.khovBound lower.jacobian.poly)

/-- Explicit Jacobian-count bound from a canonical chain-2 lower system. -/
theorem jacobian_count_of_chain2_lower_system_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧
      restrictedJacobianPred F G M c yExpr expXExpr expYExpr z) :
    zeros.length ≤ ChainExp2NoZeros.khovBound lower.jacobian.poly :=
  count_of_chain2_predicate_system_khovBound A B hAB
    (restrictedJacobianPred F G M c yExpr expXExpr expYExpr)
    lower.jacobian zeros hnd hz

/-- Explicit separator-count bound from a canonical chain-2 lower system. -/
theorem separator_count_of_chain2_lower_system_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ sep z) :
    zeros.length ≤ ChainExp2NoZeros.khovBound lower.separator.poly :=
  count_of_chain2_predicate_system_khovBound A B hAB sep
    lower.separator zeros hnd hz

/-- A canonical chain-2 lower system yields the descent certificate consumed
by the two-exp Khovanskii-Rolle layer. -/
theorem descentCertificate_of_chain2_lower_system
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  { jacobianCount := count_of_chain2_predicate_system A B hAB
      (restrictedJacobianPred F G M c yExpr expXExpr expYExpr)
      lower.jacobian,
    separatorCount := count_of_chain2_predicate_system A B hAB
      sep lower.separator }

/-- Local curve consumer for a canonical chain-2 lower system. -/
theorem khovanskii_rolle_curve_of_chain2_lower_system
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
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
    (descentCertificate_of_chain2_lower_system F G A B hAB M c yExpr expXExpr expYExpr
      sep lower)
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Local curve consumer with the explicit chain-2 syntactic Jacobian bound. -/
theorem khovanskii_rolle_curve_of_chain2_lower_system_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
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
    zeros_g.length ≤ ChainExp2NoZeros.khovBound lower.jacobian.poly + 1 := by
  exact khovanskii_rolle_count_curve
    (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G)
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G))
    yc a b hab hf2 hg2 hfy_nz hid
    (ChainExp2NoZeros.khovBound lower.jacobian.poly)
    (fun zeros_J hnd hJlocal =>
      jacobian_count_of_chain2_lower_system_khovBound F G A B hAB M c yExpr expXExpr
        expYExpr sep lower zeros_J hnd (fun z hzmem => by
          obtain ⟨hza, hzb, hJac⟩ := hJlocal z hzmem
          obtain ⟨hA, hB⟩ := hsub z hza hzb
          exact ⟨hA, hB, hJac⟩))
    zeros_g hzeros_nd hzeros

/-- Full global consumer for a canonical chain-2 lower system. -/
theorem khovanskii_rolle_full_of_chain2_lower_system
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
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
    (descentCertificate_of_chain2_lower_system F G A B hAB M c yExpr expXExpr expYExpr
      sep lower)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Full global consumer with explicit chain-2 syntactic separator and
Jacobian bounds. -/
theorem khovanskii_rolle_full_of_chain2_lower_system_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
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
      (ChainExp2NoZeros.khovBound lower.separator.poly + 1) *
        (ChainExp2NoZeros.khovBound lower.jacobian.poly + 1) := by
  have harcRich :
      ∀ arc ∈ (hd :: s),
        arc.zeros.length ≤ ChainExp2NoZeros.khovBound lower.jacobian.poly + 1 := by
    intro arc harcmem
    exact khovanskii_rolle_curve_of_chain2_lower_system_khovBound
      F G A B hAB M c yExpr expXExpr expYExpr sep lower arc.yc arc.lo arc.hi
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
    (ChainExp2NoZeros.khovBound lower.separator.poly)
    (ChainExp2NoZeros.khovBound lower.jacobian.poly)
    (fun ss hnd hss =>
      separator_count_of_chain2_lower_system_khovBound F G A B hAB M c yExpr expXExpr
        expYExpr sep lower ss hnd (fun x hx => hss x hx))
    (hd.rep, hd.zeros) (s.map (fun arc => (arc.rep, arc.zeros))) hchainPairs ?_
  · have htail :
        ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
          (s.flatMap (fun arc => arc.zeros)).length :=
        flatMap_arc_pair_zeros_length_chain2 s
    simpa [htail] using hglobal
  · intro pair hpairmem
    cases hpairmem with
    | head =>
        exact harcRich hd (List.mem_cons_self _ _)
    | tail _ hp =>
        obtain ⟨arc, harcmem, hpair⟩ := List.mem_map.mp hp
        cases hpair
        exact harcRich arc (List.mem_cons_of_mem _ harcmem)

/-- Single-arc consumer for a canonical chain-2 lower system. -/
theorem khovanskii_rolle_single_of_chain2_lower_system
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
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
    (descentCertificate_of_chain2_lower_system F G A B hAB M c yExpr expXExpr expYExpr
      sep lower)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Single-arc consumer with explicit chain-2 syntactic separator and
Jacobian bounds. -/
theorem khovanskii_rolle_single_of_chain2_lower_system_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
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
      (ChainExp2NoZeros.khovBound lower.separator.poly + 1) *
        (ChainExp2NoZeros.khovBound lower.jacobian.poly + 1) := by
  have hglobal := khovanskii_rolle_full_of_chain2_lower_system_khovBound
    F G A B hAB M c yExpr expXExpr expYExpr sep lower arc [] trivial
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

/-- A reusable package for the solved canonical chain-2 descent island:
the interval proof, the lower predicate systems, and the computable
syntactic bounds derived from their polynomials. -/
structure Chain2DescentPackage
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  interval_nonempty : A < B
  lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep

/-- Certificate view of a canonical chain-2 descent package. -/
theorem Chain2DescentPackage.certificate
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_chain2_lower_system F G A B pkg.interval_nonempty M c
    yExpr expXExpr expYExpr sep pkg.lower

/-- Generic lower-system view of a canonical chain-2 descent package. -/
noncomputable def Chain2DescentPackage.genericLower
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpLowerSystem F G A B M c yExpr expXExpr expYExpr sep :=
  lowerSystem_of_chain2_lowerSystem F G A B M c yExpr expXExpr expYExpr sep pkg.lower

/-- The generic lower-system view preserves the package's chain-2 Jacobian
rank. -/
theorem Chain2DescentPackage.genericLower_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.genericLower.jacobianRank = pkg.lower.jacobian.rank :=
  by simp [Chain2DescentPackage.genericLower,
    lowerSystem_of_chain2_lowerSystem_jacobianRank]

/-- The generic lower-system view preserves the package's chain-2 separator
rank. -/
theorem Chain2DescentPackage.genericLower_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.genericLower.separatorRank = pkg.lower.separator.rank :=
  by simp [Chain2DescentPackage.genericLower,
    lowerSystem_of_chain2_lowerSystem_separatorRank]

/-- Certificate view obtained by first forgetting the package to the generic
`TwoExpLowerSystem` interface. This is less sharp than the direct chain-2
certificate, but it is useful for consumers already written against generic
lower systems. -/
theorem Chain2DescentPackage.genericCertificate
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_lower_system F G A B pkg.interval_nonempty M c
    yExpr expXExpr expYExpr sep pkg.genericLower

/-- A canonical chain-2 package yields the compiled-rank obligation once its
generic lower-system ranks are identified with the compiled child ranks. -/
noncomputable def Chain2DescentPackage.compiledRankObligation
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  compiledWitnessRankObligation_of_lowerSystem F G A B M c yExpr expXExpr expYExpr sep
    pkg.genericLower hJrank hSrank

/-- Variant of `compiledRankObligation` stated in terms of the original
chain-2 component ranks. -/
noncomputable def Chain2DescentPackage.compiledRankObligation_of_chain2Ranks
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  pkg.compiledRankObligation
    (by
      rw [pkg.genericLower_jacobianRank]
      exact hJrank)
    (by
      rw [pkg.genericLower_separatorRank]
      exact hSrank)

/-- Ranked-lower-system view of a canonical chain-2 package, once the
caller supplies the source rank and strict descent proofs for the generic
lower-system ranks. This is the honest handoff point into the recursive
descent vocabulary. -/
noncomputable def Chain2DescentPackage.rankedLower
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (sourceRank : Nat)
    (hJrank : pkg.genericLower.jacobianRank < sourceRank)
    (hSrank : pkg.genericLower.separatorRank < sourceRank) :
    TwoExpRankedLowerSystem F G A B M c yExpr expXExpr expYExpr sep :=
  { lower := pkg.genericLower,
    sourceRank := sourceRank,
    jacobianRank := pkg.genericLower.jacobianRank,
    separatorRank := pkg.genericLower.separatorRank,
    jacobian_descends := hJrank,
    separator_descends := hSrank }

/-- The ranked-lower view stores the package's generic lower system. -/
theorem Chain2DescentPackage.rankedLower_lower
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (sourceRank : Nat)
    (hJrank : pkg.genericLower.jacobianRank < sourceRank)
    (hSrank : pkg.genericLower.separatorRank < sourceRank) :
    (pkg.rankedLower sourceRank hJrank hSrank).lower = pkg.genericLower :=
  rfl

/-- Descent-result view of a canonical chain-2 package for an existing
source problem, once the caller supplies strict descent proofs. -/
noncomputable def Chain2DescentPackage.descentResult
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank) :
    TwoExpDescentResult F G A B M c yExpr expXExpr expYExpr sep problem :=
  descentResult_of_lowerSystem F G A B M c yExpr expXExpr expYExpr sep problem
    pkg.genericLower hJrank hSrank

/-- The descent-result view stores the package's generic lower system. -/
theorem Chain2DescentPackage.descentResult_lower
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank) :
    (pkg.descentResult problem hJrank hSrank).lower = pkg.genericLower :=
  rfl

/-- Solved-descent view of a canonical chain-2 package for an existing
source problem, once positivity of the source rank and strict child-rank
descent are supplied. -/
noncomputable def Chain2DescentPackage.solvedDescent
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  { problem := problem,
    positive_rank := hposRank,
    result := pkg.descentResult problem hJrank hSrank }

/-- The solved-descent view stores the supplied source problem. -/
theorem Chain2DescentPackage.solvedDescent_problem
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank) :
    (pkg.solvedDescent problem hposRank hJrank hSrank).problem = problem :=
  rfl

/-- Certificate view obtained from the package's solved-descent wrapper. -/
theorem Chain2DescentPackage.certificate_of_solvedDescent
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedDescent problem hposRank hJrank hSrank)

/-- Recover the standard compiled-rank obligation from the solved-descent
view of a canonical chain-2 package. This uses the generic solved-descent
route rather than the direct lower-system route. -/
noncomputable def Chain2DescentPackage.compiledRankObligation_of_solvedDescent
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank)
    (hsource :
      problem.sourceRank =
        twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  compiledRankObligation_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedDescent problem hposRank hJrank hSrank) hsource

/-- The solved-descent compiled-rank route stores the package's generic
Jacobian rank. -/
theorem Chain2DescentPackage.compiledRankObligation_of_solvedDescent_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank)
    (hsource :
      problem.sourceRank =
        twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation_of_solvedDescent problem hposRank hJrank hSrank
      hsource).jacobianRank = pkg.genericLower.jacobianRank :=
  rfl

/-- The solved-descent compiled-rank route stores the package's generic
separator rank. -/
theorem Chain2DescentPackage.compiledRankObligation_of_solvedDescent_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank)
    (hsource :
      problem.sourceRank =
        twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation_of_solvedDescent problem hposRank hJrank hSrank
      hsource).separatorRank = pkg.genericLower.separatorRank :=
  rfl

/-- Explicit separator bound carried by a canonical chain-2 descent package. -/
noncomputable def Chain2DescentPackage.separatorBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) : Nat :=
  ChainExp2NoZeros.khovBound pkg.lower.separator.poly

/-- Explicit Jacobian bound carried by a canonical chain-2 descent package. -/
noncomputable def Chain2DescentPackage.jacobianBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) : Nat :=
  ChainExp2NoZeros.khovBound pkg.lower.jacobian.poly

/-- Explicit global two-exp bound carried by a canonical chain-2 descent
package. -/
noncomputable def Chain2DescentPackage.globalBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) : Nat :=
  (pkg.separatorBound + 1) * (pkg.jacobianBound + 1)

/-- The package's explicit bound pair agrees with the lower-system bound
pair. -/
theorem Chain2DescentPackage.boundPair_eq
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    (pkg.separatorBound, pkg.jacobianBound) = pkg.lower.khovBoundPair :=
  rfl

/-- The package's global bound is exactly the KR product of the lower-system
bound pair. -/
theorem Chain2DescentPackage.globalBound_eq_boundPair
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.globalBound =
      (pkg.lower.khovBoundPair.1 + 1) * (pkg.lower.khovBoundPair.2 + 1) :=
  rfl

/-- Package-level Jacobian count bound. -/
theorem Chain2DescentPackage.jacobian_count_khovBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧
      restrictedJacobianPred F G M c yExpr expXExpr expYExpr z) :
    zeros.length ≤ pkg.jacobianBound := by
  simpa [Chain2DescentPackage.jacobianBound]
    using jacobian_count_of_chain2_lower_system_khovBound
      F G A B pkg.interval_nonempty M c yExpr expXExpr expYExpr sep
      pkg.lower zeros hnd hz

/-- Package-level separator count bound. -/
theorem Chain2DescentPackage.separator_count_khovBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ sep z) :
    zeros.length ≤ pkg.separatorBound := by
  simpa [Chain2DescentPackage.separatorBound]
    using separator_count_of_chain2_lower_system_khovBound
      F G A B pkg.interval_nonempty M c yExpr expXExpr expYExpr sep
      pkg.lower zeros hnd hz

/-- A certificate together with the explicit chain-2 bounds that justify its
two lower counts. This keeps the count-shaped certificate available while
also exposing the computable syntactic ceilings. -/
structure Chain2BoundedDescentCertificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  certificate : TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep
  jacobianBound : Nat
  separatorBound : Nat
  jacobianCount :
    ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, A < z ∧ z < B ∧
        restrictedJacobianPred F G M c yExpr expXExpr expYExpr z) →
      zeros_J.length ≤ jacobianBound
  separatorCount :
    ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, A < s ∧ s < B ∧ sep s) → ss.length ≤ separatorBound

/-- Bound pair carried by a bounded chain-2 certificate:
separator/critical count first, Jacobian count second. -/
noncomputable def Chain2BoundedDescentCertificate.boundPair
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep) :
    Nat × Nat :=
  (bc.separatorBound, bc.jacobianBound)

/-- The global KR product bound carried by a bounded chain-2 certificate. -/
noncomputable def Chain2BoundedDescentCertificate.globalBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep) :
    Nat :=
  (bc.separatorBound + 1) * (bc.jacobianBound + 1)

/-- The bounded certificate's global bound is the KR product of its bound
pair. -/
theorem Chain2BoundedDescentCertificate.globalBound_eq_boundPair
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep) :
    bc.globalBound = (bc.boundPair.1 + 1) * (bc.boundPair.2 + 1) :=
  rfl

/-- Local curve consumer for a bounded chain-2 certificate. -/
theorem khovanskii_rolle_curve_of_chain2_boundedCertificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
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
    zeros_g.length ≤ bc.jacobianBound + 1 := by
  exact khovanskii_rolle_count_curve
    (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G)
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G))
    (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G))
    yc a b hab hf2 hg2 hfy_nz hid bc.jacobianBound
    (fun zeros_J hnd hJlocal =>
      bc.jacobianCount zeros_J hnd (fun z hzmem => by
        obtain ⟨hza, hzb, hJac⟩ := hJlocal z hzmem
        obtain ⟨hA, hB⟩ := hsub z hza hzb
        exact ⟨hA, hB, hJac⟩))
    zeros_g hzeros_nd hzeros

/-- Full global consumer for a bounded chain-2 certificate. This is the
certificate-only version of the package-level explicit bound theorem. -/
theorem khovanskii_rolle_full_of_chain2_boundedCertificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
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
    ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ bc.globalBound := by
  have harcRich :
      ∀ arc ∈ (hd :: s), arc.zeros.length ≤ bc.jacobianBound + 1 := by
    intro arc harcmem
    exact khovanskii_rolle_count_curve
      (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G)
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G))
      arc.yc arc.lo arc.hi (hinside arc harcmem).2.1
      (hf2 arc harcmem) (hg2 arc harcmem) (hfy_nz arc harcmem) (hid arc harcmem)
      bc.jacobianBound
      (fun zeros_J hnd hJlocal =>
        bc.jacobianCount zeros_J hnd (fun z hzmem => by
          obtain ⟨hzlo, hzhi, hJac⟩ := hJlocal z hzmem
          exact ⟨lt_trans_ax (hinside arc harcmem).1 hzlo,
            lt_trans_ax hzhi (hinside arc harcmem).2.2, hJac⟩))
      arc.zeros (hzeros_nd arc harcmem) (hzeros arc harcmem)
  have hchainPairs : ChainSep (fun x => A < x ∧ x < B ∧ sep x) (hd.rep, hd.zeros).1
      ((s.map (fun arc => (arc.rep, arc.zeros))).map (fun pair => pair.1)) := by
    simpa [List.map_map] using hchain
  have hglobal := khovanskii_rolle_full (fun x => A < x ∧ x < B ∧ sep x)
    bc.separatorBound bc.jacobianBound
    (fun ss hnd hss => bc.separatorCount ss hnd (fun x hx => hss x hx))
    (hd.rep, hd.zeros) (s.map (fun arc => (arc.rep, arc.zeros))) hchainPairs ?_
  · have htail :
        ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
          (s.flatMap (fun arc => arc.zeros)).length :=
        flatMap_arc_pair_zeros_length_chain2 s
    simpa [Chain2BoundedDescentCertificate.globalBound, htail] using hglobal
  · intro pair hpairmem
    cases hpairmem with
    | head =>
        exact harcRich hd (List.mem_cons_self _ _)
    | tail _ hp =>
        obtain ⟨arc, harcmem, hpair⟩ := List.mem_map.mp hp
        cases hpair
        exact harcRich arc (List.mem_cons_of_mem _ harcmem)

/-- Single-arc consumer for a bounded chain-2 certificate. -/
theorem khovanskii_rolle_single_of_chain2_boundedCertificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
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
    arc.zeros.length ≤ bc.globalBound := by
  have hglobal := khovanskii_rolle_full_of_chain2_boundedCertificate
    F G A B M c yExpr expXExpr expYExpr sep bc arc [] trivial
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

/-- Bundle a chain-2 descent package as a bounded certificate with the
package's explicit syntactic bounds. -/
noncomputable def Chain2DescentPackage.boundedCertificate
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  { certificate := pkg.certificate,
    jacobianBound := pkg.jacobianBound,
    separatorBound := pkg.separatorBound,
    jacobianCount := pkg.jacobian_count_khovBound,
    separatorCount := pkg.separator_count_khovBound }

/-- The bounded certificate produced from a package carries the package's
direct chain-2 certificate. -/
theorem Chain2DescentPackage.boundedCertificate_certificate
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.boundedCertificate.certificate = pkg.certificate :=
  rfl

/-- The bounded certificate produced from a package carries the package's
bound pair. -/
theorem Chain2DescentPackage.boundedCertificate_boundPair
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.boundedCertificate.boundPair = (pkg.separatorBound, pkg.jacobianBound) :=
  rfl

/-- The bounded certificate produced from a package carries the package's
global bound. -/
theorem Chain2DescentPackage.boundedCertificate_globalBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.boundedCertificate.globalBound = pkg.globalBound :=
  rfl

/-- Package-level local curve consumer with the package's explicit Jacobian
bound. -/
theorem khovanskii_rolle_curve_of_chain2_descentPackage_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
    zeros_g.length ≤ pkg.jacobianBound + 1 := by
  simpa [Chain2DescentPackage.jacobianBound]
    using khovanskii_rolle_curve_of_chain2_lower_system_khovBound
      F G A B pkg.interval_nonempty M c yExpr expXExpr expYExpr sep pkg.lower
      yc a b hab hsub hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros

/-- Package-level full global consumer with the package's own explicit
syntactic bound. -/
theorem khovanskii_rolle_full_of_chain2_descentPackage_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
    ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ pkg.globalBound := by
  simpa [Chain2DescentPackage.globalBound,
    Chain2DescentPackage.separatorBound, Chain2DescentPackage.jacobianBound]
    using khovanskii_rolle_full_of_chain2_lower_system_khovBound
      F G A B pkg.interval_nonempty M c yExpr expXExpr expYExpr sep pkg.lower
      hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Package-level single-arc consumer with the package's explicit global
bound. -/
theorem khovanskii_rolle_single_of_chain2_descentPackage_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
    arc.zeros.length ≤ pkg.globalBound := by
  simpa [Chain2DescentPackage.globalBound,
    Chain2DescentPackage.separatorBound, Chain2DescentPackage.jacobianBound]
    using khovanskii_rolle_single_of_chain2_lower_system_khovBound
      F G A B pkg.interval_nonempty M c yExpr expXExpr expYExpr sep pkg.lower
      arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

end TwoExp
end MultiVarMod
end MachLib
