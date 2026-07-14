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

/-- Source-ready chain-2 package. This extends the count/lower-system
package with exactly the source hypotheses needed to form a
`TwoExpDescentProblem` at the lightweight compiled source rank. -/
structure Chain2CompiledDescentPackage
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop) where
  package : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep
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

/-- Direct constructor for a source-ready chain-2 package from its interval,
lower systems, and source hypotheses. This avoids forcing callers to build
the nested `Chain2DescentPackage` record by hand. -/
noncomputable def Chain2CompiledDescentPackage.ofLowerSystem
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (hAB : A < B)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (isExp : IsExpChain c)
    (coherent : c.IsCoherentOn A B)
    (positive : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (jacobian_nonzero : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (separator_nonzero : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (separator_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep :=
  { package := { interval_nonempty := hAB, lower := lower },
    isExp := isExp,
    coherent := coherent,
    positive := positive,
    jacobian_nonzero := jacobian_nonzero,
    separator_nonzero := separator_nonzero,
    separator_zero := separator_zero }

/-- The direct constructor stores the supplied interval proof. -/
theorem Chain2CompiledDescentPackage.ofLowerSystem_interval_nonempty
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (hAB : A < B)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (isExp : IsExpChain c)
    (coherent : c.IsCoherentOn A B)
    (positive : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (jacobian_nonzero : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (separator_nonzero : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (separator_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    (Chain2CompiledDescentPackage.ofLowerSystem hAB lower isExp coherent positive
      jacobian_nonzero separator_nonzero separator_zero).package.interval_nonempty = hAB :=
  rfl

/-- The direct constructor stores the supplied lower system. -/
theorem Chain2CompiledDescentPackage.ofLowerSystem_lower
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (hAB : A < B)
    (lower : Chain2LowerSystem F G A B M c yExpr expXExpr expYExpr sep)
    (isExp : IsExpChain c)
    (coherent : c.IsCoherentOn A B)
    (positive : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (jacobian_nonzero : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (separator_nonzero : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (separator_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    (Chain2CompiledDescentPackage.ofLowerSystem hAB lower isExp coherent positive
      jacobian_nonzero separator_nonzero separator_zero).package.lower = lower :=
  rfl

/-- The compiled-source problem carried by a source-ready chain-2 package. -/
noncomputable def Chain2CompiledDescentPackage.sourceProblem
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep :=
  { interval_nonempty := pkg.package.interval_nonempty,
    isExp := pkg.isExp,
    coherent := pkg.coherent,
    positive := pkg.positive,
    jacobian_nonzero := pkg.jacobian_nonzero,
    separator_nonzero := pkg.separator_nonzero,
    separator_zero := pkg.separator_zero,
    sourceRank := twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr }

/-- The source-ready chain-2 package uses the lightweight compiled source
rank. -/
theorem Chain2CompiledDescentPackage.sourceProblem_sourceRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.sourceProblem.sourceRank =
      twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr :=
  rfl

/-- The compiled-source problem stores the package's interval proof. -/
theorem Chain2CompiledDescentPackage.sourceProblem_interval_nonempty
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.sourceProblem.interval_nonempty = pkg.package.interval_nonempty :=
  rfl

/-- The compiled-source problem stores the supplied exp-chain proof. -/
theorem Chain2CompiledDescentPackage.sourceProblem_isExp
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.sourceProblem.isExp = pkg.isExp :=
  rfl

/-- The compiled-source problem stores the supplied coherence proof. -/
theorem Chain2CompiledDescentPackage.sourceProblem_coherent
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.sourceProblem.coherent = pkg.coherent :=
  rfl

/-- The compiled-source problem stores the supplied positivity proof. -/
theorem Chain2CompiledDescentPackage.sourceProblem_positive
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.sourceProblem.positive = pkg.positive :=
  rfl

/-- The compiled-source problem stores the supplied Jacobian nonzero
witness. -/
theorem Chain2CompiledDescentPackage.sourceProblem_jacobian_nonzero
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.sourceProblem.jacobian_nonzero = pkg.jacobian_nonzero :=
  rfl

/-- The compiled-source problem stores the supplied separator nonzero
witness. -/
theorem Chain2CompiledDescentPackage.sourceProblem_separator_nonzero
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.sourceProblem.separator_nonzero = pkg.separator_nonzero :=
  rfl

/-- The compiled-source problem stores the supplied separator-zero bridge. -/
theorem Chain2CompiledDescentPackage.sourceProblem_separator_zero
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.sourceProblem.separator_zero = pkg.separator_zero :=
  rfl

/-- The compiled-source problem is in the positive-rank branch. -/
theorem Chain2CompiledDescentPackage.sourceProblem_positiveRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    0 < pkg.sourceProblem.sourceRank :=
  twoExpCompiledSourceRank_pos F G A B M c yExpr expXExpr expYExpr

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

/-- The direct compiled-rank obligation stores the package's generic
Jacobian child rank. -/
theorem Chain2DescentPackage.compiledRankObligation_jacobianRank
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
    (pkg.compiledRankObligation hJrank hSrank).jacobianRank = pkg.genericLower.jacobianRank :=
  rfl

/-- The direct compiled-rank obligation stores the package's generic
separator child rank. -/
theorem Chain2DescentPackage.compiledRankObligation_separatorRank
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
    (pkg.compiledRankObligation hJrank hSrank).separatorRank = pkg.genericLower.separatorRank :=
  rfl

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

/-- The chain-2-rank variant stores the original chain-2 Jacobian rank. -/
theorem Chain2DescentPackage.compiledRankObligation_of_chain2Ranks_jacobianRank
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
    (pkg.compiledRankObligation_of_chain2Ranks hJrank hSrank).jacobianRank =
      pkg.lower.jacobian.rank := by
  simp [Chain2DescentPackage.compiledRankObligation_of_chain2Ranks,
    Chain2DescentPackage.compiledRankObligation_jacobianRank,
    Chain2DescentPackage.genericLower_jacobianRank]

/-- The chain-2-rank variant stores the original chain-2 separator rank. -/
theorem Chain2DescentPackage.compiledRankObligation_of_chain2Ranks_separatorRank
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
    (pkg.compiledRankObligation_of_chain2Ranks hJrank hSrank).separatorRank =
      pkg.lower.separator.rank := by
  simp [Chain2DescentPackage.compiledRankObligation_of_chain2Ranks,
    Chain2DescentPackage.compiledRankObligation_separatorRank,
    Chain2DescentPackage.genericLower_separatorRank]

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

/-- The ranked-lower view stores the supplied source rank. -/
theorem Chain2DescentPackage.rankedLower_sourceRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (sourceRank : Nat)
    (hJrank : pkg.genericLower.jacobianRank < sourceRank)
    (hSrank : pkg.genericLower.separatorRank < sourceRank) :
    (pkg.rankedLower sourceRank hJrank hSrank).sourceRank = sourceRank :=
  rfl

/-- The ranked-lower view stores the package's generic Jacobian rank. -/
theorem Chain2DescentPackage.rankedLower_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (sourceRank : Nat)
    (hJrank : pkg.genericLower.jacobianRank < sourceRank)
    (hSrank : pkg.genericLower.separatorRank < sourceRank) :
    (pkg.rankedLower sourceRank hJrank hSrank).jacobianRank = pkg.genericLower.jacobianRank :=
  rfl

/-- The ranked-lower view stores the package's generic separator rank. -/
theorem Chain2DescentPackage.rankedLower_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (sourceRank : Nat)
    (hJrank : pkg.genericLower.jacobianRank < sourceRank)
    (hSrank : pkg.genericLower.separatorRank < sourceRank) :
    (pkg.rankedLower sourceRank hJrank hSrank).separatorRank = pkg.genericLower.separatorRank :=
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

/-- The descent-result view stores the package's generic Jacobian rank. -/
theorem Chain2DescentPackage.descentResult_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank) :
    (pkg.descentResult problem hJrank hSrank).jacobianRank = pkg.genericLower.jacobianRank :=
  rfl

/-- The descent-result view stores the package's generic separator rank. -/
theorem Chain2DescentPackage.descentResult_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank) :
    (pkg.descentResult problem hJrank hSrank).separatorRank = pkg.genericLower.separatorRank :=
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

/-- The solved-descent view stores the supplied positive-rank proof. -/
theorem Chain2DescentPackage.solvedDescent_positive_rank
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
    (pkg.solvedDescent problem hposRank hJrank hSrank).positive_rank = hposRank :=
  rfl

/-- The solved-descent view stores the package's descent-result view. -/
theorem Chain2DescentPackage.solvedDescent_result
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
    (pkg.solvedDescent problem hposRank hJrank hSrank).result =
      pkg.descentResult problem hJrank hSrank :=
  rfl

/-- Source-ready chain-2 packages produce a solved descent at the lightweight
compiled source rank once their generic lower ranks are identified with the
compiled child ranks. -/
noncomputable def Chain2CompiledDescentPackage.solvedCompiledDescent
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  pkg.package.solvedDescent pkg.sourceProblem
    pkg.sourceProblem_positiveRank
    (by
      rw [hJrank, Chain2CompiledDescentPackage.sourceProblem_sourceRank]
      exact twoExpCompiledJacobianChildRank_lt_source
        F G A B M c yExpr expXExpr expYExpr)
    (by
      rw [hSrank, Chain2CompiledDescentPackage.sourceProblem_sourceRank]
      exact twoExpCompiledSeparatorChildRank_lt_source
        F G A B M c yExpr expXExpr expYExpr)

/-- Source-ready solved descent from equalities stated for the original
chain-2 component ranks. -/
noncomputable def Chain2CompiledDescentPackage.solvedCompiledDescent_of_chain2Ranks
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpSolvedDescent F G A B M c yExpr expXExpr expYExpr sep :=
  pkg.solvedCompiledDescent
    (by
      rw [pkg.package.genericLower_jacobianRank]
      exact hJrank)
    (by
      rw [pkg.package.genericLower_separatorRank]
      exact hSrank)

/-- The chain-rank solved compiled descent stores the compiled source
problem. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_of_chain2Ranks_problem
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank).problem = pkg.sourceProblem :=
  rfl

/-- The chain-rank solved compiled descent stores the package's generic
lower system. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_of_chain2Ranks_lower
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank).result.lower =
      pkg.package.genericLower :=
  rfl

/-- The chain-rank solved compiled descent stores the original chain-2
Jacobian rank. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_of_chain2Ranks_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank).result.jacobianRank =
      pkg.package.lower.jacobian.rank := by
  rw [Chain2CompiledDescentPackage.solvedCompiledDescent_of_chain2Ranks,
    Chain2CompiledDescentPackage.solvedCompiledDescent,
    Chain2DescentPackage.solvedDescent,
    Chain2DescentPackage.descentResult_jacobianRank,
    Chain2DescentPackage.genericLower_jacobianRank]

/-- The chain-rank solved compiled descent stores the original chain-2
separator rank. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_of_chain2Ranks_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank).result.separatorRank =
      pkg.package.lower.separator.rank := by
  rw [Chain2CompiledDescentPackage.solvedCompiledDescent_of_chain2Ranks,
    Chain2CompiledDescentPackage.solvedCompiledDescent,
    Chain2DescentPackage.solvedDescent,
    Chain2DescentPackage.descentResult_separatorRank,
    Chain2DescentPackage.genericLower_separatorRank]

/-- The solved compiled descent stores the compiled source problem. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_problem
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent hJrank hSrank).problem = pkg.sourceProblem :=
  rfl

/-- The solved compiled descent stores the compiled source-rank witness. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_positive_rank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent hJrank hSrank).positive_rank =
      pkg.sourceProblem_positiveRank :=
  rfl

/-- The solved compiled descent has the lightweight compiled source rank. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_sourceRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent hJrank hSrank).problem.sourceRank =
      twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr := by
  rw [Chain2CompiledDescentPackage.solvedCompiledDescent_problem,
    Chain2CompiledDescentPackage.sourceProblem_sourceRank]

/-- The solved compiled descent stores the package's generic lower system. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_lower
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent hJrank hSrank).result.lower =
      pkg.package.genericLower :=
  rfl

/-- The solved compiled descent stores the package's generic Jacobian rank. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent hJrank hSrank).result.jacobianRank =
      pkg.package.genericLower.jacobianRank :=
  rfl

/-- The solved compiled descent's Jacobian rank is the compiled Jacobian
child rank. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_compiledJacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent hJrank hSrank).result.jacobianRank =
      twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr := by
  rw [Chain2CompiledDescentPackage.solvedCompiledDescent_jacobianRank, hJrank]

/-- The solved compiled descent stores the package's generic separator rank. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent hJrank hSrank).result.separatorRank =
      pkg.package.genericLower.separatorRank :=
  rfl

/-- The solved compiled descent's separator rank is the compiled separator
child rank. -/
theorem Chain2CompiledDescentPackage.solvedCompiledDescent_compiledSeparatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.solvedCompiledDescent hJrank hSrank).result.separatorRank =
      twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr := by
  rw [Chain2CompiledDescentPackage.solvedCompiledDescent_separatorRank, hSrank]

/-- Certificate view of a source-ready chain-2 package through its solved
compiled descent. -/
theorem Chain2CompiledDescentPackage.certificate_of_solvedCompiledDescent
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  descentCertificate_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent hJrank hSrank)

/-- Compiled-rank obligation recovered from the solved compiled descent. -/
noncomputable def Chain2CompiledDescentPackage.compiledRankObligation_of_solvedCompiledDescent
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  compiledRankObligation_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent hJrank hSrank)
    (by
      rw [Chain2CompiledDescentPackage.solvedCompiledDescent_problem]
      exact pkg.sourceProblem_sourceRank)

/-- The solved-compiled rank obligation stores the package's generic
Jacobian rank. -/
theorem Chain2CompiledDescentPackage.compiledRankObligation_of_solvedCompiledDescent_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation_of_solvedCompiledDescent hJrank hSrank).jacobianRank =
      pkg.package.genericLower.jacobianRank :=
  rfl

/-- The solved-compiled rank obligation carries the Jacobian rank-decrease
proof against the compiled source rank. -/
theorem Chain2CompiledDescentPackage.compiledRankObligation_of_solvedCompiledDescent_jacobian_descends
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation_of_solvedCompiledDescent hJrank hSrank).jacobianRank <
      twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr :=
  (pkg.compiledRankObligation_of_solvedCompiledDescent hJrank hSrank).jacobian_descends

/-- The solved-compiled rank obligation stores the package's generic
separator rank. -/
theorem Chain2CompiledDescentPackage.compiledRankObligation_of_solvedCompiledDescent_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation_of_solvedCompiledDescent hJrank hSrank).separatorRank =
      pkg.package.genericLower.separatorRank :=
  rfl

/-- The solved-compiled rank obligation carries the separator rank-decrease
proof against the compiled source rank. -/
theorem Chain2CompiledDescentPackage.compiledRankObligation_of_solvedCompiledDescent_separator_descends
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation_of_solvedCompiledDescent hJrank hSrank).separatorRank <
      twoExpCompiledSourceRank F G A B M c yExpr expXExpr expYExpr :=
  (pkg.compiledRankObligation_of_solvedCompiledDescent hJrank hSrank).separator_descends

/-- Direct compiled-rank obligation for a source-ready package, stated in
terms of its generic lower-system ranks. -/
noncomputable def Chain2CompiledDescentPackage.compiledRankObligation
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  pkg.package.compiledRankObligation hJrank hSrank

/-- Direct compiled-rank obligation for a source-ready package, stated in
terms of the original chain-2 component ranks. -/
noncomputable def Chain2CompiledDescentPackage.compiledRankObligation_of_chain2Ranks
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    TwoExpCompiledRankObligation F G A B M c yExpr expXExpr expYExpr :=
  pkg.package.compiledRankObligation_of_chain2Ranks hJrank hSrank

/-- The direct compiled-rank obligation stores the source-ready package's
generic Jacobian rank. -/
theorem Chain2CompiledDescentPackage.compiledRankObligation_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation hJrank hSrank).jacobianRank =
      pkg.package.genericLower.jacobianRank :=
  rfl

/-- The direct compiled-rank obligation stores the source-ready package's
generic separator rank. -/
theorem Chain2CompiledDescentPackage.compiledRankObligation_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation hJrank hSrank).separatorRank =
      pkg.package.genericLower.separatorRank :=
  rfl

/-- The chain-2-rank direct obligation stores the original chain-2 Jacobian
rank. -/
theorem Chain2CompiledDescentPackage.compiledRankObligation_of_chain2Ranks_jacobianRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation_of_chain2Ranks hJrank hSrank).jacobianRank =
      pkg.package.lower.jacobian.rank :=
  pkg.package.compiledRankObligation_of_chain2Ranks_jacobianRank hJrank hSrank

/-- The chain-2-rank direct obligation stores the original chain-2 separator
rank. -/
theorem Chain2CompiledDescentPackage.compiledRankObligation_of_chain2Ranks_separatorRank
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr) :
    (pkg.compiledRankObligation_of_chain2Ranks hJrank hSrank).separatorRank =
      pkg.package.lower.separator.rank :=
  pkg.package.compiledRankObligation_of_chain2Ranks_separatorRank hJrank hSrank

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

/-- Certificate view reconstructed from the explicit bounds carried by a
bounded chain-2 certificate. This does not use the stored `certificate`
field; it repackages the bounded-count fields directly into the ordinary
count-shaped certificate interface. -/
theorem Chain2BoundedDescentCertificate.certificateFromBounds
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep) :
    TwoExpDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  { jacobianCount := ⟨bc.jacobianBound, bc.jacobianCount⟩,
    separatorCount := ⟨bc.separatorBound, bc.separatorCount⟩ }

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

/-- Ordinary local curve consumer for a bounded chain-2 certificate, using
the certificate reconstructed from its explicit bounds. -/
theorem khovanskii_rolle_curve_of_chain2_boundedCertificate_certificate
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
    (hid : ∀ t, TwoExpBivarExpr.denote F t (yc t) = 0) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ TwoExpBivarExpr.denote G z (yc z) = 0) →
      zeros_g.length ≤ N + 1 :=
  khovanskii_rolle_curve_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    bc.certificateFromBounds yc a b hab hsub hf2 hg2 hfy_nz hid

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

/-- Ordinary full global consumer for a bounded chain-2 certificate, using
the certificate reconstructed from its explicit bounds. -/
theorem khovanskii_rolle_full_of_chain2_boundedCertificate_certificate
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
    ∃ Ncrit N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    bc.certificateFromBounds hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Ordinary full global consumer for a bounded chain-2 certificate with an
externally supplied separator count. This keeps the bounded certificate's
Jacobian count while allowing a sharper separator/critical bound. -/
theorem khovanskii_rolle_full_of_chain2_boundedCertificate_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
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
    F G A B M c yExpr expXExpr expYExpr sep bc.certificateFromBounds
    Ncrit hNcrit_interval hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

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

/-- Ordinary single-arc consumer for a bounded chain-2 certificate, using
the certificate reconstructed from its explicit bounds. -/
theorem khovanskii_rolle_single_of_chain2_boundedCertificate_certificate
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
    ∃ Ncrit N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_single_of_descent_certificate F G A B M c yExpr expXExpr expYExpr sep
    bc.certificateFromBounds arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Ordinary single-arc consumer for a bounded chain-2 certificate with an
externally supplied separator count. -/
theorem khovanskii_rolle_single_of_chain2_boundedCertificate_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (bc : Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep)
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
    F G A B M c yExpr expXExpr expYExpr sep bc.certificateFromBounds
    Ncrit hNcrit_interval arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

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

/-- The bounded certificate produced from a package reconstructs the same
ordinary certificate from its explicit bounds. -/
theorem Chain2DescentPackage.boundedCertificate_certificateFromBounds
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.boundedCertificate.certificateFromBounds = pkg.certificate :=
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

/-- Bounded-certificate view of a source-ready chain-2 package. -/
noncomputable def Chain2CompiledDescentPackage.boundedCertificate
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    Chain2BoundedDescentCertificate F G A B M c yExpr expXExpr expYExpr sep :=
  pkg.package.boundedCertificate

/-- Explicit separator bound carried by a source-ready chain-2 package. -/
noncomputable def Chain2CompiledDescentPackage.separatorBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) : Nat :=
  pkg.package.separatorBound

/-- Explicit Jacobian bound carried by a source-ready chain-2 package. -/
noncomputable def Chain2CompiledDescentPackage.jacobianBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) : Nat :=
  pkg.package.jacobianBound

/-- Global KR product bound carried by a source-ready chain-2 package. -/
noncomputable def Chain2CompiledDescentPackage.globalBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) : Nat :=
  pkg.package.globalBound

/-- The bounded certificate of a source-ready package is the package's
bounded certificate. -/
theorem Chain2CompiledDescentPackage.boundedCertificate_eq
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.boundedCertificate = pkg.package.boundedCertificate :=
  rfl

/-- The source-ready package carries the same bound pair as its underlying
chain-2 package. -/
theorem Chain2CompiledDescentPackage.boundPair_eq
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.boundedCertificate.boundPair = (pkg.separatorBound, pkg.jacobianBound) :=
  rfl

/-- The source-ready package's explicit bound pair agrees with the
underlying lower-system bound pair. -/
theorem Chain2CompiledDescentPackage.boundPair_eq_lower
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    (pkg.separatorBound, pkg.jacobianBound) = pkg.package.lower.khovBoundPair :=
  rfl

/-- The source-ready package's global bound is the KR product of its
separator and Jacobian bounds. -/
theorem Chain2CompiledDescentPackage.globalBound_eq
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep) :
    pkg.globalBound = (pkg.separatorBound + 1) * (pkg.jacobianBound + 1) :=
  rfl

/-- Source-ready package Jacobian count bound. -/
theorem Chain2CompiledDescentPackage.jacobian_count_khovBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧
      restrictedJacobianPred F G M c yExpr expXExpr expYExpr z) :
    zeros.length ≤ pkg.jacobianBound :=
  pkg.package.jacobian_count_khovBound zeros hnd hz

/-- Source-ready package separator count bound. -/
theorem Chain2CompiledDescentPackage.separator_count_khovBound
    {F G : TwoExpBivarExpr}
    {A B : Real}
    {M : Nat} {c : PfaffianChain (M + 2)}
    {yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2)}
    {sep : Real → Prop}
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (zeros : List Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, A < z ∧ z < B ∧ sep z) :
    zeros.length ≤ pkg.separatorBound :=
  pkg.package.separator_count_khovBound zeros hnd hz

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

/-- Package-level ordinary local curve consumer, routed through the bounded
certificate exported by the package. -/
theorem khovanskii_rolle_curve_of_chain2_descentPackage_certificate
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
    (hid : ∀ t, TwoExpBivarExpr.denote F t (yc t) = 0) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ TwoExpBivarExpr.denote G z (yc z) = 0) →
      zeros_g.length ≤ N + 1 :=
  khovanskii_rolle_curve_of_chain2_boundedCertificate_certificate
    F G A B M c yExpr expXExpr expYExpr sep pkg.boundedCertificate
    yc a b hab hsub hf2 hg2 hfy_nz hid

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

/-- Package-level ordinary full global consumer, routed through the bounded
certificate exported by the package. -/
theorem khovanskii_rolle_full_of_chain2_descentPackage_certificate
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
    ∃ Ncrit N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full_of_chain2_boundedCertificate_certificate
    F G A B M c yExpr expXExpr expYExpr sep pkg.boundedCertificate
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Package-level full global consumer with an externally supplied separator
count and the package's compiled Jacobian certificate. -/
theorem khovanskii_rolle_full_of_chain2_descentPackage_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
  khovanskii_rolle_full_of_chain2_boundedCertificate_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep pkg.boundedCertificate
    Ncrit hNcrit_interval hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

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

/-- Package-level ordinary single-arc consumer, routed through the bounded
certificate exported by the package. -/
theorem khovanskii_rolle_single_of_chain2_descentPackage_certificate
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
    ∃ Ncrit N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_single_of_chain2_boundedCertificate_certificate
    F G A B M c yExpr expXExpr expYExpr sep pkg.boundedCertificate
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Package-level single-arc consumer with an externally supplied separator
count and the package's compiled Jacobian certificate. -/
theorem khovanskii_rolle_single_of_chain2_descentPackage_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
  khovanskii_rolle_single_of_chain2_boundedCertificate_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep pkg.boundedCertificate
    Ncrit hNcrit_interval arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Package-level local curve consumer through the package's solved-descent
view. This is the construction-shaped endpoint for callers already carrying
a source descent problem and rank descent proofs. -/
theorem khovanskii_rolle_curve_of_chain2_solvedPackage
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank)
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
  khovanskii_rolle_curve_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedDescent problem hposRank hJrank hSrank)
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Package-level full global consumer through the package's solved-descent
view. -/
theorem khovanskii_rolle_full_of_chain2_solvedPackage
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank)
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
  khovanskii_rolle_full_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedDescent problem hposRank hJrank hSrank)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Package-level single-arc consumer through the package's solved-descent
view. -/
theorem khovanskii_rolle_single_of_chain2_solvedPackage
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank)
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
  khovanskii_rolle_single_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedDescent problem hposRank hJrank hSrank)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Package-level full global solved-descent consumer with an externally
supplied separator count. -/
theorem khovanskii_rolle_full_of_chain2_solvedPackage_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank)
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
  khovanskii_rolle_full_of_solved_descent_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedDescent problem hposRank hJrank hSrank)
    Ncrit hNcrit_interval hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Package-level single-arc solved-descent consumer with an externally
supplied separator count. -/
theorem khovanskii_rolle_single_of_chain2_solvedPackage_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2DescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (problem : TwoExpDescentProblem F G A B M c yExpr expXExpr expYExpr sep)
    (hposRank : 0 < problem.sourceRank)
    (hJrank : pkg.genericLower.jacobianRank < problem.sourceRank)
    (hSrank : pkg.genericLower.separatorRank < problem.sourceRank)
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
  khovanskii_rolle_single_of_solved_descent_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedDescent problem hposRank hJrank hSrank)
    Ncrit hNcrit_interval arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package local curve consumer with the underlying chain-2
package's explicit Jacobian bound. This route uses the solved chain-2 count
island directly and does not require compiled rank-identification proofs. -/
theorem khovanskii_rolle_curve_of_chain2_compiledPackage_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
    zeros_g.length ≤ pkg.jacobianBound + 1 :=
  khovanskii_rolle_curve_of_chain2_descentPackage_khovBound
    F G A B M c yExpr expXExpr expYExpr sep pkg.package
    yc a b hab hsub hf2 hg2 hfy_nz hid zeros_g hzeros_nd hzeros

/-- Source-ready package full global consumer with the underlying chain-2
package's explicit global bound. -/
theorem khovanskii_rolle_full_of_chain2_compiledPackage_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
    ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ pkg.globalBound :=
  khovanskii_rolle_full_of_chain2_descentPackage_khovBound
    F G A B M c yExpr expXExpr expYExpr sep pkg.package
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package single-arc consumer with the underlying chain-2
package's explicit global bound. -/
theorem khovanskii_rolle_single_of_chain2_compiledPackage_khovBound
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
    arc.zeros.length ≤ pkg.globalBound :=
  khovanskii_rolle_single_of_chain2_descentPackage_khovBound
    F G A B M c yExpr expXExpr expYExpr sep pkg.package
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package ordinary local curve consumer through its
underlying chain-2 package. -/
theorem khovanskii_rolle_curve_of_chain2_compiledPackage_certificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
  khovanskii_rolle_curve_of_chain2_descentPackage_certificate
    F G A B M c yExpr expXExpr expYExpr sep pkg.package
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Source-ready package ordinary full global consumer through its
underlying chain-2 package. -/
theorem khovanskii_rolle_full_of_chain2_compiledPackage_certificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
  khovanskii_rolle_full_of_chain2_descentPackage_certificate
    F G A B M c yExpr expXExpr expYExpr sep pkg.package
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package ordinary single-arc consumer through its underlying
chain-2 package. -/
theorem khovanskii_rolle_single_of_chain2_compiledPackage_certificate
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
  khovanskii_rolle_single_of_chain2_descentPackage_certificate
    F G A B M c yExpr expXExpr expYExpr sep pkg.package
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package full global consumer through its underlying
chain-2 package, with an externally supplied separator count. -/
theorem khovanskii_rolle_full_of_chain2_compiledPackage_certificate_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
  khovanskii_rolle_full_of_chain2_descentPackage_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep pkg.package
    Ncrit hNcrit_interval hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package single-arc consumer through its underlying chain-2
package, with an externally supplied separator count. -/
theorem khovanskii_rolle_single_of_chain2_compiledPackage_certificate_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
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
  khovanskii_rolle_single_of_chain2_descentPackage_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep pkg.package
    Ncrit hNcrit_interval arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package local curve consumer through the compiled solved
descent. The caller supplies only the rank-identification equalities needed
to connect the chain-2 lower ranks to the compiled child ranks. -/
theorem khovanskii_rolle_curve_of_chain2_compiledPackage
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_curve_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent hJrank hSrank)
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Source-ready package full global consumer through the compiled solved
descent. -/
theorem khovanskii_rolle_full_of_chain2_compiledPackage
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_full_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent hJrank hSrank)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package single-arc consumer through the compiled solved
descent. -/
theorem khovanskii_rolle_single_of_chain2_compiledPackage
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_single_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent hJrank hSrank)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package full global consumer through the compiled solved
descent, with an externally supplied separator count. -/
theorem khovanskii_rolle_full_of_chain2_compiledPackage_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_full_of_solved_descent_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent hJrank hSrank)
    Ncrit hNcrit_interval hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package single-arc consumer through the compiled solved
descent, with an externally supplied separator count. -/
theorem khovanskii_rolle_single_of_chain2_compiledPackage_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.genericLower.jacobianRank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.genericLower.separatorRank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_single_of_solved_descent_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent hJrank hSrank)
    Ncrit hNcrit_interval arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package local curve consumer through the compiled solved
descent, with rank identifications stated for the original chain-2 component
ranks. -/
theorem khovanskii_rolle_curve_of_chain2_compiledPackage_of_chain2Ranks
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_curve_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank)
    yc a b hab hsub hf2 hg2 hfy_nz hid

/-- Source-ready package full global consumer through the compiled solved
descent, with rank identifications stated for original chain-2 component
ranks. -/
theorem khovanskii_rolle_full_of_chain2_compiledPackage_of_chain2Ranks
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_full_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank)
    hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package single-arc consumer through the compiled solved
descent, with rank identifications stated for original chain-2 component
ranks. -/
theorem khovanskii_rolle_single_of_chain2_compiledPackage_of_chain2Ranks
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_single_of_solved_descent F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank)
    arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package full global consumer through the compiled solved
descent, with an externally supplied separator count and rank
identifications stated for original chain-2 component ranks. -/
theorem khovanskii_rolle_full_of_chain2_compiledPackage_of_chain2Ranks_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_full_of_solved_descent_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank)
    Ncrit hNcrit_interval hd s hchain hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

/-- Source-ready package single-arc consumer through the compiled solved
descent, with an externally supplied separator count and rank
identifications stated for original chain-2 component ranks. -/
theorem khovanskii_rolle_single_of_chain2_compiledPackage_of_chain2Ranks_and_separator_count
    (F G : TwoExpBivarExpr)
    (A B : Real)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (sep : Real → Prop)
    (pkg : Chain2CompiledDescentPackage F G A B M c yExpr expXExpr expYExpr sep)
    (hJrank :
      pkg.package.lower.jacobian.rank =
        twoExpCompiledJacobianChildRank F G A B M c yExpr expXExpr expYExpr)
    (hSrank :
      pkg.package.lower.separator.rank =
        twoExpCompiledSeparatorChildRank F A B M c yExpr expXExpr expYExpr)
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
  khovanskii_rolle_single_of_solved_descent_and_separator_count
    F G A B M c yExpr expXExpr expYExpr sep
    (pkg.solvedCompiledDescent_of_chain2Ranks hJrank hSrank)
    Ncrit hNcrit_interval arc hinside hzeros_nd hf2 hg2 hfy_nz hid hzeros

end TwoExp
end MultiVarMod
end MachLib
