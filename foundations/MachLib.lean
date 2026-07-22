import MachLib.Basic
import MachLib.Exp
import MachLib.Log
import MachLib.Trig
import MachLib.EML
import MachLib.EMLDomainSafety
import MachLib.EMLAtlasWitness
import MachLib.SelfMapConjugacy
import MachLib.Hyperbolic
import MachLib.FieldLemmas
import MachLib.HyperbolicId
import MachLib.HyperbolicPreservation
import MachLib.Forge
import MachLib.ForgeTest
import MachLib.Ring
import MachLib.MultiVar
import MachLib.MultiVarBezout
import MachLib.MultiVarSubst
import MachLib.MultiVarToPoly
import MachLib.MultiVarBezoutFiber
import MachLib.MultiVarCoeffY
import MachLib.MultiVarCoeffYFree
import MachLib.MultiVarEliminate
import MachLib.MultiVarResultantLinear
import MachLib.MultiVarResultantGen
import MachLib.MultiVarShift
import MachLib.MultiVarReduce
import MachLib.MultiVarReduceVanish
import MachLib.MultiVarPRS
import MachLib.MultiVarPRSYFree
import MachLib.MultiVarResultant
import MachLib.MultiVarBucket
import MachLib.MultiVarBezoutGeneral
import MachLib.MultiVarEvalAt
import MachLib.MultiVarReduceAtVanish
import MachLib.MultiVarPRSAt
import MachLib.MultiVarCoeffY3
import MachLib.MultiVarResultant3
import MachLib.MultiVarExpBridge
import MachLib.MultiVarRung1
import MachLib.MultiVarRung1Count
import MachLib.MultiVarElimCoeff
import MachLib.MultiVarElimReduce
import MachLib.MultiVarElimReduceVanish
import MachLib.MultiVarElimYFree
import MachLib.MultiVarElimPRS
import MachLib.MultiVarElimResultant
import MachLib.MultiVarElimPreserve
import MachLib.MultiVarMixedElim
import MachLib.MultiVarMixedCount
import MachLib.MultiVarMixedSolution
import MachLib.MultiVarTwoExpRolle
import MachLib.MultiVarTwoExpInstance
import MachLib.MultiVarTwoExpSum
import MachLib.MonotoneFromDeriv
import MachLib.IntermediateValue
import MachLib.MonotoneRoot
import MachLib.BivariateDeriv
import MachLib.TwoExpCurveCount
import MachLib.TwoExpCurveValidation
import MachLib.ArcCount
import MachLib.TwoExpArcCount
import MachLib.TwoExpPfaffianBridge
import MachLib.TwoExpPfaffianRepresentation
import MachLib.TwoExpPfaffianDescent
import MachLib.TwoExpPfaffianReductionWitness
import MachLib.TwoExpPfaffianExpSum
import MachLib.TwoExpPfaffianChain2Bridge
import MachLib.Sign
import MachLib.RingTest
import MachLib.PolyRing
import MachLib.PolyRingTactic
import MachLib.MPolyRing
import MachLib.Linarith
import MachLib.LinarithTest
import MachLib.Lemmas
import MachLib.Decompose
import MachLib.LinearCombination
import MachLib.Safety.TemporalFrequency
import MachLib.ProofSpine
import MachLib.PolynomialEvidence
import MachLib.MultiPoly
import MachLib.MultiPolyDropAt
import MachLib.PfaffianChain
import MachLib.PfaffianFnBound
import MachLib.AnalyticIdentityFeasibility
import MachLib.FiniteZeroPacket
import MachLib.PolynomialRootCount
import MachLib.NormalizedPolynomialRootCount
import MachLib.HighDimensional
import MachLib.SinNotInEML
import MachLib.WitnessResidualDepth1
import MachLib.WitnessResidualCancellation
import MachLib.WitnessResidualCancellationGeneral
import MachLib.WitnessResidualChainSkeleton
import MachLib.WitnessResidualDepth2Elementary
import MachLib.WitnessResidualDepth2ABConjuncts
import MachLib.WitnessResidualTargetGeneric
import MachLib.WitnessResidualNestedTargetFamily
import MachLib.WitnessResidualNestedTargetBWitness
import MachLib.WitnessResidualSimpleRightChildren
import MachLib.WitnessResidualSimpleT1Application
import MachLib.WitnessResidualBWitnessGeneralB
import MachLib.WitnessResidualBOneLevelCompound
import MachLib.WitnessResidualBChainCompound
import MachLib.EMLExplicitBoundGlue
import MachLib.EMLZeroCrossingDepth1
import MachLib.EMLZeroCrossingDepth2Compound
import MachLib.EMLZeroCrossingDomainSplit
import MachLib.EMLZeroCrossingDomainSplitGeneral
import MachLib.EMLZeroCrossingBothCompound
import MachLib.EMLZeroCrossingBothCompoundGeneral
import MachLib.EMLZeroCrossingBothCompoundDeeper
import MachLib.EMLZeroCrossingConvexT1
import MachLib.EMLZeroCrossingBothCompoundDeeperGeneral
import MachLib.EMLZeroCrossingDepth3Compound
import MachLib.WitnessResidualBoundedNonConstant
import MachLib.WitnessResidualNonMonotonic
import MachLib.WitnessResidualUnboundedBelow
import MachLib.WitnessResidualNonMonotonicClosesBelow
import MachLib.WitnessResidualStrictMonoT1
import MachLib.WitnessResidualDirectCrossingUnboundedAbove
import MachLib.WitnessResidualWrappedCrossingUnboundedBelow
import MachLib.WitnessResidualExpWrappedNonMonotonic
import MachLib.WitnessResidualExpWrappedNonMonotonicClosed
import MachLib.EMLPfaffianValidOnCrossingObstruction
import MachLib.WitnessResidualExpWrappedNonMonotonicCPositive
import MachLib.WitnessResidualTwoEqualPointsClosure
import MachLib.WitnessResidualEntireCrossingFamilyClosed
import MachLib.WitnessResidualGrowthCompetitionWitness
import MachLib.WitnessResidualQuadraticConvexity
import MachLib.WitnessResidualGrowthCompetitionDeriv
import MachLib.WitnessResidualGrowthCompetitionNumeric
import MachLib.WitnessResidualGrowthCompetitionAssembly
import MachLib.WitnessResidualGrowthCompetitionValidOn
import MachLib.WitnessResidualRightChildrenEverywherePositive
import MachLib.WitnessResidualGrowthCompetitionDeepWitness
import MachLib.WitnessResidualDeepGSignControl
import MachLib.WitnessResidualDeepDeriv
import MachLib.WitnessResidualDeepNumeric
import MachLib.WitnessResidualDeepAssembly
import MachLib.WitnessResidualConvexZeroBoundClosure
import MachLib.WitnessResidualCrossingUnbounded
import MachLib.WitnessResidualCrossingUnboundedGeneral
import MachLib.WitnessResidualCrossingUnboundedMirror
import MachLib.WitnessResidualSignNecessity
import MachLib.WitnessResidualQuantitativeBound
import MachLib.WitnessResidualRecursiveSignLift
import MachLib.WitnessResidualClosureAttempt
import MachLib.WitnessResidualNonposChainClosure
import MachLib.WitnessResidualCrossingBoundednessBridge
import MachLib.CosNotInEML
import MachLib.EMLHierarchy
import MachLib.ExpExpNotInEML1
import MachLib.ElementaryEML
import MachLib.SinNotInEMLDepth2Partial
import MachLib.SinNotInEMLDepth2Sweep
import MachLib.IteratedExpBounds
import MachLib.ThreePointEvalClosure
import MachLib.AnalyticFiniteZeros
import MachLib.AnalyticFiniteZerosReal
import MachLib.Differentiation
import MachLib.WronskianProportional
import MachLib.PfaffianLogDegenerate
import MachLib.PfaffianChainExtend
import MachLib.PfaffianChainExtendELR
import MachLib.PfaffianChainNodes
import MachLib.EMLEncoder
import MachLib.EntropyDuality
import MachLib.KLDivergence
import MachLib.SinNotInEMLDepth2FinalVcVc
import MachLib.ExpExpExpNotInEML2
import MachLib.Pfaffian
import MachLib.EMLTreeComposition
import MachLib.EMLPfaffian
import MachLib.EMLKhovanskiiConstructive
import MachLib.ExpRationalKhovanskii
import MachLib.EMLTChartKhovanskii
import MachLib.PfaffianExpRecipClass
import MachLib.PfaffianRecipStep
import MachLib.PfaffianRecipClearAt
import MachLib.PfaffianExpRecipClassW
import MachLib.PfaffianExpLogRecipClass
import MachLib.PfaffianExpLogRecipDescent
import MachLib.PfaffianExpLogStepReduce
import MachLib.PfaffianLogGeneralDegree
import MachLib.PfaffianLogCdegSpike
import MachLib.PfaffianRecipGrowthSpike
import MachLib.PfaffianRecipHtame
import MachLib.PfaffianRolleStep
import MachLib.MultiPolyCoeffEntry
import MachLib.MultiPolyCoeffDegree
import MachLib.MultiPolyPartial
import MachLib.PfaffianCTDCongrChain
import MachLib.PfaffianLogIdN
import MachLib.PfaffianLogLeadId
import MachLib.PfaffianLogWronskian
import MachLib.PfaffianExpRecipDescent
import MachLib.PfaffianExpRecipExample
import MachLib.CosNotInEMLAnyDepth
import MachLib.LambertW
import MachLib.EMLAdditionClosureFailure
import MachLib.EMLDifferentiationClosureFailure
import MachLib.InvXNotInEML
import MachLib.EMLAsymptoticClass
import MachLib.EMLOscillationBarrier
import MachLib.Asymptotics
import MachLib.EMLAsymptoticBound
import MachLib.EMLHierarchyIterExp
import MachLib.Rolle
import MachLib.SturmNonOscillation
import MachLib.KhovanskiiLemma
import MachLib.MultiPolyToPoly
import MachLib.KhovanskiiReduction
import MachLib.SingleExpKhovanskii
import MachLib.ExpPolyEffectiveBound
import MachLib.ExpPolyBridge
import MachLib.ExpPolyPfaffianEffective
import MachLib.MultiPolyCanonY
import MachLib.MultiPolyCanonYN
import MachLib.ChainExpPoly
import MachLib.IterExpChain
import MachLib.InnerKhovanskii
import MachLib.InnerKhovanskiiExp
import MachLib.ChainExp2Instance
import MachLib.ChainExp2PathC
import MachLib.ChainExp2SingleExpUnconditional
import MachLib.IterExpChainStructural
import MachLib.PfaffianExprSingleExpBridge
import MachLib.ChainExp2Unconditional
import MachLib.PfaffianExprTwoExpBridge
import MachLib.EMLDepth1Fragment
import MachLib.EMLExplicitBound
import MachLib.EMLLogArgPosBridge
import MachLib.TwoExpPfaffianSingleExpAdapter
import MachLib.InnerKhovanskiiExpWF
import MachLib.ChainExp2WFInstance
import MachLib.ChainExp2SDR
import MachLib.Tactic.LeadingCoeffY
import MachLib.FPModel
import MachLib.FixedPoint
import MachLib.FixedPointCertifier
import MachLib.Iteration
import MachLib.ErrorAlgebra
import MachLib.ErrorAlgebraTrans
import MachLib.ForwardError
import MachLib.OperatorBasisSound
import MachLib.HybridError
import MachLib.OperatorBasisTrans
import MachLib.OperatorBasisGeneral
import MachLib.DivisionError
import MachLib.OperatorClamp3
import MachLib.OperatorBasisComplete
import MachLib.VectorError
import MachLib.OperatorAdmissibility
import MachLib.TrajectoryCertified
import MachLib.ForgeBindingDemo
import MachLib.ConditionedError
import MachLib.TrigLipschitz
import MachLib.ConditionNumber
import MachLib.RippleCarry
import MachLib.BitVecMul
import MachLib.FixedPointRTL
import MachLib.BackwardError
import MachLib.ForwardBackwardKappa
import MachLib.ClosedLoopSafety
import MachLib.LyapunovSafety
import MachLib.ProbabilisticBound
import MachLib.IntervalArith
import MachLib.AffineContraction
import MachLib.Decimal
import MachLib.SignTactic
import MachLib.CostTheory
import MachLib.LexProd
import MachLib.ChainExp2Measure
import MachLib.ChainExp2Reducer
import MachLib.ExplicitBoundRank
import MachLib.ChainExp2ExplicitBound
import MachLib.ChainExp2ExplicitTrim
import MachLib.ChainExp2ExplicitABound
import MachLib.ChainExp2ExplicitLevelBudget
import MachLib.ChainExp2ExplicitFinal
import MachLib.ChainExp2ExplicitTool
import MachLib.ChainExp2ExplicitInvPhiMono
import MachLib.IterExpDepthNRankNested
import MachLib.IterExpDepthNDegreeX
import MachLib.IterExpDepthNDegreeY
import MachLib.IterExpDepthNCanonLcYBound
import MachLib.IterExpDepthNEIBase
import MachLib.IterExpDepthNEIrank
import MachLib.IterExpDepthNBudget
import MachLib.IterExpDepthNBudgetGen
import MachLib.IterExpDepthNDescentBound
import MachLib.IterExpDepthNRankRec
import MachLib.IterExpDepthNRankRecDrop
import MachLib.IterExpDepthNRankRecReduce
import MachLib.IterExpDepthNRankRec5p
import MachLib.IterExpDepthNBudgetMono
import MachLib.IterExpDepthNDegreeYTrimLift
import MachLib.IterExpDepthNTrimQDegHelpers
import MachLib.IterExpDepthNBudget5
import MachLib.IterExpDepthNStepExplicit
import MachLib.IterExpDepthNBudgetMax
import MachLib.IterExpDepthNExplicit
import MachLib.TowerSeparation
import MachLib.DiffAlgebraic
import MachLib.KhovanskiiConcrete
import MachLib.PfaffianGeneralReduce
import MachLib.PfaffianWronskianReduce
import MachLib.PfaffianExpEliminate
import MachLib.PfaffianExpTrim
import MachLib.PfaffianExpWronskian
import MachLib.PfaffianAnalytic
import MachLib.EMLEncoderAnalytic
import MachLib.EMLEncoderDescent
import MachLib.EMLBarrierBound
import MachLib.PfaffianExpHard
import MachLib.PfaffianGeneralWF
import MachLib.PfaffianExpStepMixed
import MachLib.PfaffianGeneralHnz
import MachLib.PfaffianGeneralHnzWF
import MachLib.PfaffianGeneralSingleExp
import MachLib.PfaffianGeneralSingleExpDescent
import MachLib.PfaffianGeneralBase
import MachLib.PfaffianGeneralCTDCongr
import MachLib.PfaffianGeneralSingleExpCanon
import MachLib.PfaffianGeneralBaseHnz
import MachLib.PfaffianGeneralVehExpo
import MachLib.PfaffianGeneralVehExpoConnect
import MachLib.PfaffianGeneralBound2
import MachLib.PfaffianGeneralVehExpoTower
import MachLib.PfaffianGeneralBoundPos
import MachLib.PfaffianGeneralHnzIF
import MachLib.PfaffianGeneralBoundUncond
import MachLib.PfaffianGeneralWitness
import MachLib.PfaffianGeneralBridge
import MachLib.PfaffianGeneralFormatDegree
import MachLib.PfaffianGeneralBudgetGrow
import MachLib.PfaffianGeneralDescentBoundAlpha
import MachLib.PfaffianGeneralFormat2
import MachLib.PfaffianGeneralLevelBudgetAlpha
import MachLib.PfaffianGeneralRankRecAlpha
import MachLib.PfaffianGeneralBase2Explicit
import MachLib.PfaffianGeneralBudgetN5Alpha
import MachLib.PfaffianGeneralChainRestrictDeg
import MachLib.PfaffianGeneralHnzIFDeg
import MachLib.PfaffianGeneralBudgetMaxA
import MachLib.PfaffianGeneralStepExplicit
import MachLib.PfaffianGeneralExplicit
import MachLib.ChainExp2Trim
import MachLib.ChainExp2CanonMeasure
import MachLib.ChainExp2PolyMultRolle
import MachLib.ChainExp2LcY1CTD
import MachLib.ChainExp2Descent
import MachLib.ChainExp2YPIT
import MachLib.ChainExp2CdegInv
import MachLib.CrossTargetPairs
import MachLib.PIDCapstone
import MachLib.FixedPointSat
import MachLib.CoreModel
import MachLib.EMLToC
import MachLib.EMLToCRuntime
import MachLib.CompositeRuntimeError
import MachLib.FloatRealBridge
import MachLib.AbsoluteError
import MachLib.AbsoluteBridge
import MachLib.AbsoluteFold
import MachLib.ExpLipschitz
import MachLib.TransNodes
import MachLib.AbsoluteFoldNest
import MachLib.AbsoluteFoldLocal
import MachLib.AbsoluteFoldNestMag
import MachLib.CertifyNested

/-!
# MachLib — top-level aggregator

The independent foundations for machine-native formal mathematics.

  * `MachLib.Basic`             — axiomatic ℝ (real numbers as an
                                  ordered field with Archimedean +
                                  completeness axioms exposed where
                                  needed)
  * `MachLib.Exp`               — real exponential
  * `MachLib.Log`               — real natural logarithm
  * `MachLib.Trig`              — sine, cosine, π, periodicity
  * `MachLib.EML`               — the eml(x,y) = exp(x) − log(y)
                                  primitive
  * `MachLib.EMLDomainSafety`   — tiny checked domain-safety witnesses
                                  for Monogate EML packet obligations.
  * `MachLib.SelfMapConjugacy`  — F16 self-map conjugacies (EAL/EXL,
                                  EML/EDL) ported from legacy_eml
  * `MachLib.Hyperbolic`        — sinh, cosh + ELC-form decomposition
                                  axioms (`tanh` lives in `Trig`)
  * `MachLib.Forge`             — derived lemmas for Forge-emitted
                                  kernel proofs (order, nonneg
                                  combinators); shipped 2026-05-01
                                  to ground the @verify(lean)
                                  binding chain identified in C-127
  * `MachLib.Ring`              — `mach_ring` tactic v1: closes
                                  the "linear-in-zeros" polynomial
                                  identities Forge emits for matrix
                                  cells, vector components, and lerp
                                  endpoints. Full polynomial
                                  reflection (Lagrange, four-square)
                                  is v2.
  * `MachLib.Linarith`          — `mach_positivity` + `mach_linarith`
                                  v1: closes `0 ≤ expr` / `0 < expr`
                                  via recursive structural
                                  decomposition over the Forge
                                  combinators. Fourier-Motzkin
                                  elimination for hypothesis-driven
                                  linear arithmetic is v2.
  * `MachLib.Lemmas`            — specific named lemmas filling the
                                  Forge-shape gaps in Basic / Trig
                                  / Exp (`max_le`, `exp_le_one`,
                                  `arccos_*`, `sqrt_pos`,
                                  `abs_cos_le_one`).
  * `MachLib.Safety.TemporalFrequency` — formal contract for the
                                  Phase 1 safety-verification
                                  protocol's `temporal_frequency`
                                  class. Provides
                                  `ForgeAnalyzerWitness` +
                                  `of_analyzer_witness` +
                                  `mul_bound_additive` +
                                  `add_bound_max`. Lands 2026-05-11
                                  as step 4 of 5 to close Moat 1's
                                  Phase 1 gating criterion.
  * `MachLib.ProofSpine`         — ten small checked obligations that
                                  connect EML / Forge / Explorer /
                                  CapCard surfaces to concrete MachLib
                                  artifacts.
  * `MachLib.PolynomialEvidence` — tiny polynomial AST, evaluator, and
                                  finite root evidence substrate.
  * `MachLib.AnalyticIdentityFeasibility` — tiny checked polynomial
                                  root footholds for a future analytic
                                  identity substrate; no analytic
                                  identity theorem claim.
  * `MachLib.FiniteZeroPacket`   — sample finite-zero evidence packets
                                  over the tiny polynomial AST.
  * `MachLib.PolynomialRootCount` — first degree/root-count primitives
                                  and a checked linear-factor root-count
                                  foothold.
  * `MachLib.NormalizedPolynomialRootCount` — coefficient-list normal-form
                                  scaffold and checked nonzero-constant
                                  finite-root packet.
  * `MachLib.HighDimensional`    — compile-checked theorem queue for
                                  high-dimensional EML geometry and
                                  guarded-lowering obligations; stubs only,
                                  no proof claim.

Zero Mathlib dependency. `lake build` verifies the entire library
in seconds.
-/
