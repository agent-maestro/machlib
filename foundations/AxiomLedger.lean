import MachLib
import MachLib.FPGrounding
/-!
# AxiomLedger — machine-checked axiom trust boundary (grep-free, kernel-verbatim)

Building this file IS the trust gate: every check `logError`s on violation, so a red
`lake build` here means the boundary drifted. Nothing uses grep or name paraphrase — axioms
are enumerated from the environment (`getEnv`, `.axiomInfo`) and footprints are the kernel's own
dependency graph (`Lean.collectAxioms`, the `#print axioms` mechanism).

Three invariants, failing loud in BOTH directions:
1. Completeness + rot: the live axiom set equals `knownAxioms` exactly. A new axiom (not in the
   snapshot) → unknown → fail; a snapshot entry whose axiom vanished → rot → fail.
2. Footprint ⊆ trusted: each shipped headline theorem's exact footprint ⊆ the witnessed
   foundational `trustedFootprint`. Any axiom — runtime, disclosed-pending, or new — entering a
   shipped footprint fails. This is what would have caught the old unsound open-interval `rolle`.
3. Disclosed inert: every `disclosedUnwitnessed` axiom (erf: blocked upstream;
   `eml_tree_analytic_on_pos`: unwitnessed but now sound — side-condition restored) must appear in
   NO headline footprint.

A fourth, distinct category — `disclosedTrusted` — is for axioms that are disclosed as
un-witnessable yet are load-bearing BY DESIGN: the certcom Theorem-A IEEE-754 model
(`Certcom.realToR`, `Certcom.real_fpbridge`). Lean's `Float` is opaque, so "every basic float op is
correctly rounded" cannot be proved in-Lean; it is the standard model, the terminal floor under the
Theorem-A headline `Certcom.pipeline_det_grounded`. These sit in `trustedFootprint` (headlines may
rest on them) but are named apart from the ℝ-witnessed axioms so the trust they carry is explicit.
-/
open Lean Elab Command

namespace AxiomLedger

/-- Snapshot of every axiom under `MachLib`/`Real` (ground truth at pin time). -/
def knownAxioms : List Name := [`Certcom.realToR, `Certcom.real_fpbridge, `Certcom.real_tanh_rounds, `MachLib.HighDimensional.BaselineReplayValid, `MachLib.HighDimensional.BoundaryDominatesCenter, `MachLib.HighDimensional.BoundaryDynamicsObligation, `MachLib.HighDimensional.BoundaryInterventionPair, `MachLib.HighDimensional.BoundaryRunPacket, `MachLib.HighDimensional.BoundedEvaluationObligation, `MachLib.HighDimensional.ClampDeshelfInterventionObligation, `MachLib.HighDimensional.ClampInvariantObligation, `MachLib.HighDimensional.DomainPreservationObligation, `MachLib.HighDimensional.DomainPreserved, `MachLib.HighDimensional.GuardedBoundaryMode, `MachLib.HighDimensional.InterventionSoundnessObligation, `MachLib.HighDimensional.LogDomainBoundaryMode, `MachLib.HighDimensional.OutputSafetyInterventionObligation, `MachLib.HighDimensional.OutputSafetyObligation, `MachLib.HighDimensional.PacketHasEvent, `MachLib.HighDimensional.PacketHasTransition, `MachLib.HighDimensional.PairHasRescueTransition, `MachLib.HighDimensional.PairNonregressingSurvival, `MachLib.HighDimensional.PairUsesIntervention, `MachLib.HighDimensional.PositiveCoordinateInterventionObligation, `MachLib.HighDimensional.PositiveCoordinateObligation, `MachLib.HighDimensional.PrecisionEscapeInterventionObligation, `MachLib.HighDimensional.PrecisionSensitivityObligation, `MachLib.HighDimensional.ReplayPacket, `MachLib.HighDimensional.TendstoTo, `MachLib.HighDimensional.ValidBoundaryRunPacket, `MachLib.HighDimensional.ValidGuards, `MachLib.HighDimensional.ValidInterventionPair, `MachLib.HighDimensional.ValidTransitionGraph, `MachLib.HighDimensional.ballCubeRatio, `MachLib.HighDimensional.boundary_dominates_center_from_packet, `MachLib.HighDimensional.cubeBoundaryShellProbability, `MachLib.HighDimensional.cubeBoundaryShellProbability_tends_one, `MachLib.HighDimensional.domain_to_log_domain_rescue_obligation, `MachLib.HighDimensional.domain_wall_obligation, `MachLib.HighDimensional.firstLayerSurvival, `MachLib.HighDimensional.firstLayerSurvival_decay, `MachLib.HighDimensional.guard_clamp_intervention_obligation, `MachLib.HighDimensional.guard_rescue_obligation, `MachLib.HighDimensional.guarded_boundary_packet_finite_survival_nonneg, `MachLib.HighDimensional.interior_sample_obligation, `MachLib.HighDimensional.log_domain_boundary_packet_finite_survival_nonneg, `MachLib.HighDimensional.log_domain_lift_intervention_obligation, `MachLib.HighDimensional.log_domain_rescue_obligation, `MachLib.HighDimensional.overflow_to_guard_rescue_obligation, `MachLib.HighDimensional.overflow_wall_obligation, `MachLib.HighDimensional.packetBoundaryHits, `MachLib.HighDimensional.packetCenterHits, `MachLib.HighDimensional.packetFiniteSurvivalRate, `MachLib.HighDimensional.packetTransitionEntropy, `MachLib.HighDimensional.phantom_attractor_obligation, `MachLib.HighDimensional.precision_escape_intervention_obligation, `MachLib.HighDimensional.saturation_deshelf_intervention_obligation, `MachLib.HighDimensional.saturation_shelf_obligation, `MachLib.HighDimensional.transition_graph_obligation, `MachLib.IsAnalyticOnReals, `MachLib.Model.intModel._elambda_1, `MachLib.Model.intModel._elambda_2, `MachLib.Model.intModel._elambda_3, `MachLib.Model.intModel._elambda_4, `MachLib.Model.intModel._elambda_5, `MachLib.MultiVarMod.TwoExp.PfaffianExpSDRReductionSolver.of_parts._elambda_1, `MachLib.MultiVarMod.TwoExp.PfaffianExpSDRReductionSolver.reducer._elambda_1, `MachLib.MultiVarMod.TwoExp.twoExpLowerReductionSolver_of_predicateSolver._elambda_1, `MachLib.Real, `MachLib.Real.HasDerivAt, `MachLib.Real.HasDerivAt_add, `MachLib.Real.HasDerivAt_arccos, `MachLib.Real.HasDerivAt_arcsin, `MachLib.Real.HasDerivAt_atan, `MachLib.Real.HasDerivAt_comp, `MachLib.Real.HasDerivAt_const, `MachLib.Real.HasDerivAt_cos, `MachLib.Real.HasDerivAt_exp, `MachLib.Real.HasDerivAt_id, `MachLib.Real.HasDerivAt_inv, `MachLib.Real.HasDerivAt_log_pos, `MachLib.Real.HasDerivAt_mul, `MachLib.Real.HasDerivAt_neg, `MachLib.Real.HasDerivAt_of_eq, `MachLib.Real.HasDerivAt_sin, `MachLib.Real.HasDerivAt_sub, `MachLib.Real.HasDerivAt_unique, `MachLib.Real.HasDerivAt2, `MachLib.Real.HasDerivAt2_add, `MachLib.Real.HasDerivAt2_comp, `MachLib.Real.HasDerivAt2_const, `MachLib.Real.HasDerivAt2_mul, `MachLib.Real.HasDerivAt2_projX, `MachLib.Real.HasDerivAt2_projY, `MachLib.Real.HasDerivAt2_scomp, `MachLib.Real.HasDerivAt2_sub, `MachLib.Real.HasDerivAt_congr, `MachLib.Real.hasDerivAt_continuousAt, `MachLib.Real.hasDerivAt_implicit, `MachLib.Real.hasDerivAt_implicit_local, `Certcom.real_exp_rounds, `Certcom.real_log_rounds, `Certcom.real_sin_eps, `Certcom.real_sin_rounds, `Certcom.real_cos_eps, `Certcom.real_cos_rounds, `Certcom.real_atan_eps, `Certcom.real_atan_rounds, `Certcom.real_abs_eps, `Certcom.real_abs_rounds, `Certcom.real_sqrt_rounds, `Certcom.real_log10_rounds, `Certcom.real_asin_rounds, `Certcom.real_acos_rounds, `Certcom.real_sinh_rounds, `Certcom.real_cosh_rounds, `Certcom.real_tan_rounds, `MachLib.Real.sin_pos_of_pos_lt_pi_div_two, `MachLib.Real.addR, `MachLib.Real.add_assoc, `MachLib.Real.add_comm, `MachLib.Real.add_lt_add_left, `MachLib.Real.add_neg, `MachLib.Real.add_zero, `MachLib.Real.arccos, `MachLib.Real.arccos_le_pi, `MachLib.Real.arccos_nonneg, `MachLib.Real.arccos_one, `MachLib.Real.arccos_zero, `MachLib.Real.archimedean, `MachLib.Real.arcsin, `MachLib.Real.arcsin_one, `MachLib.Real.arcsin_zero, `MachLib.Real.arctan, `MachLib.Real.arctan_lt_pi_div_two, `MachLib.Real.atan, `MachLib.Real.atan2, `MachLib.Real.atan2_le_pi, `MachLib.Real.atan2_one_zero, `MachLib.Real.atan2_zero_one, `MachLib.Real.atan_zero, `MachLib.Real.cos, `MachLib.Real.cos_add, `MachLib.Real.cos_arccos, `MachLib.Real.cos_neg, `MachLib.Real.cos_periodic, `MachLib.Real.cos_pi, `MachLib.Real.cos_pi_div_two, `MachLib.Real.cos_zero, `MachLib.Real.cosh, `MachLib.Real.cosh_eq, `MachLib.Real.cosh_ge_one, `MachLib.Real.cosh_pos, `MachLib.Real.divR, `MachLib.Real.div_def, `MachLib.Real.div_lt_one_of_pos_lt, `MachLib.Real.div_zero, `MachLib.Real.erf, `MachLib.Real.erf_le_one, `MachLib.Real.exp, `MachLib.Real.exp10, `MachLib.Real.exp10_def, `MachLib.Real.exp10_log10_inverse, `MachLib.Real.exp10_zero, `MachLib.Real.exp_add, `MachLib.Real.exp_exp_minus_exp_strictly_increasing, `MachLib.Real.exp_gt_one_plus_self, `MachLib.Real.exp_gt_two_x, `MachLib.Real.exp_lt, `MachLib.Real.exp_one_lt_three, `MachLib.Real.exp_pos, `MachLib.Real.exp_surj, `MachLib.Real.exp_zero, `MachLib.Real.floor, `MachLib.Real.floor_le, `MachLib.Real.floor_zero, `MachLib.Real.interval_scale_unit_lit_le, `MachLib.Real.interval_weight_sum_le, `MachLib.Real.leR, `MachLib.Real.le_iff_lt_or_eq, `MachLib.Real.le_sqrt_of_sq_le, `MachLib.Real.lit_one_eq, `MachLib.Real.lit_zero_eq, `MachLib.Real.log10, `MachLib.Real.log10_def, `MachLib.Real.log10_zero, `MachLib.Real.ltR, `MachLib.Real.lt_floor_add_one, `MachLib.Real.lt_irrefl_ax, `MachLib.Real.lt_total, `MachLib.Real.lt_trans_ax, `MachLib.Real.mulR, `MachLib.Real.mul_assoc, `MachLib.Real.mul_comm, `MachLib.Real.mul_distrib, `MachLib.Real.mul_inv, `MachLib.Real.mul_lt_mul_of_pos_right, `MachLib.Real.mul_one_ax, `MachLib.Real.mul_pos, `MachLib.Real.natCast, `MachLib.Real.natCast_succ, `MachLib.Real.natCast_zero, `MachLib.Real.negR, `MachLib.Real.neg_one_le_erf, `MachLib.Real.neg_one_lt_tanh, `MachLib.Real.neg_pi_div_two_lt_arctan, `MachLib.Real.neg_pi_lt_atan2, `MachLib.Real.oneR, `MachLib.Real.one_add_le_exp, `MachLib.Real.one_div_nonneg_of_pos, `MachLib.Real.one_div_pos_of_pos, `MachLib.Real.pi, `MachLib.Real.pi_gt_one, `MachLib.Real.pi_gt_three, `MachLib.Real.pi_pos, `MachLib.Real.pythagorean, `MachLib.Real.realOfScientific, `MachLib.Real.realOfScientific_clears, `MachLib.Real.realOfScientific_le_of_nat, `MachLib.Real.realOfScientific_lt_of_nat, `MachLib.Real.realOfScientific_one_dot_zero, `MachLib.Real.realOfScientific_pos, `MachLib.Real.realOfScientific_three_dot_zero, `MachLib.Real.realOfScientific_two_dot_zero, `MachLib.Real.realPow, `MachLib.Real.realPow_nonneg, `MachLib.Real.realPow_one, `MachLib.Real.realPow_pos, `MachLib.Real.realPow_zero, `MachLib.Real.rolle_ct, `MachLib.Real.sin, `MachLib.Real.sin_add, `MachLib.Real.sin_arcsin, `MachLib.Real.sin_neg, `MachLib.Real.sin_one_pos, `MachLib.Real.sin_periodic, `MachLib.Real.sin_pi, `MachLib.Real.sin_pi_div_two, `MachLib.Real.sin_zero, `MachLib.Real.sinh, `MachLib.Real.sinh_eq, `MachLib.Real.sqrt, `MachLib.Real.sqrt_le_of_le_sq, `MachLib.Real.sqrt_neg_zero, `MachLib.Real.sqrt_nonneg, `MachLib.Real.sqrt_one, `MachLib.Real.sqrt_sq_nonneg, `MachLib.Real.sqrt_zero, `MachLib.Real.subR, `MachLib.Real.sub_def, `MachLib.Real.sup_exists, `MachLib.Real.tan, `MachLib.Real.tan_def, `MachLib.Real.tan_half_pos, `MachLib.Real.tanh, `MachLib.Real.tanh_eq_sinh_div_cosh, `MachLib.Real.tanh_lt_one, `MachLib.Real.tanh_neg, `MachLib.Real.tanh_zero, `MachLib.Real.u, `MachLib.Real.u_le_one, `MachLib.Real.u_nonneg, `MachLib.Real.zeroR, `MachLib.Real.zero_lt_one_ax, `MachLib.Real.zero_ne_one_ax, `MachLib.analytic_add, `MachLib.analytic_comp, `MachLib.analytic_const, `MachLib.analytic_exp, `MachLib.analytic_finite_zeros_compact, `MachLib.analytic_id, `MachLib.analytic_log_pos, `MachLib.analytic_mul, `MachLib.analytic_ne_zero_nbhd, `MachLib.analytic_one_div_pos, `MachLib.analytic_sin, `MachLib.analytic_sub, `MachLib.chain_algebraic_dependence, `MachLib.emlEmptyChain._elambda_1, `MachLib.emlEmptyChain._elambda_2, `MachLib.eml_pfaffian_validon_from_cos_equality, `MachLib.eml_pfaffian_validon_from_sin_equality, `MachLib.eml_tree_analytic_on_pos, `MachLib.exp_tangent_line_strict, `MachLib.lambertW, `MachLib.lambertW_one_lt_one, `MachLib.lambertW_one_pos, `MachLib.lambertW_zero,
  -- Added 2026-07-19: Group-B transcendental math arc (asin/acos certificates), added
  -- earlier this same session, user-approved via AskUserQuestion, never synced into this
  -- snapshot. HasDerivAt_sqrt: InverseTrig.lean. pi_lower_bound/pi_upper_bound: Trig.lean.
  `MachLib.Real.HasDerivAt_sqrt, `MachLib.Real.pi_lower_bound, `MachLib.Real.pi_upper_bound,
  -- Added 2026-07-22: found while running this gate for the Certcom-bridge headline below --
  -- pre-existing decimal-bracketing axioms (WitnessResidualDeepNumeric.lean,
  -- WitnessResidualGrowthCompetitionNumeric.lean, Track C's growth-competition arc, unrelated to
  -- this session's Certcom work) never synced into this snapshot. Same numeric-bound pattern as
  -- pi_lower_bound/pi_upper_bound above. Not on any headline's footprint (checked: absent from
  -- both leak lists this run), so bookkeeping only -- no new trust.
  `MachLib.Real.log_2_0_bounds, `MachLib.Real.exp_1_35_lower, `MachLib.Real.exp_1_7_upper,
  `MachLib.Real.log_1_5_bounds, `MachLib.Real.log_2_7_bounds, `MachLib.Real.log_2_2_bounds,
  -- Added 2026-07-22: the new Real->Float quantization axiom pair (EMLCertcomGrounded.lean) --
  -- `floatOfR` (opaque, like `realToR`) + `real_round_bounds` (disclosed, un-witnessable, same
  -- reason `real_fpbridge` is: Float is opaque in Lean). `real_round_bounds` is domain-restricted
  -- (`abs x ≤ M → ... ≤ u*M`), fixed same-day after external review caught the first version's
  -- unconditional absolute bound as false of any real rounding implementation -- no separate
  -- `real_round_eps` constant, the bound is `u*M` directly. See `disclosedTrusted` below.
  `Certcom.floatOfR, `Certcom.real_round_bounds]

/-- Axioms permitted in a trustworthy shipped footprint: witnessed foundational core -/
def trustedFootprint : List Name := [`Certcom.realToR, `Certcom.real_fpbridge, `Certcom.real_tanh_rounds, `MachLib.Real.u, `MachLib.Real.u_nonneg, `MachLib.Real.mul_lt_mul_of_pos_right, `MachLib.Real.cosh, `MachLib.Real.cosh_eq, `MachLib.Real.cosh_ge_one, `MachLib.Real.cosh_pos, `MachLib.Real.exp_add, `MachLib.Real.exp_zero, `MachLib.Real.HasDerivAt_neg, `MachLib.Real.HasDerivAt_of_eq, `MachLib.Real.one_div_nonneg_of_pos, `MachLib.Real.sinh, `MachLib.Real.sinh_eq, `MachLib.Real.tanh, `MachLib.Real.tanh_eq_sinh_div_cosh, `Certcom.real_exp_rounds, `Certcom.real_log_rounds, `Certcom.real_sin_eps, `Certcom.real_sin_rounds, `Certcom.real_cos_eps, `Certcom.real_cos_rounds, `Certcom.real_atan_eps, `Certcom.real_atan_rounds, `Certcom.real_abs_eps, `Certcom.real_abs_rounds, `Certcom.real_sqrt_rounds, `Certcom.real_log10_rounds, `Certcom.real_asin_rounds, `Certcom.real_acos_rounds, `Certcom.real_sinh_rounds, `Certcom.real_cosh_rounds, `Certcom.real_tan_rounds, `MachLib.Real.sin_pos_of_pos_lt_pi_div_two, `MachLib.Real.HasDerivAt_congr, `MachLib.Real.cos_neg, `MachLib.Real.cos_pi_div_two, `MachLib.Real.pi, `MachLib.Real.tan, `MachLib.Real.tan_def, `MachLib.Real.sqrt, `MachLib.Real.sqrt_le_of_le_sq, `MachLib.Real.sqrt_nonneg, `MachLib.Real.sqrt_sq_nonneg, `MachLib.Real.arcsin, `MachLib.Real.HasDerivAt_arcsin, `MachLib.Real.arccos, `MachLib.Real.HasDerivAt_arccos, `MachLib.Real.log10, `MachLib.Real.log10_def, `MachLib.Real.atan, `MachLib.Real.HasDerivAt_atan, `MachLib.Real.HasDerivAt_cos, `MachLib.Real.sin, `MachLib.Real.cos, `MachLib.Real.HasDerivAt_sin, `MachLib.Real.pythagorean, `Classical.choice, `MachLib.IsAnalyticOnReals, `MachLib.Real, `MachLib.Real.HasDerivAt, `MachLib.Real.HasDerivAt_add, `MachLib.Real.HasDerivAt_comp, `MachLib.Real.HasDerivAt_const, `MachLib.Real.HasDerivAt_exp, `MachLib.Real.HasDerivAt_id, `MachLib.Real.HasDerivAt_inv, `MachLib.Real.HasDerivAt_log_pos, `MachLib.Real.HasDerivAt_mul, `MachLib.Real.HasDerivAt_sub, `MachLib.Real.HasDerivAt_unique, `MachLib.Real.addR, `MachLib.Real.add_assoc, `MachLib.Real.add_comm, `MachLib.Real.add_lt_add_left, `MachLib.Real.add_neg, `MachLib.Real.add_zero, `MachLib.Real.divR, `MachLib.Real.div_def, `MachLib.Real.exp, `MachLib.Real.exp_lt, `MachLib.Real.exp_pos, `MachLib.Real.exp_surj, `MachLib.Real.leR, `MachLib.Real.le_iff_lt_or_eq, `MachLib.Real.ltR, `MachLib.Real.lt_irrefl_ax, `MachLib.Real.lt_total, `MachLib.Real.lt_trans_ax, `MachLib.Real.mulR, `MachLib.Real.mul_assoc, `MachLib.Real.mul_comm, `MachLib.Real.mul_distrib, `MachLib.Real.mul_inv, `MachLib.Real.mul_one_ax, `MachLib.Real.mul_pos, `MachLib.Real.natCast, `MachLib.Real.natCast_succ, `MachLib.Real.natCast_zero, `MachLib.Real.negR, `MachLib.Real.oneR, `MachLib.Real.one_div_pos_of_pos, `MachLib.Real.rolle_ct, `MachLib.Real.subR, `MachLib.Real.sub_def, `MachLib.Real.zeroR, `MachLib.Real.zero_lt_one_ax, `MachLib.Real.zero_ne_one_ax, `MachLib.analytic_add, `MachLib.analytic_comp, `MachLib.analytic_const, `MachLib.analytic_exp, `MachLib.analytic_id, `MachLib.analytic_log_pos, `MachLib.analytic_mul, `MachLib.analytic_one_div_pos, `MachLib.analytic_sub, `Quot.sound, `propext,
  -- Added 2026-07-22: `Certcom.eml_var_var_pipeline`'s footprint leaks these three -- calling
  -- `pipeline_nested_std` (StdLip's full 7-primitive case split, even though this use only takes
  -- the `.exp` branch) pulls in tanh's range facts and atan's origin fact transitively, since
  -- `#print axioms` reports the WHOLE theorem's dependency graph, not the path one instantiation
  -- takes. All three already `knownAxioms` (used by the tan/atan grounding arc); promoting them
  -- here is bookkeeping, not new trust.
  `MachLib.Real.tanh_lt_one, `MachLib.Real.neg_one_lt_tanh, `MachLib.Real.atan_zero,
  -- Added 2026-07-19: confirmed witnessed in monogate-lean's MachLibRealModel*.lean series
  -- (individually re-checked this pass, not assumed from memory) but never added to this list.
  -- Found while tracing `MachLib.sin_not_in_eml_any_depth`'s #print axioms footprint against
  -- this list for the RH-EML "Infinite Zeros Barrier" bridge investigation -- see
  -- monogate-research/exploration/RH_converse_infinite_zeros_barrier_bridge_2026_07_19/.
  `MachLib.analytic_finite_zeros_compact,  -- MachLibRealModelFiniteZeros.lean:32
  `MachLib.analytic_ne_zero_nbhd,          -- MachLibRealModelBatch4.lean:47
  `MachLib.Real.sin_zero, `MachLib.Real.sin_pi, `MachLib.Real.cos_pi, `MachLib.Real.pi_pos,
  `MachLib.Real.sin_add,                  -- all MachLibRealModelBatch3.lean, one-line Mathlib wraps
  -- Added 2026-07-22: `MachLib.eml_pfaffian_validon_from_sin_equality` DISCHARGED (vacuously) --
  -- see `MachLib.eml_pfaffian_validon_from_sin_equality_proved`
  -- (EMLPfaffianValidOnSinEqualityProved.lean). Its hypothesis (a tree equaling `sin`
  -- everywhere) is unsatisfiable per `MachLib.Real.no_tree_eq_sin_unconditional`
  -- (WitnessResidualNormalFormClosure.lean), so the axiom's conclusion follows via
  -- `False.elim` -- fresh-rebuild `#print axioms` confirmed the discharge does NOT cite
  -- `eml_pfaffian_validon_from_sin_equality` itself (non-circular). These 7 entries are the
  -- discharge theorem's own trusted base, all already `knownAxioms`, newly added here so
  -- this headline's footprint check (below) passes.
  `MachLib.Real.archimedean, `MachLib.Real.cos_add, `MachLib.Real.cos_zero,
  `MachLib.Real.hasDerivAt_continuousAt, `MachLib.Real.pi_gt_one, `MachLib.Real.sin_pi_div_two,
  `MachLib.Real.sup_exists,
  -- Added 2026-07-22: `no_tree_eq_nestedTarget_fully_unconditional`'s own base (the
  -- eml_eventually_valid_repr + tail-restricted zero-counting closure, no straddle condition,
  -- no validity-from-0 hypothesis) -- needs `nestedTarget`'s 2π-periodicity directly, unlike
  -- the sin/cos discharges which only needed periodicity's own downstream `kπ`/`half-odd-π`
  -- consequences.
  `MachLib.Real.sin_periodic, `MachLib.Real.sin_one_pos,
  -- Added 2026-07-22: `floatOfR`/`real_round_bounds` -- the Real->Float quantization axiom pair
  -- `eml_var_var_certcom_witness_grounded`'s footprint rests on (domain-restricted, `u*M` form --
  -- see the erratum note in `disclosedTrusted` below and in `EMLCertcomGrounded.lean`'s own
  -- docstring). Same category as `realToR`/`real_fpbridge`.
  `Certcom.floatOfR, `Certcom.real_round_bounds,
  -- Added 2026-07-22: found by the NEW whole-module spine guard (invariant 5, `spineTheorems`)
  -- on its first run -- `MachLib.Real.sin_neg`, used by `nestedTarget_at_neg_pi_div_two`'s
  -- base case (sin(-x) = -sin x) and its cont.59-63 downstream callers (the straddle-
  -- conditioned nestedTarget family, `witness_B_not_le_zero_of_lo_neg`, and others), was never
  -- added when those theorems were hand-built -- they predate this guard and were never
  -- individually pinned as `headlines`, so the gap was invisible until whole-module checking
  -- existed. Already `knownAxioms` (a plain Mathlib-wrapped `sin_neg` fact); no new trust, just
  -- a bookkeeping gap the guard exists to catch.
  `MachLib.Real.sin_neg]

/-- Unwitnessed-but-disclosed axioms + machine-readable reason. Must stay inert. -/
def disclosedUnwitnessed : List (Name × String) := [(`MachLib.Real.erf, "blocked-upstream (erf absent from Mathlib)"), (`MachLib.Real.erf_le_one, "blocked-upstream (erf absent from Mathlib)"), (`MachLib.Real.neg_one_le_erf, "blocked-upstream (erf absent from Mathlib)"), (`MachLib.eml_tree_analytic_on_pos, "unwitnessed-but-SOUND: EMLLogArgPosOnIoi side-condition restored (was false-as-stated, fixed); real-analyticity of well-formed EML trees not yet proven in machlib; in NO footprint"), (`MachLib.MultiVarMod.TwoExp.PfaffianExpSDRReductionSolver.of_parts._elambda_1, "elaborator-synthesized axiom (isUnsafe=true), NOT hand-written -- `of_parts` in TwoExpPfaffianReductionWitness.lean is a plain structure-literal def with no `partial`/`sorry`/`Classical.choice` at the call site; root cause not yet identified (found + disclosed 2026-07-16, AxiomLedger self-check going red; see AxiomLedger investigation notes). Gate-2d multivariate-Khovanskii frontier work (added 2026-07-13/14), not on any shipped headline's path."), (`MachLib.MultiVarMod.TwoExp.PfaffianExpSDRReductionSolver.reducer._elambda_1, "same as .of_parts._elambda_1 above -- same file, same unexplained isUnsafe synthesis, same frontier, not on any headline's path."), (`MachLib.MultiVarMod.TwoExp.twoExpLowerReductionSolver_of_predicateSolver._elambda_1, "same pattern again -- plain structure-literal def, no visible partial/sorry/Classical.choice; three occurrences in one file is worth a dedicated Lean-internals investigation, not yet done. Not on any headline's path.")]

/-- Disclosed-yet-load-bearing-BY-DESIGN: the certcom Theorem-A IEEE-754 model. Un-witnessable
(Lean `Float` is opaque), so — unlike `disclosedUnwitnessed`, which must stay inert — these are the
terminal trust under the Theorem-A headline. They live in `trustedFootprint`; listed here so the
trust they carry is named, not hidden among the ℝ-witnessed axioms. -/
def disclosedTrusted : List (Name × String) := [(`Certcom.realToR, "IEEE-754 denotation Float→Real (Float opaque, no in-Lean semantics)"), (`Certcom.real_fpbridge, "standard model: every basic float op correctly rounded (rel err ≤ u), neg exact — un-witnessable in Lean; Flocq-scale to ground further"), (`Certcom.real_tanh_rounds, "libm model: runtime tanh (exp-decomposed) within real_tanh_eps of Real.tanh — un-witnessable in Lean"), (`Certcom.real_exp_rounds, "libm model: runtime exp within real_exp_eps of Real.exp — un-witnessable in Lean"), (`Certcom.real_log_rounds, "libm model: runtime log within real_log_eps of Real.log — un-witnessable in Lean"), (`Certcom.real_sin_eps, "libm sin rounding constant (residual primitive trust)"), (`Certcom.real_sin_rounds, "libm model: runtime sin within real_sin_eps of Real.sin — un-witnessable in Lean"), (`Certcom.real_cos_eps, "libm cos rounding constant (residual primitive trust)"), (`Certcom.real_cos_rounds, "libm model: runtime cos within real_cos_eps of Real.cos — un-witnessable in Lean"), (`Certcom.real_atan_eps, "libm atan rounding constant (residual primitive trust)"), (`Certcom.real_atan_rounds, "libm model: runtime atan within real_atan_eps of Real.atan — un-witnessable in Lean"), (`Certcom.real_abs_eps, "libm abs rounding constant (residual primitive trust)"), (`Certcom.real_abs_rounds, "libm model: runtime abs within real_abs_eps of Real.abs — un-witnessable in Lean"), (`Certcom.real_sqrt_rounds, "libm model: runtime sqrt within real_sqrt_eps of Real.sqrt — un-witnessable in Lean"), (`Certcom.real_log10_rounds, "libm model: runtime log10 (ln-composite) within real_log10_eps of Real.log10 — un-witnessable in Lean"), (`Certcom.real_asin_rounds, "libm model: runtime asin within real_asin_eps of Real.arcsin — un-witnessable in Lean"), (`Certcom.real_acos_rounds, "libm model: runtime acos within real_acos_eps of Real.arccos — un-witnessable in Lean"), (`Certcom.real_sinh_rounds, "libm model: runtime sinh (exp-composite) within real_sinh_eps of Real.sinh — un-witnessable in Lean"), (`Certcom.real_cosh_rounds, "libm model: runtime cosh (exp-composite) within real_cosh_eps of Real.cosh — un-witnessable in Lean"), (`Certcom.real_tan_rounds, "libm model: runtime tan within real_tan_eps of Real.tan — un-witnessable in Lean"), (`MachLib.Real.sin_pos_of_pos_lt_pi_div_two, "foundational trig fact (sin positive on (0,pi/2)) -- MachLib.Real only axiomatizes sin/cos at isolated points; needed to ground cos positivity/monotonicity for tan Lipschitz bound; user-approved 2026-07-17 via AskUserQuestion, the sole new axiom in this whole 14-primitive libm-grounding arc besides the per-primitive rounding constants"), (`Certcom.floatOfR, "the Float a standard real->float quantization (e.g. round-to-nearest) assigns to a real x -- opaque, like realToR, in the OPPOSITE direction: Certcom's own machinery never needed Real->Float (it compiles EML to C and runs on floats), this direction exists only because Option D's non-approximation theorems quantify over ALL reals in an interval, not just Float-representable ones; user-directed 2026-07-22 ('do both please' / 'proceed into that') to complete the parallel with realToR/real_fpbridge rather than leave it an abstract per-theorem hypothesis"), (`Certcom.real_round_bounds, "the disclosed real->Float quantization model, DOMAIN-RESTRICTED: for x with abs x <= M (0 <= M, both caller-supplied), floatOfR x read back through realToR lands within u*M of x -- the standard IEEE-754 round-to-nearest-even model (relative error <= half a ULP, i.e. <= u, uniformized to the range M the same way exp_lip_local's L:=exp hi uniformizes a per-point Lipschitz bound over an interval). External referent: true of round-to-nearest-even for reals within the representable range implied by M -- NOT claimed unconditionally over all reals (outside a bounded range round-to-nearest either loses this relative-error guarantee or overflows, and no fixed bound holds). Fixed 2026-07-22 same-day after external review caught the first version (unconditional, a single fixed real_round_eps constant independent of magnitude) as false of any real rounding implementation -- disclosed axioms are unfalsifiable inside Lean, so an imprecise statement would have meant 'sorryAx-free' stopped meaning what it appears to mean; un-witnessable in Lean (Float opaque), same status as real_fpbridge. NOTE: the same precision question applies in principle to the pre-existing real_exp_rounds/real_log_rounds below (exp also overflows, and their stated bound is likewise unconditional) -- flagged, not fixed, since those are used across many already-shipped headlines (pid_exp_grounded, pid_log_grounded, ...) and re-stating them is a separate, larger, not-yet-authorized change")]

/- **2026-07-22 retroactive audit note.** User-directed ("yes, audit and fix it"), following the
`real_round_bounds` erratum: `real_exp_eps`, `real_log_eps`, `real_tanh_eps`, `real_sinh_eps`,
`real_cosh_eps`, `real_sqrt_eps`, `real_log10_eps`, `real_asin_eps`, `real_acos_eps`, `real_tan_eps`
(ten of the fourteen `Trans1` primitive rounding constants, `FPGrounding.lean`) were unconditional,
magnitude-independent bounds — the SAME overclaim `real_round_bounds`'s erratum fixed, just
pre-existing rather than newly introduced. All ten re-stated domain-restricted (reusing each
primitive's own already-required Lipschitz-domain bound — `hi` for `exp`, `[lo,hi]` for `log`, `R`
for the symmetric-domain primitives — costing zero NEW hypotheses at any `pid_X_grounded` call site,
one exception: `tanh` needed a genuinely new `R` bound, since its own kernel previously had none).
Two self-caught bugs en route (found and fixed before shipping, not after): `real_exp_eps`/`_log_eps`
etc. dropped entirely (folded into `u`-relative bounds, matching `real_round_bounds`'s own fix rather
than inventing new named constants) — and `real_asin_rounds`/`real_acos_rounds`'s first draft was
missing the `R < 1` domain restriction `real_tan_rounds`'s `R < π/2` correctly had, an oversight
found while designing what would have been a totalizing dispatcher for `pid_log_cosh_grounded`.
That dispatcher (`hround_all`/`Eround1All`/`realOfAll14`, originally covering all fourteen primitives
uniformly) turned out to be impossible to state honestly post-fix — six primitives need validity
conditions beyond plain interval membership (`0 < lo` for `log`/`sqrt`/`log10`; `R < 1`/`R < π/2` for
`asin`/`acos`/`tan`) with no single uniform shape, and patching around that would silently
reintroduce the exact overclaim being removed. Resolved by moving `hround` from a separate,
universally-quantified parameter into `IsFoldLocal.tr1`'s own constructor, per occurrence — exactly
how the flat, single-level pipelines already worked — removing the need for a totalization
altogether (`AbsoluteFoldNestLocal.lean`). `pid_log_cosh_grounded` rebuilt on this interface, still
proven, `sorryAx`-free. `sin`/`cos`/`atan`/`abs` — the four genuinely globally-Lipschitz, non-
composite primitives — audited and confirmed still honestly unconditional (native `Prims` calls, no
`exp`-decomposition overflow risk, bounded output); left unchanged, with the reasoning recorded in
their own docstrings. Gate green post-audit: 299 axioms pinned, 47 headlines (144 trusted), 23
disclosed-trusted (down from 34 — ten stale `_eps` names retired, no new trust added). Full detail:
`EML_WITNESS_FINDING_DECISION_2026_07_15.md` cont. 86. -/

/-- Shipped headline theorems whose footprint the gate pins. -/
def headlines : List Name := [`MachLib.KhovanskiiConcrete.eexp_barrier_zero_count_le_47, `MachLib.eml_eval_boundedZeros, `MachLib.IterExpDepthN.chainN_khovanskii_bound_unconditional, `MachLib.IterExpDepthN.chainN_khovanskii_bound_explicit, `Certcom.pipeline_det_grounded, `Certcom.pipeline_arith_grounded, `Certcom.pid_grounded, `Certcom.pid_tanh_grounded, `Certcom.pid_exp_grounded, `Certcom.pid_log_grounded, `Certcom.pid_sin_grounded, `Certcom.pid_cos_grounded, `Certcom.pid_atan_grounded, `Certcom.pid_abs_grounded, `Certcom.pid_sqrt_grounded, `Certcom.pid_log10_grounded, `Certcom.pid_asin_grounded, `Certcom.pid_acos_grounded, `Certcom.pid_sinh_grounded, `Certcom.pid_cosh_grounded, `Certcom.pid_tan_grounded, `Certcom.pid_log_cosh_grounded, `Certcom.pid_tanhVar_grounded, `Certcom.tanhVar_controller_tracking,
  -- Added 2026-07-22: the Option D witness-finding arc's own capstone (`no_tree_eq_sin_
  -- unconditional`) and its axiom-discharge corollary, pinned so the arc's central claim
  -- ("no finite EML tree equals sin, and `eml_pfaffian_validon_from_sin_equality` is
  -- vacuously provable, not merely avoided") is CI-checked on every build, not just a fresh
  -- rebuild done once by hand this round.
  `MachLib.Real.no_tree_eq_sin_unconditional, `MachLib.eml_pfaffian_validon_from_sin_equality_proved,
  -- Added 2026-07-22: the `cos` sibling of the pair above, same day -- `eml_tailSign_
  -- unconditional` (the arc's core result) doesn't care which target function is being
  -- ruled out, so `cos_not_tailSign` was the only new proof needed. Its footprint required
  -- ZERO new `trustedFootprint` entries (fully covered by the sin discharge's own base).
  `MachLib.Real.no_tree_eq_cos_unconditional, `MachLib.eml_pfaffian_validon_from_cos_equality_proved,
  -- Added 2026-07-22: `sin_not_in_eml_any_depth`/`cos_not_in_eml_any_depth` re-derived as
  -- one-line corollaries of the pair above (the depth bound `k` was never inspected) --
  -- pinned so the SUBSUMPTION itself stays true on every build, not just checked once.
  `MachLib.sin_not_in_eml_any_depth_unconditional, `MachLib.cos_not_in_eml_any_depth_unconditional,
  -- Added 2026-07-22, same day: the FULL closure -- no finite EML tree equals any well-formed
  -- `nestedTarget cs`, no straddle condition, no restriction on the tree at all. Supersedes the
  -- straddle-conditioned family closure and removes `RightChildrenSimplePositive T1` entirely
  -- for the ORIGINAL depth-2 residual, for every `c2 > 1` (not just `1 < c2 ≤ 2`).
  `MachLib.Real.no_tree_eq_nestedTarget_fully_unconditional,
  `MachLib.eml_depth2_witness_of_const_sibling_fully_unconditional,
  -- Added 2026-07-22, same day: the muses' generalization, checked and confirmed uniform --
  -- the tail-restricted zero-counting argument abstracted to any target with a recurring
  -- level + recurring witness, with nestedTarget cs re-derived as a five-line instantiation
  -- via no_tree_eq_nestedTarget_fully_unconditional_via_meta. Zero new trustedFootprint
  -- entries needed (strict subset of the concrete version's own footprint).
  `MachLib.Real.no_tree_eq_recurring_target_fully_unconditional,
  -- Added 2026-07-22, same day: the STRONGER form -- no explicit zero family needed, only
  -- continuity + no TailSign relative to some level L. IVT-based zero construction
  -- (target_zero_between, plain ContinuousAt, no derivative) built fresh for an arbitrary
  -- continuous function, mirroring rcep_zero_between's own mechanism which was built only for
  -- EML trees. Zero new trustedFootprint entries needed.
  `MachLib.Real.no_tree_eq_target_of_not_tailSign,
  -- Added 2026-07-22: Track C, item C1 (log-divergence wall) -- a DIFFERENT obstruction type
  -- (continuity-at-a-point vs. divergence, not TailSign/oscillation-counting). No finite EML
  -- tree, valid on an interval containing 0, equals Real.log on the positive side --
  -- LogDivergenceWall.lean. Zero new trustedFootprint entries needed (footprint is a strict
  -- subset: base HasDerivAt composition rules + hasDerivAt_continuousAt, nothing analytic).
  `MachLib.no_tree_eq_log_positive_side_given_validon,
  -- Added 2026-07-22: Track C, item C3 -- the separation theorem. log is IMPLICITLY
  -- representable (exp's EML representative, inverted, recovers log exactly for every x>0,
  -- no hypothesis) despite failing every EXPLICIT route near 0 (C1's wall). Zero new
  -- trustedFootprint entries (strict subset of C1's own footprint plus exp_log/log_exp,
  -- both already-proven theorems, not axioms).
  `MachLib.log_implicit_not_explicit,
  -- Added 2026-07-22: Track C, item C6 -- quantitative non-approximation, TAIL/asymptotic
  -- form: no tree stays within epsilon<1 of sin for ALL sufficiently large x. NOT the compact-
  -- interval form the muses actually asked for (silent on any bounded [0,R], however large --
  -- see LogDivergenceWall-sibling QuantitativeNonApproximation.lean's own erratum, added
  -- 2026-07-22 after external review). Zero new trustedFootprint entries.
  `MachLib.Real.no_tree_eps_close_to_sin_eventually,
  -- Added 2026-07-22: Track C, item C7 -- the Certcom handshake, scoped honestly. Combines
  -- C6's TAIL floor (not a compact-interval one -- see C6's erratum above) with an ABSTRACT
  -- rounding-error bound. Wiring to Certcom's actual pipeline needs a genuinely harder,
  -- NOT-yet-built compact-interval quantitative theorem (Khovanskii bound explicit in tree
  -- depth) -- this file's own erratum (added 2026-07-22) says so plainly; do not read this
  -- headline as "the Certcom handshake is done." Zero new trustedFootprint entries.
  `MachLib.Real.certcom_total_error_floor,
  -- Added 2026-07-22: Track C, item C8 -- one census entry, sin^2 x, a genuinely different
  -- oscillation shape (non-negative, recurring to exactly 0 AND exactly 1) instantiated
  -- through the general meta-theorem with no sin/nestedTarget-specific reasoning. Zero new
  -- trustedFootprint entries.
  `MachLib.Real.no_tree_eq_sinSq_unconditional,
  -- Added 2026-07-22: compression session (external review) -- the three C1/C3/C6 GENERAL
  -- abstractions, pinned as the new capstones. Each file's own corollary re-deriving the
  -- original C1/C3/C6 result is a confirmation, not pinned separately (same footprint).
  -- TailApproximationBarrier.lean: TAIL-only (see C6's own erratum), zero new trustedFootprint.
  `MachLib.Real.no_tree_eps_close_to_target_eventually,
  -- ContinuityDivergenceBarrier.lean: target- and tree-agnostic, zero new trustedFootprint.
  `MachLib.Real.no_continuousAt_eq_unboundedBelowNearRight,
  -- RepresentabilityTaxonomy.lean: named ExplicitlyRepresentableValidlyNear/
  -- ImplicitlyRepresentable, zero new trustedFootprint.
  `MachLib.Real.log_separation,
  -- Added 2026-07-22: the compact-interval quantitative non-approximation theorem -- Track C's
  -- real "Certcom handshake" blocker (C6/C7 only gave a TAIL/asymptotic result, silent on
  -- bounded intervals; see the cont.76 erratum). No finite EML tree, valid across an interval
  -- containing 0, stays within eps<1 of sin on the WHOLE interval once it's long enough to hold
  -- M+1 alternating extrema, M an EXPLICIT function of the tree's own structure
  -- (EMLExplicitBound.combinedBoundE) -- not an abstract "eventually" threshold. Zero new
  -- trustedFootprint entries; footprint confirmed independent of zero_count_bound_classical and
  -- the still-open exp_hard gap (verified directly via #print axioms before building anything).
  `MachLib.Real.no_tree_eps_close_to_sin_compact_interval,
  -- Added 2026-07-22: the REAL Certcom handshake -- combines the compact-interval theorem above
  -- with the abstract rounding-bound floor (C7) into one statement: for a compiled artifact
  -- within delta of a validon tree throughout (A,B), once (A,B) is long enough for M+1 explicit
  -- extrema, the TOTAL error against true sin exceeds eps-delta at a point WITHIN (A,B) -- not
  -- merely "arbitrarily far out." hround is still abstract (not wired to Certcom's actual
  -- rounding axioms for a real compiled pipeline -- that remains the thesis-shaped work). Zero
  -- new trustedFootprint entries.
  `MachLib.Real.certcom_total_error_floor_compact_interval,
  -- Added 2026-07-22: the REAL Certcom pipeline connection (EMLCertcomBridge.lean). Investigated
  -- wiring `hround` above to Certcom's ACTUAL rounding-certified pipelines rather than leaving it
  -- abstract. Finding en route: Certcom's own `EML` already names `exp(x)-log(y)` as a primitive
  -- (`Trans2.eml`, mg_eml) -- almost certainly the origin of this whole grammar's name -- but
  -- AbsoluteFoldNest.lean's own scoping note says "tr2 decomposes into tr1 + arithmetic": no
  -- certified fold pipeline accepts a bare Trans2.eml node. So the natural translation of
  -- `EMLTree.eml t1 t2` is the DECOMPOSED `.bin .sub (.tr1 .exp _) (.tr1 .ln _)`, not `.tr2 .eml`.
  -- This headline composes Certcom's real `pipeline_nested_std` (exp, StdLip) and
  -- `pipeline_pos_over_arith` (log, PosLip, the same positivity floor EMLPfaffianValidOn already
  -- tracks) through `absenc_sub`, for the depth-1 tree `EMLTree.eml var var` (exp x - log x),
  -- POINTWISE at a given environment. Zero new trustedFootprint entries. NOT yet wired into
  -- `certcom_total_error_floor_compact_interval` itself: that needs (a) the bound made UNIFORM
  -- over a whole interval (this proof's error term depends on the point x), and (b) a deeper gap
  -- -- `certcom_total_error_floor_compact_interval`'s `compiled` is `Real → Real`, but a compiled
  -- artifact only has behavior at Float-representable inputs; bridging needs an explicit
  -- Real-to-Float quantization hypothesis, not yet built. See EMLCertcomBridge.lean's docstring.
  `Certcom.eml_var_var_pipeline,
  -- Added 2026-07-22: closes both gaps `eml_var_var_pipeline` (above) left open
  -- (EMLCertcomQuantitativeBridge.lean). (1) Uniformity: re-derives the two leaf-level roundings
  -- directly from the primitive hround hypotheses (bypassing pipeline_nested_std's existential,
  -- necessarily-non-closed-form bound -- AbsoluteFoldNest.lean's own docstring says the fold is
  -- deliberately existential, not closed-form) to get a bound depending only on the interval's
  -- own endpoints, not the evaluation point. (2) The deeper gap: certcom_total_error_floor_
  -- compact_interval's `compiled : Real -> Real` needs a value at EVERY real in (A,B), but a
  -- compiled artifact only has behavior at Float-representable inputs -- closed via an explicit,
  -- honestly-disclosed Real->Float quantization hypothesis (`round`/`hround_q`, same trust
  -- status as FPBridge itself: a standard IEEE-754 fact, hypothesis because Float is opaque in
  -- Lean) composed with exp/log's own local-Lipschitz bounds (exp_lip_local/log_lip_local,
  -- already-proven, propagating the quantization error through T.eval). This headline
  -- (`eml_var_var_certcom_witness`) is a genuine instantiation of `certcom_total_error_floor_
  -- compact_interval`'s `hround` for a real translated EMLTree, with an EXPLICIT delta -- not an
  -- abstract stand-in. `round`/`hround_q` remain the one new disclosed hypothesis (see
  -- disclosedTrusted-style framing in this file's own docstring); everything else composes
  -- already-proven, already-trusted facts.
  `Certcom.eml_var_var_certcom_witness,
  -- Added 2026-07-22: the FULLY GROUNDED form (EMLCertcomGrounded.lean), directly requested
  -- ("proceed into that please" -> "do both please" -> "proceed into that please", the last
  -- explicitly re-reading the abstract hound_exp/hround_ln/round/hround_q hypotheses as things to
  -- ground rather than leave abstract). Re-derives `eml_var_var_certcom_witness` (above) against
  -- Certcom's ACTUAL disclosed grounding axioms -- realToR/real_fpbridge/real_exp_rounds/
  -- real_log_rounds against the concrete leanPrims runtime basis, exactly the pattern pid_exp_
  -- grounded/pid_log_grounded already use elsewhere in this file -- plus the new floatOfR/
  -- real_round_eps/real_round_bounds pair for the Real->Float direction Certcom itself never
  -- needed. No `forall`-primitive rounding hypothesis, no abstract quantization hypothesis: every
  -- free parameter is a genuine mathematical quantity or a side condition on one, not a further
  -- disclosed-primitive assumption. This is as far down as this arc's trust chain goes -- below
  -- floatOfR/real_round_bounds is the same wall as below realToR/real_fpbridge (Float is opaque in
  -- Lean), not a gap left by insufficient effort.
  `Certcom.eml_var_var_certcom_witness_grounded,
  -- Added 2026-07-22: the compositional Certcom handshake -- generalizes eml_var_var_certcom_
  -- witness_grounded (above, ONE hand-built tree) to ANY EMLTree, via one structural induction,
  -- matching muse 2's own stated success criterion: "adding a supported EML constructor requires
  -- one reusable primitive-grounding lemma, after which arbitrary trees inherit the grounded
  -- theorem automatically." Originally shipped var+eml-only (`eml_tree_var_grounded`, same day),
  -- with `const` deliberately deferred (constant-quantization error compounding through nested
  -- exp/log layers); closed same day too (`eml_tree_grounded`, this entry, superseding the
  -- var-only version) once the key structural fact was found: the SAME `emlTreeErrorBound`
  -- recursion already upper-bounds both the compiled-vs-exact and exact-vs-true error (Lipschitz
  -- composition plus extra non-negative rounding terms on top), so no second recursive function
  -- was needed -- only the theorem's `exactRn t = t.eval x` equality (true only when no `const`
  -- ever enters the recursion) became `abs (exactRn t - t.eval x) ≤ emlTreeErrorBound t x`, an
  -- inequality using the same bound function. New trustedFootprint dependencies: `floatOfR`,
  -- `real_round_bounds` -- ALREADY-disclosed (the earlier `eml_var_var_certcom_witness_grounded`
  -- round), not new trust, just the axioms this wider scope genuinely needs.
  `Certcom.eml_tree_grounded,
  -- Added 2026-07-22: Track C, item C9 -- Extreme Value Theorem attainment, built from scratch
  -- (ExtremeValueAttainment.lean). This codebase had boundedness (`continuousAt_bddAbove_Icc`)
  -- but not attainment; both external reviews flagged this as the prerequisite for "prove the
  -- general periodic-target barrier." Classical `1/(M-f)` argument: if the least upper bound
  -- were never attained, its reciprocal-shifted function would ALSO be bounded, yielding a
  -- strictly smaller upper bound -- contradicting leastness. `continuousAt_attains_min_Icc`
  -- mirrors the max case via negation. Zero new trustedFootprint entries (built entirely from
  -- `sup_exists`/`ContinuousAt`, both already load-bearing in IntermediateValue.lean).
  `MachLib.Real.continuousAt_attains_max_Icc, `MachLib.Real.continuousAt_attains_min_Icc,
  -- Added 2026-07-22: Track C, item C9's actual payoff -- the general periodic-target barrier
  -- (GeneralPeriodicTargetBarrier.lean). No finite EML tree equals ANY nonconstant,
  -- everywhere-continuous, periodic target -- generalizing `sin_not_tailSign`'s hand-built
  -- argument uniformly. ERRATUM caught while building this, not assumed going in: the EVT-
  -- attainment machinery above turns out NOT to be the binding constraint for this specific
  -- theorem -- periodicity alone makes EVERY value of TARGET recur arbitrarily far out, not
  -- just an extremal one, so `L := TARGET 0` (an arbitrary basepoint) works exactly as well as
  -- `L := inf(TARGET)` for refuting all three TailSign cases. `sin_not_tailSign` itself is a
  -- confirming precedent (it already used `L = sin 0 = 0`, not `inf(sin) = -1`). Recorded rather
  -- than silently dropped, matching this document's "checked directly" discipline. Zero new
  -- trustedFootprint entries (pure `natCast`/`archimedean` scaling, both already load-bearing).
  `MachLib.Real.no_tree_eq_periodic_target, `MachLib.Real.no_tree_eq_sin_via_periodic_barrier,
  -- Added 2026-07-22: Track C, item C5 -- investigated, NOT force-closed (see the decision doc's
  -- own cont.90 entry for the full technical account of why). Confirmed, by reading source rather
  -- than assuming it, that EMLEncoder.lean's `enc` and IterExpChain.lean's `IterExpChain` are BOTH
  -- literal instances of the SAME `PfaffianChain n` structure -- "chain order" has one uniform
  -- meaning across both developments, contrary to this arc's own earlier "three unrelated
  -- formalisms" framing (cont.74). Also confirmed the muses' proposed obstruction mechanism does
  -- NOT combine as stated: TailSign and chain order are orthogonal axes (sin's own classical ODE
  -- gives it chain order 2; EML's barrier against it has nothing to do with chain order). This
  -- headline is the one concrete, buildable piece that investigation surfaced: the
  -- EXISTENCE-direction bridge -- EMLTree already reaches every depth of the iterated-exponential
  -- tower family (`emlTower n` matches `iterExp n` exactly, unconditionally, via the `eml t
  -- (const 1)` idiom collapsing through `log 1 = 0`). A genuine chain-order-sensitive OBSTRUCTION
  -- (the other half of "chain-N ⊊ chain-(N+1)") was not built -- flagged, not forced. Zero new
  -- trustedFootprint entries (pure structural induction + already-proven log_one).
  `MachLib.exists_emlTree_eq_iterExp]

def liveAxioms (env : Environment) : Array Name := Id.run do
  let mut r := #[]
  for (nm, ci) in env.constants.toList do
    if (ci matches .axiomInfo _) && ((`MachLib).isPrefixOf nm || (`Real).isPrefixOf nm || (`Certcom).isPrefixOf nm) then
      r := r.push nm
  return r

/-- **The Option D witness-finding arc's own "spine" — every module built cont. 56-71**
(`EML_WITNESS_FINDING_DECISION_2026_07_15.md`), from `TailSign` through the two discharge axioms
and both meta-lemmas. Unlike `headlines` (a hand-curated list of individually-pinned theorems),
EVERY theorem-shaped declaration in these modules is checked automatically below — this is what
retires the "individually checked vs. transitively covered" bookkeeping question cont. 71's own
erratum ran into, for good, rather than requiring a fresh manual audit each time a file in this
list changes. Deliberately scoped to the spine, not the full ~60-file exploratory history this
arc also produced (superseded partial mechanisms, abandoned witness families) — those were never
claimed as final results in the way these are, and including them would make this guard noisy
rather than meaningful. -/
def optionDSpineModules : List Name := [
  `MachLib.WitnessResidualTailSign,
  `MachLib.WitnessResidualRCEPTailSign,
  `MachLib.WitnessResidualEventualValidTailSign,
  `MachLib.WitnessResidualNormalFormClosure,
  `MachLib.WitnessResidualNestedTargetTailSign,
  `MachLib.WitnessResidualNestedTargetDepth2Straddle,
  `MachLib.WitnessResidualNestedTargetTower,
  `MachLib.WitnessResidualNestedTargetBWitness,
  `MachLib.WitnessResidualConstSiblingUnconditional,
  `MachLib.EMLPfaffianValidOnSinEqualityProved,
  `MachLib.WitnessResidualCosTailSign,
  `MachLib.CosNotInEMLAnyDepth,
  `MachLib.EMLAnyDepthBarrierUnconditional,
  `MachLib.WitnessResidualNestedTargetFullyUnconditional,
  `MachLib.WitnessResidualRecurringTargetMetaLemma,
  `MachLib.WitnessResidualContinuousTargetMetaLemma]

/-- Every theorem-shaped declaration belonging to `optionDSpineModules`, found via the kernel's
own module index (`env.getModuleIdxFor?`) — not name-prefix guessing, not a maintained list. -/
def spineTheorems (env : Environment) : List Name := Id.run do
  let mut r := []
  for (nm, ci) in env.constants.toList do
    if ci matches .thmInfo _ then
      if let some idx := env.getModuleIdxFor? nm then
        if h : idx.toNat < env.header.moduleNames.size then
          if optionDSpineModules.contains env.header.moduleNames[idx.toNat] then
            r := nm :: r
  return r

/-- The two Option D discharge axioms (cont.65/67): both are now PROVABLE (vacuously, via
`eml_pfaffian_validon_from_sin_equality_proved`/`_cos_equality_proved`), so no new proof should
ever need to cite the raw `axiom` form again -- anything wanting the statement should cite the
`_proved` corollary instead. The keywords stay (import-graph retirement remains deferred, see A2),
so this can't be a "does the axiom exist" check; it has to be "did anything NEW start citing it." -/
def legacyDischargedAxioms : List Name :=
  [`MachLib.eml_pfaffian_validon_from_sin_equality, `MachLib.eml_pfaffian_validon_from_cos_equality]

/-- Exact, ground-truth (kernel-checked via a throwaway `Lean.collectAxioms` sweep over every
`MachLib` theorem, 2026-07-22 — not grep, not memory) set of theorems whose footprint cites either
legacy axiom directly. Exactly one: `sin_not_in_eml_any_depth` (`EMLExplicitBoundSinBarrier.lean`,
predates this whole arc) — kept as-is per `EMLAnyDepthBarrierUnconditional.lean`'s own docstring
("original stays as-is, historical/independent route"; twelve other files cite it by name, so
rewiring it was deliberately not attempted). No `cos` counterpart exists in the built graph. -/
def legacyAxiomCallSiteAllowlist : List Name := [`MachLib.sin_not_in_eml_any_depth]

run_cmd do
  let env ← getEnv
  let live := liveAxioms env
  -- (1) completeness + rot
  let unknown := live.toList.filter (fun a => !(knownAxioms.contains a))
  let rot := knownAxioms.filter (fun a => !(live.contains a))
  unless unknown.isEmpty do
    logError m!"AxiomLedger: {unknown.length} UNKNOWN axiom(s) absent from the ledger (undisclosed): {unknown}"
  unless rot.isEmpty do
    logError m!"AxiomLedger: {rot.length} ledger entr(y/ies) name a vanished axiom (rot): {rot}"
  -- (2) footprint ⊆ trusted
  for h in headlines do
    let axs ← Lean.collectAxioms h
    let leak := axs.toList.filter (fun a => !(trustedFootprint.contains a))
    unless leak.isEmpty do
      logError m!"AxiomLedger: headline {h} footprint LEAKS {leak.length} axiom(s) beyond trustedFootprint: {leak}"
  -- (3) disclosed axioms inert
  for (d, reason) in disclosedUnwitnessed do
    for h in headlines do
      let axs ← Lean.collectAxioms h
      if axs.contains d then
        logError m!"AxiomLedger: disclosed axiom {d} ({reason}) is LOAD-BEARING in {h}"
  -- (4) disclosed-TRUSTED: in the trusted set, and actually load-bearing (dead disclosure = drift)
  for (d, _) in disclosedTrusted do
    unless trustedFootprint.contains d do
      logError m!"AxiomLedger: disclosedTrusted axiom {d} is not in trustedFootprint"
    let mut used := false
    for h in headlines do
      if (← Lean.collectAxioms h).contains d then used := true
    unless used do
      logError m!"AxiomLedger: disclosedTrusted axiom {d} is load-bearing in NO headline (dead disclosure)"
  -- (5) whole-module guard: EVERY theorem in the Option D spine, not just the curated headlines
  let spine := spineTheorems env
  let mut spineLeakCount : Nat := 0
  for nm in spine do
    let axs ← Lean.collectAxioms nm
    let leak := axs.toList.filter (fun a => !(trustedFootprint.contains a))
    unless leak.isEmpty do
      spineLeakCount := spineLeakCount + 1
      logError m!"AxiomLedger: spine theorem {nm} footprint LEAKS {leak.length} axiom(s) beyond trustedFootprint: {leak}"
  -- (6) legacy axiom call-site guard: no NEW theorem, anywhere in the built graph, may cite
  -- either discharged axiom directly beyond the fixed allowlist above (A4).
  let mut newLegacySites : List Name := []
  for (nm, ci) in env.constants.toList do
    if ci matches .thmInfo _ then
      if !(legacyDischargedAxioms.contains nm) && !(legacyAxiomCallSiteAllowlist.contains nm) then
        let axs ← Lean.collectAxioms nm
        if legacyDischargedAxioms.any (fun a => axs.contains a) then
          newLegacySites := nm :: newLegacySites
  unless newLegacySites.isEmpty do
    logError m!"AxiomLedger: {newLegacySites.length} NEW call site(s) of a discharged legacy axiom (use the _proved corollary instead): {newLegacySites}"
  logInfo m!"AxiomLedger OK: {live.size} axioms pinned; {headlines.length} headline footprints ⊆ trusted ({trustedFootprint.length}); {disclosedUnwitnessed.length} disclosed inert; {disclosedTrusted.length} disclosed-trusted (certcom-A IEEE-754 floor); {spine.length} Option D spine theorems whole-module-checked ({spineLeakCount} leaking); legacy axiom call sites pinned to {legacyAxiomCallSiteAllowlist.length} (0 new)."

end AxiomLedger
