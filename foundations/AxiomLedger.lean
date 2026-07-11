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
def knownAxioms : List Name := [`Certcom.realToR, `Certcom.real_fpbridge, `MachLib.HighDimensional.BaselineReplayValid, `MachLib.HighDimensional.BoundaryDominatesCenter, `MachLib.HighDimensional.BoundaryDynamicsObligation, `MachLib.HighDimensional.BoundaryInterventionPair, `MachLib.HighDimensional.BoundaryRunPacket, `MachLib.HighDimensional.BoundedEvaluationObligation, `MachLib.HighDimensional.ClampDeshelfInterventionObligation, `MachLib.HighDimensional.ClampInvariantObligation, `MachLib.HighDimensional.DomainPreservationObligation, `MachLib.HighDimensional.DomainPreserved, `MachLib.HighDimensional.GuardedBoundaryMode, `MachLib.HighDimensional.InterventionSoundnessObligation, `MachLib.HighDimensional.LogDomainBoundaryMode, `MachLib.HighDimensional.OutputSafetyInterventionObligation, `MachLib.HighDimensional.OutputSafetyObligation, `MachLib.HighDimensional.PacketHasEvent, `MachLib.HighDimensional.PacketHasTransition, `MachLib.HighDimensional.PairHasRescueTransition, `MachLib.HighDimensional.PairNonregressingSurvival, `MachLib.HighDimensional.PairUsesIntervention, `MachLib.HighDimensional.PositiveCoordinateInterventionObligation, `MachLib.HighDimensional.PositiveCoordinateObligation, `MachLib.HighDimensional.PrecisionEscapeInterventionObligation, `MachLib.HighDimensional.PrecisionSensitivityObligation, `MachLib.HighDimensional.ReplayPacket, `MachLib.HighDimensional.TendstoTo, `MachLib.HighDimensional.ValidBoundaryRunPacket, `MachLib.HighDimensional.ValidGuards, `MachLib.HighDimensional.ValidInterventionPair, `MachLib.HighDimensional.ValidTransitionGraph, `MachLib.HighDimensional.ballCubeRatio, `MachLib.HighDimensional.boundary_dominates_center_from_packet, `MachLib.HighDimensional.cubeBoundaryShellProbability, `MachLib.HighDimensional.cubeBoundaryShellProbability_tends_one, `MachLib.HighDimensional.domain_to_log_domain_rescue_obligation, `MachLib.HighDimensional.domain_wall_obligation, `MachLib.HighDimensional.firstLayerSurvival, `MachLib.HighDimensional.firstLayerSurvival_decay, `MachLib.HighDimensional.guard_clamp_intervention_obligation, `MachLib.HighDimensional.guard_rescue_obligation, `MachLib.HighDimensional.guarded_boundary_packet_finite_survival_nonneg, `MachLib.HighDimensional.interior_sample_obligation, `MachLib.HighDimensional.log_domain_boundary_packet_finite_survival_nonneg, `MachLib.HighDimensional.log_domain_lift_intervention_obligation, `MachLib.HighDimensional.log_domain_rescue_obligation, `MachLib.HighDimensional.overflow_to_guard_rescue_obligation, `MachLib.HighDimensional.overflow_wall_obligation, `MachLib.HighDimensional.packetBoundaryHits, `MachLib.HighDimensional.packetCenterHits, `MachLib.HighDimensional.packetFiniteSurvivalRate, `MachLib.HighDimensional.packetTransitionEntropy, `MachLib.HighDimensional.phantom_attractor_obligation, `MachLib.HighDimensional.precision_escape_intervention_obligation, `MachLib.HighDimensional.saturation_deshelf_intervention_obligation, `MachLib.HighDimensional.saturation_shelf_obligation, `MachLib.HighDimensional.transition_graph_obligation, `MachLib.IsAnalyticOnReals, `MachLib.Model.intModel._elambda_1, `MachLib.Model.intModel._elambda_2, `MachLib.Model.intModel._elambda_3, `MachLib.Model.intModel._elambda_4, `MachLib.Model.intModel._elambda_5, `MachLib.Real, `MachLib.Real.HasDerivAt, `MachLib.Real.HasDerivAt_add, `MachLib.Real.HasDerivAt_atan, `MachLib.Real.HasDerivAt_comp, `MachLib.Real.HasDerivAt_const, `MachLib.Real.HasDerivAt_cos, `MachLib.Real.HasDerivAt_exp, `MachLib.Real.HasDerivAt_id, `MachLib.Real.HasDerivAt_inv, `MachLib.Real.HasDerivAt_log_pos, `MachLib.Real.HasDerivAt_mul, `MachLib.Real.HasDerivAt_neg, `MachLib.Real.HasDerivAt_of_eq, `MachLib.Real.HasDerivAt_sin, `MachLib.Real.HasDerivAt_sub, `MachLib.Real.HasDerivAt_unique, `MachLib.Real.PfaffianFunction.zero_count_bound_classical, `MachLib.Real.addR, `MachLib.Real.add_assoc, `MachLib.Real.add_comm, `MachLib.Real.add_lt_add_left, `MachLib.Real.add_neg, `MachLib.Real.add_zero, `MachLib.Real.arccos, `MachLib.Real.arccos_le_pi, `MachLib.Real.arccos_nonneg, `MachLib.Real.arccos_one, `MachLib.Real.arccos_zero, `MachLib.Real.archimedean, `MachLib.Real.arcsin, `MachLib.Real.arcsin_one, `MachLib.Real.arcsin_zero, `MachLib.Real.arctan, `MachLib.Real.arctan_lt_pi_div_two, `MachLib.Real.atan, `MachLib.Real.atan2, `MachLib.Real.atan2_le_pi, `MachLib.Real.atan2_one_zero, `MachLib.Real.atan2_zero_one, `MachLib.Real.atan_zero, `MachLib.Real.cos, `MachLib.Real.cos_add, `MachLib.Real.cos_arccos, `MachLib.Real.cos_neg, `MachLib.Real.cos_periodic, `MachLib.Real.cos_pi, `MachLib.Real.cos_pi_div_two, `MachLib.Real.cos_zero, `MachLib.Real.cosh, `MachLib.Real.cosh_eq, `MachLib.Real.cosh_ge_one, `MachLib.Real.cosh_pos, `MachLib.Real.divR, `MachLib.Real.div_def, `MachLib.Real.div_lt_one_of_pos_lt, `MachLib.Real.div_zero, `MachLib.Real.erf, `MachLib.Real.erf_le_one, `MachLib.Real.exp, `MachLib.Real.exp10, `MachLib.Real.exp10_def, `MachLib.Real.exp10_log10_inverse, `MachLib.Real.exp10_zero, `MachLib.Real.exp_add, `MachLib.Real.exp_exp_minus_exp_strictly_increasing, `MachLib.Real.exp_gt_one_plus_self, `MachLib.Real.exp_gt_two_x, `MachLib.Real.exp_lt, `MachLib.Real.exp_one_lt_three, `MachLib.Real.exp_pos, `MachLib.Real.exp_surj, `MachLib.Real.exp_zero, `MachLib.Real.floor, `MachLib.Real.floor_le, `MachLib.Real.floor_zero, `MachLib.Real.interval_scale_unit_lit_le, `MachLib.Real.interval_weight_sum_le, `MachLib.Real.leR, `MachLib.Real.le_iff_lt_or_eq, `MachLib.Real.le_sqrt_of_sq_le, `MachLib.Real.lit_one_eq, `MachLib.Real.lit_zero_eq, `MachLib.Real.log10, `MachLib.Real.log10_def, `MachLib.Real.log10_zero, `MachLib.Real.ltR, `MachLib.Real.lt_floor_add_one, `MachLib.Real.lt_irrefl_ax, `MachLib.Real.lt_total, `MachLib.Real.lt_trans_ax, `MachLib.Real.mulR, `MachLib.Real.mul_assoc, `MachLib.Real.mul_comm, `MachLib.Real.mul_distrib, `MachLib.Real.mul_inv, `MachLib.Real.mul_lt_mul_of_pos_right, `MachLib.Real.mul_one_ax, `MachLib.Real.mul_pos, `MachLib.Real.natCast, `MachLib.Real.natCast_succ, `MachLib.Real.natCast_zero, `MachLib.Real.negR, `MachLib.Real.neg_one_le_erf, `MachLib.Real.neg_one_lt_tanh, `MachLib.Real.neg_pi_div_two_lt_arctan, `MachLib.Real.neg_pi_lt_atan2, `MachLib.Real.oneR, `MachLib.Real.one_add_le_exp, `MachLib.Real.one_div_nonneg_of_pos, `MachLib.Real.one_div_pos_of_pos, `MachLib.Real.pi, `MachLib.Real.pi_gt_one, `MachLib.Real.pi_gt_three, `MachLib.Real.pi_pos, `MachLib.Real.pythagorean, `MachLib.Real.realOfScientific, `MachLib.Real.realOfScientific_clears, `MachLib.Real.realOfScientific_le_of_nat, `MachLib.Real.realOfScientific_lt_of_nat, `MachLib.Real.realOfScientific_one_dot_zero, `MachLib.Real.realOfScientific_pos, `MachLib.Real.realOfScientific_three_dot_zero, `MachLib.Real.realOfScientific_two_dot_zero, `MachLib.Real.realPow, `MachLib.Real.realPow_nonneg, `MachLib.Real.realPow_one, `MachLib.Real.realPow_pos, `MachLib.Real.realPow_zero, `MachLib.Real.rolle_ct, `MachLib.Real.sin, `MachLib.Real.sin_add, `MachLib.Real.sin_arcsin, `MachLib.Real.sin_neg, `MachLib.Real.sin_one_pos, `MachLib.Real.sin_periodic, `MachLib.Real.sin_pi, `MachLib.Real.sin_pi_div_two, `MachLib.Real.sin_zero, `MachLib.Real.sinh, `MachLib.Real.sinh_eq, `MachLib.Real.sqrt, `MachLib.Real.sqrt_le_of_le_sq, `MachLib.Real.sqrt_neg_zero, `MachLib.Real.sqrt_nonneg, `MachLib.Real.sqrt_one, `MachLib.Real.sqrt_sq_nonneg, `MachLib.Real.sqrt_zero, `MachLib.Real.subR, `MachLib.Real.sub_def, `MachLib.Real.sup_exists, `MachLib.Real.tan, `MachLib.Real.tan_def, `MachLib.Real.tan_half_pos, `MachLib.Real.tanh, `MachLib.Real.tanh_eq_sinh_div_cosh, `MachLib.Real.tanh_lt_one, `MachLib.Real.tanh_neg, `MachLib.Real.tanh_zero, `MachLib.Real.u, `MachLib.Real.u_le_one, `MachLib.Real.u_nonneg, `MachLib.Real.zeroR, `MachLib.Real.zero_lt_one_ax, `MachLib.Real.zero_ne_one_ax, `MachLib.analytic_add, `MachLib.analytic_comp, `MachLib.analytic_const, `MachLib.analytic_exp, `MachLib.analytic_finite_zeros_compact, `MachLib.analytic_id, `MachLib.analytic_log_pos, `MachLib.analytic_mul, `MachLib.analytic_ne_zero_nbhd, `MachLib.analytic_one_div_pos, `MachLib.analytic_sin, `MachLib.analytic_sub, `MachLib.chain_algebraic_dependence, `MachLib.emlEmptyChain._elambda_1, `MachLib.emlEmptyChain._elambda_2, `MachLib.eml_pfaffian_validon_from_cos_equality, `MachLib.eml_pfaffian_validon_from_sin_equality, `MachLib.eml_tree_analytic_on_pos, `MachLib.exp_tangent_line_strict, `MachLib.lambertW, `MachLib.lambertW_one_lt_one, `MachLib.lambertW_one_pos, `MachLib.lambertW_zero, `MachLib.pi_div_one_plus_one_lt_pi, `MachLib.pi_div_one_plus_one_pos]

/-- Axioms permitted in a trustworthy shipped footprint: witnessed foundational core -/
def trustedFootprint : List Name := [`Certcom.realToR, `Certcom.real_fpbridge, `MachLib.Real.u, `MachLib.Real.u_nonneg, `MachLib.Real.mul_lt_mul_of_pos_right, `Classical.choice, `MachLib.IsAnalyticOnReals, `MachLib.Real, `MachLib.Real.HasDerivAt, `MachLib.Real.HasDerivAt_add, `MachLib.Real.HasDerivAt_comp, `MachLib.Real.HasDerivAt_const, `MachLib.Real.HasDerivAt_exp, `MachLib.Real.HasDerivAt_id, `MachLib.Real.HasDerivAt_inv, `MachLib.Real.HasDerivAt_log_pos, `MachLib.Real.HasDerivAt_mul, `MachLib.Real.HasDerivAt_sub, `MachLib.Real.HasDerivAt_unique, `MachLib.Real.addR, `MachLib.Real.add_assoc, `MachLib.Real.add_comm, `MachLib.Real.add_lt_add_left, `MachLib.Real.add_neg, `MachLib.Real.add_zero, `MachLib.Real.divR, `MachLib.Real.div_def, `MachLib.Real.exp, `MachLib.Real.exp_pos, `MachLib.Real.exp_surj, `MachLib.Real.leR, `MachLib.Real.le_iff_lt_or_eq, `MachLib.Real.ltR, `MachLib.Real.lt_irrefl_ax, `MachLib.Real.lt_total, `MachLib.Real.lt_trans_ax, `MachLib.Real.mulR, `MachLib.Real.mul_assoc, `MachLib.Real.mul_comm, `MachLib.Real.mul_distrib, `MachLib.Real.mul_inv, `MachLib.Real.mul_one_ax, `MachLib.Real.mul_pos, `MachLib.Real.natCast, `MachLib.Real.natCast_succ, `MachLib.Real.natCast_zero, `MachLib.Real.negR, `MachLib.Real.oneR, `MachLib.Real.one_div_pos_of_pos, `MachLib.Real.rolle_ct, `MachLib.Real.subR, `MachLib.Real.sub_def, `MachLib.Real.zeroR, `MachLib.Real.zero_lt_one_ax, `MachLib.Real.zero_ne_one_ax, `MachLib.analytic_add, `MachLib.analytic_comp, `MachLib.analytic_const, `MachLib.analytic_exp, `MachLib.analytic_id, `MachLib.analytic_log_pos, `MachLib.analytic_mul, `MachLib.analytic_one_div_pos, `MachLib.analytic_sub, `Quot.sound, `propext]

/-- Unwitnessed-but-disclosed axioms + machine-readable reason. Must stay inert. -/
def disclosedUnwitnessed : List (Name × String) := [(`MachLib.Real.erf, "blocked-upstream (erf absent from Mathlib)"), (`MachLib.Real.erf_le_one, "blocked-upstream (erf absent from Mathlib)"), (`MachLib.Real.neg_one_le_erf, "blocked-upstream (erf absent from Mathlib)"), (`MachLib.eml_tree_analytic_on_pos, "unwitnessed-but-SOUND: EMLLogArgPosOnIoi side-condition restored (was false-as-stated, fixed); real-analyticity of well-formed EML trees not yet proven in machlib; in NO footprint")]

/-- Disclosed-yet-load-bearing-BY-DESIGN: the certcom Theorem-A IEEE-754 model. Un-witnessable
(Lean `Float` is opaque), so — unlike `disclosedUnwitnessed`, which must stay inert — these are the
terminal trust under the Theorem-A headline. They live in `trustedFootprint`; listed here so the
trust they carry is named, not hidden among the ℝ-witnessed axioms. -/
def disclosedTrusted : List (Name × String) := [(`Certcom.realToR, "IEEE-754 denotation Float→Real (Float opaque, no in-Lean semantics)"), (`Certcom.real_fpbridge, "standard model: every basic float op correctly rounded (rel err ≤ u), neg exact — un-witnessable in Lean; Flocq-scale to ground further")]

/-- Shipped headline theorems whose footprint the gate pins. -/
def headlines : List Name := [`MachLib.KhovanskiiConcrete.eexp_barrier_zero_count_le_47, `MachLib.eml_eval_boundedZeros, `MachLib.IterExpDepthN.chainN_khovanskii_bound_unconditional, `MachLib.IterExpDepthN.chainN_khovanskii_bound_explicit, `Certcom.pipeline_det_grounded, `Certcom.pipeline_arith_grounded, `Certcom.pid_grounded]

def liveAxioms (env : Environment) : Array Name := Id.run do
  let mut r := #[]
  for (nm, ci) in env.constants.toList do
    if (ci matches .axiomInfo _) && ((`MachLib).isPrefixOf nm || (`Real).isPrefixOf nm || (`Certcom).isPrefixOf nm) then
      r := r.push nm
  return r

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
  logInfo m!"AxiomLedger OK: {live.size} axioms pinned; {headlines.length} headline footprints ⊆ trusted ({trustedFootprint.length}); {disclosedUnwitnessed.length} disclosed inert; {disclosedTrusted.length} disclosed-trusted (certcom-A IEEE-754 floor)."

end AxiomLedger
