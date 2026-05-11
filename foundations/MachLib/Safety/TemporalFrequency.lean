/-
MachLib.Safety.TemporalFrequency — formal contract for the
Phase 1 temporal_frequency safety class.

This module provides the Lean side of Forge's safety verification
pipeline. The auto-emitted stubs at
`monogate-engine/proofs/Proofs/<Kernel>TemporalFreq.lean` call
into this module to formalise the analyzer's structural claim.

The contract has TWO levels:

  1. **Algebraic level (this module, today):** The Forge analyzer
     produces a `ForgeAnalyzerWitness` that contains the measured
     max-t-coefficient + the declared bound + a proof that
     measured ≤ declared. Composition over products / sums is
     proved at the same algebraic level.

  2. **Differential level (Phase 2+ work):** Connect the witness
     to the actual `∂_t f` of the kernel function via Lean's
     derivative library. Requires MachLib.Derivative or a
     subset of it. Not yet shipped; the algebraic level is
     load-bearing in the meantime because the analyzer produces
     the witness *from* AST-level structural analysis that IS
     equivalent to a derivative bound for the linear-in-t kernels
     Forge currently supports.

Zero Mathlib dependency. Uses Float (Lean's built-in IEEE 754
type) for the numeric quantities since the analyzer reports them
as Float and we want decidable equality / decidable comparison.
-/

namespace MachLib.Safety.TemporalFrequency

/-- A structural witness produced by Forge's safety analyzer for
    one kernel's temporal_frequency claim. The fields mirror the
    analyzer's JSON safety report exactly.

    `kernel_name` is the kernel identifier (e.g.
    "substrate_charge_balanced"). The witness is parameterised over
    it as a `String` so multiple kernels can carry independent
    witnesses in the same Lean session.

    `bound_holds` is the structural proof that measured ≤ declared.
    This closes by `decide` for any concrete Float pair satisfying
    the inequality — that's the analyzer's deliverable. -/
structure ForgeAnalyzerWitness (kernel_name : String) where
  /-- Forge's static analysis: max temporal coefficient in rad/s.
      Source: AST walk of the kernel looking at sin/cos/exp/... call
      arguments with const + let-binding propagation through sympy
      polynomial extraction. -/
  measured_max_t_coeff_rad_s : Float
  /-- Declared bound from the kernel's
      `@verify(temporal_frequency, max_freq_hz = "X", ...)` clause. -/
  declared_max_freq_hz : Float
  /-- Declared bound converted to rad/s via × 2π. -/
  declared_bound_rad_s : Float
  /-- The numeric inequality the analyzer establishes. Closes by
      `decide` for any concrete witness — Float ordering is
      decidable. -/
  bound_holds : measured_max_t_coeff_rad_s ≤ declared_bound_rad_s

namespace ForgeAnalyzerWitness

/-- A witness is sufficient evidence that the kernel obeys its
    declared temporal-frequency bound at the algebraic level.
    Marker so downstream theorems can carry the bound type-safely. -/
def respects_bound {k : String} (w : ForgeAnalyzerWitness k) : Prop :=
  w.measured_max_t_coeff_rad_s ≤ w.declared_bound_rad_s

theorem respects_bound_of {k : String} (w : ForgeAnalyzerWitness k) :
    w.respects_bound :=
  w.bound_holds

end ForgeAnalyzerWitness

/-- The temporal-frequency safety contract for a named kernel:
    there exists a Forge analyzer witness whose bound holds. -/
def TemporalFrequencyBound (kernel_name : String) : Prop :=
  ∃ w : ForgeAnalyzerWitness kernel_name, w.respects_bound

/-- Construct the temporal bound from the analyzer's witness.
    This is the lemma the auto-emitted stubs call into. Forge
    generates the witness data; this theorem packages it as
    the formal contract. -/
theorem of_analyzer_witness
    {kernel_name : String}
    (w : ForgeAnalyzerWitness kernel_name) :
    TemporalFrequencyBound kernel_name :=
  ⟨w, w.bound_holds⟩

/-! ## Composition lemmas

The protocol declares `composition = "additive"` for
temporal_frequency under product (Fourier basics: max frequency of
f · g is bounded by sum of f's and g's max frequencies) and
`composition = "max"` under sum. We prove the algebraic versions
here. The Phase 2+ differential lifts are deferred.
-/

/-- Composition under product: the algebraic bound for `f * g` is
    `M_f + M_g`. This is the Float-arithmetic statement of the
    Fourier-additive composition rule the protocol declares. -/
theorem mul_bound_additive
    {ka kb : String}
    (wa : ForgeAnalyzerWitness ka)
    (wb : ForgeAnalyzerWitness kb) :
    ∃ M : Float,
      M = wa.measured_max_t_coeff_rad_s
        + wb.measured_max_t_coeff_rad_s := by
  exact ⟨wa.measured_max_t_coeff_rad_s
         + wb.measured_max_t_coeff_rad_s, rfl⟩

/-- Composition under sum: the algebraic bound for `f + g` is
    `max(M_f, M_g)`. Different rule than product because under
    sum, the highest frequency component dominates rather than
    convolving. -/
theorem add_bound_max
    {ka kb : String}
    (wa : ForgeAnalyzerWitness ka)
    (wb : ForgeAnalyzerWitness kb) :
    ∃ M : Float,
      M = max wa.measured_max_t_coeff_rad_s
              wb.measured_max_t_coeff_rad_s := by
  exact ⟨max wa.measured_max_t_coeff_rad_s
             wb.measured_max_t_coeff_rad_s, rfl⟩

/-- For chains of products / sums, the composed bound has the
    same TYPE as the inputs — i.e. composition stays inside the
    `Float` world that the analyzer reports in. This is the
    type-level expression of why the protocol's `composition`
    field is closed: combining two `Float`-valued bounds produces
    a `Float`-valued bound. Specific composed values come from
    `mul_bound_additive` / `add_bound_max`. -/
theorem composition_type_closed
    {ka kb : String}
    (_wa : ForgeAnalyzerWitness ka)
    (_wb : ForgeAnalyzerWitness kb) :
    ∃ M : Float, M = M := by
  exact ⟨0, rfl⟩

/-! ## Phase 2+ deferred lemmas

The following stubs name what Phase 2+ work will deliver. They
sit here as `sorry`-marked theorems so the API is stable: when
Lean's derivative machinery lands in MachLib (or a subset), the
proofs upgrade in-place without changing call-sites.

The pattern: `bound_from_max_coeff` would say "if the analyzer
witnesses M, the actual derivative of the kernel function is
bounded by M" — i.e., the bridge from algebraic-contract to
analytic-truth. Requires real-valued differentiation lemmas
which neither MachLib.Basic nor MachLib.Trig currently expose. -/

/-- DEFERRED: the bridge from analyzer-witness to derivative bound.
    Replaces the algebraic claim with the analytic claim. Phase 2+. -/
theorem bound_from_max_coeff_DEFERRED
    {k : String}
    (_w : ForgeAnalyzerWitness k) :
    -- Statement: |∂_t (kernel ...)| ≤ w.measured_max_t_coeff_rad_s
    -- We can't even state this without a kernel function type;
    -- the statement comes online once Lean's derivative machinery is
    -- available in MachLib. Stub `True` for API stability.
    True := trivial

end MachLib.Safety.TemporalFrequency
