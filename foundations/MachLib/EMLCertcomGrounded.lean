import MachLib.EMLCertcomQuantitativeBridge
import MachLib.FPGrounding

/-!
# Fully grounded: no free hypotheses beyond Certcom's own disclosed axioms

`EMLCertcomQuantitativeBridge.lean` closed the uniformity and Real→Float-quantization gaps, but
still carried THREE free hypotheses per call: `hround_exp`/`hround_ln` (an abstract, `u`-relative
rounding shape) and `round`/`hround_q` (an abstract quantization map). `FPGrounding.lean` shows this
codebase already has REAL, disclosed axioms for exactly the first two — `real_exp_rounds`/
`real_log_rounds`, ABSOLUTE-epsilon bounds (not `u`-relative) against the concrete runtime basis
`leanPrims`, discharged the same way `pid_exp_grounded`/`pid_log_grounded` ground their own
kernel. This file re-derives the uniform + quantized-pointwise + witness trio directly against
`realToR`/`real_fpbridge`/`real_exp_rounds`/`real_log_rounds` — no `∀ toR, FPBridge toR → …`,
no `∀`-primitive rounding hypothesis, matching every other `pid_*_grounded` theorem's own shape.

The third hypothesis — `round`/`hround_q`, "some reasonable Real→Float quantization exists" — has
no existing counterpart anywhere in this codebase: Certcom only ever needs Float→Real (it compiles
EML to C and runs on floats; it never needs to turn an arbitrary mathematical real into a float).
That direction is needed here specifically because Option D's non-approximation theorem quantifies
over ALL reals in an interval, not just Float-representable ones. It gets the SAME treatment as
`realToR`/`real_fpbridge`: a new disclosed axiom pair (`floatOfR`, `real_round_eps`/
`real_round_bounds`), same un-witnessability reason (`Float` is opaque), registered in
`AxiomLedger`'s `disclosedTrusted` alongside the rest of the IEEE-754 floor.
-/

namespace Certcom

open MachLib MachLib.Real

/-- The `Float` that a standard real→float quantization (e.g. round-to-nearest) assigns to a real
`x`. Opaque, like `realToR`: Lean's `Float` has no in-Lean constructive "quantize an arbitrary real"
operation, so this map is axiomatized, not defined. -/
axiom floatOfR : Real → Float

/-- The disclosed real→Float quantization bound. Same status as `real_exp_eps`/`real_log_eps` (a
global absolute constant, not a magnitude-dependent one — matching this codebase's existing
convention for every other libm rounding constant). -/
axiom real_round_eps : MachLib.Real

/-- **The disclosed real→Float quantization model.** Every real, quantized via `floatOfR` and read
back through `realToR`, lands within `real_round_eps` of the original real — the standard
"correctly-rounded input" fact underlying a compiled kernel's very first step (turning a
mathematical real-valued input into its float representation). Un-witnessable in Lean (`Float` is
opaque); the terminal floor of this direction of the Float↔Real bridge, disclosed exactly like
`real_fpbridge`. -/
axiom real_round_bounds : ∀ x : Real, abs (realToR (floatOfR x) - x) ≤ real_round_eps

/-- `real_round_eps` is non-negative — not a separate axiom, derived from `real_round_bounds` itself
(`0 ≤ abs (...) ≤ real_round_eps` at any point, e.g. `x = 0`). -/
theorem real_round_eps_nonneg : (0 : MachLib.Real) ≤ real_round_eps :=
  le_trans (abs_nonneg _) (real_round_bounds 0)

/-- **Part 1, grounded.** `eml_var_var_pipeline_uniform`, with the abstract `u`-relative `hround_exp`/
`hround_ln` hypotheses replaced by the REAL, already-disclosed `real_exp_rounds`/`real_log_rounds`
axioms against the concrete `leanPrims` runtime basis — no `∀`-primitive rounding hypothesis. -/
theorem eml_var_var_pipeline_uniform_grounded (env : Env) (A B : MachLib.Real) (hA1 : 1 ≤ A)
    (hlo : A ≤ realToR (env "x").toF) (hhi : realToR (env "x").toF ≤ B) :
    AbsEnc (u * ((exp B + real_exp_eps) + (log B + real_log_eps)) + (real_exp_eps + real_log_eps))
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC emlVarVar)).toF)
      (exp (realToR (env "x").toF) - log (realToR (env "x").toF)) := by
  have hX1 : (1 : MachLib.Real) ≤ realToR (env "x").toF := le_trans hA1 hlo
  have hX0 : (0 : MachLib.Real) < realToR (env "x").toF := lt_of_lt_of_le zero_lt_one_ax hX1
  have hE1 : AbsEnc real_exp_eps
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .exp (.var "x")))).toF)
      (exp (realToR (env "x").toF)) := by
    have heq : (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .exp (.var "x")))).toF
        = stdI1 leanPrims .exp (env "x").toF := by
      show stdR1 leanPrims (Trans1.exp).cName (env "x").toF = stdI1 leanPrims .exp (env "x").toF
      exact std_hrt1 leanPrims .exp (env "x").toF
    rw [heq]; exact real_exp_rounds (env "x").toF
  have hE2 : AbsEnc real_log_eps
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .ln (.var "x")))).toF)
      (log (realToR (env "x").toF)) := by
    have heq : (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .ln (.var "x")))).toF
        = stdI1 leanPrims .ln (env "x").toF := by
      show stdR1 leanPrims (Trans1.ln).cName (env "x").toF = stdI1 leanPrims .ln (env "x").toF
      exact std_hrt1 leanPrims .ln (env "x").toF
    rw [heq]; exact real_log_rounds (env "x").toF
  have hsub : RoundsW u (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC emlVarVar)).toF)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .exp (.var "x")))).toF
        - realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .ln (.var "x")))).toF) := by
    show RoundsW u
        (realToR ((evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .exp (.var "x")))).toF
            - (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .ln (.var "x")))).toF))
        (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .exp (.var "x")))).toF
          - realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (.tr1 .ln (.var "x")))).toF)
    exact real_fpbridge.sub _ _
  have htight := absenc_sub hE1 hE2 hsub
  have hEexp : abs (exp (realToR (env "x").toF)) = exp (realToR (env "x").toF) :=
    abs_of_nonneg (le_of_lt (exp_pos _))
  have hElog : abs (log (realToR (env "x").toF)) = log (realToR (env "x").toF) :=
    abs_of_nonneg (log_nonneg hX1)
  rw [hEexp, hElog] at htight
  have hloosen : u * ((exp (realToR (env "x").toF) + real_exp_eps)
        + (log (realToR (env "x").toF) + real_log_eps)) + (real_exp_eps + real_log_eps)
      ≤ u * ((exp B + real_exp_eps) + (log B + real_log_eps)) + (real_exp_eps + real_log_eps) := by
    have hstep : exp (realToR (env "x").toF) + real_exp_eps + (log (realToR (env "x").toF) + real_log_eps)
        ≤ exp B + real_exp_eps + (log B + real_log_eps) :=
      add_le_add (add_le_add (exp_monotone hhi) (le_refl real_exp_eps))
        (add_le_add (log_le_log hX0 hhi) (le_refl real_log_eps))
    exact add_le_add (mul_le_mul_of_nonneg_left hstep u_nonneg) (le_refl _)
  unfold AbsEnc at htight ⊢
  exact le_trans htight hloosen

/-- **Part 2, grounded.** `eml_var_var_quantized_pointwise`, with `round`/`ρ`/`hround_q` replaced by
the disclosed `floatOfR`/`real_round_eps`/`real_round_bounds`. -/
theorem eml_var_var_quantized_pointwise_grounded (env : Env) (A B : MachLib.Real)
    (hAρ : 1 ≤ A - real_round_eps) (x : Real) (hxA : A < x) (hxB : x < B) :
    abs (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt env floatOfR x)
        (emitC emlVarVar)).toF - (EMLTree.eml EMLTree.var EMLTree.var).eval x)
      ≤ u * ((exp (B + real_round_eps) + real_exp_eps) + (log (B + real_round_eps) + real_log_eps))
          + (real_exp_eps + real_log_eps)
        + (exp (B + real_round_eps) + 1 / (A - real_round_eps)) * real_round_eps := by
  have hAρ' : (0 : MachLib.Real) < A - real_round_eps := lt_of_lt_of_le zero_lt_one_ax hAρ
  have hclose : abs (realToR (floatOfR x) - x) ≤ real_round_eps := real_round_bounds x
  have h1 : -real_round_eps ≤ realToR (floatOfR x) - x := (abs_le_iff.mp hclose).1
  have h5 : realToR (floatOfR x) - x ≤ real_round_eps := (abs_le_iff.mp hclose).2
  have h3 : x + -real_round_eps = x - real_round_eps := by mach_mpoly [x, real_round_eps]
  have h4 : x + (realToR (floatOfR x) - x) = realToR (floatOfR x) := by
    mach_mpoly [x, realToR (floatOfR x)]
  have h2 : x - real_round_eps ≤ realToR (floatOfR x) := by
    have h2' : x + -real_round_eps ≤ x + (realToR (floatOfR x) - x) := add_le_add_left h1 x
    rw [h3, h4] at h2'; exact h2'
  have h6 : realToR (floatOfR x) ≤ x + real_round_eps := by
    have h6' : x + (realToR (floatOfR x) - x) ≤ x + real_round_eps := add_le_add_left h5 x
    rw [h4] at h6'; exact h6'
  have hAρA : A - real_round_eps ≤ A := sub_le_self real_round_eps_nonneg
  have hBBρ : B ≤ B + real_round_eps := by
    have e : B + 0 = B := by mach_mpoly [B]
    have h := add_le_add_left real_round_eps_nonneg B
    rw [e] at h; exact h
  have hloX' : A - real_round_eps ≤ realToR (floatOfR x) :=
    le_trans (sub_le_sub_right (le_of_lt hxA) real_round_eps) h2
  have hhiX' : realToR (floatOfR x) ≤ B + real_round_eps :=
    le_trans h6 (add_le_add (le_of_lt hxB) (le_refl real_round_eps))
  have hlox : A - real_round_eps ≤ x := le_trans hAρA (le_of_lt hxA)
  have hhix : x ≤ B + real_round_eps := le_trans (le_of_lt hxB) hBBρ
  have hp1 := eml_var_var_pipeline_uniform_grounded (envAt env floatOfR x)
    (A - real_round_eps) (B + real_round_eps) hAρ
    (by rw [envAt_x_toF]; exact hloX') (by rw [envAt_x_toF]; exact hhiX')
  rw [envAt_x_toF] at hp1
  have hlip_exp : abs (exp (realToR (floatOfR x)) - exp x)
      ≤ exp (B + real_round_eps) * abs (realToR (floatOfR x) - x) :=
    exp_lip_local (A - real_round_eps) (B + real_round_eps) (realToR (floatOfR x)) x
      hloX' hhiX' hlox hhix
  have hlip_log : abs (log (realToR (floatOfR x)) - log x)
      ≤ (1 / (A - real_round_eps)) * abs (realToR (floatOfR x) - x) :=
    log_lip_local (A - real_round_eps) (B + real_round_eps) hAρ' (realToR (floatOfR x)) x
      hloX' hhiX' hlox hhix
  have htri : abs ((exp (realToR (floatOfR x)) - log (realToR (floatOfR x))) - (exp x - log x))
      ≤ abs (exp (realToR (floatOfR x)) - exp x) + abs (log (realToR (floatOfR x)) - log x) := by
    have e : (exp (realToR (floatOfR x)) - log (realToR (floatOfR x))) - (exp x - log x)
        = (exp (realToR (floatOfR x)) - exp x) - (log (realToR (floatOfR x)) - log x) := by
      mach_mpoly [exp (realToR (floatOfR x)), log (realToR (floatOfR x)), exp x, log x]
    rw [e]; exact abs_sub_le' _ _
  have hfactor : exp (B + real_round_eps) * abs (realToR (floatOfR x) - x)
        + (1 / (A - real_round_eps)) * abs (realToR (floatOfR x) - x)
      = (exp (B + real_round_eps) + 1 / (A - real_round_eps)) * abs (realToR (floatOfR x) - x) := by
    mach_mpoly [exp (B + real_round_eps), (1 : MachLib.Real) / (A - real_round_eps),
      abs (realToR (floatOfR x) - x)]
  have hnnfactor : (0 : MachLib.Real) ≤ exp (B + real_round_eps) + 1 / (A - real_round_eps) :=
    add_nonneg (le_of_lt (exp_pos _)) (le_of_lt (one_div_pos_of_pos hAρ'))
  have hlipbound : abs ((exp (realToR (floatOfR x)) - log (realToR (floatOfR x))) - (exp x - log x))
      ≤ (exp (B + real_round_eps) + 1 / (A - real_round_eps)) * real_round_eps := by
    have step1 : abs ((exp (realToR (floatOfR x)) - log (realToR (floatOfR x))) - (exp x - log x))
        ≤ (exp (B + real_round_eps) + 1 / (A - real_round_eps)) * abs (realToR (floatOfR x) - x) := by
      rw [← hfactor]; exact le_trans htri (add_le_add hlip_exp hlip_log)
    exact le_trans step1 (mul_le_mul_of_nonneg_left hclose hnnfactor)
  have heq : realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt env floatOfR x)
        (emitC emlVarVar)).toF - (EMLTree.eml EMLTree.var EMLTree.var).eval x
      = (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt env floatOfR x)
            (emitC emlVarVar)).toF
          - (exp (realToR (floatOfR x)) - log (realToR (floatOfR x))))
        + ((exp (realToR (floatOfR x)) - log (realToR (floatOfR x))) - (exp x - log x)) := by
    rw [emlVarVar_eval]
    mach_mpoly [realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt env floatOfR x)
      (emitC emlVarVar)).toF, exp (realToR (floatOfR x)), log (realToR (floatOfR x)), exp x, log x]
  rw [heq]
  refine le_trans (abs_add _ _) ?_
  refine add_le_add ?_ hlipbound
  unfold AbsEnc at hp1
  exact hp1

open MachLib.EMLExplicitBound in
/-- **The fully grounded `hround` instantiation.** For `T := EMLTree.eml EMLTree.var EMLTree.var`
(`T.eval x = exp x − log x`), Certcom's actual disclosed grounding axioms — `realToR`,
`real_fpbridge`, `real_exp_rounds`, `real_log_rounds`, and the new `floatOfR`/`real_round_bounds` —
together deliver `certcom_total_error_floor_compact_interval`'s `hround`, with **no `∀`-primitive
rounding hypothesis and no abstract quantization hypothesis**: every free parameter this theorem
takes is either a genuine mathematical quantity (`A`, `B`, `ε`, `env`) or a side condition on those
quantities (`hA0`, `hεlt1`, `hAρ`, `hδε`, `hMB`) — not a further disclosed-primitive assumption. -/
theorem eml_var_var_certcom_witness_grounded (env : Env) (A B ε : MachLib.Real)
    (hA0 : A < ext 0) (hεlt1 : ε < 1) (hAρ : 1 ≤ A - real_round_eps)
    (hδε : u * ((exp (B + real_round_eps) + real_exp_eps) + (log (B + real_round_eps) + real_log_eps))
          + (real_exp_eps + real_log_eps)
        + (exp (B + real_round_eps) + 1 / (A - real_round_eps)) * real_round_eps < ε)
    (hMB : ext (combinedBoundE
        (len (EMLTree.eml EMLTree.var EMLTree.var) 0)
        (enc (EMLTree.eml EMLTree.var EMLTree.var) emlEmptyChain).1
        (encTags (EMLTree.eml EMLTree.var EMLTree.var) emlEmptyChain ())
        (enc (EMLTree.eml EMLTree.var EMLTree.var) emlEmptyChain).2 + 1) < B) :
    ∃ x : MachLib.Real, A < x ∧ x < B ∧
      ε - (u * ((exp (B + real_round_eps) + real_exp_eps) + (log (B + real_round_eps) + real_log_eps))
            + (real_exp_eps + real_log_eps)
          + (exp (B + real_round_eps) + 1 / (A - real_round_eps)) * real_round_eps)
        ≤ abs (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt env floatOfR x)
            (emitC emlVarVar)).toF - Real.sin x) := by
  have hA0' : (0 : MachLib.Real) < A :=
    lt_of_lt_of_le zero_lt_one_ax (le_trans hAρ (sub_le_self real_round_eps_nonneg))
  have hvalidon : EMLPfaffianValidOn (EMLTree.eml EMLTree.var EMLTree.var) A B :=
    ⟨trivial, trivial, fun x hxA _ => lt_of_lt_of_le hA0' (le_of_lt hxA)⟩
  exact certcom_total_error_floor_compact_interval (EMLTree.eml EMLTree.var EMLTree.var) A B ε
    (u * ((exp (B + real_round_eps) + real_exp_eps) + (log (B + real_round_eps) + real_log_eps))
        + (real_exp_eps + real_log_eps)
      + (exp (B + real_round_eps) + 1 / (A - real_round_eps)) * real_round_eps)
    hA0 hεlt1 hδε hvalidon
    (fun x => realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt env floatOfR x)
      (emitC emlVarVar)).toF)
    (fun x hxA hxB => eml_var_var_quantized_pointwise_grounded env A B hAρ x hxA hxB)
    hMB

end Certcom
