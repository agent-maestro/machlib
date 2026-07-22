import MachLib.EMLCertcomBridge
import MachLib.CertcomCompactIntervalHandshake
import MachLib.ExpLipschitz
import MachLib.TransNodes
import MachLib.SignTactic

/-!
# From a pointwise bridge to a real `hround` instantiation

`EMLCertcomBridge.lean` certified Certcom's compiled evaluation of `emlVarVar` against its exact
value POINTWISE, at one environment. This file closes the two gaps that file's docstring left open:

1. **Uniformity.** The pointwise bound's error term depends on the evaluation point. Here it is
   made uniform over a whole interval `[A, B]` (`1 ≤ A`, so `log` stays non-negative throughout,
   avoiding a sign split) by deriving the two leaf-level roundings DIRECTLY from the primitive
   `hround` hypotheses rather than through `pipeline_nested_std`'s existential, StdLip-generic bound
   — the existential form deliberately has no closed formula (`AbsoluteFoldNest.lean`'s own
   docstring), so it cannot be bounded uniformly without first re-deriving the leaf case by hand.

2. **The deeper gap.** `certcom_total_error_floor_compact_interval`'s `compiled : Real → Real` is
   asked for a value at EVERY real in `(A, B)` — uncountably many — but a compiled artifact only has
   behavior at Float-representable inputs. Closed here with an explicit, honestly-disclosed
   quantization hypothesis (`round : Real → Float`, `hround_q`, matching the existing house pattern
   of treating IEEE-754 facts as hypotheses, not internally derived — same status as `FPBridge`
   itself) plus propagating the resulting input error through `exp`/`log`'s own local-Lipschitz
   bounds (`exp_lip_local`, `log_lip_local`, already proven in `ExpLipschitz.lean`/`TransNodes.lean`
   for exactly this purpose).

Composing both gives `eml_var_var_certcom_witness`: a genuine instantiation of
`certcom_total_error_floor_compact_interval`'s `hround` for a real translated `EMLTree`, with an
EXPLICIT `δ` in terms of `u`, `A`, `B`, and the quantization bound `ρ` — not an abstract hypothesis.
-/

namespace Certcom

open MachLib MachLib.Real

/-- The environment binding `"x"` to the Float `round x` — a plain top-level `def` (not a tactic-mode
`set`/`let`, which this codebase's `set` doesn't support — see `TACTIC_NOTES.md`) so it unfolds via
`rfl`/`show` everywhere it's used. -/
def envAt (env : Env) (round : Real → Float) (x : Real) : Env :=
  env.update "x" (Val.scalar (round x))

theorem envAt_x_toF (env : Env) (round : Real → Float) (x : Real) :
    ((envAt env round x) "x").toF = round x := rfl

/-- **Part 1 — uniform bound.** `eml_var_var_pipeline`'s `AbsEnc` bound, made uniform over
`[A, B]` (`1 ≤ A`), by deriving the two leaf roundings directly. -/
theorem eml_var_var_pipeline_uniform {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (a b : Float), r2 t.cName a b = i2 t a b)
    (hround_exp : ∀ a : Float, abs (toR (i1 .exp a) - exp (toR a)) ≤ u * abs (exp (toR a)))
    (hround_ln : ∀ a : Float, abs (toR (i1 .ln a) - log (toR a)) ≤ u * abs (log (toR a)))
    (env : Env) (A B : MachLib.Real) (hA1 : 1 ≤ A)
    (hlo : A ≤ toR (env "x").toF) (hhi : toR (env "x").toF ≤ B) :
    AbsEnc (u * ((1 + 1) + u) * (exp B + log B))
      (toR (evalC r1 r2 env (emitC emlVarVar)).toF)
      (exp (toR (env "x").toF) - log (toR (env "x").toF)) := by
  have hX1 : (1 : MachLib.Real) ≤ toR (env "x").toF := le_trans hA1 hlo
  have hX0 : (0 : MachLib.Real) < toR (env "x").toF := lt_of_lt_of_le zero_lt_one_ax hX1
  have hE1 : AbsEnc (u * abs (exp (toR (env "x").toF)))
      (toR (evalC r1 r2 env (emitC (.tr1 .exp (.var "x")))).toF) (exp (toR (env "x").toF)) := by
    have heq : (evalC r1 r2 env (emitC (.tr1 .exp (.var "x")))).toF
        = i1 .exp (env "x").toF := by
      show r1 (Trans1.exp).cName (env "x").toF = i1 .exp (env "x").toF
      exact hrt1 .exp (env "x").toF
    rw [heq]; exact hround_exp (env "x").toF
  have hE2 : AbsEnc (u * abs (log (toR (env "x").toF)))
      (toR (evalC r1 r2 env (emitC (.tr1 .ln (.var "x")))).toF) (log (toR (env "x").toF)) := by
    have heq : (evalC r1 r2 env (emitC (.tr1 .ln (.var "x")))).toF
        = i1 .ln (env "x").toF := by
      show r1 (Trans1.ln).cName (env "x").toF = i1 .ln (env "x").toF
      exact hrt1 .ln (env "x").toF
    rw [heq]; exact hround_ln (env "x").toF
  have hsub : RoundsW u (toR (evalC r1 r2 env (emitC emlVarVar)).toF)
      (toR (evalC r1 r2 env (emitC (.tr1 .exp (.var "x")))).toF
        - toR (evalC r1 r2 env (emitC (.tr1 .ln (.var "x")))).toF) := by
    show RoundsW u
        (toR ((evalC r1 r2 env (emitC (.tr1 .exp (.var "x")))).toF
            - (evalC r1 r2 env (emitC (.tr1 .ln (.var "x")))).toF))
        (toR (evalC r1 r2 env (emitC (.tr1 .exp (.var "x")))).toF
          - toR (evalC r1 r2 env (emitC (.tr1 .ln (.var "x")))).toF)
    exact br.sub _ _
  have htight := absenc_sub hE1 hE2 hsub
  have hEexp : abs (exp (toR (env "x").toF)) = exp (toR (env "x").toF) :=
    abs_of_nonneg (le_of_lt (exp_pos _))
  have hElog : abs (log (toR (env "x").toF)) = log (toR (env "x").toF) :=
    abs_of_nonneg (log_nonneg hX1)
  rw [hEexp, hElog] at htight
  have hcollapse :
      u * ((exp (toR (env "x").toF) + u * exp (toR (env "x").toF))
          + (log (toR (env "x").toF) + u * log (toR (env "x").toF)))
        + (u * exp (toR (env "x").toF) + u * log (toR (env "x").toF))
      = u * ((1 + 1) + u) * (exp (toR (env "x").toF) + log (toR (env "x").toF)) := by
    mach_mpoly [u, exp (toR (env "x").toF), log (toR (env "x").toF)]
  have htight' : AbsEnc (u * ((1 + 1) + u) * (exp (toR (env "x").toF) + log (toR (env "x").toF)))
      (toR (evalC r1 r2 env (emitC emlVarVar)).toF)
      (exp (toR (env "x").toF) - log (toR (env "x").toF)) := by
    unfold AbsEnc at htight ⊢
    rw [← hcollapse]; exact htight
  have hloosen : u * ((1 + 1) + u) * (exp (toR (env "x").toF) + log (toR (env "x").toF))
      ≤ u * ((1 + 1) + u) * (exp B + log B) := by
    have hnn : 0 ≤ u * ((1 + 1) + u) :=
      mul_nonneg u_nonneg
        (add_nonneg (add_nonneg (le_of_lt zero_lt_one_ax) (le_of_lt zero_lt_one_ax)) u_nonneg)
    exact mul_le_mul_of_nonneg_left
      (add_le_add (exp_monotone hhi) (log_le_log hX0 hhi)) hnn
  unfold AbsEnc at htight' ⊢
  exact le_trans htight' hloosen

/-- **Part 2 — pointwise total error against `sin`, for a real quantized input.** `round : Real →
Float` is the honestly-disclosed quantization hypothesis (some reasonable float rounding of a real
input exists, within absolute error `ρ`) — the same status as `FPBridge` itself: a standard IEEE-754
fact, taken as a hypothesis because `Float` is opaque in Lean. Combines the uniform bound (Part 1,
applied to the quantized point) with `exp`/`log`'s own local-Lipschitz bounds (propagating the
quantization error through `T.eval` itself) via the triangle inequality. -/
theorem eml_var_var_quantized_pointwise {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (a b : Float), r2 t.cName a b = i2 t a b)
    (hround_exp : ∀ a : Float, abs (toR (i1 .exp a) - exp (toR a)) ≤ u * abs (exp (toR a)))
    (hround_ln : ∀ a : Float, abs (toR (i1 .ln a) - log (toR a)) ≤ u * abs (log (toR a)))
    (round : Real → Float) (ρ : MachLib.Real) (hρ : 0 ≤ ρ)
    (hround_q : ∀ x : Real, abs (toR (round x) - x) ≤ ρ)
    (env : Env) (A B : MachLib.Real) (hAρ : 1 ≤ A - ρ)
    (x : Real) (hxA : A < x) (hxB : x < B) :
    abs (toR (evalC r1 r2 (envAt env round x) (emitC emlVarVar)).toF
        - (EMLTree.eml EMLTree.var EMLTree.var).eval x)
      ≤ u * ((1 + 1) + u) * (exp (B + ρ) + log (B + ρ)) + (exp (B + ρ) + 1 / (A - ρ)) * ρ := by
  have hAρ' : (0 : MachLib.Real) < A - ρ := lt_of_lt_of_le zero_lt_one_ax hAρ
  have hclose : abs (toR (round x) - x) ≤ ρ := hround_q x
  have h1 : -ρ ≤ toR (round x) - x := (abs_le_iff.mp hclose).1
  have h5 : toR (round x) - x ≤ ρ := (abs_le_iff.mp hclose).2
  have h3 : x + -ρ = x - ρ := by mach_mpoly [x, ρ]
  have h4 : x + (toR (round x) - x) = toR (round x) := by mach_mpoly [x, toR (round x)]
  have h2 : x - ρ ≤ toR (round x) := by
    have h2' : x + -ρ ≤ x + (toR (round x) - x) := add_le_add_left h1 x
    rw [h3, h4] at h2'; exact h2'
  have h6 : toR (round x) ≤ x + ρ := by
    have h6' : x + (toR (round x) - x) ≤ x + ρ := add_le_add_left h5 x
    rw [h4] at h6'; exact h6'
  have hAρA : A - ρ ≤ A := sub_le_self hρ
  have hBBρ : B ≤ B + ρ := by
    have e : B + 0 = B := by mach_mpoly [B]
    have h := add_le_add_left hρ B
    rw [e] at h; exact h
  have hloX' : A - ρ ≤ toR (round x) := le_trans (sub_le_sub_right (le_of_lt hxA) ρ) h2
  have hhiX' : toR (round x) ≤ B + ρ := le_trans h6 (add_le_add (le_of_lt hxB) (le_refl ρ))
  have hlox : A - ρ ≤ x := le_trans hAρA (le_of_lt hxA)
  have hhix : x ≤ B + ρ := le_trans (le_of_lt hxB) hBBρ
  have hp1 := eml_var_var_pipeline_uniform br i1 i2 r1 r2 hrt1 hrt2 hround_exp hround_ln
    (envAt env round x) (A - ρ) (B + ρ) hAρ
    (by rw [envAt_x_toF]; exact hloX') (by rw [envAt_x_toF]; exact hhiX')
  rw [envAt_x_toF] at hp1
  have hlip_exp : abs (exp (toR (round x)) - exp x) ≤ exp (B + ρ) * abs (toR (round x) - x) :=
    exp_lip_local (A - ρ) (B + ρ) (toR (round x)) x hloX' hhiX' hlox hhix
  have hlip_log : abs (log (toR (round x)) - log x) ≤ (1 / (A - ρ)) * abs (toR (round x) - x) :=
    log_lip_local (A - ρ) (B + ρ) hAρ' (toR (round x)) x hloX' hhiX' hlox hhix
  have htri : abs ((exp (toR (round x)) - log (toR (round x))) - (exp x - log x))
      ≤ abs (exp (toR (round x)) - exp x) + abs (log (toR (round x)) - log x) := by
    have e : (exp (toR (round x)) - log (toR (round x))) - (exp x - log x)
        = (exp (toR (round x)) - exp x) - (log (toR (round x)) - log x) := by
      mach_mpoly [exp (toR (round x)), log (toR (round x)), exp x, log x]
    rw [e]; exact abs_sub_le' _ _
  have hfactor : exp (B + ρ) * abs (toR (round x) - x) + (1 / (A - ρ)) * abs (toR (round x) - x)
      = (exp (B + ρ) + 1 / (A - ρ)) * abs (toR (round x) - x) := by
    mach_mpoly [exp (B + ρ), (1 : MachLib.Real) / (A - ρ), abs (toR (round x) - x)]
  have hnnfactor : (0 : MachLib.Real) ≤ exp (B + ρ) + 1 / (A - ρ) :=
    add_nonneg (le_of_lt (exp_pos _)) (le_of_lt (one_div_pos_of_pos hAρ'))
  have hlipbound : abs ((exp (toR (round x)) - log (toR (round x))) - (exp x - log x))
      ≤ (exp (B + ρ) + 1 / (A - ρ)) * ρ := by
    have step1 : abs ((exp (toR (round x)) - log (toR (round x))) - (exp x - log x))
        ≤ (exp (B + ρ) + 1 / (A - ρ)) * abs (toR (round x) - x) := by
      rw [← hfactor]; exact le_trans htri (add_le_add hlip_exp hlip_log)
    exact le_trans step1 (mul_le_mul_of_nonneg_left hclose hnnfactor)
  have heq : toR (evalC r1 r2 (envAt env round x) (emitC emlVarVar)).toF
      - (EMLTree.eml EMLTree.var EMLTree.var).eval x
      = (toR (evalC r1 r2 (envAt env round x) (emitC emlVarVar)).toF
          - (exp (toR (round x)) - log (toR (round x))))
        + ((exp (toR (round x)) - log (toR (round x))) - (exp x - log x)) := by
    rw [emlVarVar_eval]
    mach_mpoly [toR (evalC r1 r2 (envAt env round x) (emitC emlVarVar)).toF,
      exp (toR (round x)), log (toR (round x)), exp x, log x]
  rw [heq]
  refine le_trans (abs_add _ _) ?_
  refine add_le_add ?_ hlipbound
  unfold AbsEnc at hp1
  exact hp1

open MachLib.EMLExplicitBound in
/-- **The real `hround` instantiation.** For `T := EMLTree.eml EMLTree.var EMLTree.var`
(`T.eval x = exp x − log x`), Certcom's real pipeline machinery + an honestly-disclosed
Real→Float quantization hypothesis together deliver a genuine `compiled : Real → Real` (the
quantized, compiled evaluation of `emlVarVar`) satisfying `certcom_total_error_floor_compact_
interval`'s `hround`, with an EXPLICIT `δ` — not an abstract stand-in. -/
theorem eml_var_var_certcom_witness {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (a b : Float), r2 t.cName a b = i2 t a b)
    (hround_exp : ∀ a : Float, abs (toR (i1 .exp a) - exp (toR a)) ≤ u * abs (exp (toR a)))
    (hround_ln : ∀ a : Float, abs (toR (i1 .ln a) - log (toR a)) ≤ u * abs (log (toR a)))
    (round : Real → Float) (ρ : MachLib.Real) (hρ : 0 ≤ ρ)
    (hround_q : ∀ x : Real, abs (toR (round x) - x) ≤ ρ)
    (env : Env) (A B ε : MachLib.Real) (hA0 : A < ext 0) (hεlt1 : ε < 1) (hAρ : 1 ≤ A - ρ)
    (hδε : u * ((1 + 1) + u) * (exp (B + ρ) + log (B + ρ)) + (exp (B + ρ) + 1 / (A - ρ)) * ρ < ε)
    (hMB : ext (combinedBoundE
        (len (EMLTree.eml EMLTree.var EMLTree.var) 0)
        (enc (EMLTree.eml EMLTree.var EMLTree.var) emlEmptyChain).1
        (encTags (EMLTree.eml EMLTree.var EMLTree.var) emlEmptyChain ())
        (enc (EMLTree.eml EMLTree.var EMLTree.var) emlEmptyChain).2 + 1) < B) :
    ∃ x : MachLib.Real, A < x ∧ x < B ∧
      ε - (u * ((1 + 1) + u) * (exp (B + ρ) + log (B + ρ)) + (exp (B + ρ) + 1 / (A - ρ)) * ρ)
        ≤ abs (toR (evalC r1 r2 (envAt env round x) (emitC emlVarVar)).toF - Real.sin x) := by
  have hA0' : (0 : MachLib.Real) < A := lt_of_lt_of_le zero_lt_one_ax (le_trans hAρ (sub_le_self hρ))
  have hvalidon : EMLPfaffianValidOn (EMLTree.eml EMLTree.var EMLTree.var) A B :=
    ⟨trivial, trivial, fun x hxA _ => lt_of_lt_of_le hA0' (le_of_lt hxA)⟩
  exact certcom_total_error_floor_compact_interval (EMLTree.eml EMLTree.var EMLTree.var) A B ε
    (u * ((1 + 1) + u) * (exp (B + ρ) + log (B + ρ)) + (exp (B + ρ) + 1 / (A - ρ)) * ρ)
    hA0 hεlt1 hδε hvalidon
    (fun x => toR (evalC r1 r2 (envAt env round x) (emitC emlVarVar)).toF)
    (fun x hxA hxB => eml_var_var_quantized_pointwise br i1 i2 r1 r2 hrt1 hrt2 hround_exp hround_ln
      round ρ hρ hround_q env A B hAρ x hxA hxB)
    hMB

end Certcom
