import MachLib.AbsoluteFoldNestMag
import MachLib.TransNodes
import MachLib.SqrtNode

/-!
# `pipeline_pos_over_arith` — the one-sided-domain primitives (`log`, `sqrt`) over an arithmetic core

The symmetric-domain fold (`nested_fold_mag`) cannot certify `log`/`sqrt`: their domain is one-sided
`[lo, ∞)` (`lo > 0`), and a symmetric magnitude bound `|·| ≤ M` gives an upper bound but no POSITIVE
lower bound — subtraction and sign-changing products can drive an arithmetic value to zero or below,
where `log` diverges and `sqrt` stops being Lipschitz.

The honest resolution factors the obligation. The arithmetic argument's fold ALREADY delivers, for free,
the two-sided data `nested_fold_mag` produces with `P = (fun _ => False)` (an arithmetic-only tree): an
`AbsEnc` and a magnitude `M`, hence the UPPER bound `M + E` on both the exact value and its float image.
The ONE thing the fold cannot derive — a positive LOWER bound `lo` on the argument — is taken as a
hypothesis (`hlo_xe`, `hlo_fl`), exactly the way `FPBridge` and the rounding spec are hypotheses. That
bound is the kernel's own domain assumption (a strictly-positive sensor floor, a sum-of-squares plus a
positive constant, …) — stated, not faked. Given it, the `log`/`sqrt` node closes on `[lo, M + E]`.

So `log`/`sqrt` enter the certified fold for any arithmetic argument the caller can bound below by a
positive `lo`. `sorryAx`-free.
-/

namespace Certcom

open MachLib.Real

/-- Real semantics of the one-sided-domain primitives; anything else is `id` (never used — `PosLip`
excludes it). -/
noncomputable def realOfPos : Trans1 → MachLib.Real → MachLib.Real
  | .ln => log
  | .sqrt => sqrt
  | _ => id

/-- The one-sided-domain primitives this pipeline covers (`ln` is EML's natural log). -/
def PosLip (t : Trans1) : Prop := t = .ln ∨ t = .sqrt

/-- **`log`/`sqrt` over an arithmetic core, hypotheses pre-discharged except the positive lower bound.**
For an arithmetic argument `arg` (`IsFold (fun _ => False) arg` — no `tr1` nodes) and a positive lower
bound `lo` on both its exact value and its float image, the emitted C for `t(arg)` (`t ∈ {log, sqrt}`)
is within SOME absolute bound of `realOfPos t (exactRn … arg)`, given the primitive's rounding. The
upper bound `M + E` comes free from the argument's own magnitude fold; only `lo` is supplied. -/
theorem pipeline_pos_over_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (t : Trans1) (hP : PosLip t) (arg : EML) (harg : IsFold (fun _ => False) arg)
    (lo : MachLib.Real) (hlo : 0 < lo)
    (hround_t : ∀ a : Float, abs (toR (i1 t a) - realOfPos t (toR a)) ≤ u * abs (realOfPos t (toR a)))
    (hlo_xe : lo ≤ exactRn toR realOfPos env arg)
    (hlo_fl : lo ≤ toR (evalEML i1 i2 env arg).toF) :
    ∃ E, AbsEnc E (toR (evalC r1 r2 env (emitC (.tr1 t arg))).toF)
                   (realOfPos t (exactRn toR realOfPos env arg)) := by
  -- 1. the arithmetic argument's fold: AbsEnc + magnitude, for free (P = fun _ => False, so vacuous).
  obtain ⟨E, M, hAbs, hMagB⟩ :=
    nested_fold_mag br realOfPos (fun _ _ => 0) (fun _ _ => 0) i1 i2 env
      (fun _ _ h => h.elim) (fun _ _ h => h.elim) (fun _ _ h => h.elim) (fun _ _ h => h.elim) arg harg
  have hEnn : 0 ≤ E := absenc_nonneg hAbs
  have hxe_hi : exactRn toR realOfPos env arg ≤ M + E :=
    le_trans (abs_le_iff.mp hMagB).2 (le_add_of_nonneg_right hEnn)
  have hfl_hi : toR (evalEML i1 i2 env arg).toF ≤ M + E :=
    (abs_le_iff.mp (le_trans (abs_le_add_err hAbs) (add_le_add_both hMagB (le_refl E)))).2
  -- 2. cap the arithmetic core with the one-sided-domain node on [lo, M + E].
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 (.tr1 t arg) env]
  rcases hP with rfl | rfl
  · show ∃ E', AbsEnc E' (toR (i1 .ln (evalEML i1 i2 env arg).toF))
                          (log (exactRn toR realOfPos env arg))
    exact ⟨_, absenc_log_local hlo hAbs hlo_fl hfl_hi hlo_xe hxe_hi (hround_t _)⟩
  · show ∃ E', AbsEnc E' (toR (i1 .sqrt (evalEML i1 i2 env arg).toF))
                          (sqrt (exactRn toR realOfPos env arg))
    exact ⟨_, absenc_sqrt_local hlo hAbs hlo_fl hfl_hi hlo_xe hxe_hi (hround_t _)⟩

/-- Non-vacuity: `sqrt(x·x + c)` — `sqrt` over a genuine arithmetic core (a product plus a constant) —
is an arithmetic-only argument, so `pipeline_pos_over_arith` applies given a positive lower bound. -/
example : IsFold (fun _ => False) (.bin .add (.bin .mul (.var "x") (.var "x")) (.lit 1.0)) :=
  .add _ _ (.mul _ _ (.var "x") (.var "x")) (.lit 1.0)

end Certcom
