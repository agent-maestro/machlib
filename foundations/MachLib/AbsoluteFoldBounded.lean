import MachLib.InverseTrigBounded
import MachLib.AbsoluteFoldPos

/-!
# `pipeline_bdd_over_arith` — the symmetric-bounded-domain primitives (`arcsin`, `arccos`) over an
arithmetic core

`AbsoluteFoldPos.pipeline_pos_over_arith` handles the ONE-SIDED-domain primitives (`log`, `sqrt`,
domain `[lo, ∞)`): the arithmetic argument's own fold gives an upper bound `M + E` for free, but the
POSITIVE lower bound `lo` cannot be derived from a symmetric magnitude bound, so it is taken as a
caller-supplied hypothesis.

`arcsin`/`arccos` (`InverseTrigBounded`) are the MIRROR case: their domain guard is a symmetric
UPPER magnitude bound `R < 1` (from `HasDerivAt_arcsin`/`HasDerivAt_arccos`'s `abs x < 1` side
condition), not a one-sided lower bound. This is actually the SIMPLER shape to plumb: unlike
`log`/`sqrt`, there is no separate positivity search needed — `nested_fold_mag`'s own `AbsEnc`
(applied to the arithmetic-only argument, `P = fun _ => False`) supplies exactly the rounding-error
data `absenc_arcsin_local`/`absenc_arccos_local` need; the caller only has to supply the domain
witness `abs (exact value) ≤ R` and `abs (float image) ≤ R` directly (the kernel's own structural
bound — e.g. a normalized dot-product or clamped ratio that is provably `< 1` in magnitude), exactly
the way `pipeline_pos_over_arith` takes `lo` as a hypothesis rather than deriving it.

`sorryAx`-free.
-/

namespace Certcom

open MachLib.Real

/-- Real semantics of the symmetric-bounded-domain primitives (`arcsin`, `arccos`); anything else is
`id` (never used — `BddLip` excludes it). -/
noncomputable def realOfBdd : Trans1 → MachLib.Real → MachLib.Real
  | .asin => arcsin
  | .acos => arccos
  | _ => id

/-- The symmetric-bounded-domain primitives this pipeline covers. -/
def BddLip (t : Trans1) : Prop := t = .asin ∨ t = .acos

/-- **`arcsin`/`arccos` over an arithmetic core, hypotheses pre-discharged except the domain bound
`R < 1`.** For an arithmetic argument `arg` (`IsFold (fun _ => False) arg`) whose exact value AND
float image both lie in `[-R, R]` (`R < 1`), the emitted C for `t(arg)` (`t ∈ {arcsin, arccos}`) is
within SOME absolute bound of `realOfBdd t (exactRn … arg)`, given the primitive's rounding. Unlike
`pipeline_pos_over_arith`, BOTH domain bounds are supplied directly (not split into a free upper
bound from the fold plus a hypothesis-only lower bound) — a symmetric magnitude bound has no "free"
half to extract, so the caller states the domain witness whole. -/
theorem pipeline_bdd_over_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (t : Trans1) (hP : BddLip t) (arg : EML) (harg : IsFold (fun _ => False) arg)
    (R : MachLib.Real) (hR : R < 1)
    (hround_t : ∀ a : Float, abs (toR (i1 t a) - realOfBdd t (toR a)) ≤ u * abs (realOfBdd t (toR a)))
    (hxe_R : abs (exactRn toR realOfPos env arg) ≤ R)
    (hfl_R : abs (toR (evalEML i1 i2 env arg).toF) ≤ R) :
    ∃ E, AbsEnc E (toR (evalC r1 r2 env (emitC (.tr1 t arg))).toF)
                   (realOfBdd t (exactRn toR realOfPos env arg)) := by
  -- 1. the arithmetic argument's fold: AbsEnc, for free (P = fun _ => False, so vacuous). The
  --    magnitude half of `nested_fold_mag`'s output is discarded — the symmetric domain bound
  --    `R` is supplied directly via `hxe_R`/`hfl_R`, not derived from the fold's own `M`.
  obtain ⟨E, _, hAbs, _⟩ :=
    nested_fold_mag br realOfPos (fun _ _ => 0) (fun _ _ => 0) i1 i2 env
      (fun _ _ h => h.elim) (fun _ _ h => h.elim) (fun _ _ h => h.elim) (fun _ _ h => h.elim) arg harg
  -- 2. cap the arithmetic core with the symmetric-bounded-domain node on [-R, R].
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 (.tr1 t arg) env]
  rcases hP with rfl | rfl
  · show ∃ E', AbsEnc E' (toR (i1 .asin (evalEML i1 i2 env arg).toF))
                          (arcsin (exactRn toR realOfPos env arg))
    exact ⟨_, absenc_arcsin_local hR hAbs hfl_R hxe_R (hround_t _)⟩
  · show ∃ E', AbsEnc E' (toR (i1 .acos (evalEML i1 i2 env arg).toF))
                          (arccos (exactRn toR realOfPos env arg))
    exact ⟨_, absenc_arccos_local hR hAbs hfl_R hxe_R (hround_t _)⟩

/-- Non-vacuity: `arcsin(0.5·(x−y))` — `arcsin` over a genuine arithmetic core (a scaled difference)
— is an arithmetic-only argument, so `pipeline_bdd_over_arith` applies given `R < 1` domain evidence
(e.g. `x, y` normalized so the half-difference never exceeds `0.9` in magnitude). -/
example : IsFold (fun _ => False) (.bin .mul (.lit 0.5) (.bin .sub (.var "x") (.var "y"))) :=
  .mul _ _ (.lit 0.5) (.sub _ _ (.var "x") (.var "y"))

end Certcom
