import MachLib.AbsoluteFoldNest
import MachLib.ExpLipschitz

/-!
# FULL local-Lipschitz nesting — via magnitude propagation

`AbsoluteFoldNest` nested the GLOBALLY-Lipschitz primitives (no domain). The local-Lipschitz ones
(`exp`, `sinh`, `cosh`) need a domain, and inside a nest the domain at each node depends on the
accumulated error — the coupling that made this the open piece. The resolution: propagate a **magnitude
bound** `M` with `|exactRn e| ≤ M` alongside the existential error `E`. Magnitude propagates cleanly
(`|a+b| ≤ M_a+M_b`, `|a·b| ≤ M_a·M_b` — no interval sign-cases), and the *float image* magnitude is then
DERIVED, not tracked: `|toR (evalEML e).toF| ≤ M + E` straight from `AbsEnc`. So a local tr1 node over a
SYMMETRIC domain uses `R = M + E` (both inputs land in `[-R, R]`), and its Lipschitz constant `LipOf t R`
+ output magnitude `MagOf t M` are per-primitive functions of `R`/`M`.

`nested_fold_mag` reuses `exactRn`/`IsFold` from `AbsoluteFoldNest` unchanged; it just carries the extra
`M` and closes the tr1 case with `absenc_lip_local` at `R = M + E`. This covers the symmetric-domain
locals (`exp` on `[-M,M]`, `sinh`/`cosh` on `|·| ≤ M`) to ARBITRARY nesting depth. (`log` stays out: its
domain is one-sided `[lo,∞)`, which a symmetric magnitude bound cannot certify.) `sorryAx`-free.
-/

namespace Certcom

open MachLib.Real

/-- Local monotonicity of `·` in both nonneg args (the private one in `AbsoluteError` isn't exported). -/
private theorem mul_le_mul_both2 {a b c d : MachLib.Real}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) : a * c ≤ b * d :=
  le_trans (mul_le_mul_of_nonneg_right hab hc) (mul_le_mul_of_nonneg_left hcd (le_trans ha hab))

/-- **Full local-Lipschitz nesting.** For any `IsFold P e` (arithmetic + `tr1` nodes for primitives `P`
marks, at any depth), the emitted `evalEML` through `toR` is within SOME absolute bound of `exactRn … e`,
AND `|exactRn … e|` is bounded by some `M`. Each `tr1` node is discharged by `absenc_lip_local` at the
symmetric domain `[-(M+E), M+E]` (both the exact input, `≤ M`, and the float image, `≤ M+E`, land there),
using the per-primitive Lipschitz `LipOf t R` on `[-R,R]` and output magnitude `MagOf t M`. -/
theorem nested_fold_mag {toR : Float → MachLib.Real} (br : FPBridge toR)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real)
    (LipOf MagOf : Trans1 → MachLib.Real → MachLib.Real) {P : Trans1 → Prop}
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env)
    (hLipNonneg : ∀ t R, P t → 0 ≤ LipOf t R)
    (hLip : ∀ t R, P t → ∀ p q : MachLib.Real,
        abs p ≤ R → abs q ≤ R → abs (realOf1 t p - realOf1 t q) ≤ LipOf t R * abs (p - q))
    (hMag : ∀ t M, P t → ∀ x : MachLib.Real, abs x ≤ M → abs (realOf1 t x) ≤ MagOf t M)
    (hround : ∀ (t : Trans1) (a : Float), P t →
        abs (toR (i1 t a) - realOf1 t (toR a)) ≤ u * abs (realOf1 t (toR a))) :
    ∀ e : EML, IsFold P e →
      ∃ E M, AbsEnc E (toR (evalEML i1 i2 env e).toF) (exactRn toR realOf1 env e)
             ∧ abs (exactRn toR realOf1 env e) ≤ M := by
  intro e he
  induction he with
  | lit c => exact ⟨0, abs (toR c), absenc_exact (toR c), le_refl _⟩
  | var s => exact ⟨0, abs (toR (env s).toF), absenc_exact (toR (env s).toF), le_refl _⟩
  | add a b _ _ iha ihb =>
      obtain ⟨Ea, Ma, hAa, hMa⟩ := iha; obtain ⟨Eb, Mb, hAb, hMb⟩ := ihb
      refine ⟨_, Ma + Mb,
        absenc_add hAa hAb (br.add (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF), ?_⟩
      show abs (exactRn toR realOf1 env a + exactRn toR realOf1 env b) ≤ Ma + Mb
      exact le_trans (abs_add _ _) (add_le_add_both hMa hMb)
  | sub a b _ _ iha ihb =>
      obtain ⟨Ea, Ma, hAa, hMa⟩ := iha; obtain ⟨Eb, Mb, hAb, hMb⟩ := ihb
      refine ⟨_, Ma + Mb,
        absenc_sub hAa hAb (br.sub (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF), ?_⟩
      show abs (exactRn toR realOf1 env a - exactRn toR realOf1 env b) ≤ Ma + Mb
      exact le_trans (abs_sub_le' _ _) (add_le_add_both hMa hMb)
  | mul a b _ _ iha ihb =>
      obtain ⟨Ea, Ma, hAa, hMa⟩ := iha; obtain ⟨Eb, Mb, hAb, hMb⟩ := ihb
      refine ⟨_, Ma * Mb,
        absenc_mul hAa hAb (br.mul (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF), ?_⟩
      show abs (exactRn toR realOf1 env a * exactRn toR realOf1 env b) ≤ Ma * Mb
      rw [abs_mul]
      exact mul_le_mul_both2 (abs_nonneg _) hMa (abs_nonneg _) hMb
  | neg a _ iha =>
      obtain ⟨Ea, Ma, hAa, hMa⟩ := iha
      refine ⟨Ea, Ma, ?_, ?_⟩
      · show AbsEnc Ea (toR (-(evalEML i1 i2 env a).toF)) (-(exactRn toR realOf1 env a))
        rw [br.neg (evalEML i1 i2 env a).toF]; exact absenc_neg hAa
      · show abs (-(exactRn toR realOf1 env a)) ≤ Ma
        rw [abs_neg]; exact hMa
  | tr1 t a hP _ iha =>
      obtain ⟨Ee, Me, hAbs, hMag_a⟩ := iha
      have hEe_nn : 0 ≤ Ee := absenc_nonneg hAbs
      have hxe_mag : abs (exactRn toR realOf1 env a) ≤ Me + Ee :=
        le_trans hMag_a (le_add_of_nonneg_right hEe_nn)
      have hfl_mag : abs (toR (evalEML i1 i2 env a).toF) ≤ Me + Ee :=
        le_trans (abs_le_add_err hAbs) (add_le_add_both hMag_a (le_refl Ee))
      have hxe := abs_le_iff.mp hxe_mag
      have hfl := abs_le_iff.mp hfl_mag
      refine ⟨_, MagOf t Me,
        absenc_lip_local (f := realOf1 t) (L := LipOf t (Me + Ee)) (lo := -(Me + Ee)) (hi := Me + Ee)
          (hLipNonneg t (Me + Ee) hP)
          (fun p q hlp php hlq phq =>
            hLip t (Me + Ee) hP p q (abs_le_iff.mpr ⟨hlp, php⟩) (abs_le_iff.mpr ⟨hlq, phq⟩))
          hAbs hfl.1 hfl.2 hxe.1 hxe.2 (hround t (evalEML i1 i2 env a).toF hP),
        hMag t Me hP (exactRn toR realOf1 env a) hMag_a⟩

/-- **The full-nesting pipeline, through the emitted C.** For any `IsFold P e`, the emitted C's value,
through `toR`, is within some absolute bound of `exactRn … e` — arbitrary nesting of arithmetic and the
symmetric-domain local (and globally-Lipschitz) transcendentals. -/
theorem pipeline_nested_mag {toR : Float → MachLib.Real} (br : FPBridge toR)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real)
    (LipOf MagOf : Trans1 → MachLib.Real → MachLib.Real) {P : Trans1 → Prop}
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hLipNonneg : ∀ t R, P t → 0 ≤ LipOf t R)
    (hLip : ∀ t R, P t → ∀ p q : MachLib.Real,
        abs p ≤ R → abs q ≤ R → abs (realOf1 t p - realOf1 t q) ≤ LipOf t R * abs (p - q))
    (hMag : ∀ t M, P t → ∀ x : MachLib.Real, abs x ≤ M → abs (realOf1 t x) ≤ MagOf t M)
    (hround : ∀ (t : Trans1) (a : Float), P t →
        abs (toR (i1 t a) - realOf1 t (toR a)) ≤ u * abs (realOf1 t (toR a)))
    (e : EML) (he : IsFold P e) :
    ∃ E M, AbsEnc E (toR (evalC r1 r2 env (emitC e)).toF) (exactRn toR realOf1 env e)
           ∧ abs (exactRn toR realOf1 env e) ≤ M := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env]
  exact nested_fold_mag br realOf1 LipOf MagOf i1 i2 env hLipNonneg hLip hMag hround e he

/-- **Concrete `exp` nesting** — `pipeline_nested_mag` for `P = (· = .exp)`, discharging the Lipschitz
(`exp R`-Lipschitz on `[-R,R]`, from `exp_lip_local`) and magnitude (`|exp x| = exp x ≤ exp M` for
`|x| ≤ M`) hypotheses. So `exp(exp(x·y − z·w))`, `exp(sin …)` mixed with arithmetic — any nesting of
`exp` over arithmetic — is covered end-to-end, sorryAx-free, given only the `exp` primitive's rounding. -/
theorem pipeline_nested_exp {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hround : ∀ a : Float, abs (toR (i1 .exp a) - exp (toR a)) ≤ u * abs (exp (toR a)))
    (e : EML) (he : IsFold (· = .exp) e) :
    ∃ E M, AbsEnc E (toR (evalC r1 r2 env (emitC e)).toF) (exactRn toR (fun _ => exp) env e)
           ∧ abs (exactRn toR (fun _ => exp) env e) ≤ M := by
  refine pipeline_nested_mag br (fun _ => exp) (fun _ R => exp R) (fun _ M => exp M)
    i1 i2 r1 r2 hrt1 hrt2 env ?_ ?_ ?_ ?_ e he
  · intro _ R _; exact le_of_lt (exp_pos R)
  · intro t R hP p q hp hq
    subst hP
    exact exp_lip_local (-R) R p q (abs_le_iff.mp hp).1 (abs_le_iff.mp hp).2
      (abs_le_iff.mp hq).1 (abs_le_iff.mp hq).2
  · intro t M hP x hx
    subst hP
    rw [abs_of_nonneg (le_of_lt (exp_pos x))]
    exact exp_monotone (abs_le_iff.mp hx).2
  · intro t a hP; subst hP; exact hround a

/-- Non-vacuity + genuine DEPTH: `exp(exp(x))` — a local primitive nested over itself — is in the
fragment, so `pipeline_nested_exp` covers arbitrary `exp`-depth, the case one-layer pipelines could not. -/
example : IsFold (· = .exp) (.tr1 .exp (.tr1 .exp (.var "x"))) :=
  .tr1 _ _ rfl (.tr1 _ _ rfl (.var "x"))

end Certcom
