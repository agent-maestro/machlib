import MachLib.EMLCtxDegenerate

/-!
# The div-clamp: removing degenerate `div` nodes without changing the value

`(es)`/`(et)` established what is needed to close `OneQueryDichotomy`'s remaining gap. The failing
hypothesis is the **whole context's** denominator `bipev (ctxFrac C).2`, which is a product over the
whole tree and is zeroed when some `div` node's divisor has an identically-zero numerator —
`DivDenomsOK` holds regardless (`divDegenerateCtx_divDenomsOK`).

`divClamp` replaces every `div` node whose **divisor is eventually zero** by `const 0`. Two things
make that sound:

* **the value is preserved**, because `a / 0 = 0` and the replacement is `0`;
* **the zero factor leaves the denominator**, because the node then contributes `const 0`'s
  denominator `[[1]]` instead of the divisor's numerator `[[0]]`.

## Why the uniformity problem `declamp` has does not arise

`declamp t a b` is a different tree per interval, because a log argument's sign can differ from
interval to interval — hence `declampVariants` and the reachability subtlety. Here the trigger is
`EvZeroF`, a **ray property**: once the ray is far enough out the clamped context is *fixed*. So this
carries no variant list and no `variantBounds_hypothesis_unsatisfiable` analogue.

## Scope

This module does the definition and the **value-preservation** half. The denominator half — that the
clamped context's `bipev (ctxFrac ·).2` is eventually non-zero, via `bipolyNoOscillation_holds` on
each surviving factor — is not done here.
-/

namespace MachLib

open Real
open Classical

/-- Local copies. `EMLNegTranslation` exports these, but no import path reaches it from here; a
sixth and seventh restatement of `a ≤ a + b`, for the reason recorded in `EMLRayIdentity`. -/
private theorem le_addr {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have v := add_le_add_wit (le_refl a) hb
  have e : a + (0 : Real) = a := by mach_ring
  rw [e] at v; exact v

private theorem le_addl {a b : Real} (ha : 0 ≤ a) : b ≤ a + b := by
  have v := add_le_add_wit ha (le_refl b)
  have e : (0 : Real) + b = b := by mach_ring
  rw [e] at v; exact v

/-- The germ a context is evaluated against, named once so the clamp condition reads clearly. -/
noncomputable abbrev qGerm (P Q : List Real) (C : FCtx) : Real → Real :=
  fun x => FCtx.eval C x (Fbasis (pev P x / pev Q x))

/-- **Replace each `div` whose divisor is eventually zero by `const 0`.** Justified by `a / 0 = 0`;
see `divClamp_eval`. -/
noncomputable def divClamp (P Q : List Real) : FCtx → FCtx
  | .hole    => .hole
  | .const c => .const c
  | .var     => .var
  | .add a b => .add (divClamp P Q a) (divClamp P Q b)
  | .sub a b => .sub (divClamp P Q a) (divClamp P Q b)
  | .mul a b => .mul (divClamp P Q a) (divClamp P Q b)
  | .div a b =>
      if EvZeroF (qGerm P Q b) then .const 0
      else .div (divClamp P Q a) (divClamp P Q b)

/-- **The clamp preserves the value on a ray.**

The ray is assembled by addition rather than by a maximum: every sub-ray is `≥ 1`, so a sum dominates
each, and the corpus has no `Real.max` order lemmas to hand. The `div` case is where the content is —
clamped, both sides are `0`; unclamped, it is the two inductive hypotheses.

Stated with `FCtx.eval` written out rather than through `qGerm`: `qGerm` is an `abbrev`, so the goal
displays unfolded and `rw` cannot match the folded form. It survives only as the clamp's *condition*,
where nothing rewrites through it. -/
theorem divClamp_eval (P Q : List Real) : ∀ C : FCtx,
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      FCtx.eval (divClamp P Q C) x (Fbasis (pev P x / pev Q x))
        = FCtx.eval C x (Fbasis (pev P x / pev Q x)) := by
  intro C
  induction C with
  | hole => exact ⟨1, le_refl 1, fun _ _ => rfl⟩
  | const c => exact ⟨1, le_refl 1, fun _ _ => rfl⟩
  | var => exact ⟨1, le_refl 1, fun _ _ => rfl⟩
  | add a b iha ihb =>
      obtain ⟨Xa, hXa, ha⟩ := iha
      obtain ⟨Xb, hXb, hb⟩ := ihb
      have hda : Xa ≤ Xa + Xb := le_addr (le_trans (le_of_lt zero_lt_one_ax) hXb)
      have hdb : Xb ≤ Xa + Xb := le_addl (le_trans (le_of_lt zero_lt_one_ax) hXa)
      refine ⟨Xa + Xb, le_trans hXa hda, fun x hx => ?_⟩
      show FCtx.eval (divClamp P Q a) x (Fbasis (pev P x / pev Q x))
          + FCtx.eval (divClamp P Q b) x (Fbasis (pev P x / pev Q x))
          = FCtx.eval a x (Fbasis (pev P x / pev Q x)) + FCtx.eval b x (Fbasis (pev P x / pev Q x))
      rw [ha x (le_trans hda hx), hb x (le_trans hdb hx)]
  | sub a b iha ihb =>
      obtain ⟨Xa, hXa, ha⟩ := iha
      obtain ⟨Xb, hXb, hb⟩ := ihb
      have hda : Xa ≤ Xa + Xb := le_addr (le_trans (le_of_lt zero_lt_one_ax) hXb)
      have hdb : Xb ≤ Xa + Xb := le_addl (le_trans (le_of_lt zero_lt_one_ax) hXa)
      refine ⟨Xa + Xb, le_trans hXa hda, fun x hx => ?_⟩
      show FCtx.eval (divClamp P Q a) x (Fbasis (pev P x / pev Q x))
          - FCtx.eval (divClamp P Q b) x (Fbasis (pev P x / pev Q x))
          = FCtx.eval a x (Fbasis (pev P x / pev Q x)) - FCtx.eval b x (Fbasis (pev P x / pev Q x))
      rw [ha x (le_trans hda hx), hb x (le_trans hdb hx)]
  | mul a b iha ihb =>
      obtain ⟨Xa, hXa, ha⟩ := iha
      obtain ⟨Xb, hXb, hb⟩ := ihb
      have hda : Xa ≤ Xa + Xb := le_addr (le_trans (le_of_lt zero_lt_one_ax) hXb)
      have hdb : Xb ≤ Xa + Xb := le_addl (le_trans (le_of_lt zero_lt_one_ax) hXa)
      refine ⟨Xa + Xb, le_trans hXa hda, fun x hx => ?_⟩
      show FCtx.eval (divClamp P Q a) x (Fbasis (pev P x / pev Q x))
          * FCtx.eval (divClamp P Q b) x (Fbasis (pev P x / pev Q x))
          = FCtx.eval a x (Fbasis (pev P x / pev Q x)) * FCtx.eval b x (Fbasis (pev P x / pev Q x))
      rw [ha x (le_trans hda hx), hb x (le_trans hdb hx)]
  | div a b iha ihb =>
      by_cases hz : EvZeroF (qGerm P Q b)
      · -- `id hz` so the destructuring does not consume `hz`, which `if_pos` still needs
        obtain ⟨Xz, hXz, hzero⟩ := id hz
        refine ⟨Xz, hXz, fun x hx => ?_⟩
        have hbz : FCtx.eval b x (Fbasis (pev P x / pev Q x)) = 0 := hzero x hx
        rw [show divClamp P Q (FCtx.div a b) = FCtx.const 0 from by
              rw [divClamp]; exact if_pos hz]
        show (0 : Real) = FCtx.eval a x (Fbasis (pev P x / pev Q x)) / FCtx.eval b x (Fbasis (pev P x / pev Q x))
        rw [hbz, div_zero]
      · obtain ⟨Xa, hXa, ha⟩ := iha
        obtain ⟨Xb, hXb, hb⟩ := ihb
        have hda : Xa ≤ Xa + Xb := le_addr (le_trans (le_of_lt zero_lt_one_ax) hXb)
        have hdb : Xb ≤ Xa + Xb := le_addl (le_trans (le_of_lt zero_lt_one_ax) hXa)
        refine ⟨Xa + Xb, le_trans hXa hda, fun x hx => ?_⟩
        rw [show divClamp P Q (FCtx.div a b)
              = FCtx.div (divClamp P Q a) (divClamp P Q b) from by
              rw [divClamp]; exact if_neg hz]
        show FCtx.eval (divClamp P Q a) x (Fbasis (pev P x / pev Q x))
            / FCtx.eval (divClamp P Q b) x (Fbasis (pev P x / pev Q x))
            = FCtx.eval a x (Fbasis (pev P x / pev Q x)) / FCtx.eval b x (Fbasis (pev P x / pev Q x))
        rw [ha x (le_trans hda hx), hb x (le_trans hdb hx)]

end MachLib
