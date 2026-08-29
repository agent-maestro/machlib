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

## Both halves

Value preservation is `divClamp_eval`. The denominator half is
`divClamp_denom_and_divDenomsOK`, and it is proved as a **conjunction with `DivDenomsOK`** rather than
alone — the `div` case needs `ctxFrac_eval`, whose own hypotheses are exactly `DivDenomsOK` and the
denominator being non-zero, so separating them would make the induction circular.
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

/-- Two rays, dominated. Written once because the induction below combines rays in every case, and
inlining the `add_le_add_wit` chain each time is what tangled the first attempt. -/
private theorem two_bound {a b : Real} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a + b ∧ a ≤ a + b ∧ b ≤ a + b := by
  have ha0 : (0 : Real) ≤ a := le_trans (le_of_lt zero_lt_one_ax) ha
  have hb0 : (0 : Real) ≤ b := le_trans (le_of_lt zero_lt_one_ax) hb
  have h1 : a ≤ a + b := le_addr hb0
  exact ⟨le_trans ha h1, h1, le_addl ha0⟩

/-- Three rays, dominated. -/
private theorem three_bound {a b c : Real} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    1 ≤ a + b + c ∧ a ≤ a + b + c ∧ b ≤ a + b + c ∧ c ≤ a + b + c := by
  obtain ⟨hab1, haab, hbab⟩ := two_bound ha hb
  obtain ⟨h1, hl, hr⟩ := two_bound hab1 hc
  exact ⟨h1, le_trans haab hl, le_trans hbab hl, hr⟩

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

/-! ## The denominator half

The `div` case is the whole content. Its denominator is `den(a') · num(b')` — the *numerator* of the
divisor — and clamping is precisely what removes the case where that numerator is degenerate.
`bipolyNoOscillation_holds` turns "not eventually zero" into "eventually non-zero", and
`ctxFrac_eval` is what converts a degenerate numerator into a degenerate *value*, contradicting the
clamp's own negative condition. -/

/-- **The clamped context has a non-vanishing denominator, and satisfies `DivDenomsOK`.**

Proved as a conjunction because the two are mutually load-bearing: `ctxFrac_eval` — needed in the
`div` case to rule out a degenerate numerator — takes `DivDenomsOK` and non-vanishing as *hypotheses*,
so an induction proving either alone cannot invoke it.

`hQ` is the standing ray hypothesis that `bipolyNoOscillation_holds` requires; it is the same
non-vanishing `RatGerm` is defined by. -/
theorem divClamp_denom_and_divDenomsOK (P Q : List Real) (XQ : Real) (hXQ : 1 ≤ XQ)
    (hQ : ∀ x : Real, XQ ≤ x → pev Q x ≠ 0) : ∀ C : FCtx,
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      DivDenomsOK (divClamp P Q C) x (Fbasis (pev P x / pev Q x))
      ∧ bipev (ctxFrac (divClamp P Q C)).2 x (Fbasis (pev P x / pev Q x)) ≠ 0 := by
  have hone : ∀ x y : Real, bipev [[(1 : Real)]] x y = 1 := by
    intro x y
    show (1 : Real) + x * pev [] x + y * 0 = 1
    show (1 : Real) + x * 0 + y * 0 = 1
    mach_ring
  have hone_ne : ∀ x y : Real, bipev [[(1 : Real)]] x y ≠ 0 := by
    intro x y h
    rw [hone x y] at h
    exact absurd h.symm (ne_of_lt zero_lt_one_ax)
  intro C
  induction C with
  | hole => exact ⟨1, le_refl 1, fun x _ => ⟨True.intro, hone_ne x _⟩⟩
  | const c => exact ⟨1, le_refl 1, fun x _ => ⟨True.intro, hone_ne x _⟩⟩
  | var => exact ⟨1, le_refl 1, fun x _ => ⟨True.intro, hone_ne x _⟩⟩
  | add a b iha ihb =>
      obtain ⟨Xa, hXa, ha⟩ := iha
      obtain ⟨Xb, hXb, hb⟩ := ihb
      have hda : Xa ≤ Xa + Xb := le_addr (le_trans (le_of_lt zero_lt_one_ax) hXb)
      have hdb : Xb ≤ Xa + Xb := le_addl (le_trans (le_of_lt zero_lt_one_ax) hXa)
      refine ⟨Xa + Xb, le_trans hXa hda, fun x hx => ?_⟩
      obtain ⟨hAok, hAne⟩ := ha x (le_trans hda hx)
      obtain ⟨hBok, hBne⟩ := hb x (le_trans hdb hx)
      refine ⟨⟨hAok, hBok⟩, ?_⟩
      show bipev (bimul _ _) x _ ≠ 0
      rw [bipev_bimul]
      exact mul_ne_zero hAne hBne
  | sub a b iha ihb =>
      obtain ⟨Xa, hXa, ha⟩ := iha
      obtain ⟨Xb, hXb, hb⟩ := ihb
      have hda : Xa ≤ Xa + Xb := le_addr (le_trans (le_of_lt zero_lt_one_ax) hXb)
      have hdb : Xb ≤ Xa + Xb := le_addl (le_trans (le_of_lt zero_lt_one_ax) hXa)
      refine ⟨Xa + Xb, le_trans hXa hda, fun x hx => ?_⟩
      obtain ⟨hAok, hAne⟩ := ha x (le_trans hda hx)
      obtain ⟨hBok, hBne⟩ := hb x (le_trans hdb hx)
      refine ⟨⟨hAok, hBok⟩, ?_⟩
      show bipev (bimul _ _) x _ ≠ 0
      rw [bipev_bimul]
      exact mul_ne_zero hAne hBne
  | mul a b iha ihb =>
      obtain ⟨Xa, hXa, ha⟩ := iha
      obtain ⟨Xb, hXb, hb⟩ := ihb
      have hda : Xa ≤ Xa + Xb := le_addr (le_trans (le_of_lt zero_lt_one_ax) hXb)
      have hdb : Xb ≤ Xa + Xb := le_addl (le_trans (le_of_lt zero_lt_one_ax) hXa)
      refine ⟨Xa + Xb, le_trans hXa hda, fun x hx => ?_⟩
      obtain ⟨hAok, hAne⟩ := ha x (le_trans hda hx)
      obtain ⟨hBok, hBne⟩ := hb x (le_trans hdb hx)
      refine ⟨⟨hAok, hBok⟩, ?_⟩
      show bipev (bimul _ _) x _ ≠ 0
      rw [bipev_bimul]
      exact mul_ne_zero hAne hBne
  | div a b iha ihb =>
      by_cases hz : EvZeroF (qGerm P Q b)
      · -- clamped to `const 0`: denominator `[[1]]`, nothing to check
        refine ⟨1, le_refl 1, fun x _ => ?_⟩
        rw [show divClamp P Q (FCtx.div a b) = FCtx.const 0 from by
              rw [divClamp]; exact if_pos hz]
        exact ⟨True.intro, hone_ne x _⟩
      · obtain ⟨Xa, hXa, ha⟩ := iha
        obtain ⟨Xb, hXb, hb⟩ := ihb
        obtain ⟨Xe, hXe, hev⟩ := divClamp_eval P Q b
        -- the divisor's clamped NUMERATOR cannot be eventually zero: if it were,
        -- `ctxFrac_eval` would make the divisor's VALUE eventually zero, which is exactly
        -- the condition this branch assumes fails
        have hnum : ¬ EvZeroF
            (fun x => bipev (ctxFrac (divClamp P Q b)).1 x (Fbasis (pev P x / pev Q x))) := by
          rintro ⟨Yn, hYn, hn⟩
          obtain ⟨h1, hbb, hee, hnn⟩ := three_bound hXb hXe hYn
          refine hz ⟨Xb + Xe + Yn, h1, fun x hx => ?_⟩
          obtain ⟨hBok, hBne⟩ := hb x (le_trans hbb hx)
          have hkey := ctxFrac_eval (divClamp P Q b) x (Fbasis (pev P x / pev Q x)) hBok hBne
          -- typed `have`: `hn x _` lands as an unreduced `(fun x => …) x`. Fifth time today.
          have hnx : bipev (ctxFrac (divClamp P Q b)).1 x (Fbasis (pev P x / pev Q x)) = 0 :=
            hn x (le_trans hnn hx)
          rw [hnx] at hkey
          have h0 : FCtx.eval (divClamp P Q b) x (Fbasis (pev P x / pev Q x)) = 0 := by
            rcases Classical.em
                (FCtx.eval (divClamp P Q b) x (Fbasis (pev P x / pev Q x)) = 0) with h | h
            · exact h
            · exact absurd hkey (mul_ne_zero h hBne)
          show FCtx.eval b x (Fbasis (pev P x / pev Q x)) = 0
          rw [← hev x (le_trans hee hx)]; exact h0
        obtain ⟨Yb, hYb, hbne⟩ := bipolyNoOscillation_holds
          (ctxFrac (divClamp P Q b)).1 P Q XQ hXQ hQ hnum
        obtain ⟨h1, haa, hbb, hyy⟩ := three_bound hXa hXb hYb
        refine ⟨Xa + Xb + Yb, h1, fun x hx => ?_⟩
        obtain ⟨hAok, hAne⟩ := ha x (le_trans haa hx)
        obtain ⟨hBok, hBne⟩ := hb x (le_trans hbb hx)
        rw [show divClamp P Q (FCtx.div a b)
              = FCtx.div (divClamp P Q a) (divClamp P Q b) from by
              rw [divClamp]; exact if_neg hz]
        refine ⟨⟨hAok, hBok, hBne⟩, ?_⟩
        show bipev (bimul _ _) x _ ≠ 0
        rw [bipev_bimul]
        exact mul_ne_zero hAne (hbne x (le_trans hyy hx))

/-! ## The capstone

Both halves are in place, so the div-conditioned dichotomy applies to the **clamped** context and
transfers back along `divClamp_eval`. -/

/-- **`OneQueryDichotomy`.**

The clamp supplies exactly the two hypotheses `oneQueryDichotomy_divConditioned` carries and the
obligation does not: `DivDenomsOK` and the whole-context denominator's non-vanishing. Since the clamp
preserves the value on a ray, the dichotomy it yields for `divClamp P Q C` is the dichotomy for `C`.

Whether this really discharges the ledger row is not for this docstring to assert —
`check_obligations.sh` reads the corpus and decides. -/
theorem oneQueryDichotomy_holds : OneQueryDichotomy := by
  intro C P Q X hX1 hQ
  obtain ⟨Xe, hXe, hev⟩ := divClamp_eval P Q C
  obtain ⟨Xd, hXd, hd⟩ := divClamp_denom_and_divDenomsOK P Q X hX1 hQ C
  obtain ⟨h1, hxx, hee, hdd⟩ := three_bound hX1 hXe hXd
  rcases oneQueryDichotomy_divConditioned (divClamp P Q C) P Q (X + Xe + Xd) h1
      (fun x hx => hQ x (le_trans hxx hx))
      (fun x hx => (hd x (le_trans hdd hx)).1)
      (fun x hx => (hd x (le_trans hdd hx)).2) with hz | hne
  · left
    obtain ⟨Z, hZ1, hzz⟩ := hz
    obtain ⟨h1', hzt, het⟩ := two_bound hZ1 hXe
    refine ⟨Z + Xe, h1', fun x hx => ?_⟩
    have hcz : FCtx.eval (divClamp P Q C) x (Fbasis (pev P x / pev Q x)) = 0 :=
      hzz x (le_trans hzt hx)
    show FCtx.eval C x (Fbasis (pev P x / pev Q x)) = 0
    rw [← hev x (le_trans het hx)]; exact hcz
  · right
    obtain ⟨Y, hY1, hyy⟩ := hne
    obtain ⟨h1', hyt, het⟩ := two_bound hY1 hXe
    refine ⟨Y + Xe, h1', fun x hx => ?_⟩
    have hcz : FCtx.eval (divClamp P Q C) x (Fbasis (pev P x / pev Q x)) ≠ 0 :=
      hyy x (le_trans hyt hx)
    show FCtx.eval C x (Fbasis (pev P x / pev Q x)) ≠ 0
    rw [← hev x (le_trans het hx)]; exact hcz

end MachLib
