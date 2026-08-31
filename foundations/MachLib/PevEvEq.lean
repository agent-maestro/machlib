import MachLib.BipevCoeffIdentity
import MachLib.PolyEvZero

/-!
# Eventual equality of `pev`s is polynomial equality

The bridge from a **germ** identity between polynomial evaluations to a **polynomial** identity, and
the step `(fm)`'s route sketch for `¬ RatGerm (log ∘ S)` singled out as its weakest.

It is short because both halves already exist and only needed composing:

* `pnorm_eq_nil_of_evZero` — a polynomial whose evaluation is eventually zero normalises to `[]`,
  which is where *"a non-zero polynomial is not eventually zero"* actually lives;
* `peq_of_psub_nil` — a vanishing difference is an equality.

Worth having on its own because every germ-to-polynomial argument in this corpus needs exactly this
step, and until now each one open-coded it.
-/

namespace MachLib
open Real

/-- **Eventual equality of polynomial evaluations is polynomial equality.**

The step (fm)'s route sketch labelled weakest: a germ identity between `pev`s promotes to `PEq`,
because a non-zero polynomial is not eventually zero. -/
theorem peq_of_ev_eq {A B : List Real} {X : Real} (hX : 1 ≤ X)
    (h : ∀ x : Real, X ≤ x → pev A x = pev B x) : PEq A B := by
  refine peq_of_psub_nil ?_
  have hz : EvZeroF (pev (psub A B)) := by
    refine ⟨X, hX, fun x hx => ?_⟩
    rw [pev_psub, h x hx]
    mach_ring
  have hn := pnorm_eq_nil_of_evZero hz
  show pnorm (psub A B) = pnorm []
  rw [hn]
  rfl

end MachLib
