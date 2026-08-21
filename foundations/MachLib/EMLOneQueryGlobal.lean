import MachLib.EMLSignQueryCost
import MachLib.EMLOneQueryForm

/-!
# Level 1, globally — and the reduction typed rather than assumed

`one_query_normal_form` is **eventual**: its conclusion is `CtxAppliesEv C … X`, valid from some
threshold on. That is why the level-1 layer could not serve either query-cost sandwich —
`sign` is eventually constant on the positive ray, and what is open for `exp` is the negative ray.
Both live where an eventual statement cannot look.

The threshold comes off the same way it did at level 0, and for free: `one_query_decompose` is
already **global** (`CtxApplies`, at every real point, no asymptotics), and
`zero_query_finite_exception_normal_form` gives the inner argument globally off a finite set. Compose
them and the level-1 normal form is global too, with a finite exceptional set where the eventual
version had a threshold.

## And then the reduction, stated as an obligation

Having the normal form does **not** give `q_F(sign) ≥ 2`. What that needs is the level-1 analogue of
`zero_query_level_set` — *every level set of a one-query function is finite, or is everything off the
exceptional set* — and that is a genuinely different statement from `OneQueryDichotomy`, which asks
only whether a one-query context is eventually zero or eventually nonzero.

`sign` is eventually constant, so the eventual dichotomy is compatible with it and excludes nothing.
Conflating the two is the error this file exists to make impossible: `OneQueryLevelSet` is stated
separately, and `sign_not_one_query_of_levelSet` records exactly what it buys. Nothing here proves
the obligation; it types the reduction so the next attempt knows what it is attacking.
-/

namespace MachLib

open Real

/-- `CtxApplies`, off a finite exceptional set — what the eventual `CtxAppliesEv` becomes once the
threshold is replaced by a finite list. -/
def CtxAppliesOff (C : FCtx) (g f : Real → Real) (E : List Real) : Prop :=
  ∀ x : Real, x ∉ E → f x = FCtx.eval C x (Fbasis (g x))

/-- **The global one-query normal form.** `T(x) = C(x, F(P(x)/Q(x)))` outside a finite exceptional
set, with `Q` nonvanishing there — no threshold.

The context `C` is still **not** collapsed to a single quotient: that needs `OneQueryDichotomy`, and
this theorem must not assume it. What changes here is only *where* the statement holds, which is
precisely what the two query-cost sandwiches were blocked on. -/
theorem one_query_finite_exception_normal_form (T : FTerm) (h : fOcc T = 1) :
    ∃ (C : FCtx) (P Q E : List Real),
      FCtx.holes C = 1 ∧ (∀ x : Real, x ∉ E → pev Q x ≠ 0)
      ∧ CtxAppliesOff C (fun x => pev P x / pev Q x) (FTerm.eval T) E := by
  obtain ⟨C, A, hC, hA, happ⟩ := one_query_decompose T h
  obtain ⟨E, P, Q, hE⟩ := zero_query_finite_exception_normal_form A hA
  refine ⟨C, P, Q, E, hC, fun x hx => (hE x hx).1, fun x hx => ?_⟩
  rw [happ x, (hE x hx).2]

/-! ## The obligation the `sign` lower bound actually needs -/

/-- **Named obligation: the level-1 level-set theorem.** Every level set of a one-query function is
finite, or is everything off a finite exceptional set.

This is the level-1 analogue of `zero_query_level_set`, and it is **not** `OneQueryDichotomy`. That
row asks whether a one-query *context* is eventually zero or eventually nonzero; `sign` is eventually
constant, so an eventual dichotomy is compatible with it and excludes nothing. The two questions were
briefly conflated in this project's narrative, which is why they now have separate names. -/
def OneQueryLevelSet : Prop :=
  ∀ T : FTerm, fOcc T = 1 → ∀ c : Real,
    ∃ E : List Real,
      (∀ x : Real, x ∉ E → FTerm.eval T x = c) ∨ (∀ x : Real, FTerm.eval T x = c → x ∈ E)

/-- **The reduction, typed.** `OneQueryLevelSet` ⟹ no one-query term computes `sign`.

Same argument as `not_zero_query_of_two_infinite_levels`, one level up: two distinct levels, neither
exhausted by any finite list. `list_two_sided_bound` supplies the points, `sign_pos`/`sign_neg` the
values.

Stated as an implication on purpose. The obligation is open, and a reduction recorded as an
implication cannot be mistaken for a discharge — which is the failure mode the obligations ledger
exists to prevent. -/
theorem sign_not_one_query_of_levelSet (hOQ : OneQueryLevelSet) :
    ¬ ∃ T : FTerm, fOcc T = 1 ∧ ∀ x : Real, FTerm.eval T x = Real.sign x := by
  rintro ⟨T, h1, hT⟩
  obtain ⟨E, hcase⟩ := hOQ T h1 1
  obtain ⟨B, hB, hbnd⟩ := list_two_sided_bound E
  have hposlt : (0 : Real) < B + 1 :=
    lt_of_lt_of_le zero_lt_one_ax (by
      have v := add_le_add_wit hB (le_refl (1 : Real))
      have e : (0 : Real) + 1 = 1 := by mach_ring
      rw [e] at v; exact v)
  have hBnot : B + 1 ∉ E := by
    intro hmem
    have hle := (hbnd (B + 1) hmem).2
    have hlt : B < B + 1 := by
      have v := add_lt_add_left zero_lt_one_ax B
      have e : B + 0 = B := by mach_ring
      rw [e] at v; exact v
    exact lt_irrefl_ax B (lt_of_lt_of_le hlt hle)
  have hnegnot : 0 - (B + 1) ∉ E := by
    intro hmem
    have hge := (hbnd (0 - (B + 1)) hmem).1
    have hlt : 0 - (B + 1) < 0 - B := by
      have v := add_lt_add_left zero_lt_one_ax (0 - (B + 1))
      have e1 : 0 - (B + 1) + 0 = 0 - (B + 1) := by mach_ring
      have e2 : 0 - (B + 1) + 1 = 0 - B := by mach_mpoly [B]
      rw [e1, e2] at v; exact v
    exact lt_irrefl_ax (0 - (B + 1)) (lt_of_lt_of_le hlt hge)
  have hnegpos : 0 - (B + 1) < 0 := by
    have v := add_lt_add_left hposlt (0 - (B + 1))
    have el : 0 - (B + 1) + 0 = 0 - (B + 1) := by mach_ring
    have er : 0 - (B + 1) + (B + 1) = 0 := by mach_mpoly [B]
    rw [el, er] at v; exact v
  rcases hcase with hall | hfin
  · -- T = 1 off E, but T is −1 at a point off E
    have h1' := hall (0 - (B + 1)) hnegnot
    rw [hT, sign_neg hnegpos] at h1'
    exact one_ne_neg_one' h1'.symm
  · -- the 1-level is inside E, yet T = 1 at a point off E
    exact hBnot (hfin (B + 1) (by rw [hT]; exact sign_pos hposlt))

end MachLib
