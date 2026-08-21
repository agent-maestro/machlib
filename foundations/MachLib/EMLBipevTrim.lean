import MachLib.EMLFTranscendence

/-!
# The algebraic instrument, in the form callers have

`exp_not_algebraic` says `exp` satisfies no polynomial relation with polynomial coefficients, and it
takes that relation in **leading form** — `bipevLead A Ls`, the top coefficient `pev A` separated out
and known `EvDom`. That is the shape the *proof* consumes: the degree drop divides by the leading
term. It is not the shape a *caller* produces. A caller has

```
Σⱼ pⱼ(x) · yʲ = 0      eventually
```

and knows only that the relation is **nontrivial** — not every `pⱼ` dies. Extracting the top
nonvanishing index from that is bookkeeping, and paid at each call site it is the same bookkeeping
every time.

This file pays it once. `bipev_trim` puts any family into leading form or reports that the whole
family dies; `exp_not_algebraic_of_not_all_evZero` is the instrument restated to match.

Two notes on what this is not.

**No analysis is added, and nothing upstream moves.** `exp_not_algebraic` is untouched and still
does all the work; everything here is list arithmetic. Eight declarations in `EMLFTranscendence`
state or consume the leading form (`grep bipevLead`), and restating the instrument *in place* would
have had to disturb all of them. Adding the general form beside it disturbs none: the extraction is
paid once here, and a caller picks whichever shape it can supply.

**The extraction adds no classical step of its own.** `pev_dichotomy` decides each coefficient
(eventually zero, or eventually dominating), so the list induction picks the top nonvanishing index
directly; the hypothesis is `¬ ∀ …` but is discharged by handing back the `∀`, never by
`not_forall`, which this corpus has no reason to carry. Measured rather than asserted:
`exp_not_algebraic_of_not_all_evZero` has **41** axioms against `exp_not_algebraic`'s **39**, and
the two added are `Real.div_zero` and `Real.one_div_nonneg_of_pos` — both inherited from
`pev_dichotomy`'s `c₀/2`, both already in the ledger. Nothing else, and no `sorryAx`.
-/

namespace MachLib

open Real

/-! ## Coefficient-wise addition of two relation families -/

/-- Index-wise sum of two `bipev` coefficient families — `padd` one level up. -/
noncomputable def bpadd : List (List Real) → List (List Real) → List (List Real)
  | [], Ms => Ms
  | L :: Ls, [] => L :: Ls
  | L :: Ls, M :: Ms => padd L M :: bpadd Ls Ms

/-- `bipev` is additive in the coefficient family: Horner in `y` survives because `padd` adds the
coefficient lists index by index. -/
theorem bipev_bpadd : ∀ (Ls Ms : List (List Real)) (x y : Real),
    bipev (bpadd Ls Ms) x y = bipev Ls x y + bipev Ms x y := by
  intro Ls
  induction Ls with
  | nil => intro Ms x y; show bipev Ms x y = 0 + bipev Ms x y; mach_ring
  | cons L Ls ih =>
      intro Ms x y
      cases Ms with
      | nil => show bipev (L :: Ls) x y = bipev (L :: Ls) x y + 0; mach_ring
      | cons M Ms =>
          show pev (padd L M) x + y * bipev (bpadd Ls Ms) x y
              = pev L x + y * bipev Ls x y + (pev M x + y * bipev Ms x y)
          rw [pev_padd, ih Ms x y]; mach_ring

/-! ## Trimming to leading form -/

/-- A family whose every coefficient dies evaluates to `0` — for **every** `y`, since what vanishes
is the coefficients, not a polynomial in `y`. -/
theorem bipev_evZero_of_all_evZero : ∀ Ls : List (List Real),
    (∀ L : List Real, L ∈ Ls → EvZeroF (pev L)) →
    ∃ X : Real, 1 ≤ X ∧ ∀ x y : Real, X ≤ x → bipev Ls x y = 0 := by
  intro Ls
  induction Ls with
  | nil => intro _; exact ⟨1, le_refl 1, fun _ _ _ => rfl⟩
  | cons L Ls ih =>
      intro h
      obtain ⟨X₁, hX₁, hL⟩ := h L (List.mem_cons_self)
      obtain ⟨X₂, hX₂, hLs⟩ := ih (fun M hM => h M (List.mem_cons_of_mem L hM))
      obtain ⟨W, hW, hW1, hW2⟩ := two_bounds' hX₁ hX₂
      refine ⟨W, hW, fun x y hx => ?_⟩
      show pev L x + y * bipev Ls x y = 0
      rw [hL x (le_trans hW1 hx), hLs x y (le_trans hW2 hx)]
      mach_ring

/-- The one identity in the trim that reorders a product, factored out with fresh parameters:
`mach_mpoly`'s reifier rejects atoms bound by `induction`/`obtain`, and the leading term here is
built from both. -/
private theorem bipevLead_cons_shuffle (l y a p b : Real) :
    l + y * (a * p + b) = a * (y * p) + (l + y * b) := by
  mach_mpoly [l, y, a, p, b]

private theorem bipevLead_nil_shuffle (l y : Real) : l + y * 0 = l * 1 + 0 := by
  mach_mpoly [l, y]

/-- **Leading form, or nothing.** Either every coefficient of the family is eventually zero, or the
family agrees — eventually in `x`, for every `y` — with a `bipevLead` whose separated leading
coefficient is `EvDom`.

The induction walks the family from the low end and keeps the first (hence, on the way out, the
top) coefficient `pev_dichotomy` reports as dominating; everything above it is eventually zero, so
`bipev_evZero_of_all_evZero` retires the tail. -/
theorem bipev_trim : ∀ Ls : List (List Real),
    (∀ L : List Real, L ∈ Ls → EvZeroF (pev L)) ∨
    ∃ (A : List Real) (Ls' : List (List Real)) (X : Real), EvDom (pev A) ∧ 1 ≤ X ∧
      ∀ x y : Real, X ≤ x → bipev Ls x y = bipevLead A Ls' x y := by
  intro Ls
  induction Ls with
  | nil => exact Or.inl (fun L hL => by cases hL)
  | cons L Ls ih =>
      rcases ih with hall | ⟨A, Ls', X, hA, hX, hEq⟩
      · rcases pev_dichotomy L with hz | hd
        · refine Or.inl (fun M hM => ?_)
          cases hM with
          | head => exact hz
          | tail _ hM' => exact hall M hM'
        · obtain ⟨X₀, hX₀, hzero⟩ := bipev_evZero_of_all_evZero Ls hall
          refine Or.inr ⟨L, [], X₀, hd, hX₀, fun x y hx => ?_⟩
          show pev L x + y * bipev Ls x y = pev L x * powNat y 0 + bipev [] x y
          rw [hzero x y hx, powNat_zero]
          exact bipevLead_nil_shuffle (pev L x) y
      · refine Or.inr ⟨A, L :: Ls', X, hA, hX, fun x y hx => ?_⟩
        show pev L x + y * bipev Ls x y
            = pev A x * powNat y (L :: Ls').length + (pev L x + y * bipev Ls' x y)
        rw [hEq x y hx]
        show pev L x + y * (pev A x * powNat y Ls'.length + bipev Ls' x y)
            = pev A x * (y * powNat y Ls'.length) + (pev L x + y * bipev Ls' x y)
        exact bipevLead_cons_shuffle (pev L x) y (pev A x) (powNat y Ls'.length)
          (bipev Ls' x y)

/-! ## The instrument, restated -/

/-- **`exp` satisfies no *nontrivial* polynomial relation with polynomial coefficients.**

Same content as `exp_not_algebraic`, hypothesised the way a caller can supply it: the relation is
nontrivial, rather than presented with its leading coefficient already separated and `EvDom`. The
extraction is `bipev_trim`, once, here — not once per call site. -/
theorem exp_not_algebraic_of_not_all_evZero (Ls : List (List Real))
    (hne : ¬ ∀ L : List Real, L ∈ Ls → EvZeroF (pev L))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → bipev Ls x (exp x) = 0) : False := by
  rcases bipev_trim Ls with hall | ⟨A, Ls', X₁, hA, hX₁, hEq⟩
  · exact hne hall
  · obtain ⟨X₂, hX₂, hz⟩ := hrel
    obtain ⟨W, hW, hW1, hW2⟩ := two_bounds' hX₁ hX₂
    refine exp_not_algebraic A Ls' hA ⟨W, hW, fun x hx => ?_⟩
    rw [← hEq x (exp x) (le_trans hW1 hx)]
    exact hz x (le_trans hW2 hx)

end MachLib
