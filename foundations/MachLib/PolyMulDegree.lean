import MachLib.PolyDivision

/-!
# The product of canonical polynomials is canonical, and degree is additive

`ord_q(ab) = ord_q(a) + ord_q(b)` is the theorem the whole pole-order argument runs on, and it needs
this first: multiplying two canonical nonzero polynomials **cannot** produce a trailing zero, so no
renormalisation happens and the lengths add.

## Why this cannot be obtained through `pev`

The obvious route is to prove the ring facts for the *functions* and transport. That route is
**closed inside this layer**, and not by accident of what has been built.

`AxiomLedger`'s `algebraFootprint` is exactly the theory of fields — and fields have **finite
models**. Over `𝔽₂` the polynomial `X² + X` vanishes at every point and is not the zero polynomial.
So `(∀ x, pev L x = 0) → pnorm L = []` is *false* in a model of the allowed axioms, hence unprovable
from them. Measured confirmation of where the missing strength sits: `pev_zero_or_finite_roots` is
field-only (it is synthetic division), while `finite_list_avoidable` — "there is a point outside a
finite list", i.e. `ℝ` is infinite — carries `ltR`, `leR`, `lt_total`, `lt_trans_ax`,
`add_lt_add_left`, `le_iff_lt_or_eq`, `mul_pos`, `zero_lt_one_ax`.

**Consequence for the spine.** Divisibility, gcd and multiplicity must be defined on *coefficients*,
never as `∃ M, ∀ x, pev A x = pev q x * pev M x`. A functional divisibility would force a degree
comparison, a degree comparison would force extensionality, and extensionality would drag the
ordered-real base into a layer whose whole point is being algebraic. The gate would catch it; the
model argument above says there is no clever proof to find.

## The mechanism

`pmul` recurses on its *first* argument's head while canonicity is a statement about the *last*
entry, so the induction runs head-first and reads the leading coefficient off the longer summand:

```
pmul (a :: as) M = padd (pscale a M) (0 :: pmul as M)
```

With `as ≠ []` the right summand is strictly longer, so it alone determines the last entry, which by
induction is `lead as * lead M`. With `as = []` the left summand is everything and the last entry is
`a * lead M`. Both are nonzero by `mul_ne_zero` — **this is the only place the field's lack of zero
divisors is used, and it is what makes degree additive at all.**
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Length and shape arithmetic for `padd`

No `Nat.max` anywhere: `omega` treats it as an opaque atom here (a documented gotcha), and the two
one-sided forms are what the product induction actually uses. No `getLast?` either — the concat form
that carried the division descent works again. -/

theorem padd_nil_right : ∀ L : List Real, padd L [] = L := by
  intro L; cases L with
  | nil => rfl
  | cons a as => rfl

theorem padd_length_le : ∀ L M : List Real, L.length ≤ M.length →
    (padd L M).length = M.length := by
  intro L
  induction L with
  | nil => intro M _; rfl
  | cons a as ih =>
      intro M h
      cases M with
      | nil => exact absurd h (by simp)
      | cons b bs =>
          show (padd as bs).length + 1 = bs.length + 1
          rw [ih bs (by simpa using h)]

theorem padd_length_ge : ∀ L M : List Real, M.length ≤ L.length →
    (padd L M).length = L.length := by
  intro L
  induction L with
  | nil => intro M h; cases M with
    | nil => rfl
    | cons b bs => exact absurd h (by simp)
  | cons a as ih =>
      intro M h
      cases M with
      | nil => rfl
      | cons b bs =>
          show (padd as bs).length + 1 = as.length + 1
          rw [ih bs (by simpa using h)]

theorem padd_assoc : ∀ X Y Z : List Real, padd (padd X Y) Z = padd X (padd Y Z) := by
  intro X
  induction X with
  | nil => intro Y Z; rfl
  | cons a as ih =>
      intro Y Z
      cases Y with
      | nil => rw [padd_nil_right]; rfl
      | cons b bs =>
          cases Z with
          | nil => rw [padd_nil_right, padd_nil_right]
          | cons c cs =>
              show (a + b + c) :: padd (padd as bs) cs
                  = (a + (b + c)) :: padd as (padd bs cs)
              rw [ih bs cs, add_assoc]

/-- `padd` absorbs a trailing coefficient from the longer side. The whole product argument runs on
this: it keeps the leading term of a product syntactically visible. -/
theorem padd_concat_right : ∀ (X Y : List Real), X.length ≤ Y.length → ∀ v : Real,
    padd X (Y ++ [v]) = padd X Y ++ [v] := by
  intro X
  induction X with
  | nil => intro Y _ v; rfl
  | cons a as ih =>
      intro Y h v
      cases Y with
      | nil => exact absurd h (by simp)
      | cons b bs =>
          show (a + b) :: padd as (bs ++ [v]) = ((a + b) :: padd as bs) ++ [v]
          rw [ih bs (by simpa using h) v]; rfl

/-- `padd L [0] = L` for nonempty `L` — the base case of the product induction. -/
theorem padd_zero_singleton : ∀ L : List Real, L ≠ [] → padd L [0] = L := by
  intro L hL
  cases L with
  | nil => exact absurd rfl hL
  | cons a as =>
      show (a + 0) :: padd as [] = a :: as
      rw [padd_nil_right, add_zero]

/-! ## The product -/

theorem pmul_length : ∀ (A M : List Real), A ≠ [] → M ≠ [] →
    (pmul A M).length = A.length + M.length - 1 := by
  intro A
  induction A with
  | nil => intro M hA; exact absurd rfl hA
  | cons a as ih =>
      intro M _ hM
      have hMlen : 1 ≤ M.length := by
        cases M with
        | nil => exact absurd rfl hM
        | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      cases as with
      | nil =>
          have hs : (pscale a M).length = M.length := pscale_length a M
          have hne : pscale a M ≠ [] := by
            intro h
            have h2 : (pscale a M).length = 0 := by rw [h]; rfl
            rw [pscale_length] at h2
            omega
          show (padd (pscale a M) [(0 : Real)]).length = 1 + M.length - 1
          rw [padd_zero_singleton _ hne, hs]; omega
      | cons d ds =>
          have hrec := ih M (by simp) hM
          have hle : (pscale a M).length ≤ (0 :: pmul (d :: ds) M).length := by
            rw [pscale_length]
            show M.length ≤ (pmul (d :: ds) M).length + 1
            rw [hrec]; simp; omega
          show (padd (pscale a M) (0 :: pmul (d :: ds) M)).length = ds.length + 2 + M.length - 1
          rw [padd_length_le _ _ hle]
          show (pmul (d :: ds) M).length + 1 = ds.length + 2 + M.length - 1
          rw [hrec]; simp; omega

/-- **The leading term of a product is syntactically visible.** `pmul A (M₀ ++ [μ])` ends in a
literal `α·μ` once `A` is written `A₀ ++ [α]`. -/
theorem pmul_concat_left : ∀ (A0 : List Real) (α : Real) (M : List Real), M ≠ [] →
    pmul (A0 ++ [α]) M = padd (pmul A0 M) (pshift A0.length (pscale α M)) := by
  intro A0
  induction A0 with
  | nil =>
      intro α M hM
      have hne : pscale α M ≠ [] := by
        intro h
        have := pscale_length α M
        rw [h] at this; simp at this
        cases M with
        | nil => exact hM rfl
        | cons _ _ => simp at this
      show padd (pscale α M) [(0 : Real)] = padd [] (pshift 0 (pscale α M))
      rw [padd_zero_singleton _ hne]; rfl
  | cons a as ih =>
      intro α M hM
      show padd (pscale a M) (0 :: pmul (as ++ [α]) M)
          = padd (padd (pscale a M) (0 :: pmul as M)) (0 :: pshift as.length (pscale α M))
      rw [ih α M hM, padd_assoc]
      have hz : padd ((0 : Real) :: pmul as M) (0 :: pshift as.length (pscale α M))
          = (0 : Real) :: padd (pmul as M) (pshift as.length (pscale α M)) := by
        show ((0 : Real) + 0) :: padd (pmul as M) (pshift as.length (pscale α M))
            = (0 : Real) :: padd (pmul as M) (pshift as.length (pscale α M))
        rw [add_zero]
      rw [hz]

/-- **Canonicity is closed under multiplication, and the leading coefficient multiplies.** This is
the only place the field's absence of zero divisors is used, and it is what makes degree additive. -/
theorem pmul_concat_normal (A0 M0 : List Real) (α μ : Real) (hα : α ≠ 0) (hμ : μ ≠ 0) :
    ∃ D : List Real, pmul (A0 ++ [α]) (M0 ++ [μ]) = D ++ [α * μ] := by
  have hM : M0 ++ [μ] ≠ [] := by simp
  refine ⟨padd (pmul A0 (M0 ++ [μ])) (pshift A0.length (pscale α M0)), ?_⟩
  rw [pmul_concat_left A0 α (M0 ++ [μ]) hM, pshift_pscale_concat]
  refine padd_concat_right _ _ ?_ (α * μ)
  rw [pshift_length, pscale_length]
  by_cases hA0 : A0 = []
  · rw [hA0]
    show (pmul ([] : List Real) (M0 ++ [μ])).length ≤ ([] : List Real).length + M0.length
    exact Nat.zero_le _
  · rw [pmul_length A0 (M0 ++ [μ]) hA0 hM]
    have h1 : 1 ≤ A0.length := by
      cases hc : A0 with
      | nil => exact absurd hc hA0
      | cons _ _ => simp
    simp

theorem pmul_normal {A M : List Real} (hA : PNormal A) (hM : PNormal M)
    (hAne : A ≠ []) (hMne : M ≠ []) : PNormal (pmul A M) := by
  obtain ⟨A0, α, hAc⟩ : ∃ A0 α, A = A0 ++ [α] :=
    ⟨A.dropLast, A.getLast hAne, (List.dropLast_concat_getLast hAne).symm⟩
  obtain ⟨M0, μ, hMc⟩ : ∃ M0 μ, M = M0 ++ [μ] :=
    ⟨M.dropLast, M.getLast hMne, (List.dropLast_concat_getLast hMne).symm⟩
  have hαne : α ≠ 0 := hA α (by rw [hAc]; simp)
  have hμne : μ ≠ 0 := hM μ (by rw [hMc]; simp)
  obtain ⟨D, hD⟩ := pmul_concat_normal A0 M0 α μ hαne hμne
  intro c hc
  rw [hAc, hMc, hD] at hc
  have hcv : α * μ = c := by simpa using hc
  rw [← hcv]
  exact mul_ne_zero hαne hμne

end MachLib
