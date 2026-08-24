import MachLib.Bipoly
import MachLib.PolyMulDegree

/-!
# The leading coefficient of a bipoly is syntactically visible

`Bipoly` gave the four operations and their evaluation laws. The coefficient sweep needs something
evaluation cannot supply: for `Cd = Σᵢ Aᵢ Eⁱ` of top index `α`, it has to *read off* the coefficient
of `E^(α+β)` in a product and get `A_α·B_β`. That is a statement about lists, not about values, so it
is proved on lists.

Everything here mirrors `PolyMulDegree` one level up, with `padd` for `+`, `pmul` for `·` and `[]`
for `0`:

```
padd_nil_right      biadd_nil_right
padd_length_le/ge   biadd_length_le/ge
padd_concat_right   biadd_concat_right
padd_zero_singleton biadd_nil_singleton
pmul_length         bimul_length
pmul_concat_left    bimul_concat_left
pmul_concat_normal  bimul_concat
```

The mirror is exact enough that the proofs transcribe; where the univariate proof rewrites with
`add_zero` this one rewrites with `padd_nil_right`, and that is the whole difference.

## The one place the mirror is *not* exact

`pmul_concat_normal` carries `α ≠ 0` and `μ ≠ 0`. It does not use them — the concat shape holds for
any coefficients, and the hypotheses are there because the intended *reading* is about canonical
polynomials. `bimul_concat` drops them rather than carrying an unused pair upward. The zero-divisor
question does not disappear; it moves to the caller, where `pnorm (pmul α μ) ≠ []` has to be argued
from `pnorm α ≠ []` and `pnorm μ ≠ []` — and that is `pmul_eq_nil_cancel`'s job, not a shape lemma's.

Stating it here with the hypotheses would have looked stronger and proved the same thing, while
hiding which lemma actually owns the absence of zero divisors.

## `dcoeffs` is not here

The sweep also needs `dcoeffs`'s concat and length shapes. Both already exist — `dcoeffs_concat` and
`dcoeffs_length` in `BipevDcoeffsShape`, written for the elimination arc — and re-proving them here
was caught by the module system rather than by review: two identical theorems, one name. Keeping
them there also keeps this module clear of `BipevClearedDeriv`, which matters, because that import
would have carried `exp` into a module the algebra spine checks for field axioms only.
-/

namespace MachLib

open Real

/-- `bishift k L` is `Eᵏ·L`: `k` zero coefficients in front of a little-endian list. -/
noncomputable def bishift : Nat → List (List Real) → List (List Real)
  | 0,     L => L
  | k + 1, L => [] :: bishift k L

theorem bishift_length : ∀ (k : Nat) (L : List (List Real)),
    (bishift k L).length = k + L.length := by
  intro k
  induction k with
  | zero => intro L; show L.length = 0 + L.length; omega
  | succ n ih =>
      intro L
      show (bishift n L).length + 1 = n + 1 + L.length
      rw [ih L]; omega

theorem bishift_concat : ∀ (k : Nat) (L : List (List Real)) (w : List Real),
    bishift k (L ++ [w]) = bishift k L ++ [w] := by
  intro k
  induction k with
  | zero => intro L w; rfl
  | succ n ih =>
      intro L w
      show ([] : List Real) :: bishift n (L ++ [w]) = (([] : List Real) :: bishift n L) ++ [w]
      rw [ih L w]; rfl

/-! ## `biadd` -/

theorem biadd_nil_right : ∀ L : List (List Real), biadd L [] = L := by
  intro L; cases L with
  | nil => rfl
  | cons A As => rfl

theorem biadd_length_le : ∀ L M : List (List Real), L.length ≤ M.length →
    (biadd L M).length = M.length := by
  intro L
  induction L with
  | nil => intro M _; rfl
  | cons A As ih =>
      intro M h
      cases M with
      | nil => exact absurd h (by simp)
      | cons B Bs =>
          show (biadd As Bs).length + 1 = Bs.length + 1
          rw [ih Bs (by simpa using h)]

theorem biadd_length_ge : ∀ L M : List (List Real), M.length ≤ L.length →
    (biadd L M).length = L.length := by
  intro L
  induction L with
  | nil => intro M h; cases M with
    | nil => rfl
    | cons B Bs => exact absurd h (by simp)
  | cons A As ih =>
      intro M h
      cases M with
      | nil => rfl
      | cons B Bs =>
          show (biadd As Bs).length + 1 = As.length + 1
          rw [ih Bs (by simpa using h)]

theorem biadd_assoc : ∀ X Y Z : List (List Real), biadd (biadd X Y) Z = biadd X (biadd Y Z) := by
  intro X
  induction X with
  | nil => intro Y Z; rfl
  | cons A As ih =>
      intro Y Z
      cases Y with
      | nil => cases Z with
        | nil => rfl
        | cons C Cs => rfl
      | cons B Bs =>
          cases Z with
          | nil => show biadd (padd A B :: biadd As Bs) [] = _
                   rw [biadd_nil_right]; rfl
          | cons C Cs =>
              show padd (padd A B) C :: biadd (biadd As Bs) Cs
                  = padd A (padd B C) :: biadd As (biadd Bs Cs)
              rw [ih Bs Cs, padd_assoc]

/-- `biadd` absorbs a trailing coefficient from the longer side — the bivariate
`padd_concat_right`, and for the same reason: it keeps the leading term of a product syntactically
visible. -/
theorem biadd_concat_right : ∀ (X Y : List (List Real)), X.length ≤ Y.length →
    ∀ v : List Real, biadd X (Y ++ [v]) = biadd X Y ++ [v] := by
  intro X
  induction X with
  | nil => intro Y _ v; rfl
  | cons A As ih =>
      intro Y h v
      cases Y with
      | nil => exact absurd h (by simp)
      | cons B Bs =>
          show padd A B :: biadd As (Bs ++ [v]) = (padd A B :: biadd As Bs) ++ [v]
          rw [ih Bs (by simpa using h) v]; rfl

/-- `biadd L [[]] = L` for nonempty `L` — the base case of the product induction. The bivariate zero
coefficient is `[]`, so the singleton to absorb is `[[]]`, not `[0]`. -/
theorem biadd_nil_singleton : ∀ L : List (List Real), L ≠ [] → biadd L [[]] = L := by
  intro L hL
  cases L with
  | nil => exact absurd rfl hL
  | cons A As =>
      show padd A [] :: biadd As [] = A :: As
      rw [biadd_nil_right, padd_nil_right]

/-! ## `biscale` -/

theorem biscale_length : ∀ (A : List Real) (B : List (List Real)),
    (biscale A B).length = B.length := by
  intro A B
  induction B with
  | nil => rfl
  | cons B Bs ih => show (biscale A Bs).length + 1 = Bs.length + 1; rw [ih]

theorem biscale_concat : ∀ (A : List Real) (B : List (List Real)) (w : List Real),
    biscale A (B ++ [w]) = biscale A B ++ [pmul A w] := by
  intro A B
  induction B with
  | nil => intro w; rfl
  | cons B Bs ih =>
      intro w
      show pmul A B :: biscale A (Bs ++ [w]) = (pmul A B :: biscale A Bs) ++ [pmul A w]
      rw [ih w]; rfl

theorem bishift_biscale_concat (k : Nat) (c w : List Real) (B0 : List (List Real)) :
    bishift k (biscale c (B0 ++ [w])) = bishift k (biscale c B0) ++ [pmul c w] := by
  rw [biscale_concat, bishift_concat]

/-! ## `bimul` -/

theorem bimul_length : ∀ (A M : List (List Real)), A ≠ [] → M ≠ [] →
    (bimul A M).length = A.length + M.length - 1 := by
  intro A
  induction A with
  | nil => intro M hA; exact absurd rfl hA
  | cons A As ih =>
      intro M _ hM
      cases As with
      | nil =>
          have hs : (biscale A M).length = M.length := biscale_length A M
          have hne : biscale A M ≠ [] := by
            intro h
            have h2 : (biscale A M).length = 0 := by rw [h]; rfl
            rw [biscale_length] at h2
            cases M with
            | nil => exact absurd rfl hM
            | cons _ _ => simp at h2
          show (biadd (biscale A M) [([] : List Real)]).length = 1 + M.length - 1
          rw [biadd_nil_singleton _ hne, hs]; omega
      | cons D Ds =>
          have hrec := ih M (by simp) hM
          have hle : (biscale A M).length ≤ (([] : List Real) :: bimul (D :: Ds) M).length := by
            rw [biscale_length]
            show M.length ≤ (bimul (D :: Ds) M).length + 1
            rw [hrec]; simp; omega
          show (biadd (biscale A M) (([] : List Real) :: bimul (D :: Ds) M)).length
              = Ds.length + 2 + M.length - 1
          rw [biadd_length_le _ _ hle]
          show (bimul (D :: Ds) M).length + 1 = Ds.length + 2 + M.length - 1
          rw [hrec]; simp; omega

theorem bimul_concat_left : ∀ (A0 : List (List Real)) (α : List Real) (M : List (List Real)),
    M ≠ [] → bimul (A0 ++ [α]) M = biadd (bimul A0 M) (bishift A0.length (biscale α M)) := by
  intro A0
  induction A0 with
  | nil =>
      intro α M hM
      have hne : biscale α M ≠ [] := by
        intro h
        have hl := biscale_length α M
        rw [h] at hl
        cases M with
        | nil => exact hM rfl
        | cons _ _ => simp at hl
      show biadd (biscale α M) [([] : List Real)] = biadd [] (bishift 0 (biscale α M))
      rw [biadd_nil_singleton _ hne]; rfl
  | cons A As ih =>
      intro α M hM
      show biadd (biscale A M) (([] : List Real) :: bimul (As ++ [α]) M)
          = biadd (biadd (biscale A M) (([] : List Real) :: bimul As M))
              (([] : List Real) :: bishift As.length (biscale α M))
      rw [ih α M hM, biadd_assoc]
      have hz : biadd (([] : List Real) :: bimul As M)
            (([] : List Real) :: bishift As.length (biscale α M))
          = ([] : List Real) :: biadd (bimul As M) (bishift As.length (biscale α M)) := by
        show padd ([] : List Real) [] :: biadd (bimul As M) (bishift As.length (biscale α M))
            = ([] : List Real) :: biadd (bimul As M) (bishift As.length (biscale α M))
        rw [padd_nil_right]
      rw [hz]

/-- **The leading coefficient of a product is `pmul` of the leading coefficients**, syntactically.
No hypothesis on `α` or `μ`: the shape holds for any coefficients, and whether `pmul α μ` is
*nonzero* is a separate question owned by `pmul_eq_nil_cancel`. -/
theorem bimul_concat (A0 M0 : List (List Real)) (α μ : List Real) :
    ∃ D : List (List Real), bimul (A0 ++ [α]) (M0 ++ [μ]) = D ++ [pmul α μ] := by
  have hM : M0 ++ [μ] ≠ [] := by simp
  refine ⟨biadd (bimul A0 (M0 ++ [μ])) (bishift A0.length (biscale α M0)), ?_⟩
  rw [bimul_concat_left A0 α (M0 ++ [μ]) hM, bishift_biscale_concat]
  refine biadd_concat_right _ _ ?_ (pmul α μ)
  rw [bishift_length, biscale_length]
  by_cases hA0 : A0 = []
  · rw [hA0]
    show (bimul ([] : List (List Real)) (M0 ++ [μ])).length
        ≤ ([] : List (List Real)).length + M0.length
    exact Nat.zero_le _
  · rw [bimul_length A0 (M0 ++ [μ]) hA0 hM]
    have h1 : 1 ≤ A0.length := by
      cases hc : A0 with
      | nil => exact absurd hc hA0
      | cons _ _ => simp
    simp

/-- `bisub`, in the same shape. The subtracted side's leading coefficient is `−μ` scaled through
`biscale`, so it is `pmul [0 - 1] μ` rather than a literal negation. -/
theorem bisub_concat_right : ∀ (X Y : List (List Real)), X.length ≤ Y.length →
    ∀ v : List Real, bisub X (Y ++ [v]) = bisub X Y ++ [pmul [0 - 1] v] := by
  intro X Y h v
  show biadd X (biscale [0 - 1] (Y ++ [v])) = biadd X (biscale [0 - 1] Y) ++ [pmul [0 - 1] v]
  rw [biscale_concat]
  exact biadd_concat_right X (biscale [0 - 1] Y) (by rw [biscale_length]; exact h) _

end MachLib
