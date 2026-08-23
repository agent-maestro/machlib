import MachLib.PolyDerivShort

/-!
# `pnsum` arithmetic — the last algebraic gap before the coefficient identity

The eliminated coefficient is

```
C = (Q²·v' + m·D·v)·u − v·(Q²·u' + j·D·u)  =  Q²·(v'u − vu') + (m−j)·D·v·u
```

and `cleared_relation_impossible` consumes it in the form `(u'v − uv')·Q² ≈ Nc·D·(u·v)` with
`Nc = (m−j)·1`. Getting between the two needs three facts about `pnsum`, and all three are
**exact list identities** rather than `PEq` statements — which is why they belong here and not in
the composition.

* `pnsum n (A·B) = (pnsum n A)·B` — the multiple slides out of a product, by `pmul_padd_left`.
* `pnsum (a+b) X = pnsum a X + pnsum b X` — additivity of the multiple.
* hence `pnsum m X` minus `pnsum j X` is `pnsum (m−j) X` when `j ≤ m`, which is where `m − j`
  enters the identity at all.

The third is a `PEq` statement, because subtraction of coefficient lists is only well behaved up to
normalisation — the same reason every subtraction in this arc has been.
-/

namespace MachLib

open Real

/-! ## `pnsum` respects `PEq` -/

theorem peq_pnsum : ∀ (n : Nat) {X Y : List Real}, PEq X Y → PEq (pnsum n X) (pnsum n Y) := by
  intro n
  induction n with
  | zero => intro X Y _; exact PEq.refl []
  | succ k ih => intro X Y h; exact peq_padd h (ih h)

/-! ## The multiple slides out of a product -/

theorem pnsum_pmul : ∀ (n : Nat) (A B : List Real),
    pnsum n (pmul A B) = pmul (pnsum n A) B := by
  intro n
  induction n with
  | zero => intro A B; rfl
  | succ k ih =>
      intro A B
      show padd (pmul A B) (pnsum k (pmul A B)) = pmul (padd A (pnsum k A)) B
      rw [ih A B, pmul_padd_left]

/-- With `A = [1]`, the multiple becomes an honest constant factor. -/
theorem peq_pnsum_const (n : Nat) (B : List Real) :
    PEq (pnsum n B) (pmul (pnsum n [1]) B) := by
  have h := pnsum_pmul n [(1 : Real)] B
  show pnorm (pnsum n B) = pnorm (pmul (pnsum n [1]) B)
  rw [← h]
  exact peq_pnsum n (peq_pmul_one_left B).symm

/-! ## Additivity of the multiple -/

theorem pnsum_add : ∀ (a b : Nat) (X : List Real),
    pnsum (a + b) X = padd (pnsum a X) (pnsum b X) := by
  intro a
  induction a with
  | zero =>
      intro b X
      rw [show 0 + b = b from by omega]
      show pnsum b X = padd [] (pnsum b X)
      rfl
  | succ k ih =>
      intro b X
      show pnsum (k + 1 + b) X = padd (padd X (pnsum k X)) (pnsum b X)
      rw [show k + 1 + b = (k + b) + 1 from by omega]
      show padd X (pnsum (k + b) X) = _
      rw [ih b X, padd_assoc]

/-- **`pnsum m X − pnsum j X ≈ pnsum (m−j) X`** for `j ≤ m`. This is where the degree gap `m − j`
enters the coefficient identity. -/
theorem peq_pnsum_sub {m j : Nat} (hjm : j ≤ m) (X : List Real) :
    PEq (psub (pnsum m X) (pnsum j X)) (pnsum (m - j) X) := by
  have he : j + (m - j) = m := by omega
  have hsplit : pnsum m X = padd (pnsum j X) (pnsum (m - j) X) := by
    -- rewrite the hypothesis, not the goal: `← he` would also hit the `m` inside `m − j`
    have h := pnsum_add j (m - j) X
    rw [he] at h
    exact h
  rw [hsplit]
  exact peq_psub_padd_cancel (pnsum j X) (pnsum (m - j) X)

end MachLib
