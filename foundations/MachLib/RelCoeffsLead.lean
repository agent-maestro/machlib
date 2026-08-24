import MachLib.BipolyLead
import MachLib.BipevRearrange
import MachLib.BipevDcoeffsShape

/-!
# Reading the top coefficient off `relCoeffs`

`relCoeffs_nil_ratLog` says every coefficient of the rearrangement is the zero polynomial. That is a
statement about all of them; the argument needs *one* — the coefficient of the highest surviving
power of `E` — because that is the one whose vanishing is an equation between the two leading
coefficients `α` of `Cd` and `β` of `Cd₁`.

With `a = |As|` and `b = |Bs|` the degrees of `Cd = As ++ [α]` and `Cd₁ = Bs ++ [β]`, the three cases
are genuinely different equations, not three instances of one:

```
a > b   index 2a      α·(K·α)                                  K = (m+1)·Q·D
a < b   index a+b     α·(P·β*) − (P·α*)·β
a = b   index 2a      α·(P·β* + K·α) − (P·α*)·β
```

where `α* = Q²·α' + a·D·α` and `β* = Q²·β' + b·D·β` are `dcoeffs`' trailing entries. The `K·α` term
survives only when `Cd` is at least as long as `Cd₁`, which is exactly why `a > b` collapses to a
single product and `a < b` does not see `K` at all.

## Why `dtop` is a definition

`α*` is written `dtop Q D a α`. Not for brevity: it is the *same expression* as the bracket
`coeff_identity` consumes (`padd (pmul QQ (pderiv v)) (pnsum m (pmul D v))`), so the `a < b`
reading and that theorem's hypothesis are one expression rather than two that have to be
reconciled. The naming is the reconciliation.

## No hypotheses on `α`, `β`, `P`, `Q`

Same discipline as `bimul_concat`. These are shape lemmas: they say where a coefficient *is*, not
that it is nonzero, and every nonvanishing question belongs to the caller that has the pole. In
particular the `a < b` and `a = b` readings carry the `pmul [0 - 1]` that `bisub` produces rather
than a `psub`; converting costs `pmul_singleton` and a `≠ []`, and that `≠ []` is exactly the kind of
side condition this layer refuses to invent.
-/

namespace MachLib

open Real

/-- `Q²·a' + n·D·a` — the trailing entry of `dcoeffs Q² D 0 (Ls ++ [a])` at `n = |Ls|`. -/
noncomputable def dtop (Q D : List Real) (n : Nat) (a : List Real) : List Real :=
  padd (pmul (pmul Q Q) (pderiv a)) (pnsum n (pmul D a))

/-- The `(m+1)·Q·D` factor `relCoeffs` scales `Cd` by. -/
noncomputable def relK (Q D : List Real) (m : Nat) : List Real :=
  pmul (pnsum (m + 1) [1]) (pmul Q D)

theorem relCoeffs_unfold (P Q D : List Real) (m : Nat) (Cd Cd1 : List (List Real)) :
    relCoeffs P Q D m Cd Cd1
      = bisub (bimul Cd (biadd (biscale P (dcoeffs (pmul Q Q) D 0 Cd1))
                               (biscale (relK Q D m) Cd)))
              (bimul (biscale P (dcoeffs (pmul Q Q) D 0 Cd)) Cd1) := rfl

/-! ## The two products, split -/

/-- `bimul_concat` with the prefix length, which the `bisub` comparison needs. -/
private theorem bimul_concat' (A0 M0 : List (List Real)) (α μ : List Real) :
    ∃ Z : List (List Real), bimul (A0 ++ [α]) (M0 ++ [μ]) = Z ++ [pmul α μ]
      ∧ Z.length = A0.length + M0.length := by
  obtain ⟨Z, hZ⟩ := bimul_concat A0 M0 α μ
  refine ⟨Z, hZ, ?_⟩
  have h := bimul_length (A0 ++ [α]) (M0 ++ [μ]) (by simp) (by simp)
  rw [hZ] at h
  simp at h
  omega

/-- The scaled derivative family splits at its last entry, with `dtop` as that entry. -/
theorem biscale_dcoeffs_concat (P Q D : List Real) (Ls : List (List Real)) (a : List Real) :
    biscale P (dcoeffs (pmul Q Q) D 0 (Ls ++ [a]))
      = biscale P (dcoeffs (pmul Q Q) D 0 Ls) ++ [pmul P (dtop Q D Ls.length a)] := by
  rw [dcoeffs_concat, biscale_concat, Nat.zero_add]
  rfl

theorem biscale_dcoeffs_length (P Q D : List Real) (Ls : List (List Real)) :
    (biscale P (dcoeffs (pmul Q Q) D 0 Ls)).length = Ls.length := by
  rw [biscale_length, dcoeffs_length]

/-- `T₂ = (P·dcoeffs Cd)·Cd₁`, split at its last entry. Independent of the three cases. -/
private theorem relCoeffs_T2 (P Q D : List Real) (As Bs : List (List Real)) (α β : List Real) :
    ∃ Z : List (List Real),
      bimul (biscale P (dcoeffs (pmul Q Q) D 0 (As ++ [α]))) (Bs ++ [β])
        = Z ++ [pmul (pmul P (dtop Q D As.length α)) β]
      ∧ Z.length = As.length + Bs.length := by
  rw [biscale_dcoeffs_concat]
  obtain ⟨Z, hZ, hlen⟩ :=
    bimul_concat' (biscale P (dcoeffs (pmul Q Q) D 0 As)) Bs (pmul P (dtop Q D As.length α)) β
  exact ⟨Z, hZ, by rw [hlen, biscale_dcoeffs_length]⟩

/-! ## The inner sum, per case -/

/-- `a > b`: the derivative family is strictly shorter, so `K·α` is alone at the top. -/
private theorem inner_gt {P Q D : List Real} {m : Nat} {As Bs : List (List Real)}
    {α β : List Real} (h : Bs.length + 1 ≤ As.length) :
    ∃ Z : List (List Real),
      biadd (biscale P (dcoeffs (pmul Q Q) D 0 (Bs ++ [β]))) (biscale (relK Q D m) (As ++ [α]))
        = Z ++ [pmul (relK Q D m) α] ∧ Z.length = As.length := by
  have hd : (biscale P (dcoeffs (pmul Q Q) D 0 (Bs ++ [β]))).length = Bs.length + 1 := by
    rw [biscale_dcoeffs_length]; simp
  have hk : (biscale (relK Q D m) As).length = As.length := biscale_length _ _
  have hle : (biscale P (dcoeffs (pmul Q Q) D 0 (Bs ++ [β]))).length
      ≤ (biscale (relK Q D m) As).length := by rw [hd, hk]; exact h
  rw [biscale_concat]
  refine ⟨biadd (biscale P (dcoeffs (pmul Q Q) D 0 (Bs ++ [β]))) (biscale (relK Q D m) As),
    biadd_concat_right _ _ hle _, ?_⟩
  -- the SECOND summand is the longer one here, so the sum has its length
  rw [biadd_length_le _ _ hle, hk]

/-- `a < b`: `K·α` sits strictly below the top, so the top is `P·β*` alone. -/
private theorem inner_lt {P Q D : List Real} {m : Nat} {As Bs : List (List Real)}
    {α β : List Real} (h : As.length + 1 ≤ Bs.length) :
    ∃ Z : List (List Real),
      biadd (biscale P (dcoeffs (pmul Q Q) D 0 (Bs ++ [β]))) (biscale (relK Q D m) (As ++ [α]))
        = Z ++ [pmul P (dtop Q D Bs.length β)] ∧ Z.length = Bs.length := by
  have hd : (biscale P (dcoeffs (pmul Q Q) D 0 Bs)).length = Bs.length :=
    biscale_dcoeffs_length P Q D Bs
  have hk : (biscale (relK Q D m) (As ++ [α])).length = As.length + 1 := by
    rw [biscale_length]; simp
  have hle : (biscale (relK Q D m) (As ++ [α])).length
      ≤ (biscale P (dcoeffs (pmul Q Q) D 0 Bs)).length := by rw [hd, hk]; exact h
  rw [biscale_dcoeffs_concat]
  refine ⟨biadd (biscale P (dcoeffs (pmul Q Q) D 0 Bs)) (biscale (relK Q D m) (As ++ [α])),
    biadd_concat_left _ _ hle _, ?_⟩
  -- the FIRST summand is the longer one here
  rw [biadd_length_ge _ _ hle, hd]

/-- `a = b`: both reach the top, and the entries add. -/
private theorem inner_eq {P Q D : List Real} {m : Nat} {As Bs : List (List Real)}
    {α β : List Real} (h : As.length = Bs.length) :
    ∃ Z : List (List Real),
      biadd (biscale P (dcoeffs (pmul Q Q) D 0 (Bs ++ [β]))) (biscale (relK Q D m) (As ++ [α]))
        = Z ++ [padd (pmul P (dtop Q D Bs.length β)) (pmul (relK Q D m) α)]
      ∧ Z.length = Bs.length := by
  have hd : (biscale P (dcoeffs (pmul Q Q) D 0 Bs)).length = Bs.length :=
    biscale_dcoeffs_length P Q D Bs
  have hk : (biscale (relK Q D m) As).length = As.length := biscale_length _ _
  have heq : (biscale P (dcoeffs (pmul Q Q) D 0 Bs)).length
      = (biscale (relK Q D m) As).length := by rw [hd, hk, h]
  have hle : (biscale (relK Q D m) As).length
      ≤ (biscale P (dcoeffs (pmul Q Q) D 0 Bs)).length := Nat.le_of_eq heq.symm
  rw [biscale_dcoeffs_concat, biscale_concat]
  refine ⟨biadd (biscale P (dcoeffs (pmul Q Q) D 0 Bs)) (biscale (relK Q D m) As),
    biadd_concat_both _ _ heq _ _, ?_⟩
  rw [biadd_length_ge _ _ hle, hd]

/-! ## The three readings

Each is the same three steps — split the inner sum, multiply, subtract — differing only in which
`bisub` lemma applies, and that is decided by whether the two products have equal length. -/

/-- **`a > b`: the top coefficient is `α·(K·α)`.** Nothing from `Cd₁` reaches index `2a`, so the
whole coefficient is the `(m+1)·Q·D·α²` term. -/
theorem relCoeffs_top_gt {P Q D : List Real} {m : Nat} {As Bs : List (List Real)}
    {α β : List Real} (h : Bs.length + 1 ≤ As.length) :
    ∃ Z : List (List Real),
      relCoeffs P Q D m (As ++ [α]) (Bs ++ [β]) = Z ++ [pmul α (pmul (relK Q D m) α)] := by
  obtain ⟨Z1, hZ1, hl1⟩ := inner_gt (P := P) (Q := Q) (D := D) (m := m) (β := β) h
  obtain ⟨Z2, hZ2, hl2⟩ := relCoeffs_T2 P Q D As Bs α β
  rw [relCoeffs_unfold, hZ1, hZ2]
  obtain ⟨Z1', hZ1', hl1'⟩ := bimul_concat' As Z1 α (pmul (relK Q D m) α)
  rw [hZ1']
  refine ⟨bisub Z1' (Z2 ++ [pmul (pmul P (dtop Q D As.length α)) β]), ?_⟩
  refine bisub_concat_left _ _ ?_ _
  rw [hl1', hl1]
  simp only [List.length_append, List.length_singleton]
  omega

/-- **`a < b`: the top coefficient is `α·(P·β*) − (P·α*)·β`.** `K·α` sits at index `2a < a+b` and
does not appear. -/
theorem relCoeffs_top_lt {P Q D : List Real} {m : Nat} {As Bs : List (List Real)}
    {α β : List Real} (h : As.length + 1 ≤ Bs.length) :
    ∃ Z : List (List Real),
      relCoeffs P Q D m (As ++ [α]) (Bs ++ [β])
        = Z ++ [padd (pmul α (pmul P (dtop Q D Bs.length β)))
                     (pmul [0 - 1] (pmul (pmul P (dtop Q D As.length α)) β))] := by
  obtain ⟨Z1, hZ1, hl1⟩ := inner_lt (P := P) (Q := Q) (D := D) (m := m) (α := α) h
  obtain ⟨Z2, hZ2, hl2⟩ := relCoeffs_T2 P Q D As Bs α β
  rw [relCoeffs_unfold, hZ1, hZ2]
  obtain ⟨Z1', hZ1', hl1'⟩ := bimul_concat' As Z1 α (pmul P (dtop Q D Bs.length β))
  rw [hZ1']
  exact ⟨bisub Z1' Z2, bisub_concat_both _ _ (by rw [hl1', hl1, hl2]) _ _⟩

/-- **`a = b`: both terms reach the top.** The `K·α` term survives *and* the two derivative terms
do, which is why this case lands on the logarithmic count rather than the exponential one. -/
theorem relCoeffs_top_eq {P Q D : List Real} {m : Nat} {As Bs : List (List Real)}
    {α β : List Real} (h : As.length = Bs.length) :
    ∃ Z : List (List Real),
      relCoeffs P Q D m (As ++ [α]) (Bs ++ [β])
        = Z ++ [padd (pmul α (padd (pmul P (dtop Q D Bs.length β)) (pmul (relK Q D m) α)))
                     (pmul [0 - 1] (pmul (pmul P (dtop Q D As.length α)) β))] := by
  obtain ⟨Z1, hZ1, hl1⟩ := inner_eq (P := P) (Q := Q) (D := D) (m := m) h
  obtain ⟨Z2, hZ2, hl2⟩ := relCoeffs_T2 P Q D As Bs α β
  rw [relCoeffs_unfold, hZ1, hZ2]
  obtain ⟨Z1', hZ1', hl1'⟩ :=
    bimul_concat' As Z1 α (padd (pmul P (dtop Q D Bs.length β)) (pmul (relK Q D m) α))
  rw [hZ1']
  exact ⟨bisub Z1' Z2, bisub_concat_both _ _ (by rw [hl1', hl1, hl2]) _ _⟩

/-- The bridge from "every coefficient is nil" to "*this* coefficient is nil". Trivial, and stated
because the readings deliver a concat and `relCoeffs_nil_ratLog` delivers a membership. -/
theorem pnorm_top_of_all_nil {L Z : List (List Real)} {v : List Real}
    (hL : L = Z ++ [v]) (hall : ∀ A : List Real, A ∈ L → pnorm A = []) : pnorm v = [] :=
  hall v (by rw [hL]; simp)

end MachLib
