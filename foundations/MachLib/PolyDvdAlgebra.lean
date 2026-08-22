import MachLib.PolyDvd

/-!
# Associativity up to `pnorm`, and the closure properties of divisibility

`Pdvd` is transitive and closed under sums, but neither is available until `pmul` associates — and
`pmul` does **not** associate on the nose (`PolyDvd`: the two bracketings differ by trailing zeros).
So the associativity proved here is the `pnorm`-level one, and that is not a weakening: `Pdvd` is
itself a statement up to `pnorm`, so this is exactly the strength its closure properties consume.

## Why the second-argument congruence appears now

`PolyDvd` needed only `pnorm_pmul_left`. Transitivity needs the other side: the witness produced for
`Pdvd r A` is `pmul N M`, which has no reason to be canonical, and `Pdvd` requires canonical
witnesses. Taking `pnorm (pmul N M)` instead is only legitimate if `pmul` cannot tell the difference
— which is `pnorm_pmul_right`. With it, **every witness can be normalised on the way out**, and all
the `N = []` / `M = []` edge cases disappear rather than needing separate treatment. That is the
whole reason this file exists before Bézout rather than after.

Both congruences reduce to the same two facts as before (`pnorm_padd_congr` and `pnorm_decomp`), and
the `padd`-left version is one `padd_comm` away from the `padd`-right version already proved.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## `pscale` composition -/

/-- `pscale` distributes over `padd` — distinct from `pscale_add_left`, which splits the *scalar*. -/
theorem pscale_padd : ∀ (c : Real) (M N : List Real),
    pscale c (padd M N) = padd (pscale c M) (pscale c N) := by
  intro c M
  induction M with
  | nil => intro N; rfl
  | cons m ms ih =>
      intro N
      cases N with
      | nil =>
          show pscale c (m :: ms) = padd (pscale c (m :: ms)) []
          rw [padd_nil_right]
      | cons n ns =>
          show (c * (m + n)) :: pscale c (padd ms ns)
              = (c * m + c * n) :: padd (pscale c ms) (pscale c ns)
          have h : c * (m + n) = c * m + c * n := by mach_ring
          rw [h, ih ns]

/-- Right-distributivity of `pmul`. The left version was the cheap direction; this one costs one
more induction and is what divisibility's closure under sums needs. -/
theorem pmul_padd_right : ∀ (Z M N : List Real),
    pmul Z (padd M N) = padd (pmul Z M) (pmul Z N) := by
  intro Z
  induction Z with
  | nil => intro M N; rfl
  | cons z zs ih =>
      intro M N
      show padd (pscale z (padd M N)) ((0 : Real) :: pmul zs (padd M N))
          = padd (padd (pscale z M) ((0 : Real) :: pmul zs M))
                 (padd (pscale z N) ((0 : Real) :: pmul zs N))
      rw [pscale_padd, ih M N, ← padd_zero_cons (pmul zs M) (pmul zs N), padd_middle_four]

theorem pscale_pscale : ∀ (x y : Real) (Z : List Real),
    pscale x (pscale y Z) = pscale (x * y) Z := by
  intro x y Z
  induction Z with
  | nil => rfl
  | cons z zs ih =>
      show (x * (y * z)) :: pscale x (pscale y zs) = ((x * y) * z) :: pscale (x * y) zs
      have h : x * (y * z) = (x * y) * z := by mach_ring
      rw [h, ih]

theorem pmul_pscale_left : ∀ (x : Real) (Y Z : List Real),
    pmul (pscale x Y) Z = pscale x (pmul Y Z) := by
  intro x Y
  induction Y with
  | nil => intro Z; rfl
  | cons y ys ih =>
      intro Z
      have hx0 : x * 0 = 0 := by mach_ring
      show padd (pscale (x * y) Z) ((0 : Real) :: pmul (pscale x ys) Z)
          = pscale x (padd (pscale y Z) ((0 : Real) :: pmul ys Z))
      rw [pscale_padd, pscale_pscale]
      show padd (pscale (x * y) Z) ((0 : Real) :: pmul (pscale x ys) Z)
          = padd (pscale (x * y) Z) ((x * 0) :: pscale x (pmul ys Z))
      rw [hx0, ih Z]

/-! ## `pnorm` congruence on the remaining sides -/

theorem pnorm_padd_left_concat_zero (X Y : List Real) :
    pnorm (padd (X ++ [0]) Y) = pnorm (padd X Y) := by
  rw [padd_comm (X ++ [0]) Y, padd_comm X Y]
  exact pnorm_padd_concat_zero Y X

theorem pnorm_pmul_right_concat_zero : ∀ (Z L : List Real),
    pnorm (pmul Z (L ++ [0])) = pnorm (pmul Z L) := by
  intro Z
  induction Z with
  | nil => intro L; rfl
  | cons z zs ih =>
      intro L
      have hz0 : z * 0 = 0 := by mach_ring
      show pnorm (padd (pscale z (L ++ [0])) ((0 : Real) :: pmul zs (L ++ [0])))
          = pnorm (padd (pscale z L) ((0 : Real) :: pmul zs L))
      rw [pscale_concat, hz0, pnorm_padd_left_concat_zero]
      refine pnorm_padd_congr _ ?_
      show pconsN (0 : Real) (pnorm (pmul zs (L ++ [0])))
          = pconsN (0 : Real) (pnorm (pmul zs L))
      rw [ih L]

theorem pnorm_pmul_right_replicate : ∀ (n : Nat) (Z L : List Real),
    pnorm (pmul Z (L ++ List.replicate n 0)) = pnorm (pmul Z L) := by
  intro n
  induction n with
  | zero => intro Z L; simp
  | succ k ih =>
      intro Z L
      have hsplit : L ++ List.replicate (k + 1) (0 : Real) = (L ++ List.replicate k 0) ++ [0] := by
        rw [List.append_assoc]; congr 1; rw [List.replicate_succ']
      rw [hsplit, pnorm_pmul_right_concat_zero, ih Z L]

/-- **`pmul` sees only the normal form of its right argument** — what lets every witness be
normalised on the way out of a divisibility proof. -/
theorem pnorm_pmul_right (Z Y : List Real) :
    pnorm (pmul Z Y) = pnorm (pmul Z (pnorm Y)) := by
  obtain ⟨n, hn⟩ := pnorm_decomp Y
  have h := pnorm_pmul_right_replicate n Z (pnorm Y)
  rw [← hn] at h
  exact h

/-! ## Associativity, up to `pnorm` -/

/-- A leading zero factors out of a product, up to normalisation. -/
theorem pnorm_pmul_cons_zero (W Z : List Real) :
    pnorm (pmul ((0 : Real) :: W) Z) = pnorm ((0 : Real) :: pmul W Z) := by
  show pnorm (padd (pscale 0 Z) ((0 : Real) :: pmul W Z)) = pnorm ((0 : Real) :: pmul W Z)
  rw [padd_comm, pscale_zero_replicate]
  have h := pnorm_padd_replicate Z.length ((0 : Real) :: pmul W Z) []
  rw [List.nil_append, padd_nil_right] at h
  exact h

/-- **`pmul` associates up to normalisation** — and only up to it, by `PolyDvd`'s observation. -/
theorem pmul_assoc_pnorm : ∀ (X Y Z : List Real),
    pnorm (pmul (pmul X Y) Z) = pnorm (pmul X (pmul Y Z)) := by
  intro X
  induction X with
  | nil => intro Y Z; rfl
  | cons x xs ih =>
      intro Y Z
      show pnorm (pmul (padd (pscale x Y) ((0 : Real) :: pmul xs Y)) Z)
          = pnorm (padd (pscale x (pmul Y Z)) ((0 : Real) :: pmul xs (pmul Y Z)))
      rw [pmul_padd_left, pmul_pscale_left]
      refine pnorm_padd_congr _ ?_
      rw [pnorm_pmul_cons_zero]
      show pconsN (0 : Real) (pnorm (pmul (pmul xs Y) Z))
          = pconsN (0 : Real) (pnorm (pmul xs (pmul Y Z)))
      rw [ih Y Z]

/-! ## Divisibility is transitive and closed under sums -/

theorem Pdvd_trans {r q A : List Real} (h₁ : Pdvd r q) (h₂ : Pdvd q A) : Pdvd r A := by
  obtain ⟨N, _, hN⟩ := h₁
  obtain ⟨M, _, hM⟩ := h₂
  refine ⟨pnorm (pmul N M), pnorm_normal _, ?_⟩
  rw [← pnorm_pmul_right r (pmul N M), ← pmul_assoc_pnorm r N M, hM]
  exact pnorm_pmul_congr M hN

theorem Pdvd_padd {q A B : List Real} (h₁ : Pdvd q A) (h₂ : Pdvd q B) :
    Pdvd q (padd A B) := by
  obtain ⟨M, _, hM⟩ := h₁
  obtain ⟨N, _, hN⟩ := h₂
  refine ⟨pnorm (padd M N), pnorm_normal _, ?_⟩
  rw [← pnorm_pmul_right q (padd M N), pmul_padd_right]
  rw [pnorm_padd_congr A hN, padd_comm A, pnorm_padd_congr (pmul q N) hM, padd_comm (pmul q N)]

/-- Everything divides the zero polynomial, with a canonical witness. -/
theorem Pdvd_zero {q : List Real} : Pdvd q [] := by
  refine ⟨[], pNormal_nil, ?_⟩
  rw [pmul_nil_right, pnorm_replicate_zero]
  rfl

end MachLib
