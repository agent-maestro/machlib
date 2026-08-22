import MachLib.PolyRingLaws

/-!
# The division identity in coefficient form

`pdivmod_spec` states `A = B·Q + R` through `pev`. Everything downstream — divisibility, gcd,
Bézout, `ord_q` — needs it as a **coefficient** identity instead, because the transport back from
`pev` is refutable in a model of the allowed axioms (`PolyMulDegree`, the `𝔽₂` argument). This file
does the transport the only way left: syntactically.

## The one nontrivial ingredient

Everything reduces to `pnorm` being insensitive to what a summand looks like below its normal form:

```
pnorm (padd M Y) = pnorm (padd M (pnorm Y))
```

which is *not* a congruence one gets for free — `padd` pads to the longer argument, so shortening
`Y` can shorten the sum, and the entries at the boundary differ syntactically (`m + 0` versus `m`)
while being propositionally equal. Both effects are handled by stripping one trailing zero at a
time (`pnorm_padd_concat_zero`), and by the observation that **every list is its normal form
followed by zeros** (`pnorm_decomp`).

With that, the recursion assembles: the step subtracted `M = xᵏ·c·B`, the quotient contributed
`xᵏ·c`, and `pmul_pshift_singleton` says those are the same list.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## `pnorm` versus `padd` -/

/-- Stripping one trailing zero from a summand does not change the sum's normal form. The two cases
are the two ways it can happen: the zero falls beyond `M` and survives into the sum (where `pnorm`
removes it), or it falls inside `M` and contributes `m + 0 = m`. -/
theorem pnorm_padd_concat_zero : ∀ (M L : List Real),
    pnorm (padd M (L ++ [0])) = pnorm (padd M L) := by
  intro M
  induction M with
  | nil => intro L; show pnorm (L ++ [0]) = pnorm L; exact pnorm_concat_zero L
  | cons m ms ih =>
      intro L
      cases L with
      | nil =>
          show pnorm (padd (m :: ms) [(0 : Real)]) = pnorm (padd (m :: ms) [])
          rw [padd_nil_right, padd_zero_singleton _ (by simp)]
      | cons l ls =>
          show pnorm ((m + l) :: padd ms (ls ++ [0])) = pnorm ((m + l) :: padd ms ls)
          show pconsN (m + l) (pnorm (padd ms (ls ++ [0])))
              = pconsN (m + l) (pnorm (padd ms ls))
          rw [ih ls]

theorem pnorm_padd_replicate : ∀ (n : Nat) (M L : List Real),
    pnorm (padd M (L ++ List.replicate n 0)) = pnorm (padd M L) := by
  intro n
  induction n with
  | zero => intro M L; simp
  | succ k ih =>
      intro M L
      have hsplit : L ++ List.replicate (k + 1) (0 : Real) = (L ++ List.replicate k 0) ++ [0] := by
        rw [List.append_assoc]
        congr 1
        rw [List.replicate_succ']
      rw [hsplit, pnorm_padd_concat_zero, ih M L]

/-- **Every list is its normal form followed by zeros.** -/
theorem pnorm_decomp : ∀ L : List Real, ∃ n : Nat, L = pnorm L ++ List.replicate n (0 : Real) := by
  intro L
  induction L with
  | nil => exact ⟨0, rfl⟩
  | cons c cs ih =>
      obtain ⟨n, hn⟩ := ih
      cases h : pnorm cs with
      | nil =>
          rw [h] at hn
          by_cases hc : c = 0
          · refine ⟨n + 1, ?_⟩
            show c :: cs = pconsN c (pnorm cs) ++ List.replicate (n + 1) (0 : Real)
            rw [h]
            show c :: cs = (if c = 0 then [] else [c]) ++ List.replicate (n + 1) (0 : Real)
            rw [if_pos hc, hc, List.nil_append, List.replicate_succ, hn]
            simp
          · refine ⟨n, ?_⟩
            show c :: cs = pconsN c (pnorm cs) ++ List.replicate n (0 : Real)
            rw [h]
            show c :: cs = (if c = 0 then [] else [c]) ++ List.replicate n (0 : Real)
            rw [if_neg hc]
            simpa using hn
      | cons d ds =>
          refine ⟨n, ?_⟩
          show c :: cs = pconsN c (pnorm cs) ++ List.replicate n (0 : Real)
          rw [h]
          show c :: cs = (c :: d :: ds) ++ List.replicate n (0 : Real)
          rw [← h, List.cons_append, ← hn]

/-- **`pnorm` sees only the normal form of a summand.** -/
theorem pnorm_padd_right (M Y : List Real) :
    pnorm (padd M Y) = pnorm (padd M (pnorm Y)) := by
  obtain ⟨n, hn⟩ := pnorm_decomp Y
  have h := pnorm_padd_replicate n M (pnorm Y)
  rw [← hn] at h
  exact h

/-- Congruence: summands with the same normal form give sums with the same normal form. -/
theorem pnorm_padd_congr {Y Z : List Real} (M : List Real) (h : pnorm Y = pnorm Z) :
    pnorm (padd M Y) = pnorm (padd M Z) := by
  rw [pnorm_padd_right M Y, pnorm_padd_right M Z, h]

/-! ## Adding back what the step subtracted -/

theorem padd_neg_self : ∀ M : List Real,
    padd M (pscale (0 - 1) M) = List.replicate M.length (0 : Real) := by
  intro M
  induction M with
  | nil => rfl
  | cons m ms ih =>
      show (m + (0 - 1) * m) :: padd ms (pscale (0 - 1) ms)
          = List.replicate (ms.length + 1) (0 : Real)
      have hz : m + (0 - 1) * m = 0 := by mach_ring
      rw [hz, ih]
      rfl

/-- `M + (A − M) = A`, up to normalisation — which is all the identity ever needs. -/
theorem pnorm_padd_psub (A M : List Real) : pnorm (padd M (psub A M)) = pnorm A := by
  show pnorm (padd M (padd A (pscale (0 - 1) M))) = pnorm A
  rw [padd_left_comm, padd_neg_self]
  have h := pnorm_padd_replicate M.length A []
  rw [List.nil_append, padd_nil_right] at h
  exact h

/-! ## The identity -/

/-- **`A = Q·B + R` as coefficient lists.** The quotient sits on the left of `pmul` throughout,
because `pmul` recurses on its first argument and left-distributivity is the cheap direction. -/
theorem pdivmod_identity : ∀ (fuel : Nat) (A B : List Real), B ≠ [] →
    pnorm A = pnorm (padd (pmul (pdivmod fuel A B).1 B) (pdivmod fuel A B).2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro A B _
      rw [pdivmod_zero]
      show pnorm A = pnorm (padd (pmul ([] : List Real) B) A)
      rw [show pmul ([] : List Real) B = [] from rfl]
      rfl
  | succ fuel ih =>
      intro A B hBne
      rw [pdivmod_succ]
      by_cases h : A.length < B.length
      · rw [if_pos h]
        show pnorm A = pnorm (padd (pmul ([] : List Real) B) A)
        rw [show pmul ([] : List Real) B = [] from rfl]
        rfl
      · rw [if_neg h]
        have hIH := ih (pdivStep A B) B hBne
        show pnorm A
            = pnorm (padd (pmul (padd (pdivMono A B) (pdivmod fuel (pdivStep A B) B).1) B)
                (pdivmod fuel (pdivStep A B) B).2)
        rw [pmul_padd_left, padd_assoc]
        -- the quotient's monomial IS the list the step subtracted
        have hmono : pmul (pdivMono A B) B
            = pshift (A.length - B.length)
                (pscale (A.getLastD 0 / B.getLastD 0) B) := by
          show pmul (pshift (A.length - B.length) [A.getLastD 0 / B.getLastD 0]) B = _
          exact pmul_pshift_singleton _ _ B hBne
        rw [hmono]
        -- and the recursive half is the step's normal form
        have hstep : pnorm (pdivStep A B)
            = pnorm (padd (pmul (pdivmod fuel (pdivStep A B) B).1 B)
                (pdivmod fuel (pdivStep A B) B).2) := hIH
        have hA' : pnorm (psub A (pshift (A.length - B.length)
            (pscale (A.getLastD 0 / B.getLastD 0) B)))
            = pnorm (padd (pmul (pdivmod fuel (pdivStep A B) B).1 B)
                (pdivmod fuel (pdivStep A B) B).2) := by
          rw [← hstep]
          show _ = pnorm (pnorm (psub A _))
          rw [pnorm_idem]
        rw [← pnorm_padd_congr _ hA']
        exact (pnorm_padd_psub A _).symm

end MachLib
