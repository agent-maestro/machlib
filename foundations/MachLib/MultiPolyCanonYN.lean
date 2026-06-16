import MachLib.MultiPoly

/-!
# MachLib.MultiPolyCanonYN — generalized y-coefficient canonical form

Extends the SingleExp `MultiPolyCanonY` to arbitrary chain length.
For any `MultiPoly n` and chain-variable index `i : Fin n`, `yCoeffsAt i p`
returns `[a_0, a_1, ..., a_d] : List (MultiPoly n)` such that
`p = Σ_k a_k · y_i^k`, where each `a_k` has `degreeY i = 0` (no
y_i dependence but may still contain x and y_j for j ≠ i).

This is the foundation for multi-chain triangular Pfaffian Khovanskii:
the canonical form lets us decompose any polynomial in the highest
chain variable, apply scaledReduction's strict-decrease, then drop
the chain length via `dropLast` once degreeY_last reaches 0.

## What ships in this commit

- Generalized list arithmetic: `listAddN`, `listSubN`, `listScaleN`,
  `listMulN` parameterized over `n`.
- `yCoeffsAt i : MultiPoly n → List (MultiPoly n)`.
- `yCoeffsAt_nonempty`: every extraction produces a non-empty list.
- The y-freeness structural property is the multi-session follow-up
  (mirrors `yCoeffs_entries_y_free` but for general n).
-/

namespace MachLib
namespace MultiPolyMod
namespace MultiPoly

/-! ## Generalized list arithmetic over `MultiPoly n` -/

/-- Pointwise addition of two coefficient lists (general n). -/
def listAddN {n : Nat} :
    List (MultiPoly n) → List (MultiPoly n) → List (MultiPoly n)
  | [], qs => qs
  | p :: ps, [] => p :: ps
  | p :: ps, q :: qs => add p q :: listAddN ps qs

theorem listAddN_nil_left {n : Nat} (l : List (MultiPoly n)) :
    listAddN [] l = l := rfl

theorem listAddN_cons_nil {n : Nat} (p : MultiPoly n)
    (ps : List (MultiPoly n)) :
    listAddN (p :: ps) [] = p :: ps := rfl

theorem listAddN_cons_cons {n : Nat} (p q : MultiPoly n)
    (ps qs : List (MultiPoly n)) :
    listAddN (p :: ps) (q :: qs) = add p q :: listAddN ps qs := rfl

/-- Pointwise subtraction (general n). -/
noncomputable def listSubN {n : Nat} :
    List (MultiPoly n) → List (MultiPoly n) → List (MultiPoly n)
  | [], [] => []
  | [], q :: qs => sub (const 0) q :: listSubN [] qs
  | ps, [] => ps
  | p :: ps, q :: qs => sub p q :: listSubN ps qs

/-- Scale a list by a single MultiPoly (general n). -/
def listScaleN {n : Nat} (p : MultiPoly n) :
    List (MultiPoly n) → List (MultiPoly n)
  | [] => []
  | q :: qs => mul p q :: listScaleN p qs

theorem listScaleN_nil {n : Nat} (p : MultiPoly n) :
    listScaleN p [] = [] := rfl

theorem listScaleN_cons {n : Nat} (p q : MultiPoly n)
    (qs : List (MultiPoly n)) :
    listScaleN p (q :: qs) = mul p q :: listScaleN p qs := rfl

/-- Polynomial convolution (general n). -/
noncomputable def listMulN {n : Nat} :
    List (MultiPoly n) → List (MultiPoly n) → List (MultiPoly n)
  | [], _ => []
  | p :: ps, qs => listAddN (listScaleN p qs) (const 0 :: listMulN ps qs)

theorem listMulN_nil {n : Nat} (l : List (MultiPoly n)) :
    listMulN [] l = [] := rfl

theorem listMulN_cons {n : Nat} (p : MultiPoly n)
    (ps : List (MultiPoly n)) (qs : List (MultiPoly n)) :
    listMulN (p :: ps) qs =
    listAddN (listScaleN p qs) (const 0 :: listMulN ps qs) := rfl

/-! ## Y-coefficient extraction (general index `i : Fin n`)

For p : MultiPoly n and index i, returns the list
`[a_0, a_1, ..., a_d]` where `p = Σ_k a_k · y_i^k`. Each `a_k` is in
MultiPoly n but inductively has `degreeY i = 0` (no y_i dependence). -/

/-- Y-coefficient extraction at index `i`. -/
noncomputable def yCoeffsAt {n : Nat} (i : Fin n) :
    MultiPoly n → List (MultiPoly n)
  | const c => [const c]
  | varX => [varX]
  | varY j => if j = i then [const 0, const 1] else [varY j]
  | add p q => listAddN (yCoeffsAt i p) (yCoeffsAt i q)
  | sub p q => listSubN (yCoeffsAt i p) (yCoeffsAt i q)
  | mul p q => listMulN (yCoeffsAt i p) (yCoeffsAt i q)

/-! ## Structural sanity -/

/-- `yCoeffsAt i` never produces an empty list. -/
theorem yCoeffsAt_nonempty {n : Nat} (i : Fin n) (p : MultiPoly n) :
    yCoeffsAt i p ≠ [] := by
  induction p with
  | const c =>
    show ([const c] : List (MultiPoly n)) ≠ []
    intro h; cases h
  | varX =>
    show ([varX] : List (MultiPoly n)) ≠ []
    intro h; cases h
  | varY j =>
    show (if j = i then ([const 0, const 1] : List (MultiPoly n))
                   else ([varY j] : List (MultiPoly n))) ≠ []
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  | add p q ihp ihq =>
    show listAddN (yCoeffsAt i p) (yCoeffsAt i q) ≠ []
    intro h
    cases hp : yCoeffsAt i p with
    | nil => exact ihp hp
    | cons p' restp =>
      cases hq : yCoeffsAt i q with
      | nil => exact ihq hq
      | cons q' restq =>
        rw [hp, hq] at h
        cases h
  | sub p q ihp ihq =>
    show listSubN (yCoeffsAt i p) (yCoeffsAt i q) ≠ []
    intro h
    cases hp : yCoeffsAt i p with
    | nil =>
      cases hq : yCoeffsAt i q with
      | nil => exact ihq hq
      | cons q' restq =>
        rw [hp, hq] at h
        cases h
    | cons p' restp =>
      cases hq : yCoeffsAt i q with
      | nil =>
        rw [hp, hq] at h
        cases h
      | cons q' restq =>
        rw [hp, hq] at h
        cases h
  | mul p q ihp ihq =>
    show listMulN (yCoeffsAt i p) (yCoeffsAt i q) ≠ []
    intro h
    cases hp : yCoeffsAt i p with
    | nil => exact ihp hp
    | cons p' restp =>
      rw [hp] at h
      -- listMulN (p'::restp) qs = listAddN (listScaleN p' qs) (const 0 :: listMulN restp qs).
      -- Either qs is nil (giving listAddN [] (const 0 :: ...) = const 0 :: ...) or
      -- qs is cons (giving listAddN (mul p' q :: ...) (const 0 :: ...) = add (...) :: ...).
      cases hq : yCoeffsAt i q with
      | nil =>
        rw [hq] at h
        cases h
      | cons q' restq =>
        rw [hq] at h
        cases h

end MultiPoly
end MultiPolyMod
end MachLib
