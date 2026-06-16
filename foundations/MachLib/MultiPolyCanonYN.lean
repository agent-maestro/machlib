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

/-! ## Y-freeness of yCoeffsAt entries

Generalizes `yCoeffs_entries_y_free` (MultiPoly 1, index 0) to
arbitrary index i. Every coefficient extracted by yCoeffsAt at
index i has degreeY i = 0 (no dependence on the i-th chain variable). -/

/-- listAddN preserves degreeY-i-freeness of all entries. -/
theorem listAddN_entries_degreeY_zero {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n))
    (h1 : ∀ c ∈ l1, degreeY i c = 0)
    (h2 : ∀ c ∈ l2, degreeY i c = 0) :
    ∀ c ∈ listAddN l1 l2, degreeY i c = 0 := by
  induction l1 generalizing l2 with
  | nil =>
    intro c hc
    rw [listAddN_nil_left] at hc
    exact h2 c hc
  | cons p ps ih =>
    cases l2 with
    | nil =>
      intro c hc
      rw [listAddN_cons_nil] at hc
      exact h1 c hc
    | cons q qs =>
      intro c hc
      rw [listAddN_cons_cons] at hc
      cases hc with
      | head =>
        show Nat.max (degreeY i p) (degreeY i q) = 0
        rw [h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)]
        rfl
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

/-- listSubN preserves degreeY-i-freeness of all entries. -/
theorem listSubN_entries_degreeY_zero {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n))
    (h1 : ∀ c ∈ l1, degreeY i c = 0)
    (h2 : ∀ c ∈ l2, degreeY i c = 0) :
    ∀ c ∈ listSubN l1 l2, degreeY i c = 0 := by
  induction l1 generalizing l2 with
  | nil =>
    induction l2 with
    | nil =>
      intro c hc
      exact absurd hc (List.not_mem_nil _)
    | cons q qs ihq =>
      intro c hc
      -- listSubN [] (q::qs) = sub (const 0) q :: listSubN [] qs.
      show degreeY i c = 0
      change c ∈ (sub (const 0) q :: listSubN [] qs) at hc
      cases hc with
      | head =>
        show Nat.max (degreeY i (const 0 : MultiPoly n))
                     (degreeY i q) = 0
        rw [h2 q (List.mem_cons_self _ _)]
        rfl
      | tail _ hc' =>
        exact ihq (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'
  | cons p ps ih =>
    cases l2 with
    | nil =>
      intro c hc
      change c ∈ (p :: ps) at hc
      exact h1 c hc
    | cons q qs =>
      intro c hc
      change c ∈ (sub p q :: listSubN ps qs) at hc
      cases hc with
      | head =>
        show Nat.max (degreeY i p) (degreeY i q) = 0
        rw [h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)]
        rfl
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

/-- listScaleN by a y-free poly preserves y-freeness. -/
theorem listScaleN_entries_degreeY_zero {n : Nat} (i : Fin n)
    (p : MultiPoly n) (hp : degreeY i p = 0)
    (l : List (MultiPoly n))
    (hl : ∀ c ∈ l, degreeY i c = 0) :
    ∀ c ∈ listScaleN p l, degreeY i c = 0 := by
  induction l with
  | nil =>
    intro c hc
    rw [listScaleN_nil] at hc
    exact absurd hc (List.not_mem_nil _)
  | cons q qs ih =>
    intro c hc
    rw [listScaleN_cons] at hc
    cases hc with
    | head =>
      show degreeY i p + degreeY i q = 0
      rw [hp, hl q (List.mem_cons_self _ _)]
    | tail _ hc' =>
      exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) c hc'

/-- listMulN preserves degreeY-i-freeness of all entries. -/
theorem listMulN_entries_degreeY_zero {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n))
    (h1 : ∀ c ∈ l1, degreeY i c = 0)
    (h2 : ∀ c ∈ l2, degreeY i c = 0) :
    ∀ c ∈ listMulN l1 l2, degreeY i c = 0 := by
  induction l1 with
  | nil =>
    intro c hc
    rw [listMulN_nil] at hc
    exact absurd hc (List.not_mem_nil _)
  | cons p ps ih =>
    intro c hc
    rw [listMulN_cons] at hc
    apply listAddN_entries_degreeY_zero i
            (listScaleN p l2) (const 0 :: listMulN ps l2)
    · exact listScaleN_entries_degreeY_zero i p
              (h1 p (List.mem_cons_self _ _)) l2 h2
    · intro c' hc'
      cases hc' with
      | head => rfl
      | tail _ hc'' =>
        exact ih (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) c' hc''
    exact hc

/-- **Main structural lemma**: every entry in `yCoeffsAt i p` has
`degreeY i = 0`. Generalizes `yCoeffs_entries_y_free`. -/
theorem yCoeffsAt_entries_degreeY_zero {n : Nat} (i : Fin n)
    (p : MultiPoly n) :
    ∀ c ∈ yCoeffsAt i p, degreeY i c = 0 := by
  induction p with
  | const c =>
    intro c' hc'
    change c' ∈ ([const c] : List (MultiPoly n)) at hc'
    cases hc' with
    | head => rfl
    | tail _ h => exact absurd h (List.not_mem_nil _)
  | varX =>
    intro c' hc'
    change c' ∈ ([varX] : List (MultiPoly n)) at hc'
    cases hc' with
    | head => rfl
    | tail _ h => exact absurd h (List.not_mem_nil _)
  | varY j =>
    intro c' hc'
    -- yCoeffsAt i (varY j) = if j = i then [const 0, const 1] else [varY j].
    by_cases hji : j = i
    · change c' ∈ (if j = i then ([const 0, const 1] : List (MultiPoly n))
                              else ([varY j] : List (MultiPoly n))) at hc'
      simp [hji] at hc'
      cases hc' with
      | inl h => rw [h]; rfl
      | inr h => rw [h]; rfl
    · change c' ∈ (if j = i then ([const 0, const 1] : List (MultiPoly n))
                              else ([varY j] : List (MultiPoly n))) at hc'
      simp [hji] at hc'
      -- c' = varY j. degreeY i (varY j) = (if i = j then 1 else 0) = 0 since j ≠ i.
      rw [hc']
      show (if i = j then (1 : Nat) else 0) = 0
      have h_ne : i ≠ j := fun heq => hji heq.symm
      simp [h_ne]
  | add p q ihp ihq =>
    intro c hc
    change c ∈ listAddN (yCoeffsAt i p) (yCoeffsAt i q) at hc
    exact listAddN_entries_degreeY_zero i
            (yCoeffsAt i p) (yCoeffsAt i q) ihp ihq c hc
  | sub p q ihp ihq =>
    intro c hc
    change c ∈ listSubN (yCoeffsAt i p) (yCoeffsAt i q) at hc
    exact listSubN_entries_degreeY_zero i
            (yCoeffsAt i p) (yCoeffsAt i q) ihp ihq c hc
  | mul p q ihp ihq =>
    intro c hc
    change c ∈ listMulN (yCoeffsAt i p) (yCoeffsAt i q) at hc
    exact listMulN_entries_degreeY_zero i
            (yCoeffsAt i p) (yCoeffsAt i q) ihp ihq c hc

end MultiPoly
end MultiPolyMod
end MachLib
