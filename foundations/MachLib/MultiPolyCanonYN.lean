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

/-! ## listEvalAuxN evaluator — eval coefficient list as polynomial in y_i

For coefficients `[a_0, a_1, ..., a_d]` extracted at index i, evaluates
`Σ_k (eval a_k x env) · (env i)^k`. The power is of `varY i`, mirroring
the MultiPoly 1 case's use of `varY 0`. -/

/-- Evaluate a coefficient list at offset `k` and index `i`. -/
noncomputable def listEvalAuxN {n : Nat} (i : Fin n) :
    List (MultiPoly n) → Nat → Real → (Fin n → Real) → Real
  | [], _, _, _ => 0
  | c :: rest, k, x, env =>
      eval c x env * eval (pow (varY i) k) x env +
      listEvalAuxN i rest (k + 1) x env

/-- Offset-0 wrapper. -/
noncomputable def listEvalN {n : Nat} (i : Fin n)
    (coeffs : List (MultiPoly n)) (x : Real)
    (env : Fin n → Real) : Real :=
  listEvalAuxN i coeffs 0 x env

theorem listEvalAuxN_nil {n : Nat} (i : Fin n) (k : Nat)
    (x : Real) (env : Fin n → Real) :
    listEvalAuxN i ([] : List (MultiPoly n)) k x env = 0 := rfl

theorem listEvalAuxN_cons {n : Nat} (i : Fin n)
    (c : MultiPoly n) (rest : List (MultiPoly n))
    (k : Nat) (x : Real) (env : Fin n → Real) :
    listEvalAuxN i (c :: rest) k x env =
    eval c x env * eval (pow (varY i) k) x env +
    listEvalAuxN i rest (k + 1) x env := rfl

/-! ## listAddN, listSubN eval correctness -/

theorem listEvalAuxN_listAddN {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n)) (k : Nat)
    (x : Real) (env : Fin n → Real) :
    listEvalAuxN i (listAddN l1 l2) k x env =
    listEvalAuxN i l1 k x env + listEvalAuxN i l2 k x env := by
  induction l1 generalizing l2 k with
  | nil =>
    rw [listAddN_nil_left, listEvalAuxN_nil, Real.zero_add]
  | cons p ps ih =>
    cases l2 with
    | nil =>
      rw [listAddN_cons_nil, listEvalAuxN_nil, Real.add_zero]
    | cons q qs =>
      rw [listAddN_cons_cons, listEvalAuxN_cons, listEvalAuxN_cons,
          listEvalAuxN_cons, eval_add, ih qs (k + 1),
          Real.mul_distrib_right]
      ac_rfl

theorem listEvalN_listAddN {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n)) (x : Real) (env : Fin n → Real) :
    listEvalN i (listAddN l1 l2) x env =
    listEvalN i l1 x env + listEvalN i l2 x env :=
  listEvalAuxN_listAddN i l1 l2 0 x env

theorem listSubN_nil_nil {n : Nat} :
    listSubN ([] : List (MultiPoly n)) [] = [] := rfl

theorem listSubN_nil_cons {n : Nat} (q : MultiPoly n)
    (qs : List (MultiPoly n)) :
    listSubN [] (q :: qs) = sub (const 0) q :: listSubN [] qs := rfl

theorem listSubN_cons_nil {n : Nat} (p : MultiPoly n)
    (ps : List (MultiPoly n)) :
    listSubN (p :: ps) [] = p :: ps := rfl

theorem listSubN_cons_cons {n : Nat} (p q : MultiPoly n)
    (ps qs : List (MultiPoly n)) :
    listSubN (p :: ps) (q :: qs) = sub p q :: listSubN ps qs := rfl

theorem listEvalAuxN_listSubN {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n)) (k : Nat)
    (x : Real) (env : Fin n → Real) :
    listEvalAuxN i (listSubN l1 l2) k x env =
    listEvalAuxN i l1 k x env - listEvalAuxN i l2 k x env := by
  induction l1 generalizing l2 k with
  | nil =>
    induction l2 generalizing k with
    | nil =>
      rw [listSubN_nil_nil, listEvalAuxN_nil, Real.sub_def, Real.neg_zero,
          Real.add_zero]
    | cons q qs ihq =>
      rw [listSubN_nil_cons, listEvalAuxN_cons, listEvalAuxN_cons,
          listEvalAuxN_nil, ihq (k + 1), eval_sub]
      simp only [Real.sub_def, Real.mul_distrib_right, Real.neg_add,
                 Real.neg_mul, Real.zero_add, Real.zero_mul, eval_const,
                 listEvalAuxN_nil, Real.add_zero, Real.neg_zero]
  | cons p ps ih =>
    cases l2 with
    | nil =>
      rw [listSubN_cons_nil, listEvalAuxN_nil, Real.sub_def, Real.neg_zero,
          Real.add_zero]
    | cons q qs =>
      rw [listSubN_cons_cons, listEvalAuxN_cons, listEvalAuxN_cons,
          listEvalAuxN_cons, eval_sub, ih qs (k + 1)]
      simp only [Real.sub_def, Real.mul_distrib_right, Real.neg_add,
                 Real.neg_mul]
      ac_rfl

theorem listEvalN_listSubN {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n)) (x : Real) (env : Fin n → Real) :
    listEvalN i (listSubN l1 l2) x env =
    listEvalN i l1 x env - listEvalN i l2 x env :=
  listEvalAuxN_listSubN i l1 l2 0 x env

/-! ## Shift identity for listEvalAuxN -/

theorem listEvalAuxN_succ_offset {n : Nat} (i : Fin n)
    (l : List (MultiPoly n)) (k : Nat)
    (x : Real) (env : Fin n → Real) :
    listEvalAuxN i l (k + 1) x env =
    env i * listEvalAuxN i l k x env := by
  induction l generalizing k with
  | nil =>
    rw [listEvalAuxN_nil, listEvalAuxN_nil, Real.mul_zero]
  | cons c rest ih =>
    rw [listEvalAuxN_cons, listEvalAuxN_cons, ih (k + 1)]
    have h_pow_succ : eval (pow (varY i) (k + 1)) x env =
                      env i * eval (pow (varY i) k) x env := by
      rw [eval_pow_succ]
      rfl
    rw [h_pow_succ, Real.mul_distrib]
    ac_rfl

/-! ## listScaleN + listMulN eval correctness -/

theorem listEvalAuxN_listScaleN {n : Nat} (i : Fin n)
    (p : MultiPoly n) (l : List (MultiPoly n)) (k : Nat)
    (x : Real) (env : Fin n → Real) :
    listEvalAuxN i (listScaleN p l) k x env =
    eval p x env * listEvalAuxN i l k x env := by
  induction l generalizing k with
  | nil =>
    rw [listScaleN_nil, listEvalAuxN_nil]
    show (0 : Real) = eval p x env * 0
    rw [Real.mul_zero]
  | cons q qs ih =>
    rw [listScaleN_cons, listEvalAuxN_cons, listEvalAuxN_cons, eval_mul,
        ih (k + 1), Real.mul_distrib]
    ac_rfl

theorem listEvalAuxN_listMulN {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n)) (k : Nat)
    (x : Real) (env : Fin n → Real) :
    listEvalAuxN i (listMulN l1 l2) k x env =
    listEvalAuxN i l1 k x env * listEvalAuxN i l2 0 x env := by
  induction l1 generalizing k with
  | nil =>
    rw [listMulN_nil, listEvalAuxN_nil]
    show (0 : Real) = 0 * listEvalAuxN i l2 0 x env
    rw [Real.zero_mul]
  | cons p ps ih =>
    rw [listMulN_cons, listEvalAuxN_listAddN, listEvalAuxN_listScaleN,
        listEvalAuxN_cons, ih (k + 1), listEvalAuxN_cons]
    have h_shift_l2 : listEvalAuxN i l2 k x env =
                      eval (pow (varY i) k) x env *
                      listEvalAuxN i l2 0 x env := by
      induction k with
      | zero => rw [eval_pow_zero, Real.one_mul_thm]
      | succ k ihk =>
        rw [listEvalAuxN_succ_offset, ihk, eval_pow_succ]
        show env i * (eval (pow (varY i) k) x env *
                      listEvalAuxN i l2 0 x env) =
             env i * eval (pow (varY i) k) x env *
             listEvalAuxN i l2 0 x env
        rw [Real.mul_assoc]
    rw [h_shift_l2, eval_const, Real.zero_mul, Real.zero_add,
        Real.mul_distrib_right]
    ac_rfl

theorem listEvalN_listMulN {n : Nat} (i : Fin n)
    (l1 l2 : List (MultiPoly n)) (x : Real) (env : Fin n → Real) :
    listEvalN i (listMulN l1 l2) x env =
    listEvalN i l1 x env * listEvalN i l2 x env :=
  listEvalAuxN_listMulN i l1 l2 0 x env

/-! ## Eval correctness — base cases for yCoeffsAt -/

theorem eval_yCoeffsAt_const {n : Nat} (i : Fin n) (c : Real)
    (x : Real) (env : Fin n → Real) :
    listEvalN i (yCoeffsAt i (const c : MultiPoly n)) x env =
    eval (const c : MultiPoly n) x env := by
  show eval (const c : MultiPoly n) x env *
       eval (pow (varY i) 0) x env + 0 = c
  show (c : Real) * 1 + 0 = c
  rw [Real.mul_one_ax, Real.add_zero]

theorem eval_yCoeffsAt_varX {n : Nat} (i : Fin n)
    (x : Real) (env : Fin n → Real) :
    listEvalN i (yCoeffsAt i (varX : MultiPoly n)) x env =
    eval (varX : MultiPoly n) x env := by
  show eval (varX : MultiPoly n) x env *
       eval (pow (varY i) 0) x env + 0 = x
  show x * 1 + 0 = x
  rw [Real.mul_one_ax, Real.add_zero]

theorem eval_yCoeffsAt_varY {n : Nat} (i j : Fin n)
    (x : Real) (env : Fin n → Real) :
    listEvalN i (yCoeffsAt i (varY j : MultiPoly n)) x env =
    eval (varY j : MultiPoly n) x env := by
  have hy : yCoeffsAt i (varY j : MultiPoly n) =
            if j = i then ([const 0, const 1] : List (MultiPoly n))
                      else ([varY j] : List (MultiPoly n)) := by
    simp only [yCoeffsAt]
  rw [hy]
  by_cases hji : j = i
  · -- j = i: list is [const 0, const 1].
    subst hji
    simp only [if_pos rfl]
    show eval (const 0 : MultiPoly n) x env *
           eval (pow (varY j) 0) x env +
         (eval (const 1 : MultiPoly n) x env *
           eval (pow (varY j) 1) x env + 0) = env j
    show (0 : Real) * 1 +
         (1 * (eval (varY j : MultiPoly n) x env *
                eval (pow (varY j) 0) x env) + 0) = env j
    rw [Real.zero_mul, Real.zero_add, Real.add_zero, Real.one_mul_thm]
    show eval (varY j : MultiPoly n) x env * 1 = env j
    rw [Real.mul_one_ax]
    rfl
  · -- j ≠ i: list is [varY j].
    simp only [if_neg hji]
    show eval (varY j : MultiPoly n) x env *
         eval (pow (varY i) 0) x env + 0 =
         eval (varY j : MultiPoly n) x env
    show env j * 1 + 0 = env j
    rw [Real.mul_one_ax, Real.add_zero]

/-! ## Eval correctness — compound cases via `change` -/

theorem eval_yCoeffsAt_add_via_induction {n : Nat} (i : Fin n)
    (p q : MultiPoly n) (x : Real) (env : Fin n → Real)
    (ihp : listEvalN i (yCoeffsAt i p) x env = eval p x env)
    (ihq : listEvalN i (yCoeffsAt i q) x env = eval q x env) :
    listEvalN i (yCoeffsAt i (add p q)) x env =
    eval (add p q) x env := by
  change listEvalN i (listAddN (yCoeffsAt i p) (yCoeffsAt i q)) x env =
         eval p x env + eval q x env
  rw [listEvalN_listAddN, ihp, ihq]

theorem eval_yCoeffsAt_sub_via_induction {n : Nat} (i : Fin n)
    (p q : MultiPoly n) (x : Real) (env : Fin n → Real)
    (ihp : listEvalN i (yCoeffsAt i p) x env = eval p x env)
    (ihq : listEvalN i (yCoeffsAt i q) x env = eval q x env) :
    listEvalN i (yCoeffsAt i (sub p q)) x env =
    eval (sub p q) x env := by
  change listEvalN i (listSubN (yCoeffsAt i p) (yCoeffsAt i q)) x env =
         eval p x env - eval q x env
  rw [listEvalN_listSubN, ihp, ihq]

theorem eval_yCoeffsAt_mul_via_induction {n : Nat} (i : Fin n)
    (p q : MultiPoly n) (x : Real) (env : Fin n → Real)
    (ihp : listEvalN i (yCoeffsAt i p) x env = eval p x env)
    (ihq : listEvalN i (yCoeffsAt i q) x env = eval q x env) :
    listEvalN i (yCoeffsAt i (mul p q)) x env =
    eval (mul p q) x env := by
  change listEvalN i (listMulN (yCoeffsAt i p) (yCoeffsAt i q)) x env =
         eval p x env * eval q x env
  rw [listEvalN_listMulN, ihp, ihq]

/-! ## Integrated eval correctness theorem -/

/-- **THE INTEGRATED EVAL CORRECTNESS** for `yCoeffsAt`. Every MultiPoly
n evaluates to the same value as its yCoeffsAt canonical-form
representation at any index i. Generalizes `eval_yCoeffs`. -/
theorem eval_yCoeffsAt {n : Nat} (i : Fin n) (p : MultiPoly n)
    (x : Real) (env : Fin n → Real) :
    listEvalN i (yCoeffsAt i p) x env = eval p x env := by
  induction p with
  | const c => exact eval_yCoeffsAt_const i c x env
  | varX => exact eval_yCoeffsAt_varX i x env
  | varY j => exact eval_yCoeffsAt_varY i j x env
  | add p q ihp ihq =>
    exact eval_yCoeffsAt_add_via_induction i p q x env ihp ihq
  | sub p q ihp ihq =>
    exact eval_yCoeffsAt_sub_via_induction i p q x env ihp ihq
  | mul p q ihp ihq =>
    exact eval_yCoeffsAt_mul_via_induction i p q x env ihp ihq

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
