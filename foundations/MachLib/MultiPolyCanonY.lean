import MachLib.MultiPoly

/-!
# MachLib.MultiPolyCanonY — y-coefficient canonical form for MultiPoly 1

The canonical "polynomial in y_0" form for a `MultiPoly 1` extracts
the list of coefficients of `y_0^k`:

  `p = Σ_k coeffs[k] · y_0^k`

where each `coeffs[k] : MultiPoly 1` has `degreeY 0 = 0` (i.e., it's a
polynomial in x only).

This is the multi-variable canonical form needed to canonicalize
arbitrary `MultiPoly 1` expressions into bridge-image form (i.e.,
images of `ExpPoly.toMultiPoly1`). Once shipped, every MultiPoly 1 is
semantically equivalent to a bridge image, and the constructive
Khovanskii bound (PfaffianFn_singleExp_auto_bound_via_bridge) applies
to ALL PfaffianFns over SingleExpChain — not just bridge images.

## What ships in this commit

  - `listAdd`, `listSub`: pointwise sum/diff of coefficient lists
    (padding the shorter with const 0).
  - `listScale`: scale a list by a single MultiPoly.
  - `listMul`: polynomial convolution of coefficient lists.
  - `yCoeffs : MultiPoly 1 → List (MultiPoly 1)`: the extraction
    function. Each compound case uses the list operations.

The eval correctness theorem (`eval p x env = listEval (yCoeffs p) x env`)
is the next session's piece.
-/

namespace MachLib
namespace MultiPolyMod
namespace MultiPoly

/-! ## List arithmetic for coefficient lists -/

/-- Pointwise addition of two coefficient lists. The shorter list is
padded with the (implicit) `const 0` entries. -/
def listAdd :
    List (MultiPoly 1) → List (MultiPoly 1) → List (MultiPoly 1)
  | [], qs => qs
  | p :: ps, [] => p :: ps
  | p :: ps, q :: qs => add p q :: listAdd ps qs

theorem listAdd_nil_left (l : List (MultiPoly 1)) : listAdd [] l = l := rfl

theorem listAdd_cons_nil (p : MultiPoly 1) (ps : List (MultiPoly 1)) :
    listAdd (p :: ps) [] = p :: ps := rfl

theorem listAdd_cons_cons (p q : MultiPoly 1) (ps qs : List (MultiPoly 1)) :
    listAdd (p :: ps) (q :: qs) = add p q :: listAdd ps qs := rfl

/-- Pointwise subtraction of two coefficient lists. The first list's
extra entries pass through; the second list's extra entries are
negated via `sub (const 0) _`. -/
noncomputable def listSub :
    List (MultiPoly 1) → List (MultiPoly 1) → List (MultiPoly 1)
  | [], [] => []
  | [], q :: qs => sub (const 0) q :: listSub [] qs
  | ps, [] => ps
  | p :: ps, q :: qs => sub p q :: listSub ps qs

/-- Scale a coefficient list by a single MultiPoly. Multiplies each
entry by `p`. -/
def listScale (p : MultiPoly 1) :
    List (MultiPoly 1) → List (MultiPoly 1)
  | [] => []
  | q :: qs => mul p q :: listScale p qs

/-- Polynomial convolution: multiply two coefficient lists.
For `[p_0, p_1, ..., p_d]` and `[q_0, q_1, ..., q_e]`, the result is
`[Σ_{k+j=0} p_k q_j, Σ_{k+j=1} p_k q_j, ..., Σ_{k+j=d+e} p_k q_j]`. -/
noncomputable def listMul :
    List (MultiPoly 1) → List (MultiPoly 1) → List (MultiPoly 1)
  | [], _ => []
  | p :: ps, qs => listAdd (listScale p qs) (const 0 :: listMul ps qs)

/-! ## Y-coefficient extraction -/

/-- **Y-coefficient extraction.** Returns the list of coefficients
`[a_0, a_1, ..., a_d]` such that `p = Σ_k a_k · y_0^k`.

Each compound case uses the corresponding list operation. The result's
entries inductively have `degreeY 0 = 0` (proven in a follow-up). -/
noncomputable def yCoeffs : MultiPoly 1 → List (MultiPoly 1)
  | const c => [const c]
  | varX => [varX]
  | varY _ => [const 0, const 1]
  | add p q => listAdd (yCoeffs p) (yCoeffs q)
  | sub p q => listSub (yCoeffs p) (yCoeffs q)
  | mul p q => listMul (yCoeffs p) (yCoeffs q)

/-! ## Structural sanity for yCoeffs

The extraction never produces an empty list (the const 0 case ships a
single-element list). This is a structural lemma used by the eval
correctness proof in the follow-up commit. -/

/-- `yCoeffs` never produces an empty list. The base cases all return
single- or two-element lists; the compound cases preserve non-emptiness
by induction on the list operations. -/
theorem yCoeffs_nonempty (p : MultiPoly 1) : yCoeffs p ≠ [] := by
  induction p with
  | const c =>
    show [const c] ≠ []
    intro h; cases h
  | varX =>
    show [varX] ≠ []
    intro h; cases h
  | varY _ =>
    show [const 0, const 1] ≠ []
    intro h; cases h
  | add p q ihp ihq =>
    -- listAdd preserves non-emptiness when both args are non-empty.
    show listAdd (yCoeffs p) (yCoeffs q) ≠ []
    intro h
    cases hp : yCoeffs p with
    | nil => exact ihp hp
    | cons p' rest =>
      cases hq : yCoeffs q with
      | nil => exact ihq hq
      | cons q' restq =>
        rw [hp, hq] at h
        show False
        cases h
  | sub p q ihp ihq =>
    show listSub (yCoeffs p) (yCoeffs q) ≠ []
    intro h
    cases hp : yCoeffs p with
    | nil => exact ihp hp
    | cons p' rest =>
      cases hq : yCoeffs q with
      | nil => exact ihq hq
      | cons q' restq =>
        rw [hp, hq] at h
        show False
        cases h
  | mul p q ihp ihq =>
    show listMul (yCoeffs p) (yCoeffs q) ≠ []
    intro h
    cases hp : yCoeffs p with
    | nil => exact ihp hp
    | cons p' restp =>
      cases hq : yCoeffs q with
      | nil =>
        rw [hp, hq] at h
        show False
        -- listMul (p'::restp) [] = listAdd (listScale p' []) (const 0 :: listMul restp [])
        --                       = listAdd [] (const 0 :: listMul restp [])
        --                       = const 0 :: listMul restp []
        -- which is non-empty.
        cases h
      | cons q' restq =>
        rw [hp, hq] at h
        show False
        -- listMul (p'::restp) (q'::restq) = listAdd (listScale p' (q'::restq)) ...
        -- listScale p' (q'::restq) = mul p' q' :: listScale p' restq
        -- listAdd (mul p' q' :: ...) (const 0 :: ...) = add (mul p' q') (const 0) :: ...
        -- which is non-empty.
        cases h

/-! ## listEval — evaluating a coefficient list as a polynomial in y

For coefficients `[a_0, a_1, ..., a_d]`, `listEval` computes
`Σ_k (eval a_k x env) · (env 0)^k`. The shift uses `pow (varY 0) k`
so the indexing matches the bridge's offset structure. -/

/-- Evaluate a coefficient list at offset `k`: sum of
`eval a_j · pow (varY 0) (k+j)` for j over the list. -/
noncomputable def listEvalAux : List (MultiPoly 1) → Nat → Real →
    (Fin 1 → Real) → Real
  | [], _, _, _ => 0
  | c :: rest, k, x, env =>
      eval c x env * eval (pow (varY 0) k) x env +
      listEvalAux rest (k + 1) x env

/-- Evaluate a coefficient list at offset 0. -/
noncomputable def listEval (coeffs : List (MultiPoly 1)) (x : Real)
    (env : Fin 1 → Real) : Real :=
  listEvalAux coeffs 0 x env

/-! ## Eval correctness for base cases (const, varX, varY)

The full eval-correctness theorem `eval p x env = listEval (yCoeffs p) x env`
follows by structural induction. This commit ships the three base cases.
The compound cases (add, sub, mul) need eval-correctness for the list
operations (`listAdd_eval`, `listSub_eval`, `listMul_eval`) — multi-session
follow-up. -/

/-- **Const case**: `yCoeffs (const c) = [const c]`, which evaluates to
just `c · 1 = c`. -/
theorem eval_yCoeffs_const (c : Real) (x : Real) (env : Fin 1 → Real) :
    listEval (yCoeffs (const c)) x env = eval (const c : MultiPoly 1) x env := by
  show eval (const c : MultiPoly 1) x env *
       eval (pow (varY 0) 0) x env + 0 = c
  show (c : Real) * 1 + 0 = c
  rw [Real.mul_one_ax, Real.add_zero]

/-- **varX case**: `yCoeffs varX = [varX]`, evaluates to `x · 1 = x`. -/
theorem eval_yCoeffs_varX (x : Real) (env : Fin 1 → Real) :
    listEval (yCoeffs (varX : MultiPoly 1)) x env =
    eval (varX : MultiPoly 1) x env := by
  show eval (varX : MultiPoly 1) x env *
       eval (pow (varY 0) 0) x env + 0 = x
  show x * 1 + 0 = x
  rw [Real.mul_one_ax, Real.add_zero]

/-- **varY case**: `yCoeffs (varY 0) = [const 0, const 1]`, evaluates to
`0 · 1 + 1 · y + 0 = env 0`. -/
theorem eval_yCoeffs_varY (x : Real) (env : Fin 1 → Real) :
    listEval (yCoeffs (varY 0 : MultiPoly 1)) x env =
    eval (varY 0 : MultiPoly 1) x env := by
  show eval (const 0 : MultiPoly 1) x env *
         eval (pow (varY 0) 0) x env +
       (eval (const 1 : MultiPoly 1) x env *
         eval (pow (varY 0) 1) x env + 0) = env 0
  show (0 : Real) * 1 +
       (1 * (eval (varY 0 : MultiPoly 1) x env *
              eval (pow (varY 0) 0) x env) + 0) = env 0
  rw [Real.zero_mul, Real.zero_add, Real.add_zero]
  rw [Real.one_mul_thm]
  show eval (varY 0 : MultiPoly 1) x env * 1 = env 0
  rw [Real.mul_one_ax]
  rfl

/-! ## listAdd eval correctness — additive composition

The `listAdd` operation evaluates to the sum of its operands' evals.
This is the foundation for the `eval_yCoeffs_add` compound case. -/

theorem listEvalAux_nil (k : Nat) (x : Real) (env : Fin 1 → Real) :
    listEvalAux ([] : List (MultiPoly 1)) k x env = 0 := rfl

theorem listEvalAux_cons (c : MultiPoly 1) (rest : List (MultiPoly 1))
    (k : Nat) (x : Real) (env : Fin 1 → Real) :
    listEvalAux (c :: rest) k x env =
    eval c x env * eval (pow (varY 0) k) x env +
    listEvalAux rest (k + 1) x env := rfl

/-- **listAdd is eval-additive at any offset.** Induction on `l1`,
case-split on `l2`. The cons-cons case uses `mul_distrib_right` + AC. -/
theorem listEvalAux_listAdd (l1 l2 : List (MultiPoly 1)) (k : Nat)
    (x : Real) (env : Fin 1 → Real) :
    listEvalAux (listAdd l1 l2) k x env =
    listEvalAux l1 k x env + listEvalAux l2 k x env := by
  induction l1 generalizing l2 k with
  | nil =>
    rw [listAdd_nil_left, listEvalAux_nil, Real.zero_add]
  | cons p ps ih =>
    cases l2 with
    | nil =>
      rw [listAdd_cons_nil, listEvalAux_nil, Real.add_zero]
    | cons q qs =>
      rw [listAdd_cons_cons, listEvalAux_cons, listEvalAux_cons,
          listEvalAux_cons, eval_add, ih qs (k + 1), Real.mul_distrib_right]
      ac_rfl

/-- **listAdd is eval-additive** (offset 0). Direct from `listEvalAux_listAdd`. -/
theorem listEval_listAdd (l1 l2 : List (MultiPoly 1))
    (x : Real) (env : Fin 1 → Real) :
    listEval (listAdd l1 l2) x env =
    listEval l1 x env + listEval l2 x env :=
  listEvalAux_listAdd l1 l2 0 x env

/-! ## Eval correctness — add case via induction

The compound `eval_yCoeffs_add` uses the auto-generated equation lemma
`yCoeffs.eq_4` (or matched via `match` reduction in `induction`). When
inducting on `p`, the `add` case lets Lean unfold `yCoeffs (add p q)`
via the inductive eliminator. -/

/-- **Add case** (via induction): listEval of yCoeffs distributes over
add. Uses the inductive eliminator to access the def-eq reduction. -/
theorem eval_yCoeffs_add_via_induction
    (p q : MultiPoly 1) (x : Real) (env : Fin 1 → Real)
    (ihp : listEval (yCoeffs p) x env = eval p x env)
    (ihq : listEval (yCoeffs q) x env = eval q x env) :
    listEval (yCoeffs (add p q)) x env = eval (add p q) x env := by
  -- yCoeffs (add p q) unfolds to listAdd (yCoeffs p) (yCoeffs q)
  -- via the structural recursion. Use `change` to bypass any well-founded
  -- wrapping.
  change listEval (listAdd (yCoeffs p) (yCoeffs q)) x env =
         eval p x env + eval q x env
  rw [listEval_listAdd, ihp, ihq]

/-! ## listSub eval correctness

The `listSub` operation evaluates to the difference of its operands'
evals. The proof follows the same structure as `listEvalAux_listAdd`
but with subtraction. -/

theorem listSub_nil_nil : listSub ([] : List (MultiPoly 1)) [] = [] := rfl

theorem listSub_nil_cons (q : MultiPoly 1) (qs : List (MultiPoly 1)) :
    listSub [] (q :: qs) = sub (const 0) q :: listSub [] qs := rfl

theorem listSub_cons_nil (p : MultiPoly 1) (ps : List (MultiPoly 1)) :
    listSub (p :: ps) [] = p :: ps := rfl

theorem listSub_cons_cons (p q : MultiPoly 1) (ps qs : List (MultiPoly 1)) :
    listSub (p :: ps) (q :: qs) = sub p q :: listSub ps qs := rfl

/-- **listSub is eval-subtractive at any offset.** Induction on `l1`,
case-split on `l2`. Both compound cases use the algebraic rearrangement
`(a - b) * c = a * c - b * c` via `mul_distrib_right` + `neg_mul`. -/
theorem listEvalAux_listSub (l1 l2 : List (MultiPoly 1)) (k : Nat)
    (x : Real) (env : Fin 1 → Real) :
    listEvalAux (listSub l1 l2) k x env =
    listEvalAux l1 k x env - listEvalAux l2 k x env := by
  induction l1 generalizing l2 k with
  | nil =>
    induction l2 generalizing k with
    | nil =>
      rw [listSub_nil_nil, listEvalAux_nil, Real.sub_def, Real.neg_zero,
          Real.add_zero]
    | cons q qs ihq =>
      rw [listSub_nil_cons, listEvalAux_cons, listEvalAux_cons,
          listEvalAux_nil, ihq (k + 1), eval_sub]
      simp only [Real.sub_def, Real.mul_distrib_right, Real.neg_add,
                 Real.neg_mul, Real.zero_add, Real.zero_mul, eval_const,
                 listEvalAux_nil, Real.add_zero, Real.neg_zero]
  | cons p ps ih =>
    cases l2 with
    | nil =>
      rw [listSub_cons_nil, listEvalAux_nil, Real.sub_def, Real.neg_zero,
          Real.add_zero]
    | cons q qs =>
      rw [listSub_cons_cons, listEvalAux_cons, listEvalAux_cons,
          listEvalAux_cons, eval_sub, ih qs (k + 1)]
      simp only [Real.sub_def, Real.mul_distrib_right, Real.neg_add,
                 Real.neg_mul]
      ac_rfl

/-- **listSub is eval-subtractive** (offset 0). -/
theorem listEval_listSub (l1 l2 : List (MultiPoly 1))
    (x : Real) (env : Fin 1 → Real) :
    listEval (listSub l1 l2) x env =
    listEval l1 x env - listEval l2 x env :=
  listEvalAux_listSub l1 l2 0 x env

/-- **Sub case** (via induction): listEval of yCoeffs distributes over sub. -/
theorem eval_yCoeffs_sub_via_induction
    (p q : MultiPoly 1) (x : Real) (env : Fin 1 → Real)
    (ihp : listEval (yCoeffs p) x env = eval p x env)
    (ihq : listEval (yCoeffs q) x env = eval q x env) :
    listEval (yCoeffs (sub p q)) x env = eval (sub p q) x env := by
  change listEval (listSub (yCoeffs p) (yCoeffs q)) x env =
         eval p x env - eval q x env
  rw [listEval_listSub, ihp, ihq]

/-! ## Shift identity for listEvalAux

Incrementing the offset by 1 multiplies the eval by `env 0`. This is
the recursive step relating `listEvalAux l k` to `listEvalAux l (k+1)`.
Foundation for the listMul convolution correctness. -/

theorem listEvalAux_succ_offset (l : List (MultiPoly 1)) (k : Nat)
    (x : Real) (env : Fin 1 → Real) :
    listEvalAux l (k + 1) x env = env 0 * listEvalAux l k x env := by
  induction l generalizing k with
  | nil =>
    rw [listEvalAux_nil, listEvalAux_nil, Real.mul_zero]
  | cons c rest ih =>
    rw [listEvalAux_cons, listEvalAux_cons, ih (k + 1)]
    -- pow_succ identity for env 0:
    have h_pow_succ : eval (pow (varY 0) (k + 1)) x env =
                      env 0 * eval (pow (varY 0) k) x env := by
      rw [eval_pow_succ]
      rfl
    rw [h_pow_succ, Real.mul_distrib]
    ac_rfl

/-! ## listScale eval correctness

`listScale p l` evaluates to `eval p · listEvalAux l k`. Used in the
listMul correctness proof. -/

theorem listScale_nil (p : MultiPoly 1) :
    listScale p [] = [] := rfl

theorem listScale_cons (p q : MultiPoly 1) (qs : List (MultiPoly 1)) :
    listScale p (q :: qs) = mul p q :: listScale p qs := rfl

theorem listEvalAux_listScale (p : MultiPoly 1) (l : List (MultiPoly 1))
    (k : Nat) (x : Real) (env : Fin 1 → Real) :
    listEvalAux (listScale p l) k x env =
    eval p x env * listEvalAux l k x env := by
  induction l generalizing k with
  | nil =>
    rw [listScale_nil, listEvalAux_nil]
    show (0 : Real) = eval p x env * 0
    rw [Real.mul_zero]
  | cons q qs ih =>
    rw [listScale_cons, listEvalAux_cons, listEvalAux_cons, eval_mul,
        ih (k + 1), Real.mul_distrib]
    ac_rfl

/-! ## listMul eval correctness — the convolution case -/

theorem listMul_nil (l : List (MultiPoly 1)) :
    listMul [] l = [] := rfl

theorem listMul_cons (p : MultiPoly 1) (ps : List (MultiPoly 1))
    (qs : List (MultiPoly 1)) :
    listMul (p :: ps) qs =
    listAdd (listScale p qs) (const 0 :: listMul ps qs) := rfl

/-- **listMul is eval-multiplicative.** Induction on l1; the cons case
composes listAdd_eval + listScale_eval + the shift identity. -/
theorem listEvalAux_listMul (l1 l2 : List (MultiPoly 1)) (k : Nat)
    (x : Real) (env : Fin 1 → Real) :
    listEvalAux (listMul l1 l2) k x env =
    listEvalAux l1 k x env * listEvalAux l2 0 x env := by
  induction l1 generalizing k with
  | nil =>
    rw [listMul_nil, listEvalAux_nil]
    show (0 : Real) = 0 * listEvalAux l2 0 x env
    rw [Real.zero_mul]
  | cons p ps ih =>
    rw [listMul_cons, listEvalAux_listAdd, listEvalAux_listScale,
        listEvalAux_cons, ih (k + 1), listEvalAux_cons]
    -- LHS: eval p · listEvalAux l2 k + (eval (const 0) · pow k +
    --       listEvalAux ps (k+1) · listEvalAux l2 0)
    -- RHS: (eval p · pow k + listEvalAux ps (k+1)) · listEvalAux l2 0
    --    = eval p · pow k · listEvalAux l2 0 + listEvalAux ps (k+1) · listEvalAux l2 0
    -- For equality, need: eval p · listEvalAux l2 k = eval p · pow k · listEvalAux l2 0.
    -- Apply shift identity to l2 at offset k iteratively (or use the fact that
    -- listEvalAux l2 k = pow k · listEvalAux l2 0).
    have h_shift_l2 : listEvalAux l2 k x env =
                      eval (pow (varY 0) k) x env * listEvalAux l2 0 x env := by
      induction k with
      | zero => rw [eval_pow_zero, Real.one_mul_thm]
      | succ k ihk =>
        rw [listEvalAux_succ_offset, ihk, eval_pow_succ]
        show eval (varY 0) x env *
             (eval (pow (varY 0) k) x env * listEvalAux l2 0 x env) =
             eval (varY 0) x env * eval (pow (varY 0) k) x env *
             listEvalAux l2 0 x env
        rw [Real.mul_assoc]
    rw [h_shift_l2, eval_const, Real.zero_mul, Real.zero_add,
        Real.mul_distrib_right]
    ac_rfl

theorem listEval_listMul (l1 l2 : List (MultiPoly 1))
    (x : Real) (env : Fin 1 → Real) :
    listEval (listMul l1 l2) x env =
    listEval l1 x env * listEval l2 x env :=
  listEvalAux_listMul l1 l2 0 x env

/-- **Mul case** (via induction): listEval of yCoeffs distributes over mul. -/
theorem eval_yCoeffs_mul_via_induction
    (p q : MultiPoly 1) (x : Real) (env : Fin 1 → Real)
    (ihp : listEval (yCoeffs p) x env = eval p x env)
    (ihq : listEval (yCoeffs q) x env = eval q x env) :
    listEval (yCoeffs (mul p q)) x env = eval (mul p q) x env := by
  change listEval (listMul (yCoeffs p) (yCoeffs q)) x env =
         eval p x env * eval q x env
  rw [listEval_listMul, ihp, ihq]

/-! ## Integrated eval correctness

Combining all 6 cases via structural induction. -/

/-- **The canonical-form eval correctness theorem.** Every MultiPoly 1
evaluates to the same value as its yCoeffs canonical-form representation.

The proof is structural induction: the 3 base cases (const, varX, varY)
are direct; the 3 compound cases use `_via_induction` helpers that
access the def-eq reduction via `change`. -/
theorem eval_yCoeffs (p : MultiPoly 1) (x : Real) (env : Fin 1 → Real) :
    listEval (yCoeffs p) x env = eval p x env := by
  induction p with
  | const c => exact eval_yCoeffs_const c x env
  | varX => exact eval_yCoeffs_varX x env
  | varY j =>
    -- j : Fin 1, so j = 0.
    have : j = 0 := by
      apply Fin.eq_of_val_eq
      have := j.isLt
      omega
    subst this
    exact eval_yCoeffs_varY x env
  | add p q ihp ihq =>
    exact eval_yCoeffs_add_via_induction p q x env ihp ihq
  | sub p q ihp ihq =>
    exact eval_yCoeffs_sub_via_induction p q x env ihp ihq
  | mul p q ihp ihq =>
    exact eval_yCoeffs_mul_via_induction p q x env ihp ihq

end MultiPoly
end MultiPolyMod
end MachLib
