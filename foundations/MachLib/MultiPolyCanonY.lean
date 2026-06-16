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
noncomputable def listAdd :
    List (MultiPoly 1) → List (MultiPoly 1) → List (MultiPoly 1)
  | [], qs => qs
  | ps, [] => ps
  | p :: ps, q :: qs => add p q :: listAdd ps qs

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
noncomputable def listScale (p : MultiPoly 1) :
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

end MultiPoly
end MultiPolyMod
end MachLib
