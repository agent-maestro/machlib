import MachLib.PolyRing
import Lean

/-
MachLib.MPolyRing — a reflective MULTIVARIATE polynomial normaliser ("ring v3").

`mach_poly` (in `PolyRingTactic`) handles multivariate identities by recursively
re-running the univariate engine atom-by-atom. That is correct but its per-level
re-normalisation costs ~5^(vars) `simp` calls: the 6-variable Vec3 Lagrange
identity takes ~70 s, and the 8-variable Euler four-square identity does NOT
finish in 50 minutes (measured; memory stays flat — it is a pure CPU grind, not
divergence).

This module fixes that with a genuine normal form. A depth-`n` polynomial is a
NESTED Horner coefficient list — `MPoly 0 = Real`, `MPoly (n+1) = List (MPoly n)`
— so the WHOLE expression is reified once, normalised once (the recursive `addM`
/ `mulM` collect like monomials structurally in a single pass), and compared once
via `MPEq` (equality up to trailing zeros, recursive). Cost is polynomial in the
number of monomials, not exponential in the number of variables: the four-square
identity now closes in SECONDS, sorryAx-clean.

Two design notes for the next agent:
  * The operations (`addM`/`mulM`/`negM`) are STRUCTURAL on the depth `n`, with
    the list work pushed into standalone parameterised helpers (`zipPad`,
    `mulList`, `eqPad`). This is deliberate: mutual `def`s do NOT reduce under
    `simp` (their equation lemmas don't fire), which silently blocks the
    normalise-by-`simp` step the tactic depends on. Keep them non-mutual.
  * Soundness lands in `Real` (every `eval_*` lemma equates an `evalM` to a `Real`
    expression), so the per-step algebra is plain `mach_ring`. No commutative-ring
    structure on `MPoly n` is needed — the homomorphism lemmas suffice.

`import Lean` is Lean CORE (no Mathlib / external dependency); MachLib stays
zero-dependency.
-/

namespace MachLib
namespace Real
namespace MV

/-- A depth-`n` (n variables) polynomial as nested Horner coefficient lists.
`MPoly 0 = Real`; `MPoly (n+1) = List (MPoly n)` is `c₀ + x·c₁ + x²·c₂ + …` in the
outermost variable `x`, each `cᵢ` a polynomial in the remaining variables. -/
@[reducible] def MPoly : Nat → Type
  | 0     => Real
  | n + 1 => List (MPoly n)

/-- Evaluate at a variable assignment (outermost variable first). -/
noncomputable def evalM : (n : Nat) → MPoly n → List Real → Real
  | 0,     c,  _       => c
  | _ + 1, _,  []      => 0
  | n + 1, cs, x :: xs => (cs.map (fun c => evalM n c xs)).foldr (fun cv acc => cv + x * acc) 0

theorem evalM_z (c : MPoly 0) (xs) : evalM 0 c xs = c := rfl
theorem evalM_nil (n) (cs : List (MPoly n)) : evalM (n+1) cs [] = 0 := rfl
theorem evalM_emp (n) (x) (xs) : evalM (n+1) ([] : List (MPoly n)) (x :: xs) = 0 := rfl
theorem evalM_cons (n) (c : MPoly n) (cs) (x) (xs) :
    evalM (n+1) (c :: cs) (x :: xs) = evalM n c xs + x * evalM (n+1) cs (x :: xs) := rfl

/-! ### Standalone list helpers (non-mutual ⇒ they reduce under `simp`). -/

/-- Positional combine with implicit zero-padding of the shorter list. -/
def zipPad {α} (f : α → α → α) : List α → List α → List α
  | [],     q      => q
  | a :: p, []     => a :: p
  | a :: p, b :: q => f a b :: zipPad f p q
/-- Horner polynomial product given coefficient `mul`/`add` and a zero. -/
def mulList {α} (mul1 add1 : α → α → α) (z : α) : List α → List α → List α
  | [],     _ => []
  | a :: p, q => zipPad add1 (q.map (mul1 a)) (z :: mulList mul1 add1 z p q)
/-- Coefficient-wise equality up to trailing zeros. -/
def eqPad {α} (eqz : α → Prop) (eq2 : α → α → Prop) : List α → List α → Prop
  | [],     []     => True
  | [],     b :: q => eqz b ∧ eqPad eqz eq2 [] q
  | a :: p, []     => eqz a ∧ eqPad eqz eq2 p []
  | a :: p, b :: q => eq2 a b ∧ eqPad eqz eq2 p q

/-! ### Ring operations — structural on depth `n` (⇒ they reduce). -/

noncomputable def zeroM : (n : Nat) → MPoly n
  | 0     => (0 : Real)
  | _ + 1 => []
noncomputable def addM : (n : Nat) → MPoly n → MPoly n → MPoly n
  | 0     => fun a b => (a : Real) + (b : Real)
  | n + 1 => fun p q => zipPad (addM n) p q
noncomputable def negM : (n : Nat) → MPoly n → MPoly n
  | 0     => fun a => -(a : Real)
  | n + 1 => fun p => p.map (negM n)
noncomputable def mulM : (n : Nat) → MPoly n → MPoly n → MPoly n
  | 0     => fun a b => (a : Real) * (b : Real)
  | n + 1 => fun p q => mulList (mulM n) (addM n) (zeroM n) p q

theorem eval_zeroM : ∀ (n) (xs), evalM n (zeroM n) xs = 0
  | 0,     _      => rfl
  | _ + 1, []     => rfl
  | _ + 1, _ :: _ => rfl

/-! ### Homomorphism soundness (helpers parameterised by the lower op's soundness). -/

theorem eval_zipPad (n) (f : MPoly n → MPoly n → MPoly n)
    (hf : ∀ a b xs, evalM n (f a b) xs = evalM n a xs + evalM n b xs) :
    ∀ (p q : List (MPoly n)) (x xs),
      evalM (n+1) (zipPad f p q) (x::xs) = evalM (n+1) p (x::xs) + evalM (n+1) q (x::xs)
  | [],     q,      x, xs => by simp only [zipPad, evalM_emp, zero_add]
  | a :: p, [],     x, xs => by simp only [zipPad, evalM_emp, add_zero]
  | a :: p, b :: q, x, xs => by
      simp only [zipPad, evalM_cons]
      rw [hf a b xs, eval_zipPad n f hf p q x xs]; mach_ring
theorem eval_scaleMap (n) (mul1 : MPoly n → MPoly n → MPoly n)
    (hmul : ∀ a b xs, evalM n (mul1 a b) xs = evalM n a xs * evalM n b xs) (a : MPoly n) :
    ∀ (q : List (MPoly n)) (x xs),
      evalM (n+1) (q.map (mul1 a)) (x::xs) = evalM n a xs * evalM (n+1) q (x::xs)
  | [],     x, xs => by simp only [List.map_nil, evalM_emp, mul_zero]
  | b :: q, x, xs => by
      simp only [List.map_cons, evalM_cons]
      rw [hmul a b xs, eval_scaleMap n mul1 hmul a q x xs]; mach_ring
theorem eval_mulList (n) (mul1 add1 : MPoly n → MPoly n → MPoly n) (z : MPoly n)
    (hmul : ∀ a b xs, evalM n (mul1 a b) xs = evalM n a xs * evalM n b xs)
    (hadd : ∀ a b xs, evalM n (add1 a b) xs = evalM n a xs + evalM n b xs)
    (hz : ∀ xs, evalM n z xs = 0) :
    ∀ (p q : List (MPoly n)) (x xs),
      evalM (n+1) (mulList mul1 add1 z p q) (x::xs)
        = evalM (n+1) p (x::xs) * evalM (n+1) q (x::xs)
  | [],     q, x, xs => by simp only [mulList, evalM_emp, zero_mul]
  | a :: p, q, x, xs => by
      simp only [mulList]
      rw [eval_zipPad n add1 hadd, eval_scaleMap n mul1 hmul, evalM_cons, hz,
          eval_mulList n mul1 add1 z hmul hadd hz p q x xs, evalM_cons]
      mach_ring
theorem eval_negMap (n) (neg1 : MPoly n → MPoly n)
    (hneg : ∀ a xs, evalM n (neg1 a) xs = - evalM n a xs) :
    ∀ (p : List (MPoly n)) (x xs),
      evalM (n+1) (p.map neg1) (x::xs) = - evalM (n+1) p (x::xs)
  | [],     x, xs => by simp only [List.map_nil, evalM_emp, neg_zero]
  | a :: p, x, xs => by
      simp only [List.map_cons, evalM_cons]
      rw [hneg a xs, eval_negMap n neg1 hneg p x xs]; mach_ring

theorem eval_addM : ∀ (n) (p q : MPoly n) (xs),
    evalM n (addM n p q) xs = evalM n p xs + evalM n q xs
  | 0,     a, b, xs => by simp only [addM, evalM_z]
  | n + 1, p, q, [] => by simp only [addM, evalM_nil, add_zero]
  | n + 1, p, q, x :: xs => by simp only [addM]; exact eval_zipPad n (addM n) (eval_addM n) p q x xs
theorem eval_negM : ∀ (n) (p : MPoly n) (xs), evalM n (negM n p) xs = - evalM n p xs
  | 0,     a, xs => by simp only [negM, evalM_z]
  | n + 1, p, [] => by simp only [negM, evalM_nil, neg_zero]
  | n + 1, p, x :: xs => by simp only [negM]; exact eval_negMap n (negM n) (eval_negM n) p x xs
theorem eval_mulM : ∀ (n) (p q : MPoly n) (xs),
    evalM n (mulM n p q) xs = evalM n p xs * evalM n q xs
  | 0,     a, b, xs => by simp only [mulM, evalM_z]
  | n + 1, p, q, [] => by simp only [mulM, evalM_nil, mul_zero]
  | n + 1, p, q, x :: xs => by
      simp only [mulM]
      exact eval_mulList n (mulM n) (addM n) (zeroM n) (eval_mulM n) (eval_addM n) (eval_zeroM n) p q x xs

/-! ### Constants and atoms. -/

noncomputable def cst : (n : Nat) → Real → MPoly n
  | 0,     c => c
  | n + 1, c => [cst n c]
/-- The `i`-th variable (0 = outermost) as a depth-`n` polynomial. -/
noncomputable def atomP : (n : Nat) → Nat → MPoly n
  | 0,     _     => (0 : Real)
  | n + 1, 0     => [cst n 0, cst n 1]
  | n + 1, i + 1 => [atomP n i]
theorem eval_cst : ∀ (n) (c : Real) (xs : List Real), xs.length = n → evalM n (cst n c) xs = c
  | 0,     c, xs, _ => rfl
  | n + 1, c, [], h => by simp at h
  | n + 1, c, x :: xs, h => by
      simp only [cst, evalM_cons, evalM_emp, mul_zero, add_zero]
      exact eval_cst n c xs (by simpa using h)
theorem eval_atomP : ∀ (n i) (xs : List Real), xs.length = n → evalM n (atomP n i) xs = xs.getD i 0
  | 0,     i, [],      _ => by simp only [atomP, evalM_z, List.getD_nil]
  | 0,     i, _ :: _,  h => by simp at h
  | n + 1, 0, [],      h => by simp at h
  | n + 1, 0, x :: xs, h => by
      simp only [atomP, evalM_cons, evalM_emp, mul_zero, add_zero]
      rw [eval_cst n 0 xs (by simpa using h), eval_cst n 1 xs (by simpa using h), List.getD_cons_zero]
      mach_ring
  | n + 1, i + 1, [],      h => by simp at h
  | n + 1, i + 1, x :: xs, h => by
      simp only [atomP, evalM_cons, evalM_emp, mul_zero, add_zero]
      rw [eval_atomP n i xs (by simpa using h), List.getD_cons_succ]

/-! ### Equality up to trailing zeros + its soundness. -/

noncomputable def MPEq : (n : Nat) → MPoly n → MPoly n → Prop
  | 0     => fun a b => a = b
  | n + 1 => fun p q => eqPad (fun c => MPEq n c (zeroM n)) (MPEq n) p q
theorem eval_eq_of_eqPad (n) (eqz : MPoly n → Prop) (eq2 : MPoly n → MPoly n → Prop)
    (hz : ∀ a, eqz a → ∀ xs, evalM n a xs = 0)
    (h2 : ∀ a b, eq2 a b → ∀ xs, evalM n a xs = evalM n b xs) :
    ∀ (p q : List (MPoly n)), eqPad eqz eq2 p q → ∀ (x xs),
      evalM (n+1) p (x::xs) = evalM (n+1) q (x::xs)
  | [],     [],     _, x, xs => rfl
  | [],     b :: q, h, x, xs => by
      simp only [eqPad] at h
      simp only [evalM_emp, evalM_cons]
      rw [hz b h.1 xs, ← eval_eq_of_eqPad n eqz eq2 hz h2 [] q h.2 x xs, evalM_emp]; mach_ring
  | a :: p, [],     h, x, xs => by
      simp only [eqPad] at h
      simp only [evalM_emp, evalM_cons]
      rw [hz a h.1 xs, eval_eq_of_eqPad n eqz eq2 hz h2 p [] h.2 x xs, evalM_emp]; mach_ring
  | a :: p, b :: q, h, x, xs => by
      simp only [eqPad] at h
      simp only [evalM_cons]
      rw [h2 a b h.1 xs, eval_eq_of_eqPad n eqz eq2 hz h2 p q h.2 x xs]
theorem eval_eq_of_MPEq : ∀ (n) (p q : MPoly n), MPEq n p q → ∀ (xs), evalM n p xs = evalM n q xs
  | 0,     a, b, h, xs => by simp only [MPEq] at h; simp only [evalM_z]; exact h
  | n + 1, p, q, h, [] => by simp only [evalM_nil]
  | n + 1, p, q, h, x :: xs => by
      simp only [MPEq] at h
      exact eval_eq_of_eqPad n (fun c => MPEq n c (zeroM n)) (MPEq n)
        (fun a ha xs => (eval_eq_of_MPEq n a (zeroM n) ha xs).trans (eval_zeroM n xs))
        (fun a b hab xs => eval_eq_of_MPEq n a b hab xs) p q h x xs

/-! ### Reified syntax + the soundness bridge the tactic rewrites along. -/

inductive MPExpr where
  | atom : Nat → MPExpr
  | lit  : Real → MPExpr
  | add  : MPExpr → MPExpr → MPExpr
  | mul  : MPExpr → MPExpr → MPExpr
  | sub  : MPExpr → MPExpr → MPExpr
  | neg  : MPExpr → MPExpr
noncomputable def mdenote : MPExpr → List Real → Real
  | .atom i,  vars => vars.getD i 0
  | .lit c,   _    => c
  | .add a b, vars => mdenote a vars + mdenote b vars
  | .mul a b, vars => mdenote a vars * mdenote b vars
  | .sub a b, vars => mdenote a vars - mdenote b vars
  | .neg a,   vars => - mdenote a vars
noncomputable def mtoPoly : (d : Nat) → MPExpr → MPoly d
  | d, .atom i  => atomP d i
  | d, .lit c   => cst d c
  | d, .add a b => addM d (mtoPoly d a) (mtoPoly d b)
  | d, .mul a b => mulM d (mtoPoly d a) (mtoPoly d b)
  | d, .sub a b => addM d (mtoPoly d a) (negM d (mtoPoly d b))
  | d, .neg a   => negM d (mtoPoly d a)
theorem mdenote_eq_evalM : ∀ (d) (e : MPExpr) (vars : List Real), vars.length = d →
    mdenote e vars = evalM d (mtoPoly d e) vars
  | d, .atom i,  vars, h => by simp only [mdenote, mtoPoly, eval_atomP d i vars h]
  | d, .lit c,   vars, h => by simp only [mdenote, mtoPoly, eval_cst d c vars h]
  | d, .add a b, vars, h => by
      simp only [mdenote, mtoPoly, eval_addM, mdenote_eq_evalM d a vars h, mdenote_eq_evalM d b vars h]
  | d, .mul a b, vars, h => by
      simp only [mdenote, mtoPoly, eval_mulM, mdenote_eq_evalM d a vars h, mdenote_eq_evalM d b vars h]
  | d, .sub a b, vars, h => by
      simp only [mdenote, mtoPoly, eval_addM, eval_negM, mdenote_eq_evalM d a vars h,
        mdenote_eq_evalM d b vars h, sub_def]
  | d, .neg a,   vars, h => by simp only [mdenote, mtoPoly, eval_negM, mdenote_eq_evalM d a vars h]
/-- The entry lemma the `mach_mpoly` tactic applies: an identity holds if the two
sides reify to `MPEq`-equal normal forms. -/
theorem mach_mpoly_sound (d : Nat) (el er : MPExpr) (vars : List Real)
    (hlen : vars.length = d) (hpeq : MPEq d (mtoPoly d el) (mtoPoly d er)) :
    mdenote el vars = mdenote er vars := by
  rw [mdenote_eq_evalM d el vars hlen, mdenote_eq_evalM d er vars hlen]
  exact eval_eq_of_MPEq d _ _ hpeq vars

end MV
end Real
end MachLib

open Lean Elab Tactic Meta in
/-- Reify a `Real` expression into `MV.MPExpr` over the indexed `atoms`; anything
that is not `+`,`*`,`-`,unary `-`, or one of the atoms becomes a `lit`. -/
partial def MachLib.Real.MV.reifyMPExpr (atoms : Array Expr) (e : Expr) : MetaM Expr := do
  for i in [0:atoms.size] do
    if ← isDefEq e atoms[i]! then return mkApp (mkConst ``MV.MPExpr.atom) (mkNatLit i)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, a) => return mkApp2 (mkConst ``MV.MPExpr.add) (← reifyMPExpr atoms a[4]!) (← reifyMPExpr atoms a[5]!)
  | (``HMul.hMul, a) => return mkApp2 (mkConst ``MV.MPExpr.mul) (← reifyMPExpr atoms a[4]!) (← reifyMPExpr atoms a[5]!)
  | (``HSub.hSub, a) => return mkApp2 (mkConst ``MV.MPExpr.sub) (← reifyMPExpr atoms a[4]!) (← reifyMPExpr atoms a[5]!)
  | (``Neg.neg,  a) => return mkApp (mkConst ``MV.MPExpr.neg) (← reifyMPExpr atoms a[2]!)
  | _ => return mkApp (mkConst ``MV.MPExpr.lit) e

open Lean Elab Tactic Meta in
/-- `mach_mpoly [x, y, …]` — close a multivariate polynomial identity over the
listed atoms via a single nested-`MPoly` normalisation. Scales where the
recursive `mach_poly` cannot: the 8-variable four-square identity closes in
seconds. See the file header. -/
elab "mach_mpoly" "[" xs:term,* "]" : tactic => do
  let atoms := (← xs.getElems.toList.mapM (fun t => elabTerm t.raw none)).toArray
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).eq?
    | throwError "mach_mpoly: goal is not an equality"
  let el ← MachLib.Real.MV.reifyMPExpr atoms lhs
  let er ← MachLib.Real.MV.reifyMPExpr atoms rhs
  let varsE ← mkListLit (mkConst ``MachLib.Real) atoms.toList
  let lemE := mkAppN (mkConst ``MachLib.Real.MV.mach_mpoly_sound) #[mkNatLit atoms.size, el, er, varsE]
  let newGoals ← goal.apply lemE
  setGoals newGoals
  evalTactic (← `(tactic| all_goals (first
    | rfl
    | (simp only [MachLib.Real.MV.mtoPoly, MachLib.Real.MV.mulM, MachLib.Real.MV.mulList,
        MachLib.Real.MV.zipPad, MachLib.Real.MV.addM, MachLib.Real.MV.negM, MachLib.Real.MV.zeroM,
        MachLib.Real.MV.cst, MachLib.Real.MV.atomP, MachLib.Real.MV.MPEq, MachLib.Real.MV.eqPad,
        List.map_cons, List.map_nil]
       <;> (repeat' apply And.intro) <;> (try trivial) <;> mach_ring))))

/-! ### Regression + showcase (these double as the test suite). -/

namespace MachLib.Real.MPolyRing.Tests

example (x y : Real) : (x + y) * (x + y) = x*x + (1+1)*x*y + y*y := by mach_mpoly [x, y]
example (x y : Real) : (x + y) * (x - y) = x*x - y*y := by mach_mpoly [x, y]
example (x y z : Real) : (x + y + z) * (x + y + z)
    = x*x + y*y + z*z + (1+1)*(x*y + y*z + x*z) := by mach_mpoly [x, y, z]
-- Brahmagupta two-square identity
example (a b c d : Real) : (a*a + b*b) * (c*c + d*d)
    = (a*c - b*d)*(a*c - b*d) + (a*d + b*c)*(a*d + b*c) := by mach_mpoly [a, b, c, d]

-- Vec3 cross-product Lagrange identity |a×b|² = (a·a)(b·b) − (a·b)²  (6 vars)
theorem vec3_cross_lagrange (a1 a2 a3 b1 b2 b3 : Real) :
    (a2*b3 - a3*b2)*(a2*b3 - a3*b2) + (a3*b1 - a1*b3)*(a3*b1 - a1*b3)
      + (a1*b2 - a2*b1)*(a1*b2 - a2*b1)
    = (a1*a1 + a2*a2 + a3*a3) * (b1*b1 + b2*b2 + b3*b3)
      - (a1*b1 + a2*b2 + a3*b3)*(a1*b1 + a2*b2 + a3*b3) := by
  mach_mpoly [a1, a2, a3, b1, b2, b3]

-- Euler four-square identity (quaternion norm multiplicativity), 8 vars — the
-- target that the recursive `mach_poly` could not close in 50 minutes.
set_option maxHeartbeats 8000000 in
theorem quat_four_square (a1 a2 a3 a4 b1 b2 b3 b4 : Real) :
    (a1*a1 + a2*a2 + a3*a3 + a4*a4) * (b1*b1 + b2*b2 + b3*b3 + b4*b4)
    = (a1*b1 - a2*b2 - a3*b3 - a4*b4)*(a1*b1 - a2*b2 - a3*b3 - a4*b4)
      + (a1*b2 + a2*b1 + a3*b4 - a4*b3)*(a1*b2 + a2*b1 + a3*b4 - a4*b3)
      + (a1*b3 - a2*b4 + a3*b1 + a4*b2)*(a1*b3 - a2*b4 + a3*b1 + a4*b2)
      + (a1*b4 + a2*b3 - a3*b2 + a4*b1)*(a1*b4 + a2*b3 - a3*b2 + a4*b1) := by
  mach_mpoly [a1, a2, a3, a4, b1, b2, b3, b4]

end MachLib.Real.MPolyRing.Tests
