import MachLib.Basic
import MachLib.Ring

/-
MachLib.PolyRing — a reflective univariate polynomial normaliser ("ring v2", slice 1).

`mach_ring` v1.5 does AC + distribution but cannot COLLECT like monomials after
distribution (e.g. `−4·s² + s² = −3·s²`), so it fails on cubic+ identities such as
the smoothstep certificate `1 − s²(3−2s) = (1−s)²(1+2s)`. That blocks a whole band
of obligations across MGE (smoothstep / ease) and the eml-stdlib corpus.

A polynomial is reflected as a coefficient LIST `[c₀, c₁, c₂, …]` denoting
`c₀ + c₁·x + c₂·x² + …` (Horner). The ring operations build coefficient lists
directly, and each carries a SOUNDNESS theorem `eval (op p q) x = op (eval …)`.
The collection `mach_ring` can't do is done structurally by `add`/`mul`.

This slice = the verified algebra. The reification tactic (Expr → UPoly) is the
next slice; until then the algebra is used semi-manually.
-/

namespace MachLib
namespace Real

/-- A univariate polynomial as its coefficient list, low degree first:
`[c₀, c₁, c₂]` denotes `c₀ + c₁·x + c₂·x²`. -/
abbrev UPoly := List Real

namespace UPoly

/-- Horner evaluation: `eval [c₀,c₁,…] x = c₀ + x·(c₁ + x·(…))`. -/
noncomputable def eval : UPoly → Real → Real
  | [],      _ => 0
  | c :: cs, x => c + x * eval cs x

@[simp] theorem eval_nil (x : Real) : eval [] x = 0 := rfl
@[simp] theorem eval_cons (c : Real) (cs : UPoly) (x : Real) :
    eval (c :: cs) x = c + x * eval cs x := rfl

/-- Coefficient-wise addition with implicit zero-padding of the shorter list. -/
noncomputable def add : UPoly → UPoly → UPoly
  | [],      q       => q
  | a :: p,  []      => a :: p
  | a :: p,  b :: q  => (a + b) :: add p q

/-- `eval (add p q) x = eval p x + eval q x`. -/
theorem eval_add : ∀ (p q : UPoly) (x : Real),
    eval (add p q) x = eval p x + eval q x
  | [],      q,      x => by simp only [add, eval_nil, zero_add]
  | a :: p,  [],     x => by simp only [add, eval_nil, add_zero]
  | a :: p,  b :: q, x => by
    simp only [add, eval_cons, eval_add p q x]
    -- (a+b) + x·(P + Q) = (a + x·P) + (b + x·Q): distribute + additive AC.
    mach_ring

/-- Scalar multiply: `scale c p` denotes `c · (eval p)`. -/
noncomputable def scale (c : Real) : UPoly → UPoly
  | []      => []
  | a :: p  => (c * a) :: scale c p

theorem eval_scale : ∀ (c : Real) (p : UPoly) (x : Real),
    eval (scale c p) x = c * eval p x
  | c, [],     x => by simp only [scale, eval_nil, mul_zero]
  | c, a :: p, x => by
    simp only [scale, eval_cons, eval_scale c p x]
    -- c·a + x·(c·P) = c·(a + x·P)
    mach_ring

/-- Multiply by `x` (shift up one degree): prepend a zero coefficient. -/
noncomputable def shiftX (p : UPoly) : UPoly := (0 : Real) :: p

theorem eval_shiftX (p : UPoly) (x : Real) :
    eval (shiftX p) x = x * eval p x := by
  simp only [shiftX, eval_cons, zero_add]

/-- Polynomial product (Horner recursion): `(a + x·p)·q = a·q + x·(p·q)`. -/
noncomputable def mul : UPoly → UPoly → UPoly
  | [],      _ => []
  | a :: p,  q => add (scale a q) (shiftX (mul p q))

theorem eval_mul : ∀ (p q : UPoly) (x : Real),
    eval (mul p q) x = eval p x * eval q x
  | [],      q, x => by simp only [mul, eval_nil, zero_mul]
  | a :: p,  q, x => by
    simp only [mul, eval_add, eval_scale, eval_shiftX, eval_mul p q x, eval_cons]
    -- a·Q + x·(P·Q) = (a + x·P)·Q
    mach_ring

/-- Negation: negate every coefficient. -/
noncomputable def neg : UPoly → UPoly
  | []      => []
  | a :: p  => (-a) :: neg p

theorem eval_neg : ∀ (p : UPoly) (x : Real),
    eval (neg p) x = - eval p x
  | [],     x => by simp only [neg, eval_nil, neg_zero]
  | a :: p, x => by
    simp only [neg, eval_cons, eval_neg p x]
    -- -a + x·(-P) = -(a + x·P)
    mach_ring

/-- The constant polynomial. -/
noncomputable def C (c : Real) : UPoly := [c]

@[simp] theorem eval_C (c x : Real) : eval (C c) x = c := by
  simp only [C, eval_cons, eval_nil, mul_zero, add_zero]

/-- The variable `x`. -/
noncomputable def X : UPoly := [0, 1]

@[simp] theorem eval_X (x : Real) : eval X x = x := by
  simp only [X, eval_cons, eval_nil, mul_zero, add_zero, mul_one_ax, zero_add]

/-- **Polynomial equality up to trailing zeros.** Two coefficient lists denote the
same polynomial when their common prefix matches coefficient-for-coefficient and
any extra tail coefficients are zero. Crucially this compares coefficients
DIRECTLY (`a = b`), so each obligation is a single matchable equality — never a
difference `a + (-b) = 0`, which would force `mach_ring` to COLLECT constants
(e.g. `1 + 1 + (-1 + -1) = 0`), the one thing it cannot do. This is what lets the
reification tactic handle identities that cancel to a LOWER degree
(`(s+1) − s = 1`), where the two sides' coefficient lists have different lengths. -/
def PEq : UPoly → UPoly → Prop
  | [],     []     => True
  | [],     b :: q => b = 0 ∧ PEq [] q
  | a :: p, []     => a = 0 ∧ PEq p []
  | a :: p, b :: q => a = b ∧ PEq p q

/-- `PEq p q` ⇒ the two polynomials evaluate equally everywhere. The bridge the
reification tactic applies after reducing a `Real` identity to a `PEq` of
coefficient lists. -/
theorem eval_eq_of_PEq : ∀ (p q : UPoly), PEq p q → ∀ (x : Real), eval p x = eval q x
  | [],     [],     _, _ => rfl
  | [],     b :: q, h, x => by
      simp only [PEq] at h
      have hq : eval q x = 0 := (eval_eq_of_PEq [] q h.2 x).symm.trans (eval_nil x)
      simp only [eval_nil, eval_cons, h.1, hq, mul_zero, add_zero]
  | a :: p, [],     h, x => by
      simp only [PEq] at h
      have hp : eval p x = 0 := (eval_eq_of_PEq p [] h.2 x).trans (eval_nil x)
      simp only [eval_nil, eval_cons, h.1, hp, mul_zero, add_zero]
  | a :: p, b :: q, h, x => by
      simp only [PEq] at h
      simp only [eval_cons, h.1, eval_eq_of_PEq p q h.2 x]

end UPoly

open UPoly in
/-- **The smoothstep certificate** `1 − s²(3−2s) = (1−s)²(1+2s)`, proven THROUGH
the UPoly reflection engine — this is the cubic collection that `mach_ring` v1.5
cannot do. Reflect both sides to coefficient lists, evaluate (soundness +
`mach_ring`), and reduce the identity to per-coefficient CONSTANT equalities
(`mach_ring` handles those). This single identity unblocks every smoothstep
UPPER bound (`s²(3−2s) ≤ 1`) across MGE and the eml-stdlib corpus. -/
theorem one_sub_smoothstep_factored (s : Real) :
    (1 : Real) - s * s * ((1 + 1 + 1) - (1 + 1) * s)
      = (1 - s) * (1 - s) * (1 + (1 + 1) * s) := by
  have hL : eval (add (C 1) (neg (mul (mul X X)
              (add (C (1 + 1 + 1)) (neg (mul (C (1 + 1)) X)))))) s
            = (1 : Real) - s * s * ((1 + 1 + 1) - (1 + 1) * s) := by
    simp only [eval_add, eval_neg, eval_mul, eval_C, eval_X]; mach_ring
  have hR : eval (mul (mul (add (C 1) (neg X)) (add (C 1) (neg X)))
              (add (C 1) (mul (C (1 + 1)) X))) s
            = (1 - s) * (1 - s) * (1 + (1 + 1) * s) := by
    simp only [eval_add, eval_neg, eval_mul, eval_C, eval_X]; mach_ring
  have hP : (add (C 1) (neg (mul (mul X X)
              (add (C (1 + 1 + 1)) (neg (mul (C (1 + 1)) X))))))
          = (mul (mul (add (C 1) (neg X)) (add (C 1) (neg X)))
              (add (C 1) (mul (C (1 + 1)) X))) := by
    simp only [mul, add, scale, neg, shiftX, C, X, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> mach_ring
  rw [← hL, ← hR, hP]

/-! ### Reflection layer (slice 2): reified ring syntax → UPoly.

`PExpr` is a reified univariate ring expression over a single atom. `denote`
maps it back to `Real` (mirroring the original expression structure, so a
reification tactic's correctness step is `rfl`); `toPoly` lowers it to a `UPoly`;
`denote_eq_eval` is the soundness bridge between them. A reification tactic (next
brick) will turn a goal `lhs = rhs` into `eval (toPoly ea) x = eval (toPoly eb) x`
and close it by reducing to the coefficient lists. -/

inductive PExpr where
  | atom : PExpr
  | lit  : Real → PExpr
  | add  : PExpr → PExpr → PExpr
  | mul  : PExpr → PExpr → PExpr
  | sub  : PExpr → PExpr → PExpr
  | neg  : PExpr → PExpr

namespace PExpr

/-- Interpret a reified expression back to `Real` at atom value `x`. (Noncomputable
because `Real`'s operations are.) -/
noncomputable def denote (x : Real) : PExpr → Real
  | atom    => x
  | lit c   => c
  | add a b => denote x a + denote x b
  | mul a b => denote x a * denote x b
  | sub a b => denote x a - denote x b
  | neg a   => - denote x a

/-- Lower a reified expression to its coefficient-list polynomial. -/
noncomputable def toPoly : PExpr → UPoly
  | atom    => UPoly.X
  | lit c   => UPoly.C c
  | add a b => UPoly.add (toPoly a) (toPoly b)
  | mul a b => UPoly.mul (toPoly a) (toPoly b)
  | sub a b => UPoly.add (toPoly a) (UPoly.neg (toPoly b))
  | neg a   => UPoly.neg (toPoly a)

/-- **Soundness of the reflection.** Evaluating the reified expression equals
evaluating its lowered polynomial — the bridge a reification tactic rewrites
along to reduce a `Real` identity to a polynomial-coefficient comparison. -/
theorem denote_eq_eval (e : PExpr) (x : Real) :
    denote x e = UPoly.eval (toPoly e) x := by
  induction e with
  | atom => simp only [denote, toPoly, UPoly.eval_X]
  | lit c => simp only [denote, toPoly, UPoly.eval_C]
  | add a b iha ihb => simp only [denote, toPoly, UPoly.eval_add, iha, ihb]
  | mul a b iha ihb => simp only [denote, toPoly, UPoly.eval_mul, iha, ihb]
  | sub a b iha ihb =>
    simp only [denote, toPoly, UPoly.eval_add, UPoly.eval_neg, iha, ihb, sub_def]
  | neg a iha => simp only [denote, toPoly, UPoly.eval_neg, iha]

end PExpr
end Real
end MachLib

