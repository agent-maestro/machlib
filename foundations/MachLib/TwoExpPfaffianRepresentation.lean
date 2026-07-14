import MachLib.TwoExpPfaffianBridge

/-!
# Pfaffian representations of the lower-level two-exp predicates

`TwoExpPfaffianBridge` turns a represented one-variable Pfaffian zero
predicate into the list-bound hypotheses consumed by the two-exp
Khovanskii-Rolle layer. This file supplies the first representation
combinators:

* if `fx`, `fy`, `gx`, `gy` are represented over the same chain, then
  the Jacobian `fx*gy - fy*gx` is represented by the polynomial
  `pfx*pgy - pfy*pgx`;
* if a separator predicate is represented by a polynomial `psep`, then it
  feeds directly into the separator count bridge.

The point is deliberately modest: no topology, no Mathlib, no hidden
descent. This is the algebraic interface that the concrete two-exp
representation can plug into.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce

/-- A supplied parametrized arc for the global two-exp assembly. The theorem
below does not construct arcs; it consumes an explicit arc decomposition and
proves that represented lower-level counts bound its solution lists. -/
structure RepresentedCurveArc where
  rep : Real
  lo : Real
  hi : Real
  yc : Real → Real
  zeros : List Real

/-- A one-variable function represented by a Pfaffian-chain polynomial on an
open interval. This is the small algebraic closure layer used before building
a full expression language: it records only the polynomial witness and its
evaluation equation on `(a,b)`. -/
structure PfaffianRepOn {n : Nat} (c : PfaffianChain n) (a b : Real)
    (φ : Real → Real) where
  poly : MultiPoly n
  eval_eq : ∀ z, a < z → z < b → (pfaffianChainFn c poly).eval z = φ z

noncomputable def pfaffianRepOn_const {n : Nat} (c : PfaffianChain n) (a b k : Real) :
    PfaffianRepOn c a b (fun _ => k) :=
  { poly := MultiPoly.const k,
    eval_eq := by
      intro z _ _
      rfl }

noncomputable def pfaffianRepOn_varX {n : Nat} (c : PfaffianChain n) (a b : Real) :
    PfaffianRepOn c a b (fun z => z) :=
  { poly := MultiPoly.varX,
    eval_eq := by
      intro z _ _
      rfl }

noncomputable def pfaffianRepOn_varY {n : Nat} (c : PfaffianChain n) (a b : Real)
    (i : Fin n) :
    PfaffianRepOn c a b (fun z => c.evals i z) :=
  { poly := MultiPoly.varY i,
    eval_eq := by
      intro z _ _
      unfold pfaffianChainFn PfaffianFn.eval PfaffianChain.chainValues
      rw [MultiPoly.eval_varY] }

noncomputable def pfaffianRepOn_congr {n : Nat} {c : PfaffianChain n} {a b : Real}
    {φ ψ : Real → Real}
    (hφ : PfaffianRepOn c a b φ) (hψ : ∀ z, φ z = ψ z) :
    PfaffianRepOn c a b ψ :=
  { poly := hφ.poly,
    eval_eq := by
      intro z hza hzb
      rw [hφ.eval_eq z hza hzb, hψ z] }

noncomputable def pfaffianRepOn_add {n : Nat} {c : PfaffianChain n} {a b : Real}
    {φ ψ : Real → Real}
    (hφ : PfaffianRepOn c a b φ) (hψ : PfaffianRepOn c a b ψ) :
    PfaffianRepOn c a b (fun z => φ z + ψ z) :=
  { poly := MultiPoly.add hφ.poly hψ.poly,
    eval_eq := by
      intro z hza hzb
      unfold pfaffianChainFn PfaffianFn.eval
      rw [MultiPoly.eval_add]
      change (pfaffianChainFn c hφ.poly).eval z + (pfaffianChainFn c hψ.poly).eval z =
        φ z + ψ z
      rw [hφ.eval_eq z hza hzb, hψ.eval_eq z hza hzb] }

noncomputable def pfaffianRepOn_sub {n : Nat} {c : PfaffianChain n} {a b : Real}
    {φ ψ : Real → Real}
    (hφ : PfaffianRepOn c a b φ) (hψ : PfaffianRepOn c a b ψ) :
    PfaffianRepOn c a b (fun z => φ z - ψ z) :=
  { poly := MultiPoly.sub hφ.poly hψ.poly,
    eval_eq := by
      intro z hza hzb
      unfold pfaffianChainFn PfaffianFn.eval
      rw [MultiPoly.eval_sub]
      change (pfaffianChainFn c hφ.poly).eval z - (pfaffianChainFn c hψ.poly).eval z =
        φ z - ψ z
      rw [hφ.eval_eq z hza hzb, hψ.eval_eq z hza hzb] }

noncomputable def pfaffianRepOn_mul {n : Nat} {c : PfaffianChain n} {a b : Real}
    {φ ψ : Real → Real}
    (hφ : PfaffianRepOn c a b φ) (hψ : PfaffianRepOn c a b ψ) :
    PfaffianRepOn c a b (fun z => φ z * ψ z) :=
  { poly := MultiPoly.mul hφ.poly hψ.poly,
    eval_eq := by
      intro z hza hzb
      unfold pfaffianChainFn PfaffianFn.eval
      rw [MultiPoly.eval_mul]
      change (pfaffianChainFn c hφ.poly).eval z * (pfaffianChainFn c hψ.poly).eval z =
        φ z * ψ z
      rw [hφ.eval_eq z hza hzb, hψ.eval_eq z hza hzb] }

/-- A tiny one-variable expression language for functions represented over a
fixed Pfaffian chain: constants, the independent variable `x`, chain slots,
and ring operations. This is intentionally just a witness-producing layer,
not a simplifier or normalization engine. -/
inductive PfaffianRepExpr (n : Nat) where
  | const : Real → PfaffianRepExpr n
  | varX : PfaffianRepExpr n
  | varY : Fin n → PfaffianRepExpr n
  | add : PfaffianRepExpr n → PfaffianRepExpr n → PfaffianRepExpr n
  | sub : PfaffianRepExpr n → PfaffianRepExpr n → PfaffianRepExpr n
  | mul : PfaffianRepExpr n → PfaffianRepExpr n → PfaffianRepExpr n

namespace PfaffianRepExpr

/-- Denotation of a representation expression along a concrete chain. -/
noncomputable def denote {n : Nat} (c : PfaffianChain n) :
    PfaffianRepExpr n → Real → Real
  | const k, _ => k
  | varX, z => z
  | varY i, z => c.evals i z
  | add e₁ e₂, z => denote c e₁ z + denote c e₂ z
  | sub e₁ e₂, z => denote c e₁ z - denote c e₂ z
  | mul e₁ e₂, z => denote c e₁ z * denote c e₂ z

/-- Compile a representation expression to an explicit Pfaffian polynomial
witness on `(a,b)`. -/
noncomputable def compile {n : Nat} (c : PfaffianChain n) (a b : Real) :
    (e : PfaffianRepExpr n) → PfaffianRepOn c a b (denote c e)
  | const k => pfaffianRepOn_const c a b k
  | varX => pfaffianRepOn_varX c a b
  | varY i => pfaffianRepOn_varY c a b i
  | add e₁ e₂ => pfaffianRepOn_add (compile c a b e₁) (compile c a b e₂)
  | sub e₁ e₂ => pfaffianRepOn_sub (compile c a b e₁) (compile c a b e₂)
  | mul e₁ e₂ => pfaffianRepOn_mul (compile c a b e₁) (compile c a b e₂)

/-- The explicit polynomial produced by compiling an expression. -/
noncomputable def compilePoly {n : Nat} (c : PfaffianChain n) (a b : Real)
    (e : PfaffianRepExpr n) : MultiPoly n :=
  (compile c a b e).poly

end PfaffianRepExpr

/-- A tiny bivariate two-exponential expression language. This represents
algebra built from `x`, `y`, `exp x`, `exp y`, constants, and ring
operations. It is intentionally syntactic: restriction to an arc decides how
`y` and `exp y` become one-variable Pfaffian-representation expressions. -/
inductive TwoExpBivarExpr where
  | const : Real → TwoExpBivarExpr
  | varX : TwoExpBivarExpr
  | varY : TwoExpBivarExpr
  | expX : TwoExpBivarExpr
  | expY : TwoExpBivarExpr
  | add : TwoExpBivarExpr → TwoExpBivarExpr → TwoExpBivarExpr
  | sub : TwoExpBivarExpr → TwoExpBivarExpr → TwoExpBivarExpr
  | mul : TwoExpBivarExpr → TwoExpBivarExpr → TwoExpBivarExpr

namespace TwoExpBivarExpr

/-- Real bivariate denotation of the two-exp syntax. -/
noncomputable def denote : TwoExpBivarExpr → Real → Real → Real
  | const k, _, _ => k
  | varX, x, _ => x
  | varY, _, y => y
  | expX, x, _ => Real.exp x
  | expY, _, y => Real.exp y
  | add e₁ e₂, x, y => denote e₁ x y + denote e₂ x y
  | sub e₁ e₂, x, y => denote e₁ x y - denote e₂ x y
  | mul e₁ e₂, x, y => denote e₁ x y * denote e₂ x y

/-- Formal partial derivative with respect to `x`. -/
noncomputable def dX : TwoExpBivarExpr → TwoExpBivarExpr
  | const _ => const 0
  | varX => const 1
  | varY => const 0
  | expX => expX
  | expY => const 0
  | add e₁ e₂ => add (dX e₁) (dX e₂)
  | sub e₁ e₂ => sub (dX e₁) (dX e₂)
  | mul e₁ e₂ => add (mul (dX e₁) e₂) (mul e₁ (dX e₂))

/-- Formal partial derivative with respect to `y`. -/
noncomputable def dY : TwoExpBivarExpr → TwoExpBivarExpr
  | const _ => const 0
  | varX => const 0
  | varY => const 1
  | expX => const 0
  | expY => expY
  | add e₁ e₂ => add (dY e₁) (dY e₂)
  | sub e₁ e₂ => sub (dY e₁) (dY e₂)
  | mul e₁ e₂ => add (mul (dY e₁) e₂) (mul e₁ (dY e₂))

/-- Restrict a bivariate two-exp expression to a one-variable arc by supplying
the one-variable representatives of `y`, `exp x`, and `exp y`. The `x` atom
maps to the independent variable. -/
noncomputable def restrict {n : Nat}
    (yExpr expXExpr expYExpr : PfaffianRepExpr n) :
    TwoExpBivarExpr → PfaffianRepExpr n
  | const k => PfaffianRepExpr.const k
  | varX => PfaffianRepExpr.varX
  | varY => yExpr
  | expX => expXExpr
  | expY => expYExpr
  | add e₁ e₂ => PfaffianRepExpr.add (restrict yExpr expXExpr expYExpr e₁)
      (restrict yExpr expXExpr expYExpr e₂)
  | sub e₁ e₂ => PfaffianRepExpr.sub (restrict yExpr expXExpr expYExpr e₁)
      (restrict yExpr expXExpr expYExpr e₂)
  | mul e₁ e₂ => PfaffianRepExpr.mul (restrict yExpr expXExpr expYExpr e₁)
      (restrict yExpr expXExpr expYExpr e₂)

/-- Restrict the formal `x`-partial of a bivariate expression to a
one-variable arc representation. -/
noncomputable def restrictDX {n : Nat}
    (yExpr expXExpr expYExpr : PfaffianRepExpr n) (e : TwoExpBivarExpr) :
    PfaffianRepExpr n :=
  restrict yExpr expXExpr expYExpr (dX e)

/-- Restrict the formal `y`-partial of a bivariate expression to a
one-variable arc representation. -/
noncomputable def restrictDY {n : Nat}
    (yExpr expXExpr expYExpr : PfaffianRepExpr n) (e : TwoExpBivarExpr) :
    PfaffianRepExpr n :=
  restrict yExpr expXExpr expYExpr (dY e)

end TwoExpBivarExpr

/-- The polynomial over a shared chain representing the one-variable
Jacobian expression `fx*gy - fy*gx`, when the four partial-derivative
functions have representatives `pfx`, `pfy`, `pgx`, and `pgy`. -/
noncomputable def jacobianRepPoly {n : Nat}
    (pfx pfy pgx pgy : MultiPoly n) : MultiPoly n :=
  MultiPoly.sub (MultiPoly.mul pfx pgy) (MultiPoly.mul pfy pgx)

/-- **Jacobian representation algebra.** If the four partial-derivative
functions are represented by `pfx`, `pfy`, `pgx`, and `pgy` over the same
chain on `(a,b)`, then `jacobianRepPoly pfx pfy pgx pgy` represents
`fx*gy - fy*gx` there. -/
theorem jacobianRepPoly_eval_eq {n : Nat} (c : PfaffianChain n)
    (pfx pfy pgx pgy : MultiPoly n)
    (fx fy gx gy : Real → Real)
    (a b z : Real) (hza : a < z) (hzb : z < b)
    (hfx : ∀ x, a < x → x < b → (pfaffianChainFn c pfx).eval x = fx x)
    (hfy : ∀ x, a < x → x < b → (pfaffianChainFn c pfy).eval x = fy x)
    (hgx : ∀ x, a < x → x < b → (pfaffianChainFn c pgx).eval x = gx x)
    (hgy : ∀ x, a < x → x < b → (pfaffianChainFn c pgy).eval x = gy x) :
    (pfaffianChainFn c (jacobianRepPoly pfx pfy pgx pgy)).eval z =
      fx z * gy z - fy z * gx z := by
  unfold jacobianRepPoly pfaffianChainFn PfaffianFn.eval
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_mul]
  change (pfaffianChainFn c pfx).eval z * (pfaffianChainFn c pgy).eval z
      - (pfaffianChainFn c pfy).eval z * (pfaffianChainFn c pgx).eval z =
    fx z * gy z - fy z * gx z
  rw [hfx z hza hzb, hgy z hza hzb, hfy z hza hzb, hgx z hza hzb]

noncomputable def pfaffianRepOn_jacobian {n : Nat} {c : PfaffianChain n} {a b : Real}
    {fx fy gx gy : Real → Real}
    (hfx : PfaffianRepOn c a b fx) (hfy : PfaffianRepOn c a b fy)
    (hgx : PfaffianRepOn c a b gx) (hgy : PfaffianRepOn c a b gy) :
    PfaffianRepOn c a b (fun z => fx z * gy z - fy z * gx z) :=
  { poly := jacobianRepPoly hfx.poly hfy.poly hgx.poly hgy.poly,
    eval_eq := by
      intro z hza hzb
      exact jacobianRepPoly_eval_eq c hfx.poly hfy.poly hgx.poly hgy.poly
        fx fy gx gy a b z hza hzb
        hfx.eval_eq hfy.eval_eq hgx.eval_eq hgy.eval_eq }

namespace PfaffianRepExpr

/-- Compile four representation expressions and assemble the represented
Jacobian expression `fx*gy - fy*gx`. -/
noncomputable def compileJacobian {n : Nat} (c : PfaffianChain n) (a b : Real)
    (fx fy gx gy : PfaffianRepExpr n) :
    PfaffianRepOn c a b
      (fun z => denote c fx z * denote c gy z - denote c fy z * denote c gx z) :=
  pfaffianRepOn_jacobian
    (compile c a b fx) (compile c a b fy) (compile c a b gx) (compile c a b gy)

/-- The explicit polynomial produced by compiling a Jacobian from four
expression representatives. -/
noncomputable def compileJacobianPoly {n : Nat} (c : PfaffianChain n) (a b : Real)
    (fx fy gx gy : PfaffianRepExpr n) : MultiPoly n :=
  (compileJacobian c a b fx fy gx gy).poly

end PfaffianRepExpr

namespace TwoExpBivarExpr

/-- The compiled one-variable Pfaffian polynomial for the Jacobian of two
bivariate expressions after restricting their formal partials to an arc. -/
noncomputable def restrictedJacobianPoly {n : Nat} (c : PfaffianChain n) (a b : Real)
    (yExpr expXExpr expYExpr : PfaffianRepExpr n) (F G : TwoExpBivarExpr) :
    MultiPoly n :=
  PfaffianRepExpr.compileJacobianPoly c a b
    (restrictDX yExpr expXExpr expYExpr F)
    (restrictDY yExpr expXExpr expYExpr F)
    (restrictDX yExpr expXExpr expYExpr G)
    (restrictDY yExpr expXExpr expYExpr G)

end TwoExpBivarExpr

private theorem flatMap_arc_pair_zeros_length (s : List RepresentedCurveArc) :
    ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
      (s.flatMap (fun arc => arc.zeros)).length := by
  induction s with
  | nil => rfl
  | cons arc rest ih =>
      simp [ih]

/-- **Represented Jacobian count.** Once the four partial derivatives are
represented over a positive-coherent exp-chain, the lower-level Jacobian
zero-count bound needed by `khovanskii_rolle_count` is produced by the
general Pfaffian bound. -/
theorem pfaffian_jacobian_count_of_represented (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2))
    (pfx pfy pgx pgy : MultiPoly (M + 2))
    (fx fy gx gy : Real → Real)
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c (jacobianRepPoly pfx pfy pgx pgy)).eval z ≠ 0)
    (hfx : ∀ z, a < z → z < b → (pfaffianChainFn c pfx).eval z = fx z)
    (hfy : ∀ z, a < z → z < b → (pfaffianChainFn c pfy).eval z = fy z)
    (hgx : ∀ z, a < z → z < b → (pfaffianChainFn c pgx).eval z = gx z)
    (hgy : ∀ z, a < z → z < b → (pfaffianChainFn c pgy).eval z = gy z) :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧ fx z * gy z - fy z * gx z = 0) →
      zeros_J.length ≤ N :=
  pfaffian_jacobian_count_bridge a b hab M c (jacobianRepPoly pfx pfy pgx pgy)
    hexp hcoh hpos hne fx fy gx gy
    (fun z hza hzb hJ => by
      rw [jacobianRepPoly_eval_eq c pfx pfy pgx pgy fx fy gx gy a b z hza hzb hfx hfy hgx hgy]
      exact hJ)

/-- **Expression-compiled Jacobian count.** Four `PfaffianRepExpr`s compile
to represented partials, hence their Jacobian zero set has a Pfaffian
zero-count bound. This is the DSL-facing version of
`pfaffian_jacobian_count_of_represented`. -/
theorem pfaffian_jacobian_count_of_expr (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2))
    (fx fy gx gy : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c (PfaffianRepExpr.compileJacobianPoly c a b fx fy gx gy)).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧
        PfaffianRepExpr.denote c fx z * PfaffianRepExpr.denote c gy z -
          PfaffianRepExpr.denote c fy z * PfaffianRepExpr.denote c gx z = 0) →
      zeros_J.length ≤ N := by
  exact pfaffian_jacobian_count_of_represented a b hab M c
    (PfaffianRepExpr.compilePoly c a b fx)
    (PfaffianRepExpr.compilePoly c a b fy)
    (PfaffianRepExpr.compilePoly c a b gx)
    (PfaffianRepExpr.compilePoly c a b gy)
    (PfaffianRepExpr.denote c fx) (PfaffianRepExpr.denote c fy)
    (PfaffianRepExpr.denote c gx) (PfaffianRepExpr.denote c gy)
    hexp hcoh hpos hne
    (PfaffianRepExpr.compile c a b fx).eval_eq
    (PfaffianRepExpr.compile c a b fy).eval_eq
    (PfaffianRepExpr.compile c a b gx).eval_eq
    (PfaffianRepExpr.compile c a b gy).eval_eq

/-- Lower-level Pfaffian count for the Jacobian obtained from bivariate
two-exp syntax. This is the public “one level down” bridge:

`F,G syntax → formal partials → arc restriction → compiled Jacobian → zero count`.
-/
theorem pfaffian_jacobian_count_of_bivar_expr (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2))
    (F G : TwoExpBivarExpr)
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c a b yExpr expXExpr expYExpr F G)).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧
        PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z *
          PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z -
        PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z *
          PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z = 0) →
      zeros_J.length ≤ N :=
  pfaffian_jacobian_count_of_expr a b hab M c
    (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F)
    (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F)
    (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G)
    (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G)
    hexp hcoh hpos hne

/-- **Represented separator count.** If the separator predicate implies
vanishing of a represented Pfaffian-chain function, the lower-level critical
count needed by the arc-count layer is produced by the general Pfaffian bound.

This is intentionally predicate-shaped: concrete files can instantiate
`sep` as `fy = 0`, another critical predicate, or a locally stronger
separator condition without changing the global assembly. -/
theorem pfaffian_separator_count_of_represented (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2)) (psep : MultiPoly (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c psep).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, a < z → z < b → sep z → (pfaffianChainFn c psep).eval z = 0) :
    ∃ Ncrit : Nat, ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, a < s ∧ s < b ∧ sep s) → ss.length ≤ Ncrit :=
  pfaffian_separator_count_bridge a b hab M c psep hexp hcoh hpos hne sep hsep_zero

/-- **Expression-compiled separator count.** If an expression represents a
separator/critical predicate by implication (`sep z → e z = 0`), the general
Pfaffian bridge supplies the finite separator bound used by the arc-count
layer. -/
theorem pfaffian_separator_count_of_expr (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2))
    (e : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c (PfaffianRepExpr.compilePoly c a b e)).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, a < z → z < b → sep z → PfaffianRepExpr.denote c e z = 0) :
    ∃ Ncrit : Nat, ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, a < s ∧ s < b ∧ sep s) → ss.length ≤ Ncrit :=
  pfaffian_separator_count_of_represented a b hab M c
    (PfaffianRepExpr.compilePoly c a b e)
    hexp hcoh hpos hne sep
    (fun z hza hzb hsep => by
      unfold PfaffianRepExpr.compilePoly
      rw [(PfaffianRepExpr.compile c a b e).eval_eq z hza hzb]
      exact hsep_zero z hza hzb hsep)

/-- Separator count for vertical critical points obtained from bivariate
syntax. The separator expression is the restricted formal `y`-partial of
`F`, matching the usual arc-count separator `Fᵧ = 0`. -/
theorem pfaffian_fy_separator_count_of_bivar_expr (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2))
    (F : TwoExpBivarExpr)
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c a b
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, a < z → z < b → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0) :
    ∃ Ncrit : Nat, ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, a < s ∧ s < b ∧ sep s) → ss.length ≤ Ncrit :=
  pfaffian_separator_count_of_expr a b hab M c
    (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F)
    hexp hcoh hpos hne sep hsep_zero

/-- **Reusable curve-count interface.** If the four partial-derivative
functions are represented over one positive-coherent exp-chain along the
parameter interval, then the general Pfaffian zero-count theorem supplies the
lower-level Jacobian bound required by `khovanskii_rolle_count_curve`.

This is the reusable bridge for two-exp arc counts:

`represented partials → represented Jacobian → Pfaffian lower count → KR curve count`.
-/
theorem khovanskii_rolle_count_curve_of_represented_jacobian
    (f g : Real → Real → Real) (fx fy gx gy yc : Real → Real)
    (a b : Real) (hab : a < b)
    (hf2 : ∀ z : Real, a < z → z < b → HasDerivAt2 f (fx z) (fy z) z (yc z))
    (hg2 : ∀ z : Real, a < z → z < b → HasDerivAt2 g (gx z) (gy z) z (yc z))
    (hfy : ∀ z : Real, a < z → z < b → fy z ≠ 0)
    (hid : ∀ s : Real, f s (yc s) = 0)
    (M : Nat) (c : PfaffianChain (M + 2))
    (pfx pfy pgx pgy : MultiPoly (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c (jacobianRepPoly pfx pfy pgx pgy)).eval z ≠ 0)
    (hfx : ∀ z, a < z → z < b → (pfaffianChainFn c pfx).eval z = fx z)
    (hfy_rep : ∀ z, a < z → z < b → (pfaffianChainFn c pfy).eval z = fy z)
    (hgx : ∀ z, a < z → z < b → (pfaffianChainFn c pgx).eval z = gx z)
    (hgy : ∀ z, a < z → z < b → (pfaffianChainFn c pgy).eval z = gy z) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ g z (yc z) = 0) →
      zeros_g.length ≤ N + 1 := by
  obtain ⟨N, hJ⟩ := pfaffian_jacobian_count_of_represented a b hab M c
    pfx pfy pgx pgy fx fy gx gy hexp hcoh hpos hne hfx hfy_rep hgx hgy
  exact ⟨N, khovanskii_rolle_count_curve f g fx fy gx gy yc a b hab
    hf2 hg2 hfy hid N hJ⟩

/-- **Reusable curve-count interface from expression-compiled partials.**
This is the DSL-facing version of
`khovanskii_rolle_count_curve_of_represented_jacobian`: the four partial
derivatives are supplied as `PfaffianRepExpr`s and compiled before the
Jacobian count is fed into Khovanskii-Rolle. -/
theorem khovanskii_rolle_count_curve_of_expr_jacobian
    (f g : Real → Real → Real) (yc : Real → Real)
    (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2))
    (efx efy egx egy : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c (PfaffianRepExpr.compileJacobianPoly c a b efx efy egx egy)).eval z ≠ 0)
    (hf2 : ∀ z : Real, a < z → z < b →
      HasDerivAt2 f (PfaffianRepExpr.denote c efx z) (PfaffianRepExpr.denote c efy z) z (yc z))
    (hg2 : ∀ z : Real, a < z → z < b →
      HasDerivAt2 g (PfaffianRepExpr.denote c egx z) (PfaffianRepExpr.denote c egy z) z (yc z))
    (hfy : ∀ z : Real, a < z → z < b → PfaffianRepExpr.denote c efy z ≠ 0)
    (hid : ∀ s : Real, f s (yc s) = 0) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ g z (yc z) = 0) →
      zeros_g.length ≤ N + 1 := by
  obtain ⟨N, hJ⟩ := pfaffian_jacobian_count_of_expr a b hab M c
    efx efy egx egy hexp hcoh hpos hne
  exact ⟨N, khovanskii_rolle_count_curve f g
    (PfaffianRepExpr.denote c efx) (PfaffianRepExpr.denote c efy)
    (PfaffianRepExpr.denote c egx) (PfaffianRepExpr.denote c egy)
    yc a b hab hf2 hg2 hfy hid N hJ⟩

/-- **Curve-count interface from bivariate two-exp syntax.** Given two
syntactic expressions `F` and `G`, this theorem forms their formal partials,
restricts those partials to the supplied one-variable arc representation,
compiles the four restricted partials, and then invokes the generic
Khovanskii-Rolle/Pfaffian curve-count bridge.

The semantic derivative assumptions remain explicit: this syntax layer
selects and represents the partials, while the caller still proves that those
formal partials are the correct derivatives for the concrete denotations on
the interval. -/
theorem khovanskii_rolle_count_curve_of_bivar_expr_jacobian
    (F G : TwoExpBivarExpr) (yc : Real → Real)
    (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c a b yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hf2 : ∀ z : Real, a < z → z < b →
      HasDerivAt2 (TwoExpBivarExpr.denote F)
        (PfaffianRepExpr.denote c
          (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z)
        (PfaffianRepExpr.denote c
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z)
        z (yc z))
    (hg2 : ∀ z : Real, a < z → z < b →
      HasDerivAt2 (TwoExpBivarExpr.denote G)
        (PfaffianRepExpr.denote c
          (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z)
        (PfaffianRepExpr.denote c
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z)
        z (yc z))
    (hfy : ∀ z : Real, a < z → z < b →
      PfaffianRepExpr.denote c
        (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z ≠ 0)
    (hid : ∀ s : Real, TwoExpBivarExpr.denote F s (yc s) = 0) :
    ∃ N : Nat, ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ TwoExpBivarExpr.denote G z (yc z) = 0) →
      zeros_g.length ≤ N + 1 :=
  khovanskii_rolle_count_curve_of_expr_jacobian
    (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G) yc
    a b hab M c
    (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F)
    (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F)
    (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G)
    (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G)
    hexp hcoh hpos hne hf2 hg2 hfy hid

/-- **Global assembly with Pfaffian-produced separators.** This is the
global counterpart to `khovanskii_rolle_count_curve_of_represented_jacobian`.
The arc/intersection lists are still supplied explicitly, as in
`khovanskii_rolle_full`, but the separator/critical count `Ncrit` is no
longer a free input: it is produced by a represented Pfaffian-chain
separator predicate.

The separator predicate fed to `ChainSep` is interval-shaped,
`a < x ∧ x < b ∧ sep x`, so the Pfaffian separator bridge can be used
directly. -/
theorem khovanskii_rolle_full_of_represented_separator (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2)) (psep : MultiPoly (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c psep).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, a < z → z < b → sep z → (pfaffianChainFn c psep).eval z = 0)
    (N : Nat) (hd : Real × List Real) (s : List (Real × List Real))
    (hchain : ChainSep (fun x => a < x ∧ x < b ∧ sep x) hd.1 (s.map (fun arc => arc.1)))
    (harc : ∀ arc ∈ (hd :: s), arc.2.length ≤ N + 1) :
    ∃ Ncrit : Nat,
      ((hd :: s).flatMap (fun arc => arc.2)).length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨Ncrit, hNcrit_interval⟩ := pfaffian_separator_count_of_represented a b hab M c psep
    hexp hcoh hpos hne sep hsep_zero
  refine ⟨Ncrit, ?_⟩
  exact khovanskii_rolle_full (fun x => a < x ∧ x < b ∧ sep x) Ncrit N
    (fun ss hnd hss => hNcrit_interval ss hnd (fun x hx => hss x hx))
    hd s hchain harc

/-- **Global assembly from already-produced lower counts.** This small
wrapper packages the final shape used by concrete systems once a separator
count and a uniform per-arc count have both been produced by lower-level
machinery. -/
theorem khovanskii_rolle_full_of_lower_counts (sep : Real → Prop)
    (Ncrit N : Nat)
    (hNcrit : ∀ ss : List Real, ss.Nodup → (∀ x ∈ ss, sep x) → ss.length ≤ Ncrit)
    (hd : Real × List Real) (s : List (Real × List Real))
    (hchain : ChainSep sep hd.1 (s.map (fun arc => arc.1)))
    (harc : ∀ arc ∈ (hd :: s), arc.2.length ≤ N + 1) :
    ((hd :: s).flatMap (fun arc => arc.2)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full sep Ncrit N hNcrit hd s hchain harc

/-- **Global assembly with represented Jacobian and represented separators.**
This is the main reusable global theorem for the current bridge layer.

Inputs still include an explicit arc decomposition (`hd :: s`) and
`ChainSep` for adjacent arc representatives. What is no longer supplied
freely is the lower-level count data:

* `N` comes from the represented Jacobian via the general Pfaffian count;
* `Ncrit` comes from the represented separator predicate;
* each arc's `zeros.length ≤ N+1` is produced by
  `khovanskii_rolle_count_curve`.

The result is the same global shape as `khovanskii_rolle_full`, but with both
lower-level counts assembled from Pfaffian representations. -/
theorem khovanskii_rolle_full_of_represented_arc_data
    (f g : Real → Real → Real) (fx fy gx gy : Real → Real)
    (A B : Real) (hAB : A < B)
    (Mj : Nat) (cj : PfaffianChain (Mj + 2))
    (pfx pfy pgx pgy : MultiPoly (Mj + 2))
    (hexpJ : IsExpChain cj)
    (hcohJ : cj.IsCoherentOn A B)
    (hposJ : ∀ z, A < z → z < B → ∀ i : Fin (Mj + 2), 0 < cj.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn cj (jacobianRepPoly pfx pfy pgx pgy)).eval z ≠ 0)
    (hfx : ∀ z, A < z → z < B → (pfaffianChainFn cj pfx).eval z = fx z)
    (hfy_rep : ∀ z, A < z → z < B → (pfaffianChainFn cj pfy).eval z = fy z)
    (hgx : ∀ z, A < z → z < B → (pfaffianChainFn cj pgx).eval z = gx z)
    (hgy : ∀ z, A < z → z < B → (pfaffianChainFn cj pgy).eval z = gy z)
    (Ms : Nat) (cs : PfaffianChain (Ms + 2)) (psep : MultiPoly (Ms + 2))
    (hexpS : IsExpChain cs)
    (hcohS : cs.IsCoherentOn A B)
    (hposS : ∀ z, A < z → z < B → ∀ i : Fin (Ms + 2), 0 < cs.evals i z)
    (hneS : ∃ z, A < z ∧ z < B ∧ (pfaffianChainFn cs psep).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z → (pfaffianChainFn cs psep).eval z = 0)
    (hd : RepresentedCurveArc) (s : List RepresentedCurveArc)
    (hchain : ChainSep (fun x => A < x ∧ x < B ∧ sep x) hd.rep (s.map (fun arc => arc.rep)))
    (hinside : ∀ arc ∈ (hd :: s), A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : ∀ arc ∈ (hd :: s), arc.zeros.Nodup)
    (hf2 : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 f (fx z) (fy z) z (arc.yc z))
    (hg2 : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 g (gx z) (gy z) z (arc.yc z))
    (hfy_nz : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi → fy z ≠ 0)
    (hid : ∀ arc ∈ (hd :: s), ∀ t, f t (arc.yc t) = 0)
    (hzeros : ∀ arc ∈ (hd :: s), ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ g z (arc.yc z) = 0) :
    ∃ Ncrit N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨N, hJ⟩ := pfaffian_jacobian_count_of_represented A B hAB Mj cj
    pfx pfy pgx pgy fx fy gx gy hexpJ hcohJ hposJ hneJ hfx hfy_rep hgx hgy
  obtain ⟨Ncrit, hNcrit_interval⟩ := pfaffian_separator_count_of_represented A B hAB Ms cs psep
    hexpS hcohS hposS hneS sep hsep_zero
  have harcRich : ∀ arc ∈ (hd :: s), arc.zeros.length ≤ N + 1 := by
    intro arc harcmem
    have hcurve := khovanskii_rolle_count_curve f g fx fy gx gy arc.yc arc.lo arc.hi
      (hinside arc harcmem).2.1
      (hf2 arc harcmem) (hg2 arc harcmem) (hfy_nz arc harcmem) (hid arc harcmem)
      N
      (fun zeros_J hnd hJlocal =>
        hJ zeros_J hnd (fun z hzmem => by
          obtain ⟨hzlo, hzhi, hJac⟩ := hJlocal z hzmem
          have hA : A < z := lt_trans_ax (hinside arc harcmem).1 hzlo
          have hB : z < B := lt_trans_ax hzhi (hinside arc harcmem).2.2
          exact ⟨hA, hB, hJac⟩))
    exact hcurve arc.zeros (hzeros_nd arc harcmem) (hzeros arc harcmem)
  refine ⟨Ncrit, N, ?_⟩
  have hchainPairs : ChainSep (fun x => A < x ∧ x < B ∧ sep x) (hd.rep, hd.zeros).1
      ((s.map (fun arc => (arc.rep, arc.zeros))).map (fun pair => pair.1)) := by
    simpa [List.map_map] using hchain
  have hglobal := khovanskii_rolle_full (fun x => A < x ∧ x < B ∧ sep x) Ncrit N
    (fun ss hnd hss => hNcrit_interval ss hnd (fun x hx => hss x hx))
    (hd.rep, hd.zeros) (s.map (fun arc => (arc.rep, arc.zeros))) hchainPairs ?_
  · have htail :
        ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
          (s.flatMap (fun arc => arc.zeros)).length :=
        flatMap_arc_pair_zeros_length s
    simpa [htail] using hglobal
  · intro pair hpairmem
    cases hpairmem with
    | head =>
        exact harcRich hd (List.mem_cons_self _ _)
    | tail _ hp =>
        obtain ⟨arc, harcmem, hpair⟩ := List.mem_map.mp hp
        cases hpair
        exact harcRich arc (List.mem_cons_of_mem _ harcmem)

/-- **Global assembly from bivariate two-exp syntax.** This is the
syntax-facing analogue of `khovanskii_rolle_full_of_represented_arc_data`.

Both lower-level counts are produced from the same bivariate expression data:

* the per-arc Jacobian count comes from the restricted formal partials of
  `F` and `G`;
* the separator/critical count comes from the restricted formal `Fᵧ`.

The theorem still consumes an explicit arc decomposition and semantic
derivative hypotheses. Those are the remaining analytic/topological inputs;
the lower counting witnesses are no longer free parameters. -/
theorem khovanskii_rolle_full_of_bivar_expr_arc_data
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (hd : RepresentedCurveArc) (s : List RepresentedCurveArc)
    (hchain : ChainSep (fun x => A < x ∧ x < B ∧ sep x) hd.rep (s.map (fun arc => arc.rep)))
    (hinside : ∀ arc ∈ (hd :: s), A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : ∀ arc ∈ (hd :: s), arc.zeros.Nodup)
    (hf2 : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 (TwoExpBivarExpr.denote F)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z)
        z (arc.yc z))
    (hg2 : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 (TwoExpBivarExpr.denote G)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z)
        z (arc.yc z))
    (hfy_nz : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z ≠ 0)
    (hid : ∀ arc ∈ (hd :: s), ∀ t, TwoExpBivarExpr.denote F t (arc.yc t) = 0)
    (hzeros : ∀ arc ∈ (hd :: s), ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ TwoExpBivarExpr.denote G z (arc.yc z) = 0) :
    ∃ Ncrit N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨N, hJ⟩ := pfaffian_jacobian_count_of_bivar_expr A B hAB M c F G
    yExpr expXExpr expYExpr hexp hcoh hpos hneJ
  obtain ⟨Ncrit, hNcrit_interval⟩ :=
    pfaffian_fy_separator_count_of_bivar_expr A B hAB M c F yExpr expXExpr expYExpr
      hexp hcoh hpos hneS sep hsep_zero
  have harcRich : ∀ arc ∈ (hd :: s), arc.zeros.length ≤ N + 1 := by
    intro arc harcmem
    have hcurve := khovanskii_rolle_count_curve
      (TwoExpBivarExpr.denote F) (TwoExpBivarExpr.denote G)
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G))
      (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G))
      arc.yc arc.lo arc.hi
      (hinside arc harcmem).2.1
      (hf2 arc harcmem) (hg2 arc harcmem) (hfy_nz arc harcmem) (hid arc harcmem)
      N
      (fun zeros_J hnd hJlocal =>
        hJ zeros_J hnd (fun z hzmem => by
          obtain ⟨hzlo, hzhi, hJac⟩ := hJlocal z hzmem
          have hA : A < z := lt_trans_ax (hinside arc harcmem).1 hzlo
          have hB : z < B := lt_trans_ax hzhi (hinside arc harcmem).2.2
          exact ⟨hA, hB, hJac⟩))
    exact hcurve arc.zeros (hzeros_nd arc harcmem) (hzeros arc harcmem)
  refine ⟨Ncrit, N, ?_⟩
  have hchainPairs : ChainSep (fun x => A < x ∧ x < B ∧ sep x) (hd.rep, hd.zeros).1
      ((s.map (fun arc => (arc.rep, arc.zeros))).map (fun pair => pair.1)) := by
    simpa [List.map_map] using hchain
  have hglobal := khovanskii_rolle_full (fun x => A < x ∧ x < B ∧ sep x) Ncrit N
    (fun ss hnd hss => hNcrit_interval ss hnd (fun x hx => hss x hx))
    (hd.rep, hd.zeros) (s.map (fun arc => (arc.rep, arc.zeros))) hchainPairs ?_
  · have htail :
        ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
          (s.flatMap (fun arc => arc.zeros)).length :=
        flatMap_arc_pair_zeros_length s
    simpa [htail] using hglobal
  · intro pair hpairmem
    cases hpairmem with
    | head =>
        exact harcRich hd (List.mem_cons_self _ _)
    | tail _ hp =>
        obtain ⟨arc, harcmem, hpair⟩ := List.mem_map.mp hp
        cases hpair
        exact harcRich arc (List.mem_cons_of_mem _ harcmem)

/-- **Global assembly with represented Jacobian and an externally-produced
separator count.** This variant is useful when the separator predicate is
trivial or impossible (for example `fᵧ = 1`, so `fᵧ = 0` has no points) and
there is no reason to route it through a Pfaffian representation.

The Jacobian lower count and every per-arc count are still produced from the
represented Jacobian. -/
theorem khovanskii_rolle_full_of_represented_arc_data_and_separator_count
    (f g : Real → Real → Real) (fx fy gx gy : Real → Real)
    (A B : Real) (hAB : A < B)
    (Mj : Nat) (cj : PfaffianChain (Mj + 2))
    (pfx pfy pgx pgy : MultiPoly (Mj + 2))
    (hexpJ : IsExpChain cj)
    (hcohJ : cj.IsCoherentOn A B)
    (hposJ : ∀ z, A < z → z < B → ∀ i : Fin (Mj + 2), 0 < cj.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn cj (jacobianRepPoly pfx pfy pgx pgy)).eval z ≠ 0)
    (hfx : ∀ z, A < z → z < B → (pfaffianChainFn cj pfx).eval z = fx z)
    (hfy_rep : ∀ z, A < z → z < B → (pfaffianChainFn cj pfy).eval z = fy z)
    (hgx : ∀ z, A < z → z < B → (pfaffianChainFn cj pgx).eval z = gx z)
    (hgy : ∀ z, A < z → z < B → (pfaffianChainFn cj pgy).eval z = gy z)
    (sep : Real → Prop) (Ncrit : Nat)
    (hNcrit : ∀ ss : List Real, ss.Nodup → (∀ x ∈ ss, sep x) → ss.length ≤ Ncrit)
    (hd : RepresentedCurveArc) (s : List RepresentedCurveArc)
    (hchain : ChainSep sep hd.rep (s.map (fun arc => arc.rep)))
    (hinside : ∀ arc ∈ (hd :: s), A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : ∀ arc ∈ (hd :: s), arc.zeros.Nodup)
    (hf2 : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 f (fx z) (fy z) z (arc.yc z))
    (hg2 : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 g (gx z) (gy z) z (arc.yc z))
    (hfy_nz : ∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi → fy z ≠ 0)
    (hid : ∀ arc ∈ (hd :: s), ∀ t, f t (arc.yc t) = 0)
    (hzeros : ∀ arc ∈ (hd :: s), ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ g z (arc.yc z) = 0) :
    ∃ N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨N, hJ⟩ := pfaffian_jacobian_count_of_represented A B hAB Mj cj
    pfx pfy pgx pgy fx fy gx gy hexpJ hcohJ hposJ hneJ hfx hfy_rep hgx hgy
  have harcRich : ∀ arc ∈ (hd :: s), arc.zeros.length ≤ N + 1 := by
    intro arc harcmem
    have hcurve := khovanskii_rolle_count_curve f g fx fy gx gy arc.yc arc.lo arc.hi
      (hinside arc harcmem).2.1
      (hf2 arc harcmem) (hg2 arc harcmem) (hfy_nz arc harcmem) (hid arc harcmem)
      N
      (fun zeros_J hnd hJlocal =>
        hJ zeros_J hnd (fun z hzmem => by
          obtain ⟨hzlo, hzhi, hJac⟩ := hJlocal z hzmem
          have hA : A < z := lt_trans_ax (hinside arc harcmem).1 hzlo
          have hB : z < B := lt_trans_ax hzhi (hinside arc harcmem).2.2
          exact ⟨hA, hB, hJac⟩))
    exact hcurve arc.zeros (hzeros_nd arc harcmem) (hzeros arc harcmem)
  refine ⟨N, ?_⟩
  have hchainPairs : ChainSep sep (hd.rep, hd.zeros).1
      ((s.map (fun arc => (arc.rep, arc.zeros))).map (fun pair => pair.1)) := by
    simpa [List.map_map] using hchain
  have hglobal := khovanskii_rolle_full sep Ncrit N hNcrit
    (hd.rep, hd.zeros) (s.map (fun arc => (arc.rep, arc.zeros))) hchainPairs ?_
  · have htail :
        ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun pair => pair.2)).length =
          (s.flatMap (fun arc => arc.zeros)).length :=
        flatMap_arc_pair_zeros_length s
    simpa [htail] using hglobal
  · intro pair hpairmem
    cases hpairmem with
    | head =>
        exact harcRich hd (List.mem_cons_self _ _)
    | tail _ hp =>
        obtain ⟨arc, harcmem, hpair⟩ := List.mem_map.mp hp
        cases hpair
        exact harcRich arc (List.mem_cons_of_mem _ harcmem)

/-- **Single represented-arc assembly with represented Jacobian and an
externally-produced separator count.** This is the one-arc specialization of
`khovanskii_rolle_full_of_represented_arc_data_and_separator_count`.

It is useful for concrete examples whose zero set is already presented by a
single parametrized interval: the Jacobian count is still produced from the
Pfaffian representation, but there is no nontrivial arc-separation witness to
carry. -/
theorem khovanskii_rolle_single_represented_arc_data_and_separator_count
    (f g : Real → Real → Real) (fx fy gx gy : Real → Real)
    (A B : Real) (hAB : A < B)
    (Mj : Nat) (cj : PfaffianChain (Mj + 2))
    (pfx pfy pgx pgy : MultiPoly (Mj + 2))
    (hexpJ : IsExpChain cj)
    (hcohJ : cj.IsCoherentOn A B)
    (hposJ : ∀ z, A < z → z < B → ∀ i : Fin (Mj + 2), 0 < cj.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn cj (jacobianRepPoly pfx pfy pgx pgy)).eval z ≠ 0)
    (hfx : ∀ z, A < z → z < B → (pfaffianChainFn cj pfx).eval z = fx z)
    (hfy_rep : ∀ z, A < z → z < B → (pfaffianChainFn cj pfy).eval z = fy z)
    (hgx : ∀ z, A < z → z < B → (pfaffianChainFn cj pgx).eval z = gx z)
    (hgy : ∀ z, A < z → z < B → (pfaffianChainFn cj pgy).eval z = gy z)
    (sep : Real → Prop) (Ncrit : Nat)
    (hNcrit : ∀ ss : List Real, ss.Nodup → (∀ x ∈ ss, sep x) → ss.length ≤ Ncrit)
    (arc : RepresentedCurveArc)
    (hinside : A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : arc.zeros.Nodup)
    (hf2 : ∀ z, arc.lo < z → z < arc.hi → HasDerivAt2 f (fx z) (fy z) z (arc.yc z))
    (hg2 : ∀ z, arc.lo < z → z < arc.hi → HasDerivAt2 g (gx z) (gy z) z (arc.yc z))
    (hfy_nz : ∀ z, arc.lo < z → z < arc.hi → fy z ≠ 0)
    (hid : ∀ t, f t (arc.yc t) = 0)
    (hzeros : ∀ z ∈ arc.zeros, arc.lo < z ∧ z < arc.hi ∧ g z (arc.yc z) = 0) :
    ∃ N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨N, hN⟩ := khovanskii_rolle_full_of_represented_arc_data_and_separator_count
    f g fx fy gx gy A B hAB Mj cj pfx pfy pgx pgy
    hexpJ hcohJ hposJ hneJ hfx hfy_rep hgx hgy
    sep Ncrit hNcrit arc [] trivial
    (fun a ha => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hinside)
    (fun a ha => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hzeros_nd)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hf2 z hzlo hzhi)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hg2 z hzlo hzhi)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hfy_nz z hzlo hzhi)
    (fun a ha t => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hid t)
    (fun a ha z hzmem => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hzeros z hzmem)
  refine ⟨N, ?_⟩
  simpa using hN

/-- **Single represented-arc assembly from bivariate syntax.** This is the
one-arc specialization of `khovanskii_rolle_full_of_bivar_expr_arc_data`.
It keeps the same syntax-routed lower counts while avoiding any nontrivial
arc-separation data. -/
theorem khovanskii_rolle_single_bivar_expr_arc_data
    (F G : TwoExpBivarExpr)
    (A B : Real) (hAB : A < B)
    (M : Nat) (c : PfaffianChain (M + 2))
    (yExpr expXExpr expYExpr : PfaffianRepExpr (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn A B)
    (hpos : ∀ z, A < z → z < B → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hneJ : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (TwoExpBivarExpr.restrictedJacobianPoly c A B yExpr expXExpr expYExpr F G)).eval z ≠ 0)
    (hneS : ∃ z, A < z ∧ z < B ∧
      (pfaffianChainFn c
        (PfaffianRepExpr.compilePoly c A B
          (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F))).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, A < z → z < B → sep z →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z = 0)
    (arc : RepresentedCurveArc)
    (hinside : A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : arc.zeros.Nodup)
    (hf2 : ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 (TwoExpBivarExpr.denote F)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr F) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z)
        z (arc.yc z))
    (hg2 : ∀ z, arc.lo < z → z < arc.hi →
      HasDerivAt2 (TwoExpBivarExpr.denote G)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDX yExpr expXExpr expYExpr G) z)
        (PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr G) z)
        z (arc.yc z))
    (hfy_nz : ∀ z, arc.lo < z → z < arc.hi →
      PfaffianRepExpr.denote c (TwoExpBivarExpr.restrictDY yExpr expXExpr expYExpr F) z ≠ 0)
    (hid : ∀ t, TwoExpBivarExpr.denote F t (arc.yc t) = 0)
    (hzeros : ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ TwoExpBivarExpr.denote G z (arc.yc z) = 0) :
    ∃ Ncrit N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) := by
  obtain ⟨Ncrit, N, hN⟩ := khovanskii_rolle_full_of_bivar_expr_arc_data
    F G A B hAB M c yExpr expXExpr expYExpr hexp hcoh hpos hneJ hneS
    sep hsep_zero arc [] trivial
    (fun a ha => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hinside)
    (fun a ha => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hzeros_nd)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hf2 z hzlo hzhi)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hg2 z hzlo hzhi)
    (fun a ha z hzlo hzhi => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hfy_nz z hzlo hzhi)
    (fun a ha t => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hid t)
    (fun a ha z hzmem => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hzeros z hzmem)
  refine ⟨Ncrit, N, ?_⟩
  simpa using hN

end TwoExp
end MultiVarMod
end MachLib
