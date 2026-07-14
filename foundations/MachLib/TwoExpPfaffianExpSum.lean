import MachLib.TwoExpPfaffianDescent
import MachLib.MultiVarTwoExpSum
import MachLib.IterExpTopIdentity
import MachLib.AnalyticFiniteZerosReal

/-!
# Concrete Pfaffian representation for the exp-sum two-exp example

This specializes the generic lower-level representation bridge to the
validated example

    f(x,y) = x + y - c
    g(x,y) = exp x + exp y - d

on the line `y = c - x`. The Jacobian restricted to the line is

    J(x) = exp(c-x) - exp x.

We represent the two exponential coordinates by a positive exp-type
Pfaffian chain:

    y₀ = exp x,       y₀' =  1*y₀
    y₁ = exp(c - x), y₁' = -1*y₁

and then instantiate `pfaffian_jacobian_count_of_represented`.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.IterExpTopIdentity

private theorem flatMap_expSum_arc_pair_zeros_length (s : List RepresentedCurveArc) :
    ((s.map (fun arc => (arc.rep, arc.zeros))).flatMap (fun arc => arc.2)).length =
      (s.flatMap (fun arc => arc.zeros)).length := by
  induction s with
  | nil => rfl
  | cons arc rest ih =>
      simp [ih]

/-- Pointwise chain-value helper for `expSumLineChain`. -/
noncomputable def expSumLineEval (c : Real) (i : Fin 2) (x : Real) : Real :=
  if i.val = 0 then Real.exp x else Real.exp (c - x)

/-- The two-slot chain along the line `y = c - x`: slot `0` is `exp x`,
slot `1` is `exp(c-x)`. -/
noncomputable def expSumLineChain (c : Real) : PfaffianChain 2 :=
  { evals := fun i x => expSumLineEval c i x,
    relations := fun i =>
      if i.val = 0 then
        MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)
      else
        MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY i) }

private theorem fin2_zero_or_one (i : Fin 2) : i.val = 0 ∨ i.val = 1 := by
  have hlt := i.isLt
  omega

/-- The line chain is exp-type: each relation is `Gᵢ * yᵢ`, with constant
multiplier `1` for `exp x` and `-1` for `exp(c-x)`. -/
theorem expSumLineChain_isExp (c : Real) : IsExpChain (expSumLineChain c) := by
  intro i
  by_cases hi : i.val = 0
  · refine ⟨⟨MultiPoly.const 1, degreeY_const i 1, ?_⟩, ?_⟩
    · show (if i.val = 0 then MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)
        else MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY i))
        = MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)
      rw [if_pos hi]
    · intro j hij
      show MultiPoly.degreeY j
        (if i.val = 0 then MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)
          else MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY i)) = 0
      rw [if_pos hi, degreeY_mul' j (MultiPoly.const 1) (MultiPoly.varY i), degreeY_const]
      have hji : j ≠ i := fun h => (Nat.ne_of_lt hij) (congrArg Fin.val h).symm
      show 0 + (if j = i then 1 else 0) = 0
      rw [if_neg hji]
  · refine ⟨⟨MultiPoly.const (-1), degreeY_const i (-1), ?_⟩, ?_⟩
    · show (if i.val = 0 then MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)
        else MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY i))
        = MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY i)
      rw [if_neg hi]
    · intro j hij
      show MultiPoly.degreeY j
        (if i.val = 0 then MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)
          else MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY i)) = 0
      rw [if_neg hi, degreeY_mul' j (MultiPoly.const (-1)) (MultiPoly.varY i), degreeY_const]
      have hji : j ≠ i := fun h => (Nat.ne_of_lt hij) (congrArg Fin.val h).symm
      show 0 + (if j = i then 1 else 0) = 0
      rw [if_neg hji]

/-- The line chain is coherent on every interval. -/
theorem expSumLineChain_coh (c a b : Real) : (expSumLineChain c).IsCoherentOn a b := by
  intro x _ _ i
  rcases fin2_zero_or_one i with hi0 | hi1
  · show HasDerivAt (fun x => expSumLineEval c i x)
      (MultiPoly.eval
        (if i.val = 0 then MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)
          else MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY i))
        x ((expSumLineChain c).chainValues x)) x
    rw [if_pos hi0, MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY]
    change HasDerivAt (fun x => expSumLineEval c i x) (1 * expSumLineEval c i x) x
    unfold expSumLineEval
    rw [if_pos hi0, one_mul_thm]
    have hfun : (fun x => if i.val = 0 then Real.exp x else Real.exp (c - x)) = Real.exp := by
      funext t
      rw [if_pos hi0]
    rw [hfun]
    exact HasDerivAt_exp x
  · have hi0_ne : ¬ i.val = 0 := by omega
    show HasDerivAt (fun x => expSumLineEval c i x)
      (MultiPoly.eval
        (if i.val = 0 then MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)
          else MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.varY i))
        x ((expSumLineChain c).chainValues x)) x
    have hderiv : HasDerivAt (fun x => Real.exp (c - x)) (Real.exp (c - x) * (0 - 1)) x :=
      hasDerivAt_exp_comp (fun x => c - x) (0 - 1) x
        (HasDerivAt_sub (fun _ => c) (fun x => x) 0 1 x (HasDerivAt_const c x) (HasDerivAt_id x))
    rw [if_neg hi0_ne, MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY]
    change HasDerivAt (fun x => expSumLineEval c i x) ((-1) * expSumLineEval c i x) x
    unfold expSumLineEval
    rw [if_neg hi0_ne]
    rw [show (-1 : Real) * Real.exp (c - x) = Real.exp (c - x) * (0 - 1) from by mach_ring]
    have hfun : (fun x => if i.val = 0 then Real.exp x else Real.exp (c - x)) =
        (fun x => Real.exp (c - x)) := by
      funext t
      rw [if_neg hi0_ne]
    rw [hfun]
    exact hderiv

/-- The line chain is positive on every interval. -/
theorem expSumLineChain_pos (c a b : Real) :
    ∀ z, a < z → z < b → ∀ i : Fin 2, 0 < (expSumLineChain c).evals i z := by
  intro z _ _ i
  rcases fin2_zero_or_one i with hi0 | hi1
  · change 0 < expSumLineEval c i z
    unfold expSumLineEval
    rw [if_pos hi0]
    exact exp_pos z
  · have hi0_ne : ¬ i.val = 0 := by omega
    change 0 < expSumLineEval c i z
    unfold expSumLineEval
    rw [if_neg hi0_ne]
    exact exp_pos (c - z)

/-- The representative for the constant `1`. -/
noncomputable def expSumOnePoly : MultiPoly 2 := MultiPoly.const 1

/-- The representative for `exp x` in `expSumLineChain`. -/
noncomputable def expSumExpXPoly : MultiPoly 2 := MultiPoly.varY (⟨0, by omega⟩ : Fin 2)

/-- The representative for `exp(c-x)` in `expSumLineChain`. -/
noncomputable def expSumExpCXPoly : MultiPoly 2 := MultiPoly.varY (⟨1, by omega⟩ : Fin 2)

theorem expSumOne_rep (c a b z : Real) (_hza : a < z) (_hzb : z < b) :
    (pfaffianChainFn (expSumLineChain c) expSumOnePoly).eval z = 1 := by
  rfl

theorem expSumExpX_rep (c a b z : Real) (_hza : a < z) (_hzb : z < b) :
    (pfaffianChainFn (expSumLineChain c) expSumExpXPoly).eval z = Real.exp z := by
  unfold expSumExpXPoly pfaffianChainFn PfaffianFn.eval PfaffianChain.chainValues expSumLineChain
  rw [MultiPoly.eval_varY]
  change expSumLineEval c (⟨0, by omega⟩ : Fin 2) z = Real.exp z
  unfold expSumLineEval
  rw [if_pos rfl]

theorem expSumExpCX_rep (c a b z : Real) (_hza : a < z) (_hzb : z < b) :
    (pfaffianChainFn (expSumLineChain c) expSumExpCXPoly).eval z = Real.exp (c - z) := by
  unfold expSumExpCXPoly pfaffianChainFn PfaffianFn.eval PfaffianChain.chainValues expSumLineChain
  rw [MultiPoly.eval_varY]
  change expSumLineEval c (⟨1, by omega⟩ : Fin 2) z = Real.exp (c - z)
  unfold expSumLineEval
  rw [if_neg (by decide)]

noncomputable def expSumOne_repOn (c a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b (fun _ => 1) :=
  pfaffianRepOn_const (expSumLineChain c) a b 1

noncomputable def expSumExpX_repOn (c a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b Real.exp :=
  pfaffianRepOn_congr
    (pfaffianRepOn_varY (expSumLineChain c) a b (⟨0, by omega⟩ : Fin 2))
    (fun z => by
      change expSumLineEval c (⟨0, by omega⟩ : Fin 2) z = Real.exp z
      unfold expSumLineEval
      rw [if_pos rfl])

noncomputable def expSumExpCX_repOn (c a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b (fun z => Real.exp (c - z)) :=
  pfaffianRepOn_congr
    (pfaffianRepOn_varY (expSumLineChain c) a b (⟨1, by omega⟩ : Fin 2))
    (fun z => by
      change expSumLineEval c (⟨1, by omega⟩ : Fin 2) z = Real.exp (c - z)
      unfold expSumLineEval
      rw [if_neg (by decide)])

noncomputable def expSumRestricted_repOn (c d a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b
      (fun z => Real.exp z + Real.exp (c - z) - d) := by
  exact pfaffianRepOn_sub
    (pfaffianRepOn_add (expSumExpX_repOn c a b) (expSumExpCX_repOn c a b))
    (pfaffianRepOn_const (expSumLineChain c) a b d)

/-- DSL expression for the restricted exp-sum function
`exp x + exp(c-x) - d` along `y = c-x`. The two exponentials are represented
by the two chain slots. -/
noncomputable def expSumRestricted_expr (d : Real) : PfaffianRepExpr 2 :=
  PfaffianRepExpr.sub
    (PfaffianRepExpr.add
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)))
    (PfaffianRepExpr.const d)

/-- The bivariate expression `x + y - c`. -/
noncomputable def expSumF_bivar (c : Real) : TwoExpBivarExpr :=
  TwoExpBivarExpr.sub
    (TwoExpBivarExpr.add TwoExpBivarExpr.varX TwoExpBivarExpr.varY)
    (TwoExpBivarExpr.const c)

/-- The bivariate expression `exp x + exp y - d`. -/
noncomputable def expSumG_bivar (d : Real) : TwoExpBivarExpr :=
  TwoExpBivarExpr.sub
    (TwoExpBivarExpr.add TwoExpBivarExpr.expX TwoExpBivarExpr.expY)
    (TwoExpBivarExpr.const d)

/-- The line expression `y = c - x`, used when restricting bivariate
two-exp expressions to the exp-sum line. -/
noncomputable def expSumLineY_expr (c : Real) : PfaffianRepExpr 2 :=
  PfaffianRepExpr.sub (PfaffianRepExpr.const c) PfaffianRepExpr.varX

/-- Restrict a bivariate two-exp expression to the exp-sum line `y = c-x`,
with chain slot 0 representing `exp x` and slot 1 representing `exp(c-x)`. -/
noncomputable def expSumRestrict (c : Real) (e : TwoExpBivarExpr) : PfaffianRepExpr 2 :=
  TwoExpBivarExpr.restrict (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    e

theorem expSumG_restrict_eq (c d : Real) :
    expSumRestrict c (expSumG_bivar d) =
    expSumRestricted_expr d := by
  rfl

theorem expSumF_restrict_denote_zero (c : Real) :
    ∀ z, PfaffianRepExpr.denote (expSumLineChain c)
      (expSumRestrict c (expSumF_bivar c)) z = 0 := by
  intro z
  unfold expSumRestrict expSumF_bivar expSumLineY_expr TwoExpBivarExpr.restrict PfaffianRepExpr.denote
  show z + (c - z) - c = 0
  mach_ring

theorem expSumF_bivar_line_zero (c : Real) :
    ∀ z, TwoExpBivarExpr.denote (expSumF_bivar c) z (c - z) = 0 := by
  intro z
  unfold expSumF_bivar TwoExpBivarExpr.denote
  show z + (c - z) - c = 0
  mach_ring

theorem expSumRestricted_expr_denote (c d : Real) :
    ∀ z, PfaffianRepExpr.denote (expSumLineChain c) (expSumRestricted_expr d) z =
      Real.exp z + Real.exp (c - z) - d := by
  intro z
  unfold expSumRestricted_expr PfaffianRepExpr.denote
  change expSumLineEval c (⟨0, by omega⟩ : Fin 2) z +
      expSumLineEval c (⟨1, by omega⟩ : Fin 2) z - d =
    Real.exp z + Real.exp (c - z) - d
  unfold expSumLineEval
  rw [if_pos rfl, if_neg (by decide)]

noncomputable def expSumRestricted_expr_repOn (c d a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b
      (fun z => Real.exp z + Real.exp (c - z) - d) :=
  pfaffianRepOn_congr
    (PfaffianRepExpr.compile (expSumLineChain c) a b (expSumRestricted_expr d))
    (expSumRestricted_expr_denote c d)

noncomputable def expSumG_bivar_restrict_repOn (c d a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b
      (fun z => Real.exp z + Real.exp (c - z) - d) :=
  pfaffianRepOn_congr
    (PfaffianRepExpr.compile (expSumLineChain c) a b
      (expSumRestrict c (expSumG_bivar d)))
    (fun z => by
      rw [expSumG_restrict_eq c d]
      exact expSumRestricted_expr_denote c d z)

/-- The four partial expressions obtained by formally differentiating the
bivariate expressions and then restricting to the exp-sum line. -/
noncomputable def expSumFx_from_bivar (c : Real) : PfaffianRepExpr 2 :=
  expSumRestrict c (TwoExpBivarExpr.dX (expSumF_bivar c))
noncomputable def expSumFy_from_bivar (c : Real) : PfaffianRepExpr 2 :=
  expSumRestrict c (TwoExpBivarExpr.dY (expSumF_bivar c))
noncomputable def expSumGx_from_bivar (c d : Real) : PfaffianRepExpr 2 :=
  expSumRestrict c (TwoExpBivarExpr.dX (expSumG_bivar d))
noncomputable def expSumGy_from_bivar (c d : Real) : PfaffianRepExpr 2 :=
  expSumRestrict c (TwoExpBivarExpr.dY (expSumG_bivar d))

theorem expSumFx_from_bivar_denote (c : Real) :
    ∀ z, PfaffianRepExpr.denote (expSumLineChain c) (expSumFx_from_bivar c) z = 1 := by
  intro z
  unfold expSumFx_from_bivar expSumRestrict expSumF_bivar
  unfold TwoExpBivarExpr.dX TwoExpBivarExpr.restrict PfaffianRepExpr.denote
  show (1 : Real) + 0 - 0 = 1
  mach_ring

theorem expSumFy_from_bivar_denote (c : Real) :
    ∀ z, PfaffianRepExpr.denote (expSumLineChain c) (expSumFy_from_bivar c) z = 1 := by
  intro z
  unfold expSumFy_from_bivar expSumRestrict expSumF_bivar
  unfold TwoExpBivarExpr.dY TwoExpBivarExpr.restrict PfaffianRepExpr.denote
  show (0 : Real) + 1 - 0 = 1
  mach_ring

theorem expSumGx_from_bivar_denote (c d : Real) :
    ∀ z, PfaffianRepExpr.denote (expSumLineChain c) (expSumGx_from_bivar c d) z =
      Real.exp z := by
  intro z
  unfold expSumGx_from_bivar expSumRestrict expSumG_bivar
  unfold TwoExpBivarExpr.dX TwoExpBivarExpr.restrict PfaffianRepExpr.denote
  change expSumLineEval c (⟨0, by omega⟩ : Fin 2) z +
      0 - 0 = Real.exp z
  unfold expSumLineEval
  rw [if_pos rfl]
  mach_ring

theorem expSumGy_from_bivar_denote (c d : Real) :
    ∀ z, PfaffianRepExpr.denote (expSumLineChain c) (expSumGy_from_bivar c d) z =
      Real.exp (c - z) := by
  intro z
  unfold expSumGy_from_bivar expSumRestrict expSumG_bivar
  unfold TwoExpBivarExpr.dY TwoExpBivarExpr.restrict PfaffianRepExpr.denote
  change 0 + expSumLineEval c (⟨1, by omega⟩ : Fin 2) z -
      0 = Real.exp (c - z)
  unfold expSumLineEval
  rw [if_neg (by decide)]
  mach_ring

noncomputable def expSumJacobian_from_bivar_derivs_repOn (c d a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b
      (fun z => Real.exp (c - z) - Real.exp z) :=
  pfaffianRepOn_congr
    (PfaffianRepExpr.compileJacobian (expSumLineChain c) a b
      (expSumFx_from_bivar c) (expSumFy_from_bivar c)
      (expSumGx_from_bivar c d) (expSumGy_from_bivar c d))
    (fun z => by
      rw [expSumFx_from_bivar_denote c z, expSumFy_from_bivar_denote c z,
        expSumGx_from_bivar_denote c d z, expSumGy_from_bivar_denote c d z]
      show (1 : Real) * Real.exp (c - z) - 1 * Real.exp z =
        Real.exp (c - z) - Real.exp z
      mach_ring)

/-- Expression representatives for the four partials
`fₓ = 1`, `fᵧ = 1`, `gₓ = exp x`, `gᵧ = exp(c-x)` along the exp-sum line. -/
noncomputable def expSumFx_expr : PfaffianRepExpr 2 := PfaffianRepExpr.const 1
noncomputable def expSumFy_expr : PfaffianRepExpr 2 := PfaffianRepExpr.const 1
noncomputable def expSumGx_expr : PfaffianRepExpr 2 :=
  PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2)
noncomputable def expSumGy_expr : PfaffianRepExpr 2 :=
  PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)

/-- The Pfaffian polynomial representing the restricted exp-sum Jacobian
`exp(c-x) - exp x`. -/
noncomputable def expSumJacobianPoly : MultiPoly 2 :=
  jacobianRepPoly expSumOnePoly expSumOnePoly expSumExpXPoly expSumExpCXPoly

theorem expSumJacobian_expr_poly_eq (c a b : Real) :
    PfaffianRepExpr.compileJacobianPoly (expSumLineChain c) a b
      expSumFx_expr expSumFy_expr expSumGx_expr expSumGy_expr =
    expSumJacobianPoly := by
  rfl

noncomputable def expSumJacobian_expr_repOn (c a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b
      (fun z => Real.exp (c - z) - Real.exp z) :=
  pfaffianRepOn_congr
    (PfaffianRepExpr.compileJacobian (expSumLineChain c) a b
      expSumFx_expr expSumFy_expr expSumGx_expr expSumGy_expr)
    (fun z => by
      unfold expSumFx_expr expSumFy_expr expSumGx_expr expSumGy_expr
      unfold PfaffianRepExpr.denote
      change (1 : Real) * expSumLineEval c (⟨1, by omega⟩ : Fin 2) z -
          1 * expSumLineEval c (⟨0, by omega⟩ : Fin 2) z =
        Real.exp (c - z) - Real.exp z
      unfold expSumLineEval
      rw [if_neg (by decide), if_pos rfl]
      mach_ring)

noncomputable def expSumJacobian_repOn (c a b : Real) :
    PfaffianRepOn (expSumLineChain c) a b
      (fun z => Real.exp (c - z) - Real.exp z) :=
  pfaffianRepOn_congr
    (pfaffianRepOn_jacobian
      (expSumOne_repOn c a b) (expSumOne_repOn c a b)
      (expSumExpX_repOn c a b) (expSumExpCX_repOn c a b))
    (fun z => by
      show (1 : Real) * Real.exp (c - z) - 1 * Real.exp z =
        Real.exp (c - z) - Real.exp z
      mach_ring)

/-- The restricted exp-sum Jacobian is represented by `expSumJacobianPoly`. -/
theorem expSumJacobian_rep (c a b z : Real) (hza : a < z) (hzb : z < b) :
    (pfaffianChainFn (expSumLineChain c) expSumJacobianPoly).eval z =
      Real.exp (c - z) - Real.exp z := by
  unfold expSumJacobianPoly
  have h := jacobianRepPoly_eval_eq (expSumLineChain c)
    expSumOnePoly expSumOnePoly expSumExpXPoly expSumExpCXPoly
    (fun _ => 1) (fun _ => 1) Real.exp (fun z => Real.exp (c - z))
    a b z hza hzb
    (expSumOne_rep c a b) (expSumOne_rep c a b)
    (expSumExpX_rep c a b) (expSumExpCX_rep c a b)
  rw [show (1 : Real) * Real.exp (c - z) - 1 * Real.exp z = Real.exp (c - z) - Real.exp z from by
    mach_ring] at h
  exact h

theorem expSumJacobian_expr_rep (c a b z : Real) (hza : a < z) (hzb : z < b) :
    (pfaffianChainFn (expSumLineChain c)
      (PfaffianRepExpr.compileJacobianPoly (expSumLineChain c) a b
        expSumFx_expr expSumFy_expr expSumGx_expr expSumGy_expr)).eval z =
      Real.exp (c - z) - Real.exp z := by
  rw [expSumJacobian_expr_poly_eq c a b]
  exact expSumJacobian_rep c a b z hza hzb

/-- **Concrete lower-level Pfaffian count for the exp-sum Jacobian.** This
is the first specialization of the representation bridge: any nodup list of
zeros of `exp(c-x)-exp x` on `(a,b)` is bounded by some Pfaffian Khovanskii
bound, provided the represented Jacobian is not identically zero on the
interval. -/
theorem expSum_jacobian_pfaffian_count (c a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn (expSumLineChain c) expSumJacobianPoly).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧ Real.exp (c - z) - Real.exp z = 0) →
      zeros_J.length ≤ N :=
by
  obtain ⟨N, hN⟩ := pfaffian_jacobian_count_of_represented a b hab 0 (expSumLineChain c)
    expSumOnePoly expSumOnePoly expSumExpXPoly expSumExpCXPoly
    (fun _ => 1) (fun _ => 1) Real.exp (fun z => Real.exp (c - z))
    (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
    hne
    (expSumOne_rep c a b) (expSumOne_rep c a b)
    (expSumExpX_rep c a b) (expSumExpCX_rep c a b)
  refine ⟨N, ?_⟩
  intro zeros_J hnd hz
  exact hN zeros_J hnd (fun z hzmem => by
    obtain ⟨hza, hzb, hz0⟩ := hz z hzmem
    refine ⟨hza, hzb, ?_⟩
    rw [show (1 : Real) * Real.exp (c - z) - 1 * Real.exp z = Real.exp (c - z) - Real.exp z from by
      mach_ring]
    exact hz0)

/-- The restricted exp-sum Jacobian is not identically zero on any nonempty
interval. Pick two distinct interior points; strict antitonicity makes the
Jacobian injective, so both cannot be zeros. -/
theorem expSumJacobian_nonzero_somewhere (c a b : Real) (hab : a < b) :
    ∃ z, a < z ∧ z < b ∧ Real.exp (c - z) - Real.exp z ≠ 0 := by
  obtain ⟨m, ham, hmb⟩ := MachLib.exists_between a b hab
  obtain ⟨l, hal, hlm⟩ := MachLib.exists_between a m ham
  by_cases hl : Real.exp (c - l) - Real.exp l = 0
  · by_cases hm : Real.exp (c - m) - Real.exp m = 0
    · exfalso
      have hinj := injective_of_antitone (fun z => Real.exp (c - z) - Real.exp z) (sumJac_antitone c)
      have hsame : (fun z => Real.exp (c - z) - Real.exp z) l =
          (fun z => Real.exp (c - z) - Real.exp z) m := by
        change Real.exp (c - l) - Real.exp l = Real.exp (c - m) - Real.exp m
        rw [hl, hm]
      have hlm_eq : l = m := hinj l m hsame
      exact (ne_of_lt hlm) hlm_eq
    · exact ⟨m, ham, hmb, hm⟩
  · exact ⟨l, hal, lt_trans_ax hlm hmb, hl⟩

/-- The represented restricted exp-sum Jacobian is not identically zero on any
nonempty interval. -/
theorem expSumJacobianPoly_nonzero_somewhere (c a b : Real) (hab : a < b) :
    ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn (expSumLineChain c) expSumJacobianPoly).eval z ≠ 0 := by
  obtain ⟨z, hza, hzb, hz_ne⟩ := expSumJacobian_nonzero_somewhere c a b hab
  refine ⟨z, hza, hzb, ?_⟩
  rw [expSumJacobian_rep c a b z hza hzb]
  exact hz_ne

theorem expSumJacobianExpr_nonzero_somewhere (c a b : Real) (hab : a < b) :
    ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn (expSumLineChain c)
        (PfaffianRepExpr.compileJacobianPoly (expSumLineChain c) a b
          expSumFx_expr expSumFy_expr expSumGx_expr expSumGy_expr)).eval z ≠ 0 := by
  obtain ⟨z, hza, hzb, hz_ne⟩ := expSumJacobianPoly_nonzero_somewhere c a b hab
  refine ⟨z, hza, hzb, ?_⟩
  rw [expSumJacobian_expr_poly_eq c a b]
  exact hz_ne

theorem expSumJacobianBivar_nonzero_somewhere (c d a b : Real) (hab : a < b) :
    ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn (expSumLineChain c)
        (TwoExpBivarExpr.restrictedJacobianPoly (expSumLineChain c) a b
          (expSumLineY_expr c)
          (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
          (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
          (expSumF_bivar c) (expSumG_bivar d))).eval z ≠ 0 := by
  obtain ⟨z, hza, hzb, hz_ne⟩ := expSumJacobian_nonzero_somewhere c a b hab
  refine ⟨z, hza, hzb, ?_⟩
  have hrep := (PfaffianRepExpr.compileJacobian (expSumLineChain c) a b
    (TwoExpBivarExpr.restrictDX (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) (expSumF_bivar c))
    (TwoExpBivarExpr.restrictDY (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) (expSumF_bivar c))
    (TwoExpBivarExpr.restrictDX (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) (expSumG_bivar d))
    (TwoExpBivarExpr.restrictDY (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) (expSumG_bivar d))).eval_eq z hza hzb
  unfold TwoExpBivarExpr.restrictedJacobianPoly PfaffianRepExpr.compileJacobianPoly
  rw [hrep]
  simpa [expSumRestrict, expSumF_bivar, expSumG_bivar, expSumLineY_expr,
    TwoExpBivarExpr.restrictedJacobianPoly,
    TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
    TwoExpBivarExpr.restrictDX, TwoExpBivarExpr.restrictDY,
    PfaffianRepExpr.denote, expSumLineChain, expSumLineEval,
    show ((1 : Real) + 0 - 0) * (0 + Real.exp (c - z) - 0) -
        (0 + 1 - 0) * (Real.exp z + 0 - 0) =
      Real.exp (c - z) - Real.exp z from by mach_ring,
    show (1 : Real) * Real.exp (c - z) - 1 * Real.exp z =
      Real.exp (c - z) - Real.exp z from by mach_ring] using hz_ne

/-- Concrete lower-level Pfaffian count for the exp-sum Jacobian, routed
through the expression compiler for the four partials. -/
theorem expSum_jacobian_pfaffian_count_expr (c a b : Real) (hab : a < b) :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧ Real.exp (c - z) - Real.exp z = 0) →
      zeros_J.length ≤ N := by
  obtain ⟨N, hN⟩ := pfaffian_jacobian_count_of_expr a b hab 0 (expSumLineChain c)
    expSumFx_expr expSumFy_expr expSumGx_expr expSumGy_expr
    (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
    (expSumJacobianExpr_nonzero_somewhere c a b hab)
  refine ⟨N, ?_⟩
  intro zeros_J hnd hzeros
  exact hN zeros_J hnd (fun z hzmem => by
    obtain ⟨hza, hzb, hz0⟩ := hzeros z hzmem
    refine ⟨hza, hzb, ?_⟩
    unfold expSumFx_expr expSumFy_expr expSumGx_expr expSumGy_expr
    unfold PfaffianRepExpr.denote
    change (1 : Real) * expSumLineEval c (⟨1, by omega⟩ : Fin 2) z -
        1 * expSumLineEval c (⟨0, by omega⟩ : Fin 2) z = 0
    unfold expSumLineEval
    rw [if_neg (by decide), if_pos rfl]
    simpa [show (1 : Real) * Real.exp (c - z) - 1 * Real.exp z =
        Real.exp (c - z) - Real.exp z from by mach_ring] using hz0)

/-- Concrete lower-level Pfaffian count for the exp-sum Jacobian, routed
through the bivariate-expression bridge. This exposes the lower-level count
in the same syntax-driven form used by the bivariate curve-count endpoint. -/
theorem expSum_jacobian_pfaffian_count_bivar (c d a b : Real) (hab : a < b) :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧ Real.exp (c - z) - Real.exp z = 0) →
      zeros_J.length ≤ N := by
  obtain ⟨N, hN⟩ := pfaffian_jacobian_count_of_bivar_expr a b hab 0 (expSumLineChain c)
    (expSumF_bivar c) (expSumG_bivar d)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
    (expSumJacobianBivar_nonzero_somewhere c d a b hab)
  refine ⟨N, ?_⟩
  intro zeros_J hnd hzeros
  exact hN zeros_J hnd (fun z hzmem => by
    obtain ⟨hza, hzb, hz0⟩ := hzeros z hzmem
    refine ⟨hza, hzb, ?_⟩
    simpa [expSumF_bivar, expSumG_bivar, expSumLineY_expr,
      TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
      TwoExpBivarExpr.restrictDX, TwoExpBivarExpr.restrictDY,
      PfaffianRepExpr.denote, expSumLineChain, expSumLineEval,
      show ((1 : Real) + 0 - 0) * (0 + Real.exp (c - z) - 0) -
          (0 + 1 - 0) * (Real.exp z + 0 - 0) =
        Real.exp (c - z) - Real.exp z from by mach_ring] using hz0)

/-- Concrete lower-level Pfaffian count for the exp-sum Jacobian, with the
non-identical-vanishing witness discharged. -/
theorem expSum_jacobian_pfaffian_count_uncond (c a b : Real) (hab : a < b) :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧ Real.exp (c - z) - Real.exp z = 0) →
      zeros_J.length ≤ N :=
  expSum_jacobian_pfaffian_count c a b hab (expSumJacobianPoly_nonzero_somewhere c a b hab)

/-- **Exp-sum curve count via the Pfaffian lower-level bound.** This is the
same geometric pipeline as `curve_exp_sum_le_two`, but the Jacobian-zero
input is supplied by the Pfaffian representation/count bridge rather than by
the direct monotonic `≤ 1` argument. The resulting bound is existential
because the general Pfaffian theorem returns an existential count. -/
theorem curve_exp_sum_via_pfaffian_lower_count (c d a b : Real) (hab : a < b) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (fun s => Real.exp s + Real.exp (c - s) - d) z = 0) →
      zeros.length ≤ N + 1 := by
  obtain ⟨N, hN⟩ := expSum_jacobian_pfaffian_count_uncond c a b hab
  refine ⟨N, ?_⟩
  exact khovanskii_rolle_count_curve
    (fun a b => a + b - c) (fun a b => Real.exp a + Real.exp b - d)
    (fun _ => 1) (fun _ => 1) Real.exp (fun z => Real.exp (c - z)) (fun x => c - x) a b hab
    (fun z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (c - z)
        (HasDerivAt2_projX z (c - z)) (HasDerivAt2_projY z (c - z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (c - z) hadd (HasDerivAt2_const c z (c - z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      exact hsub)
    (fun z _ _ => hasDerivAt2_exp_sum d z (c - z))
    (fun _ _ _ => one_ne_zero)
    (fun s => by show s + (c - s) - c = 0; mach_ring)
    N
    (fun zeros_J hnd hJ =>
      hN zeros_J hnd (fun z hz => by
        obtain ⟨hza, hzb, hjz⟩ := hJ z hz
        refine ⟨hza, hzb, ?_⟩
        rw [show Real.exp (c - z) - Real.exp z =
            1 * Real.exp (c - z) - 1 * Real.exp z from by mach_ring]
        exact hjz))

/-- The restricted formal `Fᵧ` for `F = x + y - c` is not identically zero
on any nonempty interval: it is the constant `1`. This is the nonzero witness
needed by the generic Pfaffian separator-count bridge. -/
theorem expSumFy_bivar_nonzero_somewhere (c a b : Real) (hab : a < b) :
    ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn (expSumLineChain c)
        (PfaffianRepExpr.compilePoly (expSumLineChain c) a b
          (TwoExpBivarExpr.restrictDY
            (expSumLineY_expr c)
            (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
            (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
            (expSumF_bivar c)))).eval z ≠ 0 := by
  obtain ⟨m, ham, hmb⟩ := MachLib.exists_between a b hab
  refine ⟨m, ham, hmb, ?_⟩
  have hrep := (PfaffianRepExpr.compile (expSumLineChain c) a b
    (TwoExpBivarExpr.restrictDY
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      (expSumF_bivar c))).eval_eq m ham hmb
  unfold PfaffianRepExpr.compilePoly
  rw [hrep]
  simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
    TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
    show (0 : Real) + 1 - 0 = 1 from by mach_ring] using one_ne_zero

/-- Pfaffian-produced separator count for exp-sum vertical critical points,
routed through the bivariate expression `F` and its formal restricted
`y`-partial. The bound is existential because it comes from the general
Pfaffian bridge; the sharper direct bound is `0` below. -/
theorem expSum_fy_separator_count_bivar (c a b : Real) (hab : a < b) :
    ∃ Ncrit : Nat, ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, a < s ∧ s < b ∧ (1 : Real) = 0) → ss.length ≤ Ncrit :=
  pfaffian_fy_separator_count_of_bivar_expr a b hab 0 (expSumLineChain c)
    (expSumF_bivar c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
    (expSumFy_bivar_nonzero_somewhere c a b hab)
    (fun _ => (1 : Real) = 0)
    (fun z _ _ hsep => by
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
        TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsep)

/-- The exp-sum source problem for one Pfaffian descent step.

The rank value here is only a toy witness for the interface; the future
Khovanskii descent theorem should replace it with the actual complexity
measure attached to the bivariate source. -/
noncomputable def expSum_descent_problem (c d a b : Real) (hab : a < b) :
    TwoExpDescentProblem
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      (fun _ => (1 : Real) = 0) :=
  { interval_nonempty := hab,
    isExp := expSumLineChain_isExp c,
    coherent := expSumLineChain_coh c a b,
    positive := expSumLineChain_pos c a b,
    jacobian_nonzero := expSumJacobianBivar_nonzero_somewhere c d a b hab,
    separator_nonzero := expSumFy_bivar_nonzero_somewhere c a b hab,
    separator_zero := by
      intro z _ _ hsep
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
        TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsep,
    sourceRank :=
      twoExpCompiledSourceRank
        (expSumF_bivar c) (expSumG_bivar d)
        a b 0 (expSumLineChain c)
        (expSumLineY_expr c)
        (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
        (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) }

/-- The exp-sum source problem sits in the positive-rank branch of the
descent-solver interface. -/
theorem expSum_descent_problem_positive_rank (c d a b : Real) (hab : a < b) :
    0 < (expSum_descent_problem c d a b hab).sourceRank :=
  twoExpCompiledSourceRank_pos
    (expSumF_bivar c) (expSumG_bivar d)
    a b 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))

/-- The exp-sum lower systems as a solved source descent problem. The child
ranks are the ranks of the compiled lower Pfaffian witnesses. -/
noncomputable def expSum_descent_result (c d a b : Real) (hab : a < b) :
    TwoExpDescentResult
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      (fun _ => (1 : Real) = 0)
      (expSum_descent_problem c d a b hab) :=
  descentResult_of_bivar_pfaffian
    (expSumF_bivar c) (expSumG_bivar d)
    a b 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (fun _ => (1 : Real) = 0)
    (expSum_descent_problem c d a b hab)
    (twoExpCompiledJacobianChildRank
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)))
    (twoExpCompiledSeparatorChildRank
      (expSumF_bivar c)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)))
    (twoExpCompiledJacobianChildRank_lt_source
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      )
    (twoExpCompiledSeparatorChildRank_lt_source
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      )

/-- The exp-sum source problem bundled with its solved one-step descent. -/
noncomputable def expSum_solved_descent (c d a b : Real) (hab : a < b) :
    TwoExpSolvedDescent
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      (fun _ => (1 : Real) = 0) :=
  solvedDescent_of_bivar_pfaffian_compiledRank_obligation
    (expSumF_bivar c) (expSumG_bivar d)
    a b hab 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
    (expSumJacobianBivar_nonzero_somewhere c d a b hab)
    (expSumFy_bivar_nonzero_somewhere c a b hab)
    (fun _ => (1 : Real) = 0)
    (fun z _ _ hsep => by
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
        TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsep)
    (compiledWitnessRankObligation_of_bivar_lowerSystem
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
      (expSumJacobianBivar_nonzero_somewhere c d a b hab)
      (expSumFy_bivar_nonzero_somewhere c a b hab)
      (fun _ => (1 : Real) = 0)
      (fun z _ _ hsep => by
        simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
          TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsep))

/-- The solved exp-sum descent stores the compiled source rank. -/
theorem expSum_solved_descent_sourceRank (c d a b : Real) (hab : a < b) :
    (expSum_solved_descent c d a b hab).problem.sourceRank =
      twoExpCompiledSourceRank
        (expSumF_bivar c) (expSumG_bivar d)
        a b 0 (expSumLineChain c)
        (expSumLineY_expr c)
        (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
        (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) :=
  solvedDescent_of_bivar_pfaffian_compiledRank_sourceRank
    (expSumF_bivar c) (expSumG_bivar d)
    a b hab 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
    (expSumJacobianBivar_nonzero_somewhere c d a b hab)
    (expSumFy_bivar_nonzero_somewhere c a b hab)
    (fun _ => (1 : Real) = 0)
    (fun z _ _ hsep => by
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
        TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsep)
    (compiledWitnessRankObligation_of_bivar_lowerSystem
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
      (expSumJacobianBivar_nonzero_somewhere c d a b hab)
      (expSumFy_bivar_nonzero_somewhere c a b hab)
      (fun _ => (1 : Real) = 0)
      (fun z _ _ hsep => by
        simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
          TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsep))

/-- Recover the compiled-rank obligation stored in the solved exp-sum
descent. -/
noncomputable def expSum_recovered_compiled_rank_obligation (c d a b : Real) (hab : a < b) :
    TwoExpCompiledRankObligation
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) :=
  compiledRankObligation_of_solved_descent
    (expSumF_bivar c) (expSumG_bivar d)
    a b 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (fun _ => (1 : Real) = 0)
    (expSum_solved_descent c d a b hab)
    (expSum_solved_descent_sourceRank c d a b hab)

/-- The recovered exp-sum Jacobian child rank is the compiled Jacobian
witness rank. -/
theorem expSum_recovered_compiled_rank_jacobianRank (c d a b : Real) (hab : a < b) :
    (expSum_recovered_compiled_rank_obligation c d a b hab).jacobianRank =
      twoExpCompiledJacobianChildRank
        (expSumF_bivar c) (expSumG_bivar d)
        a b 0 (expSumLineChain c)
        (expSumLineY_expr c)
        (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
        (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) :=
  rfl

/-- The recovered exp-sum separator child rank is the compiled separator
witness rank. -/
theorem expSum_recovered_compiled_rank_separatorRank (c d a b : Real) (hab : a < b) :
    (expSum_recovered_compiled_rank_obligation c d a b hab).separatorRank =
      twoExpCompiledSeparatorChildRank
        (expSumF_bivar c)
        a b 0 (expSumLineChain c)
        (expSumLineY_expr c)
        (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
        (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2)) :=
  rfl

/-- The recovered exp-sum ranks agree with the ranks of the actual lower
Pfaffian systems used by the direct bridge. -/
theorem expSum_lower_system_rank_pair (c d a b : Real) (hab : a < b) :
    (expSum_recovered_compiled_rank_obligation c d a b hab).jacobianRank =
        (lowerSystem_of_bivar_pfaffian
          (expSumF_bivar c) (expSumG_bivar d)
          a b 0 (expSumLineChain c)
          (expSumLineY_expr c)
          (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
          (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
          (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
          (expSumJacobianBivar_nonzero_somewhere c d a b hab)
          (expSumFy_bivar_nonzero_somewhere c a b hab)
          (fun _ => (1 : Real) = 0)
          (fun z _ _ hsep => by
            simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
              TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
              show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsep)
        ).jacobianRank
      ∧
      (expSum_recovered_compiled_rank_obligation c d a b hab).separatorRank =
        (lowerSystem_of_bivar_pfaffian
          (expSumF_bivar c) (expSumG_bivar d)
          a b 0 (expSumLineChain c)
          (expSumLineY_expr c)
          (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
          (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
          (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
          (expSumJacobianBivar_nonzero_somewhere c d a b hab)
          (expSumFy_bivar_nonzero_somewhere c a b hab)
          (fun _ => (1 : Real) = 0)
          (fun z _ _ hsep => by
            simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
              TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
              show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsep)
        ).separatorRank := by
  exact ⟨rfl, rfl⟩

/-- The exp-sum lower systems annotated with a toy strict-rank witness,
obtained by forgetting the explicit source problem/result layer. -/
noncomputable def expSum_ranked_lower_system (c d a b : Real) (hab : a < b) :
    TwoExpRankedLowerSystem
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      (fun _ => (1 : Real) = 0) :=
  rankedLowerSystem_of_descent_result
    (expSumF_bivar c) (expSumG_bivar d)
    a b 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (fun _ => (1 : Real) = 0)
    (expSum_solved_descent c d a b hab).problem
    (expSum_solved_descent c d a b hab).result

/-- The exp-sum instance packaged as a two-exp descent certificate. This is
the explicit object the global KR/arc-count engine consumes: one field bounds
the restricted Jacobian zeros, and the other bounds the restricted `Fᵧ`
separator points. -/
theorem expSum_descent_certificate (c d a b : Real) (hab : a < b) :
    TwoExpDescentCertificate
      (expSumF_bivar c) (expSumG_bivar d)
      a b 0 (expSumLineChain c)
      (expSumLineY_expr c)
      (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
      (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
      (fun _ => (1 : Real) = 0) :=
  descentCertificate_of_solved_descent
    (expSumF_bivar c) (expSumG_bivar d)
    a b 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (fun _ => (1 : Real) = 0)
    (expSum_solved_descent c d a b hab)

/-- The exp-sum line has no critical/separator points of the form `fᵧ = 0`,
because `fᵧ = 1`. This is the separator-side specialization for the
arc-count input: any nodup list of such separators has length `0`. -/
theorem expSum_no_fy_critical_separators :
    ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, (1 : Real) = 0) → ss.length ≤ 0
  | [], _, _ => by simp
  | s :: rest, _, hsep => by
      exfalso
      exact one_ne_zero (hsep s (List.mem_cons_self _ _))

/-- Interval-shaped version of `expSum_no_fy_critical_separators`, matching
the separator-count bridge shape used for global arc-count inputs. -/
theorem expSum_no_fy_critical_separators_on (a b : Real) :
    ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, a < s ∧ s < b ∧ (1 : Real) = 0) → ss.length ≤ 0 := by
  intro ss hnd hsep
  exact expSum_no_fy_critical_separators ss hnd (fun s hs => (hsep s hs).2.2)

/-- The exp-sum curve count through the reusable represented-Jacobian
interface. This is the same result as `curve_exp_sum_via_pfaffian_lower_count`,
but now the generic theorem in `TwoExpPfaffianRepresentation` performs the
assembly from represented partials to the Khovanskii-Rolle curve count. -/
theorem curve_exp_sum_via_represented_jacobian (c d a b : Real) (hab : a < b) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (fun s => Real.exp s + Real.exp (c - s) - d) z = 0) →
      zeros.length ≤ N + 1 :=
  khovanskii_rolle_count_curve_of_represented_jacobian
    (fun a b => a + b - c) (fun a b => Real.exp a + Real.exp b - d)
    (fun _ => 1) (fun _ => 1) Real.exp (fun z => Real.exp (c - z)) (fun x => c - x)
    a b hab
    (fun z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (c - z)
        (HasDerivAt2_projX z (c - z)) (HasDerivAt2_projY z (c - z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (c - z) hadd (HasDerivAt2_const c z (c - z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      exact hsub)
    (fun z _ _ => hasDerivAt2_exp_sum d z (c - z))
    (fun _ _ _ => one_ne_zero)
    (fun s => by show s + (c - s) - c = 0; mach_ring)
    0 (expSumLineChain c)
    expSumOnePoly expSumOnePoly expSumExpXPoly expSumExpCXPoly
    (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
    (expSumJacobianPoly_nonzero_somewhere c a b hab)
    (expSumOne_rep c a b) (expSumOne_rep c a b)
    (expSumExpX_rep c a b) (expSumExpCX_rep c a b)

/-- The exp-sum curve count through expression-compiled partials. This is
the same structural result as `curve_exp_sum_via_represented_jacobian`, but
the four partials are supplied as `PfaffianRepExpr`s and compiled into the
Jacobian count. -/
theorem curve_exp_sum_via_expr_jacobian (c d a b : Real) (hab : a < b) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (fun s => Real.exp s + Real.exp (c - s) - d) z = 0) →
      zeros.length ≤ N + 1 :=
  khovanskii_rolle_count_curve_of_expr_jacobian
    (fun a b => a + b - c) (fun a b => Real.exp a + Real.exp b - d) (fun x => c - x)
    a b hab
    0 (expSumLineChain c)
    expSumFx_expr expSumFy_expr expSumGx_expr expSumGy_expr
    (expSumLineChain_isExp c) (expSumLineChain_coh c a b) (expSumLineChain_pos c a b)
    (expSumJacobianExpr_nonzero_somewhere c a b hab)
    (fun z _ _ => by
      unfold expSumFx_expr expSumFy_expr
      unfold PfaffianRepExpr.denote
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (c - z)
        (HasDerivAt2_projX z (c - z)) (HasDerivAt2_projY z (c - z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (c - z) hadd (HasDerivAt2_const c z (c - z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      exact hsub)
    (fun z _ _ => by
      unfold expSumGx_expr expSumGy_expr
      unfold PfaffianRepExpr.denote
      change HasDerivAt2 (fun a b => Real.exp a + Real.exp b - d)
        (expSumLineEval c (⟨0, by omega⟩ : Fin 2) z)
        (expSumLineEval c (⟨1, by omega⟩ : Fin 2) z) z (c - z)
      unfold expSumLineEval
      rw [if_pos rfl, if_neg (by decide)]
      exact hasDerivAt2_exp_sum d z (c - z))
    (fun _ _ _ => by
      unfold expSumFy_expr PfaffianRepExpr.denote
      exact one_ne_zero)
    (fun s => by show s + (c - s) - c = 0; mach_ring)

/-- The exp-sum curve count through the bivariate-expression layer. The
formulas `F = x + y - c` and `G = exp x + exp y - d` are differentiated
syntactically, restricted to the line `y = c - x`, compiled to a Pfaffian
Jacobian witness, and then passed to Khovanskii-Rolle. -/
theorem curve_exp_sum_via_bivar_expr_jacobian (c d a b : Real) (hab : a < b) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (fun s => Real.exp s + Real.exp (c - s) - d) z = 0) →
      zeros.length ≤ N + 1 :=
  khovanskii_rolle_curve_of_solved_descent
    (expSumF_bivar c) (expSumG_bivar d)
    a b 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (fun _ => (1 : Real) = 0)
    (expSum_solved_descent c d a b hab)
    (fun x => c - x) a b hab
    (fun z hza hzb => ⟨hza, hzb⟩)
    (fun z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (c - z)
        (HasDerivAt2_projX z (c - z)) (HasDerivAt2_projY z (c - z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (c - z) hadd (HasDerivAt2_const c z (c - z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.denote,
        TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
        PfaffianRepExpr.denote,
        show (1 : Real) + 0 - 0 = 1 from by mach_ring,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsub)
    (fun z _ _ => by
      simpa [expSumG_bivar, expSumLineY_expr, TwoExpBivarExpr.denote,
        TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
        PfaffianRepExpr.denote, expSumLineChain, expSumLineEval,
        show (0 : Real) + Real.exp (c - z) - 0 = Real.exp (c - z) from by mach_ring,
        show Real.exp z + 0 - 0 = Real.exp z from by mach_ring] using
        hasDerivAt2_exp_sum d z (c - z))
    (fun z _ _ => by
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.dY,
        TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using one_ne_zero)
    (expSumF_bivar_line_zero c)

/-- **Single-line exp-sum global bound.** This is the concrete no-topology
endpoint for the validated exp-sum example: on one supplied interval of the
line `y = c - x`, a nodup list of zeros of
`exp x + exp(c-x) - d` is bounded through the expression-compiled
Pfaffian/Jacobian/Khovanskii-Rolle route. No arc list or separator witness is
needed. -/
theorem expSum_single_line_global_bound (c d a b : Real) (hab : a < b)
    (zeros : List Real) (hzeros_nd : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, a < z ∧ z < b ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    ∃ N : Nat, zeros.length ≤ (0 + 1) * (N + 1) := by
  obtain ⟨N, hN⟩ := curve_exp_sum_via_bivar_expr_jacobian c d a b hab
  refine ⟨N, ?_⟩
  have hle : zeros.length ≤ N + 1 := hN zeros hzeros_nd (fun z hzmem => by
    exact hzeros z hzmem)
  simpa using hle

/-- The canonical represented arc for the exp-sum line `y = c - x` on a
supplied interval. The representative is just `lo`; in singleton-arc uses it
is never asked to separate from another representative. -/
noncomputable def expSumLineArc (c lo hi : Real) (zeros : List Real) : RepresentedCurveArc :=
  { rep := lo,
    lo := lo,
    hi := hi,
    yc := fun t => c - t,
    zeros := zeros }

/-- **Global exp-sum assembly in the no-critical-separator case.** For the
line `f(x,y)=x+y-c`, the vertical critical predicate `fᵧ=0` is impossible
(`1=0`). Therefore the separator count is `0`; if the supplied arc
representatives are `ChainSep`-separated by that impossible predicate and
each arc has `≤ N+1` intersections, the global count is bounded by
`(0+1)*(N+1)`.

This exercises the global arc-count layer for the exp-sum example without
pretending to derive the arc decomposition itself. -/
theorem expSum_global_no_fy_critical_bound (a b : Real) (N : Nat)
    (hd : Real × List Real) (s : List (Real × List Real))
    (hchain : ChainSep (fun x => a < x ∧ x < b ∧ (1 : Real) = 0) hd.1 (s.map (fun arc => arc.1)))
    (harc : ∀ arc ∈ (hd :: s), arc.2.length ≤ N + 1) :
    ((hd :: s).flatMap (fun arc => arc.2)).length ≤ (0 + 1) * (N + 1) :=
  khovanskii_rolle_full_of_lower_counts
    (fun x => a < x ∧ x < b ∧ (1 : Real) = 0) 0 N
    (expSum_no_fy_critical_separators_on a b)
    hd s hchain harc

/-- **Rich global exp-sum assembly.** The arc decomposition is supplied as
`RepresentedCurveArc` data, but both lower-level counts are discharged:

* the Jacobian count comes from the concrete Pfaffian representation of
  `exp(c-x)-exp x`;
* the separator count is `0`, since the critical predicate `fᵧ = 0` is
  `1 = 0`.

This is the strongest current end-to-end exp-sum global theorem short of
constructing the arc decomposition itself. -/
theorem expSum_global_via_represented_arc_data (c d A B : Real) (hAB : A < B)
    (hd : RepresentedCurveArc) (s : List RepresentedCurveArc)
    (hchain : ChainSep (fun x => A < x ∧ x < B ∧ (1 : Real) = 0) hd.rep
      (s.map (fun arc => arc.rep)))
    (hinside : ∀ arc ∈ (hd :: s), A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : ∀ arc ∈ (hd :: s), arc.zeros.Nodup)
    (hyc : ∀ arc ∈ (hd :: s), ∀ t, arc.yc t = c - t)
    (hzeros : ∀ arc ∈ (hd :: s), ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    ∃ N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (0 + 1) * (N + 1) :=
  khovanskii_rolle_full_of_represented_arc_data_and_separator_count
    (fun a b => a + b - c) (fun a b => Real.exp a + Real.exp b - d)
    (fun _ => 1) (fun _ => 1) Real.exp (fun z => Real.exp (c - z))
    A B hAB
    0 (expSumLineChain c)
    expSumOnePoly expSumOnePoly expSumExpXPoly expSumExpCXPoly
    (expSumLineChain_isExp c) (expSumLineChain_coh c A B) (expSumLineChain_pos c A B)
    (expSumJacobianPoly_nonzero_somewhere c A B hAB)
    (expSumOne_rep c A B) (expSumOne_rep c A B)
    (expSumExpX_rep c A B) (expSumExpCX_rep c A B)
    (fun x => A < x ∧ x < B ∧ (1 : Real) = 0) 0
    (expSum_no_fy_critical_separators_on A B)
    hd s hchain hinside hzeros_nd
    (fun arc harc z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (arc.yc z)
        (HasDerivAt2_projX z (arc.yc z)) (HasDerivAt2_projY z (arc.yc z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (arc.yc z) hadd (HasDerivAt2_const c z (arc.yc z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      exact hsub)
    (fun arc harc z _ _ => by
      have hbase := hasDerivAt2_exp_sum d z (c - z)
      rw [hyc arc harc z]
      exact hbase)
    (fun _ _ _ _ _ => one_ne_zero)
    (fun arc harc t => by
      rw [hyc arc harc t]
      show t + (c - t) - c = 0
      mach_ring)
    (fun arc harc z hzmem => by
      obtain ⟨hzlo, hzhi, hzero⟩ := hzeros arc harc z hzmem
      rw [hyc arc harc z]
      exact ⟨hzlo, hzhi, hzero⟩)

/-- **Global exp-sum assembly through bivariate syntax.** This routes both
lower-level counts through the bivariate expression bridges:

* the Jacobian count comes from formal partials of
  `F = x + y - c` and `G = exp x + exp y - d`;
* the separator count comes from formal `Fᵧ`.

The arc decomposition is still supplied explicitly, but the lower count
machinery now starts from the bivariate formulas rather than hand-picked
partial functions or polynomials. -/
theorem expSum_global_via_bivar_expr_arc_data (c d A B : Real) (hAB : A < B)
    (hd : RepresentedCurveArc) (s : List RepresentedCurveArc)
    (hchain : ChainSep (fun x => A < x ∧ x < B ∧ (1 : Real) = 0) hd.rep
      (s.map (fun arc => arc.rep)))
    (hinside : ∀ arc ∈ (hd :: s), A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : ∀ arc ∈ (hd :: s), arc.zeros.Nodup)
    (hyc : ∀ arc ∈ (hd :: s), ∀ t, arc.yc t = c - t)
    (hzeros : ∀ arc ∈ (hd :: s), ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    ∃ Ncrit N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_full_of_solved_descent
    (expSumF_bivar c) (expSumG_bivar d)
    A B 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (fun _ => (1 : Real) = 0)
    (expSum_solved_descent c d A B hAB)
    hd s hchain hinside hzeros_nd
    (fun arc harc z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (arc.yc z)
        (HasDerivAt2_projX z (arc.yc z)) (HasDerivAt2_projY z (arc.yc z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (arc.yc z) hadd (HasDerivAt2_const c z (arc.yc z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.denote,
        TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
        TwoExpBivarExpr.restrictDX, TwoExpBivarExpr.restrictDY,
        PfaffianRepExpr.denote,
        show (1 : Real) + 0 - 0 = 1 from by mach_ring,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsub)
    (fun arc harc z _ _ => by
      have hbase := hasDerivAt2_exp_sum d z (c - z)
      rw [hyc arc harc z]
      simpa [expSumG_bivar, expSumLineY_expr, TwoExpBivarExpr.denote,
        TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
        TwoExpBivarExpr.restrictDX, TwoExpBivarExpr.restrictDY,
        PfaffianRepExpr.denote, expSumLineChain, expSumLineEval,
        show (0 : Real) + Real.exp (c - z) - 0 = Real.exp (c - z) from by mach_ring,
        show Real.exp z + 0 - 0 = Real.exp z from by mach_ring] using hbase)
    (fun arc _ z _ _ => by
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
        TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using one_ne_zero)
    (fun arc harc t => by
      rw [hyc arc harc t]
      exact expSumF_bivar_line_zero c t)
    (fun arc harc z hzmem => by
      obtain ⟨hzlo, hzhi, hzero⟩ := hzeros arc harc z hzmem
      rw [hyc arc harc z]
      exact ⟨hzlo, hzhi, hzero⟩)

/-- **Global exp-sum assembly through bivariate syntax with the sharp
separator side.** This keeps the Jacobian count produced from the bivariate
formulas, but uses the concrete fact `Fᵧ = 1` to set the separator/arc-count
input to `0`. -/
theorem expSum_global_via_bivar_expr_arc_data_no_fy
    (c d A B : Real) (hAB : A < B)
    (hd : RepresentedCurveArc) (s : List RepresentedCurveArc)
    (hchain : ChainSep (fun x => A < x ∧ x < B ∧ (1 : Real) = 0) hd.rep
      (s.map (fun arc => arc.rep)))
    (hinside : ∀ arc ∈ (hd :: s), A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : ∀ arc ∈ (hd :: s), arc.zeros.Nodup)
    (hyc : ∀ arc ∈ (hd :: s), ∀ t, arc.yc t = c - t)
    (hzeros : ∀ arc ∈ (hd :: s), ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    ∃ N : Nat,
      ((hd :: s).flatMap (fun arc => arc.zeros)).length ≤ (0 + 1) * (N + 1) := by
  exact khovanskii_rolle_full_of_solved_descent_and_separator_count
    (expSumF_bivar c) (expSumG_bivar d)
    A B 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (fun _ => (1 : Real) = 0)
    (expSum_solved_descent c d A B hAB)
    0 (expSum_no_fy_critical_separators_on A B)
    hd s hchain hinside hzeros_nd
    (fun arc harc z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (arc.yc z)
        (HasDerivAt2_projX z (arc.yc z)) (HasDerivAt2_projY z (arc.yc z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (arc.yc z) hadd (HasDerivAt2_const c z (arc.yc z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.denote,
        TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
        TwoExpBivarExpr.restrictDX, TwoExpBivarExpr.restrictDY,
        PfaffianRepExpr.denote,
        show (1 : Real) + 0 - 0 = 1 from by mach_ring,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsub)
    (fun arc harc z _ _ => by
      have hbase := hasDerivAt2_exp_sum d z (c - z)
      rw [hyc arc harc z]
      simpa [expSumG_bivar, expSumLineY_expr, TwoExpBivarExpr.denote,
        TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
        TwoExpBivarExpr.restrictDX, TwoExpBivarExpr.restrictDY,
        PfaffianRepExpr.denote, expSumLineChain, expSumLineEval,
        show (0 : Real) + Real.exp (c - z) - 0 = Real.exp (c - z) from by mach_ring,
        show Real.exp z + 0 - 0 = Real.exp z from by mach_ring] using hbase)
    (fun arc _ z _ _ => by
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
        TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using one_ne_zero)
    (fun arc harc t => by
      rw [hyc arc harc t]
      exact expSumF_bivar_line_zero c t)
    (fun arc harc z hzmem => by
      obtain ⟨hzlo, hzhi, hzero⟩ := hzeros arc harc z hzmem
      rw [hyc arc harc z]
      exact ⟨hzlo, hzhi, hzero⟩)

/-- **Single represented-arc exp-sum global bound.** This packages the common
one-arc case of `expSum_global_via_represented_arc_data`: the caller supplies
one represented interval of the line `y = c-x` and its zero list, and the
separator side disappears because there are no adjacent arcs to separate. -/
theorem expSum_global_single_represented_arc_data (c d A B : Real) (hAB : A < B)
    (arc : RepresentedCurveArc)
    (hinside : A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : arc.zeros.Nodup)
    (hyc : ∀ t, arc.yc t = c - t)
    (hzeros : ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    ∃ N : Nat, arc.zeros.length ≤ (0 + 1) * (N + 1) := by
  exact khovanskii_rolle_single_represented_arc_data_and_separator_count
    (fun a b => a + b - c) (fun a b => Real.exp a + Real.exp b - d)
    (fun _ => 1) (fun _ => 1) Real.exp (fun z => Real.exp (c - z))
    A B hAB
    0 (expSumLineChain c)
    expSumOnePoly expSumOnePoly expSumExpXPoly expSumExpCXPoly
    (expSumLineChain_isExp c) (expSumLineChain_coh c A B) (expSumLineChain_pos c A B)
    (expSumJacobianPoly_nonzero_somewhere c A B hAB)
    (expSumOne_rep c A B) (expSumOne_rep c A B)
    (expSumExpX_rep c A B) (expSumExpCX_rep c A B)
    (fun x => A < x ∧ x < B ∧ (1 : Real) = 0) 0
    (expSum_no_fy_critical_separators_on A B)
    arc hinside hzeros_nd
    (fun z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (arc.yc z)
        (HasDerivAt2_projX z (arc.yc z)) (HasDerivAt2_projY z (arc.yc z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (arc.yc z) hadd (HasDerivAt2_const c z (arc.yc z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      exact hsub)
    (fun z _ _ => by
      have hbase := hasDerivAt2_exp_sum d z (c - z)
      rw [hyc z]
      exact hbase)
    (fun _ _ _ => one_ne_zero)
    (fun t => by
      rw [hyc t]
      show t + (c - t) - c = 0
      mach_ring)
    (fun z hzmem => by
      obtain ⟨hzlo, hzhi, hzero⟩ := hzeros z hzmem
      rw [hyc z]
      exact ⟨hzlo, hzhi, hzero⟩)

/-- **Single represented-arc exp-sum bound through bivariate syntax.** This
is the one-arc version of `expSum_global_via_bivar_expr_arc_data`: the lower
Jacobian and separator counts are both produced from the bivariate formulas
and their formal restricted partials. -/
theorem expSum_global_single_bivar_expr_arc_data (c d A B : Real) (hAB : A < B)
    (arc : RepresentedCurveArc)
    (hinside : A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : arc.zeros.Nodup)
    (hyc : ∀ t, arc.yc t = c - t)
    (hzeros : ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    ∃ Ncrit N : Nat, arc.zeros.length ≤ (Ncrit + 1) * (N + 1) :=
  khovanskii_rolle_single_of_solved_descent
    (expSumF_bivar c) (expSumG_bivar d)
    A B 0 (expSumLineChain c)
    (expSumLineY_expr c)
    (PfaffianRepExpr.varY (⟨0, by omega⟩ : Fin 2))
    (PfaffianRepExpr.varY (⟨1, by omega⟩ : Fin 2))
    (fun _ => (1 : Real) = 0)
    (expSum_solved_descent c d A B hAB)
    arc hinside hzeros_nd
    (fun z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (arc.yc z)
        (HasDerivAt2_projX z (arc.yc z)) (HasDerivAt2_projY z (arc.yc z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (arc.yc z) hadd (HasDerivAt2_const c z (arc.yc z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.denote,
        TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
        TwoExpBivarExpr.restrictDX, TwoExpBivarExpr.restrictDY,
        PfaffianRepExpr.denote,
        show (1 : Real) + 0 - 0 = 1 from by mach_ring,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using hsub)
    (fun z _ _ => by
      have hbase := hasDerivAt2_exp_sum d z (c - z)
      rw [hyc z]
      simpa [expSumG_bivar, expSumLineY_expr, TwoExpBivarExpr.denote,
        TwoExpBivarExpr.dX, TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict,
        TwoExpBivarExpr.restrictDX, TwoExpBivarExpr.restrictDY,
        PfaffianRepExpr.denote, expSumLineChain, expSumLineEval,
        show (0 : Real) + Real.exp (c - z) - 0 = Real.exp (c - z) from by mach_ring,
        show Real.exp z + 0 - 0 = Real.exp z from by mach_ring] using hbase)
    (fun z _ _ => by
      simpa [expSumF_bivar, expSumLineY_expr, TwoExpBivarExpr.restrictDY,
        TwoExpBivarExpr.dY, TwoExpBivarExpr.restrict, PfaffianRepExpr.denote,
        show (0 : Real) + 1 - 0 = 1 from by mach_ring] using one_ne_zero)
    (fun t => by
      rw [hyc t]
      exact expSumF_bivar_line_zero c t)
    (fun z hzmem => by
      obtain ⟨hzlo, hzhi, hzero⟩ := hzeros z hzmem
      rw [hyc z]
      exact ⟨hzlo, hzhi, hzero⟩)

/-- **Single represented-arc exp-sum bound through bivariate syntax with the
sharp separator side.** This is the one-arc specialization of
`expSum_global_via_bivar_expr_arc_data_no_fy`, so the separator factor is
fixed at `0 + 1`. -/
theorem expSum_global_single_bivar_expr_arc_data_no_fy
    (c d A B : Real) (hAB : A < B)
    (arc : RepresentedCurveArc)
    (hinside : A < arc.lo ∧ arc.lo < arc.hi ∧ arc.hi < B)
    (hzeros_nd : arc.zeros.Nodup)
    (hyc : ∀ t, arc.yc t = c - t)
    (hzeros : ∀ z ∈ arc.zeros,
      arc.lo < z ∧ z < arc.hi ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    ∃ N : Nat, arc.zeros.length ≤ (0 + 1) * (N + 1) := by
  obtain ⟨N, hN⟩ := expSum_global_via_bivar_expr_arc_data_no_fy c d A B hAB
    arc [] trivial
    (fun a ha => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hinside)
    (fun a ha => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hzeros_nd)
    (fun a ha t => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hyc t)
    (fun a ha z hzmem => by
      have haeq : a = arc := by simpa using ha
      subst a
      exact hzeros z hzmem)
  refine ⟨N, ?_⟩
  simpa using hN

/-- **Exp-sum represented line-arc bound from ordinary interval data.** This
is the user-facing singleton represented-arc endpoint: give an outer interval,
one inner line interval, and a nodup zero list for
`exp x + exp(c-x) - d`; the represented-Jacobian/Pfaffian assembly supplies
the existential global bound. -/
theorem expSum_global_line_arc_bound (c d A B lo hi : Real) (hAB : A < B)
    (hinside : A < lo ∧ lo < hi ∧ hi < B)
    (zeros : List Real) (hzeros_nd : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, lo < z ∧ z < hi ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    ∃ N : Nat, zeros.length ≤ (0 + 1) * (N + 1) := by
  obtain ⟨N, hN⟩ := expSum_global_single_bivar_expr_arc_data_no_fy c d A B hAB
    (expSumLineArc c lo hi zeros)
    hinside hzeros_nd (fun _ => rfl) hzeros
  refine ⟨N, ?_⟩
  simpa [expSumLineArc] using hN

/-!
## Sharp route vs structural route

The exp-sum example now has two deliberately different endpoints:

* `line_meets_exp_sum_le_two` is the sharp, direct argument. It uses the
  strict antitonicity of `exp(c-x)-exp x` to prove the concrete `≤ 2` bound.
* `expSum_global_line_arc_bound` is the structural Pfaffian route. Its bound
  is existential because the reusable Pfaffian zero-count theorem returns an
  existential count, but the proof path is the one that generalizes:
  represented partials → represented Jacobian → Pfaffian lower count →
  Khovanskii-Rolle curve/global assembly.
-/

theorem expSum_sharp_and_pfaffian_routes (c d a b : Real) (hab : a < b)
    (zeros : List Real) (hzeros_nd : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, a < z ∧ z < b ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    zeros.length ≤ 1 + 1 ∧ ∃ N : Nat, zeros.length ≤ (0 + 1) * (N + 1) := by
  refine ⟨line_meets_exp_sum_le_two c d a b hab zeros hzeros_nd hzeros, ?_⟩
  exact expSum_single_line_global_bound c d a b hab zeros hzeros_nd hzeros

/-- Sharp/direct and structural/global routes on the same supplied inner
line arc. The structural side uses an outer interval `(A,B)` containing the
arc interval `(lo,hi)`, matching the represented-arc global API. -/
theorem expSum_sharp_and_global_line_arc_routes
    (c d A B lo hi : Real) (hAB : A < B)
    (hinside : A < lo ∧ lo < hi ∧ hi < B)
    (zeros : List Real) (hzeros_nd : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, lo < z ∧ z < hi ∧ Real.exp z + Real.exp (c - z) - d = 0) :
    zeros.length ≤ 1 + 1 ∧ ∃ N : Nat, zeros.length ≤ (0 + 1) * (N + 1) := by
  refine ⟨line_meets_exp_sum_le_two c d lo hi hinside.2.1 zeros hzeros_nd hzeros, ?_⟩
  exact expSum_global_line_arc_bound c d A B lo hi hAB hinside zeros hzeros_nd hzeros

end TwoExp
end MultiVarMod
end MachLib
