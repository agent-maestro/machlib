import MachLib.MultiVar
import MachLib.BivariateDeriv

/-!
# `MultiVarExpr k` — an N-ary Pfaffian expression language + the currying bridge into `HasDerivAt2`

Gate-2d ladder, chain-2 → chain-N (`roadmap/multivariate-khovanskii-chainN-scoping.md`, bricks N.0/N.1).

`TwoExpPfaffianRepresentation.lean`'s `TwoExpBivarExpr` is hardcoded to exactly two variables
(`varX | varY | expX | expY`). This file generalizes it to `k` independent variables, reusing
`MultiVar k`'s AST (`const | var | add | sub | mul`, indexed by `Fin k`) plus `k` exponential atoms
(`expVar : Fin k → MultiVarExpr k`).

**The key finding this file exercises (see the scoping doc §1): no N-ary differentiability axiom is
needed.** The Khovanskii–Rolle induction only ever needs TWO active coordinates at a time, with the rest
frozen as parameters — and a `k`-variable function with `k−2` coordinates frozen is, by definition, a
2-variable function, so `BivariateDeriv.lean`'s existing `HasDerivAt2` axioms apply directly via currying.
`hasDerivAt2_of_multiVarExpr` below is the general bridge: for ANY `MultiVarExpr k` and any two DISTINCT
active indices `p ≠ q`, the curried closure is differentiable with the syntactically-computed partials —
proved once, by structural induction, reusing exactly the rules `hasDerivAt2_exp_sum`
(`BivariateDeriv.lean`) exercised by hand for one example.

Zero new axioms; `sorry`-free.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.Real

/-- AST for an expression in `k` independent real variables `x₀,…,x_{k-1}` PLUS their exponentials
`e^{x₀},…,e^{x_{k-1}}` — the N-ary generalization of `TwoExpBivarExpr`. Reuses `MultiVar k`'s variable
indexing (`Fin k`) and ring shape; adds one exponential atom per coordinate. -/
inductive MultiVarExpr (k : Nat) : Type where
  | const  : Real → MultiVarExpr k
  | var    : Fin k → MultiVarExpr k
  | expVar : Fin k → MultiVarExpr k
  | add    : MultiVarExpr k → MultiVarExpr k → MultiVarExpr k
  | sub    : MultiVarExpr k → MultiVarExpr k → MultiVarExpr k
  | mul    : MultiVarExpr k → MultiVarExpr k → MultiVarExpr k

namespace MultiVarExpr

/-- Real denotation at an environment `env : Fin k → Real`. -/
noncomputable def denote {k : Nat} : MultiVarExpr k → (Fin k → Real) → Real
  | const c,  _   => c
  | var i,    env => env i
  | expVar i, env => exp (env i)
  | add e₁ e₂, env => denote e₁ env + denote e₂ env
  | sub e₁ e₂, env => denote e₁ env - denote e₂ env
  | mul e₁ e₂, env => denote e₁ env * denote e₂ env

@[simp] theorem denote_const {k : Nat} (c : Real) (env : Fin k → Real) :
    denote (const c) env = c := rfl
@[simp] theorem denote_var {k : Nat} (i : Fin k) (env : Fin k → Real) :
    denote (var i) env = env i := rfl
@[simp] theorem denote_expVar {k : Nat} (i : Fin k) (env : Fin k → Real) :
    denote (expVar i) env = exp (env i) := rfl
@[simp] theorem denote_add {k : Nat} (e₁ e₂ : MultiVarExpr k) (env : Fin k → Real) :
    denote (add e₁ e₂) env = denote e₁ env + denote e₂ env := rfl
@[simp] theorem denote_sub {k : Nat} (e₁ e₂ : MultiVarExpr k) (env : Fin k → Real) :
    denote (sub e₁ e₂) env = denote e₁ env - denote e₂ env := rfl
@[simp] theorem denote_mul {k : Nat} (e₁ e₂ : MultiVarExpr k) (env : Fin k → Real) :
    denote (mul e₁ e₂) env = denote e₁ env * denote e₂ env := rfl

/-- Formal partial derivative with respect to coordinate `i` — the `Fin k`-indexed generalization of
`TwoExpBivarExpr.dX`/`.dY`. -/
noncomputable def dVar {k : Nat} (i : Fin k) : MultiVarExpr k → MultiVarExpr k
  | const _  => const 0
  | var j    => if j = i then const 1 else const 0
  | expVar j => if j = i then expVar j else const 0
  | add e₁ e₂ => add (dVar i e₁) (dVar i e₂)
  | sub e₁ e₂ => sub (dVar i e₁) (dVar i e₂)
  | mul e₁ e₂ => add (mul (dVar i e₁) e₂) (mul e₁ (dVar i e₂))

theorem dVar_const {k : Nat} (i : Fin k) (c : Real) : dVar i (const c) = const 0 := rfl
theorem dVar_var {k : Nat} (i j : Fin k) :
    dVar i (var j) = if j = i then const 1 else const 0 := rfl
theorem dVar_expVar {k : Nat} (i j : Fin k) :
    dVar i (expVar j) = if j = i then expVar j else const 0 := rfl

/-! ## The currying bridge -/

/-- Point-update of an environment at TWO indices: `p ↦ a`, `q ↦ b`, all other coordinates unchanged.
The two-index generalization of `MultiVarMod.substEnv` (`MultiVarSubst.lean`). -/
def freeze2 {k : Nat} (env : Fin k → Real) (p q : Fin k) (a b : Real) : Fin k → Real :=
  fun l => if l = p then a else if l = q then b else env l

theorem freeze2_self_left {k : Nat} (env : Fin k → Real) (p q : Fin k) (a b : Real) :
    freeze2 env p q a b p = a := if_pos rfl

theorem freeze2_self_right {k : Nat} (env : Fin k → Real) {p q : Fin k} (hpq : p ≠ q) (a b : Real) :
    freeze2 env p q a b q = b := by
  unfold freeze2
  rw [if_neg (Ne.symm hpq), if_pos rfl]

/-- **The currying bridge.** For any `MultiVarExpr k` and any two DISTINCT active indices `p ≠ q`, the
closure obtained by freezing every other coordinate at `env` and varying only `p, q` is jointly
differentiable (`HasDerivAt2`), with partials given by `dVar p`/`dVar q` evaluated at the same frozen
point — reusing `BivariateDeriv.lean`'s axioms exactly as `hasDerivAt2_exp_sum` does by hand, but proved
once for every `MultiVarExpr k`. No new axiom. -/
theorem hasDerivAt2_of_multiVarExpr {k : Nat} (e : MultiVarExpr k) (env : Fin k → Real) (p q : Fin k)
    (hpq : p ≠ q) (a b : Real) :
    HasDerivAt2 (fun x y => denote e (freeze2 env p q x y))
      (denote (dVar p e) (freeze2 env p q a b)) (denote (dVar q e) (freeze2 env p q a b)) a b := by
  induction e with
  | const c =>
      have hshow : (fun x y => denote (const c) (freeze2 env p q x y)) = (fun _ _ => c) := rfl
      rw [hshow, dVar_const, dVar_const]
      exact HasDerivAt2_const c a b
  | var l =>
      by_cases hlp : l = p
      · have hshow : (fun x y => denote (var l) (freeze2 env p q x y)) = (fun x _ => x) := by
          funext x y; show freeze2 env p q x y l = x; rw [hlp]; exact freeze2_self_left env p q x y
        rw [hshow, dVar_var, dVar_var, if_pos hlp, if_neg (by rw [hlp]; exact hpq), denote_const, denote_const]
        exact HasDerivAt2_projX a b
      · by_cases hlq : l = q
        · have hshow : (fun x y => denote (var l) (freeze2 env p q x y)) = (fun _ y => y) := by
            funext x y; show freeze2 env p q x y l = y
            rw [hlq]; exact freeze2_self_right env hpq x y
          rw [hshow, dVar_var, dVar_var, if_neg hlp, if_pos hlq, denote_const, denote_const]
          exact HasDerivAt2_projY a b
        · have hshow : (fun x y => denote (var l) (freeze2 env p q x y)) = (fun _ _ => env l) := by
            funext x y
            show freeze2 env p q x y l = env l
            unfold freeze2
            rw [if_neg hlp, if_neg hlq]
          rw [hshow, dVar_var, dVar_var, if_neg hlp, if_neg hlq]
          exact HasDerivAt2_const (env l) a b
  | expVar l =>
      by_cases hlp : l = p
      · have hshow : (fun x y => denote (expVar l) (freeze2 env p q x y)) = (fun x _ => exp x) := by
          funext x y; show exp (freeze2 env p q x y l) = exp x
          rw [hlp]; rw [freeze2_self_left env p q x y]
        rw [hshow, dVar_expVar, dVar_expVar, if_pos hlp, if_neg (by rw [hlp]; exact hpq), denote_expVar]
        rw [hlp, freeze2_self_left env p q a b]
        have hst := HasDerivAt2_scomp exp (exp a) (fun x _ => x) 1 0 a b (HasDerivAt_exp a)
          (HasDerivAt2_projX a b)
        have e1 : exp a * 1 = exp a := by mach_ring
        have e2 : exp a * 0 = 0 := by mach_ring
        rw [e1, e2] at hst
        exact hst
      · by_cases hlq : l = q
        · have hshow : (fun x y => denote (expVar l) (freeze2 env p q x y)) = (fun _ y => exp y) := by
            funext x y; show exp (freeze2 env p q x y l) = exp y
            rw [hlq]; rw [freeze2_self_right env hpq x y]
          rw [hshow, dVar_expVar, dVar_expVar, if_neg hlp, if_pos hlq, denote_expVar]
          rw [hlq, freeze2_self_right env hpq a b]
          have hst := HasDerivAt2_scomp exp (exp b) (fun _ y => y) 0 1 a b (HasDerivAt_exp b)
            (HasDerivAt2_projY a b)
          have e1 : exp b * 0 = 0 := by mach_ring
          have e2 : exp b * 1 = exp b := by mach_ring
          rw [e1, e2] at hst
          exact hst
        · have hshow : (fun x y => denote (expVar l) (freeze2 env p q x y)) = (fun _ _ => exp (env l)) := by
            funext x y; show exp (freeze2 env p q x y l) = exp (env l)
            unfold freeze2
            rw [if_neg hlp, if_neg hlq]
          rw [hshow, dVar_expVar, dVar_expVar, if_neg hlp, if_neg hlq]
          simpa using HasDerivAt2_const (exp (env l)) a b
  | add e₁ e₂ ih₁ ih₂ =>
      simpa [dVar] using HasDerivAt2_add _ _ _ _ _ _ a b ih₁ ih₂
  | sub e₁ e₂ ih₁ ih₂ =>
      simpa [dVar] using HasDerivAt2_sub _ _ _ _ _ _ a b ih₁ ih₂
  | mul e₁ e₂ ih₁ ih₂ =>
      have hmul := HasDerivAt2_mul _ _ _ _ _ _ a b ih₁ ih₂
      simpa [dVar] using hmul

/-! ## N.1b — the curve-tangent / chain-rule bridge, for free

`BivariateDeriv.lean`'s `curve_tangent_and_chain` is already stated over GENERIC `f g : Real → Real →
Real` — it never mentions `TwoExpBivarExpr`. So it applies to the curried `MultiVarExpr k` closures with
NO further proof: just supply `hasDerivAt2_of_multiVarExpr` as its two `HasDerivAt2` hypotheses. This is
exactly the corollary `khovanskii_rolle_count` (`MultiVarTwoExpRolle.lean`) needs for its `hcurve`/
`hGderiv` hypotheses — and that theorem is itself already `Real → Real`-generic (no `HasDerivAt2` or
`TwoExpBivarExpr` in its statement at all), so the whole existing single-point IFT/tangent apparatus
carries over to the N-ary case with zero new lemmas beyond this one composition. -/

/-- **The curve-tangent / chain-rule bridge for `MultiVarExpr k`.** For two expressions `f, g`, an active
pair `p ≠ q`, and a curve `yc` implicitly solving `f = 0` along the arc (supplied, not constructed — the
IFT/existence gate stays external, exactly as `curve_tangent_and_chain` and `RepresentedCurveArc.yc`
already treat it): the tangent condition and chain rule needed by `khovanskii_rolle_count` follow, with
partials computed syntactically by `dVar`. -/
theorem multiVarExpr_curve_tangent_and_chain {k : Nat} (f g : MultiVarExpr k) (env : Fin k → Real)
    (p q : Fin k) (hpq : p ≠ q) (yc : Real → Real) (x : Real)
    (hfy : denote (dVar q f) (freeze2 env p q x (yc x)) ≠ 0)
    (hid : ∀ s : Real, denote f (freeze2 env p q s (yc s)) = 0) :
    HasDerivAt yc (-(denote (dVar p f) (freeze2 env p q x (yc x)))
        / denote (dVar q f) (freeze2 env p q x (yc x))) x
      ∧ denote (dVar p f) (freeze2 env p q x (yc x))
          + denote (dVar q f) (freeze2 env p q x (yc x))
            * (-(denote (dVar p f) (freeze2 env p q x (yc x)))
                / denote (dVar q f) (freeze2 env p q x (yc x))) = 0
      ∧ HasDerivAt (fun s => denote g (freeze2 env p q s (yc s)))
          (denote (dVar p g) (freeze2 env p q x (yc x)) * 1
            + denote (dVar q g) (freeze2 env p q x (yc x))
              * (-(denote (dVar p f) (freeze2 env p q x (yc x)))
                  / denote (dVar q f) (freeze2 env p q x (yc x)))) x :=
  curve_tangent_and_chain
    (fun a b => denote f (freeze2 env p q a b)) (fun a b => denote g (freeze2 env p q a b))
    (denote (dVar p f) (freeze2 env p q x (yc x))) (denote (dVar q f) (freeze2 env p q x (yc x)))
    (denote (dVar p g) (freeze2 env p q x (yc x))) (denote (dVar q g) (freeze2 env p q x (yc x)))
    yc x
    (hasDerivAt2_of_multiVarExpr f env p q hpq x (yc x))
    (hasDerivAt2_of_multiVarExpr g env p q hpq x (yc x))
    hfy hid

end MultiVarExpr
end MultiVarMod
end MachLib
