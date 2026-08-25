import MachLib.EMLOneQueryGlobal
import MachLib.Bipoly

/-!
# The div-free fragment of `OneQueryDichotomy` is a statement about bivariate polynomials

`OneQueryDichotomy` asks whether a one-query *context* `C(x, F(S x))` is eventually zero or
eventually nonzero, for `S = P/Q` rational. `EMLGermSign` records the reason to expect it to turn on
representation rather than transcendence: sign-definiteness for `C₀` was easy *because `C₀` has a
normal form*, and the level-1 question is hard exactly where no normal form is available to read the
answer off.

This module supplies the normal form for the fragment where one exists outright.

## The fragment, and why it is the right one to do first

`FCtx` is `hole | const | var | add | sub | mul | div` — a **rational** function of `x` and the hole.
Drop `div` and it is a **polynomial** in the hole with polynomial-in-`x` coefficients: exactly a
`Bipoly`. `ctxPoly` is that translation and `divFree_eval` proves it evaluates correctly,
unconditionally and with no side conditions at all.

`div` is excluded deliberately rather than overlooked. Division needs its denominator nonzero to mean
anything (`div_def` carries `hb : b ≠ 0`), so a rational normal form has to carry a nonvanishing
condition for *every* intermediate denominator, and that bookkeeping is a separate piece of work. The
div-free fragment needs none of it, which is what makes it worth isolating.

## What the reduction says

With the normal form, the dichotomy for a div-free context is **literally** the dichotomy for its
`Bipoly` (`oneQueryDichotomy_divFree_of_bipoly`). So on this fragment the obligation contains no
context syntax and no `FCtx` at all — what is left is the question of whether a bivariate polynomial
can vanish identically along the curve `y = F(P(x)/Q(x))`, which is an algebraic-relation question
about `F ∘ (P/Q)` and nothing else.

That is the same move as `EMLSignReduction`: strip the representation until the residue is a
statement about growth or algebraic dependence, and name it.

## What is **not** claimed

`OneQueryDichotomy` stays **open**, and this does not touch the `div` case. Nothing here proves a
bivariate polynomial cannot vanish along that curve — that is the residue, and for `F = exp + log`
composed with a rational function it is exactly the transcendence input the corpus does not yet have
in this form. `Fbasis_not_algebraic` is the corresponding statement for the *identity* argument
(`F x`), not for `F (P/Q)`.
-/

namespace MachLib

open Real

/-! ## The fragment -/

/-- Contexts built without `div`. -/
def FCtx.DivFree : FCtx → Prop
  | .hole      => True
  | .const _   => True
  | .var       => True
  | .add a b   => a.DivFree ∧ b.DivFree
  | .sub a b   => a.DivFree ∧ b.DivFree
  | .mul a b   => a.DivFree ∧ b.DivFree
  | .div _ _   => False

/-- The `Bipoly` a div-free context denotes: a polynomial in the hole whose coefficients are
polynomials in `x`. The `div` branch returns the zero bipoly and is never reached under `DivFree`. -/
noncomputable def ctxPoly : FCtx → List (List Real)
  | .hole      => [[], [1]]
  | .const c   => [[c]]
  | .var       => [[0, 1]]
  | .add a b   => biadd (ctxPoly a) (ctxPoly b)
  | .sub a b   => bisub (ctxPoly a) (ctxPoly b)
  | .mul a b   => bimul (ctxPoly a) (ctxPoly b)
  | .div _ _   => []

/-- **The normal form.** No side conditions: on the div-free fragment a context *is* a `Bipoly`. -/
theorem divFree_eval : ∀ (C : FCtx), C.DivFree → ∀ x y : Real,
    C.eval x y = bipev (ctxPoly C) x y := by
  intro C
  induction C with
  | hole =>
      intro _ x y
      show y = pev [] x + y * (pev [1] x + y * 0)
      show y = 0 + y * ((1 + x * 0) + y * 0)
      mach_ring
  | const c =>
      intro _ x y
      show c = pev [c] x + y * 0
      show c = (c + x * 0) + y * 0
      mach_ring
  | var =>
      intro _ x y
      show x = pev [0, 1] x + y * 0
      show x = 0 + x * (1 + x * 0) + y * 0
      mach_ring
  | add a b iha ihb =>
      intro h x y
      show a.eval x y + b.eval x y = bipev (biadd (ctxPoly a) (ctxPoly b)) x y
      rw [bipev_biadd, iha h.1 x y, ihb h.2 x y]
  | sub a b iha ihb =>
      intro h x y
      show a.eval x y - b.eval x y = bipev (bisub (ctxPoly a) (ctxPoly b)) x y
      rw [bipev_bisub, iha h.1 x y, ihb h.2 x y]
  | mul a b iha ihb =>
      intro h x y
      show a.eval x y * b.eval x y = bipev (bimul (ctxPoly a) (ctxPoly b)) x y
      rw [bipev_bimul, iha h.1 x y, ihb h.2 x y]
  | div a b _ _ => intro h; exact absurd h (by intro hh; cases hh)

/-! ## The reduction -/

/-- **The dichotomy, for bivariate polynomials.** No `FCtx` in the statement. -/
def BipolyDichotomyAlong : Prop :=
  ∀ (N : List (List Real)) (P Q : List Real) (X : Real), 1 ≤ X →
    (∀ x : Real, X ≤ x → pev Q x ≠ 0) →
      EvZeroF (fun x => bipev N x (Fbasis (pev P x / pev Q x)))
      ∨ ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
          bipev N x (Fbasis (pev P x / pev Q x)) ≠ 0

/-- **`OneQueryDichotomy` on the div-free fragment is exactly `BipolyDichotomyAlong`.** The context
disappears; what remains is whether a bivariate polynomial can vanish along `y = F(P/Q)`. -/
theorem oneQueryDichotomy_divFree_of_bipoly (h : BipolyDichotomyAlong) :
    ∀ (C : FCtx), C.DivFree → ∀ (P Q : List Real) (X : Real), 1 ≤ X →
      (∀ x : Real, X ≤ x → pev Q x ≠ 0) →
        EvZeroF (fun x => FCtx.eval C x (Fbasis (pev P x / pev Q x)))
        ∨ ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
            FCtx.eval C x (Fbasis (pev P x / pev Q x)) ≠ 0 := by
  intro C hC P Q X hX hQ
  rcases h (ctxPoly C) P Q X hX hQ with ⟨Z, hZ, hz⟩ | ⟨Y, hY, hn⟩
  · refine Or.inl ⟨Z, hZ, fun x hx => ?_⟩
    have v : bipev (ctxPoly C) x (Fbasis (pev P x / pev Q x)) = 0 := hz x hx
    show FCtx.eval C x (Fbasis (pev P x / pev Q x)) = 0
    rw [divFree_eval C hC x (Fbasis (pev P x / pev Q x))]
    exact v
  · refine Or.inr ⟨Y, hY, fun x hx => ?_⟩
    have v : bipev (ctxPoly C) x (Fbasis (pev P x / pev Q x)) ≠ 0 := hn x hx
    show FCtx.eval C x (Fbasis (pev P x / pev Q x)) ≠ 0
    rw [divFree_eval C hC x (Fbasis (pev P x / pev Q x))]
    exact v

/-- **Discrimination.** The fragment is inhabited by something with real structure — not just the
bare hole — and `div` is genuinely excluded rather than accidentally unreachable. Without this the
normal form above could be true for an empty or trivial class. -/
theorem divFree_specimens :
    (FCtx.mul FCtx.var FCtx.hole).DivFree
    ∧ (FCtx.sub (FCtx.mul FCtx.hole FCtx.hole) (FCtx.const 1)).DivFree
    ∧ ¬ (FCtx.div FCtx.var FCtx.hole).DivFree :=
  ⟨⟨trivial, trivial⟩, ⟨⟨trivial, trivial⟩, trivial⟩, fun h => h⟩

/-- And the translation computes on one: the `Bipoly` denoted by `mul var hole` really is `x · y`. -/
theorem ctxPoly_mul_var_hole (x y : Real) :
    bipev (ctxPoly (FCtx.mul FCtx.var FCtx.hole)) x y = x * y := by
  rw [← divFree_eval _ divFree_specimens.1 x y]
  rfl

end MachLib
