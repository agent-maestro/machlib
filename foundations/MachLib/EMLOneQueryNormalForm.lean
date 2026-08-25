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

/-! ## The `div` case — a rational normal form

The div-free fragment above needed no side conditions. Division does: `div_def` carries `hb : b ≠ 0`,
so an identity `C.eval = N/D` can only hold where the denominators are actually denominators. The
statement below therefore multiplies out — `C.eval · D = N` — and carries exactly the nonvanishing it
needs, which turns out to be **one condition per `div` node** and nothing more.

Why so little: for `add`/`sub`/`mul` the denominator is `da·db`, so the top denominator being nonzero
already forces both children's. Only `div` breaks that, because its denominator is `da·nb` and `db`
appears in the *numerator* — so `db ≠ 0` has to be asked for. Everything else is derived, including
`b.eval ≠ 0`, which follows from `b.eval · db = nb` and `nb ≠ 0`. -/

/-- Numerator and denominator bipolys for an **arbitrary** context. -/
noncomputable def ctxFrac : FCtx → List (List Real) × List (List Real)
  | .hole    => ([[], [1]], [[1]])
  | .const c => ([[c]], [[1]])
  | .var     => ([[0, 1]], [[1]])
  | .add a b => (biadd (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2),
                 bimul (ctxFrac a).2 (ctxFrac b).2)
  | .sub a b => (bisub (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2),
                 bimul (ctxFrac a).2 (ctxFrac b).2)
  | .mul a b => (bimul (ctxFrac a).1 (ctxFrac b).1, bimul (ctxFrac a).2 (ctxFrac b).2)
  | .div a b => (bimul (ctxFrac a).1 (ctxFrac b).2, bimul (ctxFrac a).2 (ctxFrac b).1)

/-- The side condition, and it is minimal: at each `div` node the divisor's **denominator** bipoly
must not vanish. Nothing is asked at the other nodes. -/
def DivDenomsOK : FCtx → Real → Real → Prop
  | .hole,    _, _ => True
  | .const _, _, _ => True
  | .var,     _, _ => True
  | .add a b, x, y => DivDenomsOK a x y ∧ DivDenomsOK b x y
  | .sub a b, x, y => DivDenomsOK a x y ∧ DivDenomsOK b x y
  | .mul a b, x, y => DivDenomsOK a x y ∧ DivDenomsOK b x y
  | .div a b, x, y => DivDenomsOK a x y ∧ DivDenomsOK b x y ∧ bipev (ctxFrac b).2 x y ≠ 0

private theorem ne_zero_left {a b : Real} (h : a * b ≠ 0) : a ≠ 0 := by
  intro hz; exact h (by rw [hz]; exact zero_mul b)

private theorem ne_zero_right {a b : Real} (h : a * b ≠ 0) : b ≠ 0 := by
  intro hz; exact h (by rw [hz]; exact mul_zero a)

/-- **The rational normal form.** `C.eval x y · D(x,y) = N(x,y)` wherever the denominators are
genuine. -/
theorem ctxFrac_eval : ∀ (C : FCtx) (x y : Real), DivDenomsOK C x y →
    bipev (ctxFrac C).2 x y ≠ 0 →
      C.eval x y * bipev (ctxFrac C).2 x y = bipev (ctxFrac C).1 x y := by
  intro C
  induction C with
  | hole =>
      intro x y _ _
      show y * (pev [1] x + y * 0) = pev [] x + y * (pev [1] x + y * 0)
      show y * ((1 + x * 0) + y * 0) = 0 + y * ((1 + x * 0) + y * 0)
      mach_ring
  | const c =>
      intro x y _ _
      show c * (pev [1] x + y * 0) = pev [c] x + y * 0
      show c * ((1 + x * 0) + y * 0) = (c + x * 0) + y * 0
      mach_ring
  | var =>
      intro x y _ _
      show x * (pev [1] x + y * 0) = pev [0, 1] x + y * 0
      show x * ((1 + x * 0) + y * 0) = (0 + x * (1 + x * 0)) + y * 0
      mach_ring
  | add a b iha ihb =>
      intro x y hok hD
      have hD' : bipev (ctxFrac a).2 x y * bipev (ctxFrac b).2 x y ≠ 0 := by
        rw [← bipev_bimul]; exact hD
      show (a.eval x y + b.eval x y) * bipev (bimul (ctxFrac a).2 (ctxFrac b).2) x y
          = bipev (biadd (bimul (ctxFrac a).1 (ctxFrac b).2)
                         (bimul (ctxFrac b).1 (ctxFrac a).2)) x y
      rw [bipev_bimul, bipev_biadd, bipev_bimul, bipev_bimul,
          ← iha x y hok.1 (ne_zero_left hD'), ← ihb x y hok.2 (ne_zero_right hD')]
      mach_mpoly [a.eval x y, b.eval x y, bipev (ctxFrac a).2 x y, bipev (ctxFrac b).2 x y]
  | sub a b iha ihb =>
      intro x y hok hD
      have hD' : bipev (ctxFrac a).2 x y * bipev (ctxFrac b).2 x y ≠ 0 := by
        rw [← bipev_bimul]; exact hD
      show (a.eval x y - b.eval x y) * bipev (bimul (ctxFrac a).2 (ctxFrac b).2) x y
          = bipev (bisub (bimul (ctxFrac a).1 (ctxFrac b).2)
                         (bimul (ctxFrac b).1 (ctxFrac a).2)) x y
      rw [bipev_bimul, bipev_bisub, bipev_bimul, bipev_bimul,
          ← iha x y hok.1 (ne_zero_left hD'), ← ihb x y hok.2 (ne_zero_right hD')]
      mach_mpoly [a.eval x y, b.eval x y, bipev (ctxFrac a).2 x y, bipev (ctxFrac b).2 x y]
  | mul a b iha ihb =>
      intro x y hok hD
      have hD' : bipev (ctxFrac a).2 x y * bipev (ctxFrac b).2 x y ≠ 0 := by
        rw [← bipev_bimul]; exact hD
      show (a.eval x y * b.eval x y) * bipev (bimul (ctxFrac a).2 (ctxFrac b).2) x y
          = bipev (bimul (ctxFrac a).1 (ctxFrac b).1) x y
      rw [bipev_bimul, bipev_bimul,
          ← iha x y hok.1 (ne_zero_left hD'), ← ihb x y hok.2 (ne_zero_right hD')]
      mach_mpoly [a.eval x y, b.eval x y, bipev (ctxFrac a).2 x y, bipev (ctxFrac b).2 x y]
  | div a b iha ihb =>
      intro x y hok hD
      have hD' : bipev (ctxFrac a).2 x y * bipev (ctxFrac b).1 x y ≠ 0 := by
        rw [← bipev_bimul]; exact hD
      show (a.eval x y / b.eval x y) * bipev (bimul (ctxFrac a).2 (ctxFrac b).1) x y
          = bipev (bimul (ctxFrac a).1 (ctxFrac b).2) x y
      rw [bipev_bimul, bipev_bimul]
      have hb := ihb x y hok.2.1 hok.2.2
      have hbne : b.eval x y ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at hb
        exact (ne_zero_right hD') hb.symm
      have ha := iha x y hok.1 (ne_zero_left hD')
      rw [div_def _ _ hbne, ← hb, ← ha]
      have e : a.eval x y * (1 / b.eval x y)
            * (bipev (ctxFrac a).2 x y * (b.eval x y * bipev (ctxFrac b).2 x y))
          = (a.eval x y * bipev (ctxFrac a).2 x y * bipev (ctxFrac b).2 x y)
            * (b.eval x y * (1 / b.eval x y)) := by
        mach_mpoly [a.eval x y, 1 / b.eval x y, bipev (ctxFrac a).2 x y, b.eval x y,
                    bipev (ctxFrac b).2 x y]
      rw [e, mul_inv _ hbne]
      mach_ring

private theorem bipev_const_one (x y : Real) : bipev [[(1 : Real)]] x y = 1 := by
  show (1 + x * 0) + y * 0 = 1
  mach_ring

private theorem one_ne_zero' : (1 : Real) ≠ 0 := fun h => zero_ne_one_ax h.symm

/-- **Discrimination for `div`.** The side condition is satisfiable and the normal form fires on a
context that actually contains a division — so `ctxFrac_eval` is not a theorem about div-free
contexts in disguise. -/
theorem ctxFrac_div_specimen (x y : Real) :
    (FCtx.div FCtx.var (FCtx.const 1)).eval x y
      * bipev (ctxFrac (FCtx.div FCtx.var (FCtx.const 1))).2 x y
    = bipev (ctxFrac (FCtx.div FCtx.var (FCtx.const 1))).1 x y := by
  refine ctxFrac_eval _ x y ⟨trivial, trivial, ?_⟩ ?_
  · show bipev [[(1 : Real)]] x y ≠ 0
    rw [bipev_const_one]; exact one_ne_zero'
  · show bipev (bimul [[(1 : Real)]] [[(1 : Real)]]) x y ≠ 0
    rw [bipev_bimul, bipev_const_one]
    have e : (1 : Real) * 1 = 1 := by mach_ring
    rw [e]; exact one_ne_zero'

private theorem eq_zero_of_mul_eq_zero {a b : Real} (h : a * b = 0) (hb : b ≠ 0) : a = 0 := by
  rcases Classical.em (a = 0) with ha | ha
  · exact ha
  · exact absurd h (mul_ne_zero ha hb)

/-! ## The reduction, for arbitrary contexts

With the rational normal form the dichotomy transfers to **every** context, not just the div-free
ones — at the price of the side conditions holding along the ray, which is exactly the price
division charges and no more. -/

/-- **`OneQueryDichotomy` for arbitrary contexts, given the bivariate dichotomy.** The two extra
hypotheses are the `div` side conditions evaluated along the curve; for a div-free `C` they are
vacuous and this collapses to `oneQueryDichotomy_divFree_of_bipoly`. -/
theorem oneQueryDichotomy_of_bipoly (h : BipolyDichotomyAlong) :
    ∀ (C : FCtx) (P Q : List Real) (X : Real), 1 ≤ X →
      (∀ x : Real, X ≤ x → pev Q x ≠ 0) →
      (∀ x : Real, X ≤ x → DivDenomsOK C x (Fbasis (pev P x / pev Q x))) →
      (∀ x : Real, X ≤ x → bipev (ctxFrac C).2 x (Fbasis (pev P x / pev Q x)) ≠ 0) →
        EvZeroF (fun x => FCtx.eval C x (Fbasis (pev P x / pev Q x)))
        ∨ ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
            FCtx.eval C x (Fbasis (pev P x / pev Q x)) ≠ 0 := by
  intro C P Q X hX hQ hok hD
  rcases h (ctxFrac C).1 P Q X hX hQ with ⟨Z, hZ, hz⟩ | ⟨Y, hY, hn⟩
  · obtain ⟨W, hW, h0, h1⟩ := two_bounds' hX hZ
    refine Or.inl ⟨W, hW, fun x hx => ?_⟩
    have hid := ctxFrac_eval C x (Fbasis (pev P x / pev Q x))
      (hok x (le_trans h0 hx)) (hD x (le_trans h0 hx))
    have hNz : bipev (ctxFrac C).1 x (Fbasis (pev P x / pev Q x)) = 0 := hz x (le_trans h1 hx)
    rw [hNz] at hid
    show FCtx.eval C x (Fbasis (pev P x / pev Q x)) = 0
    exact eq_zero_of_mul_eq_zero hid (hD x (le_trans h0 hx))
  · obtain ⟨W, hW, h0, h1⟩ := two_bounds' hX hY
    refine Or.inr ⟨W, hW, fun x hx => ?_⟩
    have hid := ctxFrac_eval C x (Fbasis (pev P x / pev Q x))
      (hok x (le_trans h0 hx)) (hD x (le_trans h0 hx))
    have hNn : bipev (ctxFrac C).1 x (Fbasis (pev P x / pev Q x)) ≠ 0 := hn x (le_trans h1 hx)
    show FCtx.eval C x (Fbasis (pev P x / pev Q x)) ≠ 0
    intro hzero
    rw [hzero, zero_mul] at hid
    exact hNn hid.symm

end MachLib
