import MachLib.ChainExp2LcY0CTD
import MachLib.ChainExp2YPIT

/-!
# `chainTotalDeriv` eval-congruence — the `y`-free (pure-x) base case

The phantom-top case of the chain-2 reduce descent needs `chainTotalDeriv` to respect eval-equality
(`eval a = eval b ⇒ eval(cTD₂ a) = eval(cTD₂ b)`) for `y₁`-free polynomials, so that a phantom `lcY₁ p`
can be replaced by its canonical trim. That full statement (with a `y₀` variable) needs the `y₀`-coefficient
convolution action of `cTD₂` — a large sub-arc. This file supplies its **base case**: congruence for
`y`-free (pure-`x`) polynomials, where the argument is clean.

For a `y`-free `a`, `cTD₂ a` is `y`-free, its evaluation is env-independent, and equals — via the `mP2PFL`
bridge — the ordinary `Poly` derivative of `a` projected to `x`. So `eval a ≡ 0` (whence the projected
polynomial is the zero function) forces `eval(cTD₂ a) ≡ 0` by uniqueness of the derivative of the constant
function. Reusable: this is exactly the per-coefficient fact the full `y₁`-free congruence will call on
(each `y₀`-coefficient of a `y₁`-free poly is `y`-free).

Path B: `ChainExp2SDR` + single-exp framework untouched.
-/

namespace MachLib.ChainExp2CTDCongr

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2SDR
open MachLib.PolynomialCanonical
open MachLib.PolynomialRootCount
open MachLib.PolynomialEvidence (Poly)
open MachLib.ChainExp2LcY0CTD
open MachLib.ChainExp2YPIT

/-- **A `Poly` that evaluates to `0` everywhere has a derivative that evaluates to `0` everywhere.**
Via `HasDerivAt` uniqueness: the derivative of the constant-`0` function is `0`. -/
theorem poly_eval_polyDerivative_zero (P : Poly) (h : ∀ x : Real, Poly.eval P x = 0) :
    ∀ x : Real, Poly.eval (polyDerivative P) x = 0 := by
  intro x
  have hp : HasDerivAt (Poly.eval P) (Poly.eval (polyDerivative P) x) x :=
    polyHasDerivAt_eval P x
  have hfun : Poly.eval P = fun _ => (0 : Real) := funext h
  rw [hfun] at hp
  have hc : HasDerivAt (fun _ => (0 : Real)) 0 x := MachLib.Real.HasDerivAt_const 0 x
  exact MachLib.Real.HasDerivAt_unique (fun _ => (0 : Real))
    (Poly.eval (polyDerivative P) x) 0 x hp hc

/-- **`chainTotalDeriv` eval-congruence, `y`-free base case.** If a `y`-free (both `degreeY ⟨0⟩ = 0` and
`degreeY ⟨1⟩ = 0`) polynomial `a` evaluates to `0` everywhere, so does `cTD₂ a`. -/
theorem eval_cTD_zero_of_yfree (a : MultiPoly 2)
    (hy0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) a = 0)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a = 0)
    (hz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval a x env = 0) :
    ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (chainTotalDeriv (IterExpChain 2) a) x env = 0 := by
  -- cTD₂ a is y-free.
  have hd0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
               (chainTotalDeriv (IterExpChain 2) a) = 0 := by
    rw [degreeY0_cTD_eq_of_y1free a hy1, hy0]
  have hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
               (chainTotalDeriv (IterExpChain 2) a) = 0 := by
    rw [degreeY1_chainTotalDeriv_eq_IterExp2 a, hy1]
  -- the projected polynomial evaluates to 0 everywhere → its derivative does too.
  have hP : ∀ y : Real, Poly.eval (multiPolyToPolyForLex a) y = 0 := by
    intro y; rw [eval_multiPolyToPolyForLex_eq_eval_zero]; exact hz y (fun _ => 0)
  have hderiv := poly_eval_polyDerivative_zero (multiPolyToPolyForLex a) hP
  intro x env
  -- eval(cTD₂ a) x env is env-independent (y-free); reduce to env 0.
  let e' : Fin 2 → Real := fun j => if j = (⟨0, by omega⟩ : Fin 2) then 0 else env j
  have hstep0 : MultiPoly.eval (chainTotalDeriv (IterExpChain 2) a) x env
              = MultiPoly.eval (chainTotalDeriv (IterExpChain 2) a) x e' := by
    apply eval_eq_of_env_agree_off (⟨0, by omega⟩ : Fin 2) _ x env e' _ hd0
    intro j hj; show env j = (if j = (⟨0, by omega⟩ : Fin 2) then 0 else env j); rw [if_neg hj]
  have hstep1 : MultiPoly.eval (chainTotalDeriv (IterExpChain 2) a) x e'
              = MultiPoly.eval (chainTotalDeriv (IterExpChain 2) a) x (fun _ => 0) := by
    apply eval_eq_of_env_agree_off (⟨1, by omega⟩ : Fin 2) _ x e' (fun _ => 0) _ hd1
    intro j hj
    -- j ≠ 1 in Fin 2 ⇒ j = 0 ⇒ e' j = 0
    show (if j = (⟨0, by omega⟩ : Fin 2) then 0 else env j) = 0
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ => rw [if_pos rfl]
    | 1, _ => exact absurd rfl hj
  rw [hstep0, hstep1, ← eval_multiPolyToPolyForLex_eq_eval_zero,
      multiPolyToPolyForLex_eval_chainTotalDeriv_IterExp]
  exact hderiv x

end MachLib.ChainExp2CTDCongr
