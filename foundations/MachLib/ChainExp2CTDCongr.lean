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

/-! ### Formal partial derivatives (the `cTD₂ = ∂x + y₀·∂y₀` route to full `y₁`-free congruence)

`chainTotalDeriv` respects eval-equality via the decomposition `cTD₂ r = ∂x r + y₀·∂y₀ r` (on `y₁`-free
`r`). Each formal partial is eval-correct as an honest `HasDerivAt` (varying one coordinate), so a poly
that vanishes everywhere has vanishing partials (derivative of the constant-`0` function), hence a
vanishing `cTD₂`. This is the general-env congruence the chain-rule-at-chain-values lemma cannot give. -/

/-- Formal `y₀`-partial derivative. -/
noncomputable def partialY0 : MultiPoly 2 → MultiPoly 2
  | .const _ => .const 0
  | .varX => .const 0
  | .varY j => if j = (⟨0, by omega⟩ : Fin 2) then .const 1 else .const 0
  | .add p q => .add (partialY0 p) (partialY0 q)
  | .sub p q => .sub (partialY0 p) (partialY0 q)
  | .mul p q => .add (.mul (partialY0 p) q) (.mul p (partialY0 q))

/-- Formal `x`-partial derivative. -/
noncomputable def partialX : MultiPoly 2 → MultiPoly 2
  | .const _ => .const 0
  | .varX => .const 1
  | .varY _ => .const 0
  | .add p q => .add (partialX p) (partialX q)
  | .sub p q => .sub (partialX p) (partialX q)
  | .mul p q => .add (.mul (partialX p) q) (.mul p (partialX q))

/-- Updating `env` at index `0` with its own value is a no-op. -/
private theorem upd0_self (env : Fin 2 → Real) :
    (fun j => if j = (⟨0, by omega⟩ : Fin 2) then env (⟨0, by omega⟩ : Fin 2) else env j) = env := by
  funext j; by_cases h : j = (⟨0, by omega⟩ : Fin 2)
  · rw [if_pos h, h]
  · rw [if_neg h]

/-- Updating `env` at index `1` with its own value is a no-op. -/
private theorem upd1_self (env : Fin 2 → Real) :
    (fun j => if j = (⟨1, by omega⟩ : Fin 2) then env (⟨1, by omega⟩ : Fin 2) else env j) = env := by
  funext j; by_cases h : j = (⟨1, by omega⟩ : Fin 2)
  · rw [if_pos h, h]
  · rw [if_neg h]

/-- **`partialY0` is eval-correct**: it is the derivative of `eval r` in the `0`-th coordinate. -/
theorem hasDerivAt_eval_partialY0 (r : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    HasDerivAt
      (fun v => MultiPoly.eval r x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j))
      (MultiPoly.eval (partialY0 r) x env) (env (⟨0, by omega⟩ : Fin 2)) := by
  induction r with
  | const c =>
    have hf : (fun v => MultiPoly.eval (MultiPoly.const c) x
                (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j)) = fun _ => c := rfl
    rw [hf]; show HasDerivAt (fun _ => c) 0 _; exact MachLib.Real.HasDerivAt_const c _
  | varX =>
    have hf : (fun v => MultiPoly.eval MultiPoly.varX x
                (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j)) = fun _ => x := rfl
    rw [hf]; show HasDerivAt (fun _ => x) 0 _; exact MachLib.Real.HasDerivAt_const x _
  | varY j =>
    by_cases hj : j = (⟨0, by omega⟩ : Fin 2)
    · subst hj
      have hf : (fun w => MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) x
                  (fun j => if j = (⟨0, by omega⟩ : Fin 2) then w else env j)) = fun w => w := by
        funext w
        show (if (⟨0, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2) then w
              else env (⟨0, by omega⟩ : Fin 2)) = w
        rw [if_pos rfl]
      rw [hf]
      show HasDerivAt (fun w => w) (1 : Real) (env (⟨0, by omega⟩ : Fin 2))
      exact MachLib.Real.HasDerivAt_id _
    · have hf : (fun w => MultiPoly.eval (MultiPoly.varY j) x
                  (fun j' => if j' = (⟨0, by omega⟩ : Fin 2) then w else env j')) = fun _ => env j := by
        funext w
        show (if j = (⟨0, by omega⟩ : Fin 2) then w else env j) = env j
        rw [if_neg hj]
      rw [hf]
      have hp0 : MultiPoly.eval (partialY0 (MultiPoly.varY j)) x env = 0 := by
        show MultiPoly.eval
          (if j = (⟨0, by omega⟩ : Fin 2) then MultiPoly.const 1 else MultiPoly.const 0) x env = 0
        rw [if_neg hj]; rfl
      rw [hp0]
      exact MachLib.Real.HasDerivAt_const (env j) (env (⟨0, by omega⟩ : Fin 2))
  | add p q ihp ihq =>
    have hf : (fun v => MultiPoly.eval (MultiPoly.add p q) x
                (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j))
            = fun v => MultiPoly.eval p x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j)
                + MultiPoly.eval q x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j) := by
      funext v; exact MultiPoly.eval_add p q x _
    rw [hf]
    show HasDerivAt _ (MultiPoly.eval (partialY0 (MultiPoly.add p q)) x env) _
    rw [show MultiPoly.eval (partialY0 (MultiPoly.add p q)) x env
          = MultiPoly.eval (partialY0 p) x env + MultiPoly.eval (partialY0 q) x env
        from MultiPoly.eval_add _ _ x env]
    exact MachLib.Real.HasDerivAt_add _ _ _ _ _ ihp ihq
  | sub p q ihp ihq =>
    have hf : (fun v => MultiPoly.eval (MultiPoly.sub p q) x
                (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j))
            = fun v => MultiPoly.eval p x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j)
                - MultiPoly.eval q x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j) := by
      funext v; exact MultiPoly.eval_sub p q x _
    rw [hf]
    show HasDerivAt _ (MultiPoly.eval (partialY0 (MultiPoly.sub p q)) x env) _
    rw [show MultiPoly.eval (partialY0 (MultiPoly.sub p q)) x env
          = MultiPoly.eval (partialY0 p) x env - MultiPoly.eval (partialY0 q) x env
        from MultiPoly.eval_sub _ _ x env]
    exact MachLib.Real.HasDerivAt_sub _ _ _ _ _ ihp ihq
  | mul p q ihp ihq =>
    have hf : (fun v => MultiPoly.eval (MultiPoly.mul p q) x
                (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j))
            = fun v => MultiPoly.eval p x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j)
                * MultiPoly.eval q x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j) := by
      funext v; exact MultiPoly.eval_mul p q x _
    rw [hf]
    have hmul := MachLib.Real.HasDerivAt_mul
      (fun v => MultiPoly.eval p x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j))
      (fun v => MultiPoly.eval q x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j))
      (MultiPoly.eval (partialY0 p) x env) (MultiPoly.eval (partialY0 q) x env)
      (env (⟨0, by omega⟩ : Fin 2)) ihp ihq
    dsimp only [] at hmul
    rw [upd0_self] at hmul
    rw [show MultiPoly.eval (partialY0 (MultiPoly.mul p q)) x env
          = MultiPoly.eval (partialY0 p) x env * MultiPoly.eval q x env
            + MultiPoly.eval p x env * MultiPoly.eval (partialY0 q) x env from by
        rw [show partialY0 (MultiPoly.mul p q)
              = MultiPoly.add (MultiPoly.mul (partialY0 p) q) (MultiPoly.mul p (partialY0 q)) from rfl,
            MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul]]
    exact hmul

/-- **`partialX` is eval-correct**: it is the derivative of `eval r` in the `x` argument. -/
theorem hasDerivAt_eval_partialX (r : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    HasDerivAt (fun t => MultiPoly.eval r t env) (MultiPoly.eval (partialX r) x env) x := by
  induction r with
  | const c =>
    have hf : (fun t => MultiPoly.eval (MultiPoly.const c) t env) = fun _ => c := rfl
    rw [hf]; show HasDerivAt (fun _ => c) (0 : Real) x; exact MachLib.Real.HasDerivAt_const c x
  | varX =>
    have hf : (fun t => MultiPoly.eval MultiPoly.varX t env) = fun t => t := rfl
    rw [hf]; show HasDerivAt (fun t => t) (1 : Real) x; exact MachLib.Real.HasDerivAt_id x
  | varY j =>
    have hf : (fun t => MultiPoly.eval (MultiPoly.varY j) t env) = fun _ => env j := rfl
    rw [hf]; show HasDerivAt (fun _ => env j) (0 : Real) x
    exact MachLib.Real.HasDerivAt_const (env j) x
  | add p q ihp ihq =>
    have hf : (fun t => MultiPoly.eval (MultiPoly.add p q) t env)
            = fun t => MultiPoly.eval p t env + MultiPoly.eval q t env := by
      funext t; exact MultiPoly.eval_add p q t env
    rw [hf]
    rw [show MultiPoly.eval (partialX (MultiPoly.add p q)) x env
          = MultiPoly.eval (partialX p) x env + MultiPoly.eval (partialX q) x env
        from MultiPoly.eval_add _ _ x env]
    exact MachLib.Real.HasDerivAt_add _ _ _ _ _ ihp ihq
  | sub p q ihp ihq =>
    have hf : (fun t => MultiPoly.eval (MultiPoly.sub p q) t env)
            = fun t => MultiPoly.eval p t env - MultiPoly.eval q t env := by
      funext t; exact MultiPoly.eval_sub p q t env
    rw [hf]
    rw [show MultiPoly.eval (partialX (MultiPoly.sub p q)) x env
          = MultiPoly.eval (partialX p) x env - MultiPoly.eval (partialX q) x env
        from MultiPoly.eval_sub _ _ x env]
    exact MachLib.Real.HasDerivAt_sub _ _ _ _ _ ihp ihq
  | mul p q ihp ihq =>
    have hf : (fun t => MultiPoly.eval (MultiPoly.mul p q) t env)
            = fun t => MultiPoly.eval p t env * MultiPoly.eval q t env := by
      funext t; exact MultiPoly.eval_mul p q t env
    rw [hf]
    have hmul := MachLib.Real.HasDerivAt_mul
      (fun t => MultiPoly.eval p t env) (fun t => MultiPoly.eval q t env)
      (MultiPoly.eval (partialX p) x env) (MultiPoly.eval (partialX q) x env) x ihp ihq
    dsimp only [] at hmul
    rw [show MultiPoly.eval (partialX (MultiPoly.mul p q)) x env
          = MultiPoly.eval (partialX p) x env * MultiPoly.eval q x env
            + MultiPoly.eval p x env * MultiPoly.eval (partialX q) x env from by
        rw [show partialX (MultiPoly.mul p q)
              = MultiPoly.add (MultiPoly.mul (partialX p) q) (MultiPoly.mul p (partialX q)) from rfl,
            MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul]]
    exact hmul

/-- **The decomposition `cTD₂ r = ∂x r + y₀·∂y₀ r` (at eval), for `y₁`-free `r`.** (Fails on `varY 1`,
whose total derivative injects `y₀·y₁`; hence the `degreeY₁ r = 0` hypothesis.) -/
theorem cTD_decomp_y1free (r : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) r = 0 →
    MultiPoly.eval (chainTotalDeriv (IterExpChain 2) r) x env
    = MultiPoly.eval (partialX r) x env
      + env (⟨0, by omega⟩ : Fin 2) * MultiPoly.eval (partialY0 r) x env := by
  induction r with
  | const c => intro _; show (0 : Real) = 0 + env (⟨0, by omega⟩ : Fin 2) * 0; mach_ring
  | varX => intro _; show (1 : Real) = 1 + env (⟨0, by omega⟩ : Fin 2) * 0; mach_ring
  | varY j =>
    intro hy1
    by_cases hj : j = (⟨0, by omega⟩ : Fin 2)
    · rw [hj]
      show env (⟨0, by omega⟩ : Fin 2)
         = 0 + env (⟨0, by omega⟩ : Fin 2) * 1
      mach_ring
    · exfalso
      by_cases hj1 : j = (⟨1, by omega⟩ : Fin 2)
      · rw [hj1] at hy1
        have h1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
                    (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)) = 1 := rfl
        rw [h1] at hy1
        exact Nat.one_ne_zero hy1
      · have h0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
        have h1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
        have := j.isLt
        omega
  | add p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h' : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = 0 := hy1
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
               ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                         (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) := Nat.le_max_left _ _
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h' : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = 0 := hy1
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
               ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                         (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) := Nat.le_max_right _ _
      omega
    show MultiPoly.eval (MultiPoly.add (chainTotalDeriv (IterExpChain 2) p)
            (chainTotalDeriv (IterExpChain 2) q)) x env = _
    rw [MultiPoly.eval_add, ihp hp1, ihq hq1,
        show partialX (MultiPoly.add p q) = MultiPoly.add (partialX p) (partialX q) from rfl,
        show partialY0 (MultiPoly.add p q) = MultiPoly.add (partialY0 p) (partialY0 q) from rfl,
        MultiPoly.eval_add, MultiPoly.eval_add]
    generalize MultiPoly.eval (partialX p) x env = Xp
    generalize MultiPoly.eval (partialX q) x env = Xq
    generalize MultiPoly.eval (partialY0 p) x env = Yp
    generalize MultiPoly.eval (partialY0 q) x env = Yq
    generalize env (⟨0, by omega⟩ : Fin 2) = E
    mach_ring
  | sub p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h' : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = 0 := hy1
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
               ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                         (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) := Nat.le_max_left _ _
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h' : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = 0 := hy1
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
               ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                         (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) := Nat.le_max_right _ _
      omega
    show MultiPoly.eval (MultiPoly.sub (chainTotalDeriv (IterExpChain 2) p)
            (chainTotalDeriv (IterExpChain 2) q)) x env = _
    rw [MultiPoly.eval_sub, ihp hp1, ihq hq1,
        show partialX (MultiPoly.sub p q) = MultiPoly.sub (partialX p) (partialX q) from rfl,
        show partialY0 (MultiPoly.sub p q) = MultiPoly.sub (partialY0 p) (partialY0 q) from rfl,
        MultiPoly.eval_sub, MultiPoly.eval_sub]
    generalize MultiPoly.eval (partialX p) x env = Xp
    generalize MultiPoly.eval (partialX q) x env = Xq
    generalize MultiPoly.eval (partialY0 p) x env = Yp
    generalize MultiPoly.eval (partialY0 q) x env = Yq
    generalize env (⟨0, by omega⟩ : Fin 2) = E
    mach_ring
  | mul p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
              + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
              + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    show MultiPoly.eval (MultiPoly.add
            (MultiPoly.mul (chainTotalDeriv (IterExpChain 2) p) q)
            (MultiPoly.mul p (chainTotalDeriv (IterExpChain 2) q))) x env = _
    rw [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul, ihp hp1, ihq hq1,
        show partialX (MultiPoly.mul p q)
              = MultiPoly.add (MultiPoly.mul (partialX p) q) (MultiPoly.mul p (partialX q)) from rfl,
        show partialY0 (MultiPoly.mul p q)
              = MultiPoly.add (MultiPoly.mul (partialY0 p) q) (MultiPoly.mul p (partialY0 q)) from rfl,
        MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul,
        MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul]
    generalize MultiPoly.eval (partialX p) x env = Xp
    generalize MultiPoly.eval (partialX q) x env = Xq
    generalize MultiPoly.eval (partialY0 p) x env = Yp
    generalize MultiPoly.eval (partialY0 q) x env = Yq
    generalize MultiPoly.eval p x env = P
    generalize MultiPoly.eval q x env = Q
    generalize env (⟨0, by omega⟩ : Fin 2) = E
    mach_ring

/-- **`chainTotalDeriv` kills eval-zero, `y₁`-free case.** If a `y₁`-free `r` evaluates to `0`
everywhere, so does `cTD₂ r` — via the decomposition and eval-correctness of the two partials. -/
theorem eval_cTD_zero_of_y1free (r : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) r = 0)
    (hz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval r x env = 0) :
    ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (chainTotalDeriv (IterExpChain 2) r) x env = 0 := by
  intro x env
  rw [cTD_decomp_y1free r x env hy1]
  have hx : MultiPoly.eval (partialX r) x env = 0 := by
    have hd := hasDerivAt_eval_partialX r x env
    have hf : (fun t => MultiPoly.eval r t env) = fun _ => (0 : Real) :=
      funext (fun t => hz t env)
    rw [hf] at hd
    exact MachLib.Real.HasDerivAt_unique (fun _ => (0 : Real)) (MultiPoly.eval (partialX r) x env) 0 x
      hd (MachLib.Real.HasDerivAt_const 0 x)
  have hy : MultiPoly.eval (partialY0 r) x env = 0 := by
    have hd := hasDerivAt_eval_partialY0 r x env
    have hf : (fun v => MultiPoly.eval r x
                (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j))
            = fun _ => (0 : Real) := funext (fun v => hz x _)
    rw [hf] at hd
    exact MachLib.Real.HasDerivAt_unique (fun _ => (0 : Real)) (MultiPoly.eval (partialY0 r) x env) 0
      (env (⟨0, by omega⟩ : Fin 2)) hd (MachLib.Real.HasDerivAt_const 0 _)
  rw [hx, hy]; mach_ring

/-- **`chainTotalDeriv` eval-congruence for `y₁`-free polynomials** — the seam-A result: eval-equal
`y₁`-free polys have eval-equal chain total derivatives. This lets a phantom-top `lcY₁ p` be replaced
by its canonical trim in the reduce descent. -/
theorem eval_cTD_congr_y1free (a b : MultiPoly 2)
    (hya : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a = 0)
    (hyb : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b = 0)
    (heq : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval a x env = MultiPoly.eval b x env) :
    ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (chainTotalDeriv (IterExpChain 2) a) x env
        = MultiPoly.eval (chainTotalDeriv (IterExpChain 2) b) x env := by
  have hsub1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub a b) = 0 := by
    show Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a)
                 (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b) = 0
    rw [hya, hyb]; exact Nat.max_self 0
  have hz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval (MultiPoly.sub a b) x env = 0 := by
    intro x env; rw [MultiPoly.eval_sub, heq x env]; mach_ring
  intro x env
  have h0 := eval_cTD_zero_of_y1free (MultiPoly.sub a b) hsub1 hz x env
  rw [show chainTotalDeriv (IterExpChain 2) (MultiPoly.sub a b)
        = MultiPoly.sub (chainTotalDeriv (IterExpChain 2) a) (chainTotalDeriv (IterExpChain 2) b)
      from rfl, MultiPoly.eval_sub] at h0
  calc MultiPoly.eval (chainTotalDeriv (IterExpChain 2) a) x env
      = (MultiPoly.eval (chainTotalDeriv (IterExpChain 2) a) x env
          - MultiPoly.eval (chainTotalDeriv (IterExpChain 2) b) x env)
        + MultiPoly.eval (chainTotalDeriv (IterExpChain 2) b) x env := by mach_ring
    _ = 0 + MultiPoly.eval (chainTotalDeriv (IterExpChain 2) b) x env := by rw [h0]
    _ = MultiPoly.eval (chainTotalDeriv (IterExpChain 2) b) x env := by mach_ring

end MachLib.ChainExp2CTDCongr
