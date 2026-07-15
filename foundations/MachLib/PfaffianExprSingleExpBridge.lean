import MachLib.ChainExp2SingleExpUnconditional
import MachLib.Pfaffian

/-!
# MachLib.PfaffianExprSingleExpBridge — legacy `PfaffianExpr` → `PfaffianFn`, single-exp fragment

The sole live Khovanskii axiom `zero_count_bound_classical` is stated over the
*inductive* `PfaffianExpr`/`PfaffianFunction` type (Pfaffian.lean). The
constructive, axiom-clean Khovanskii bound proved this session
(`ChainExp2PathC.singleExp_khovanskii_bound_unconditional`) lives on the
*chain-explicit* `PfaffianFn`/`MultiPoly` type. This module builds the bridge for
the **single-exponential fragment** of `PfaffianExpr` — expressions over
`const / var / exp_atom / +,-,·` — translating them to a `MultiPoly 1` over
`SingleExpChain` and proving eval-agreement.

The payoff (`expPoly_pfaffianFunction_zero_bound`) is an **axiom-clean** Khovanskii
zero-count bound for any single-exponential `PfaffianFunction`, obtained *without*
`zero_count_bound_classical` — a first concrete reduction of the axiom's real
footprint (the `sin`/`cos`-not-in-EML consumers via `eml_pfaffian`) onto the
constructive pipeline, for the exp fragment.

The general bridge (adding `log_atom`, `comp`, `inv`, and taller chains) is the
remaining multi-session work — see AXIOM_AUDIT_V2.md §2c.
-/

namespace MachLib
namespace PfaffianExprSingleExpBridge

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod

/-- The single-exponential fragment of `PfaffianExpr`: no `log_atom`, `comp`,
or `inv`. Exactly the expressions representable as a polynomial in `(x, eˣ)`. -/
inductive IsExpPoly : MachLib.Real.PfaffianExpr → Prop
  | const (c : MachLib.Real) : IsExpPoly (.const c)
  | var : IsExpPoly .var
  | exp_atom : IsExpPoly .exp_atom
  | add {a b} : IsExpPoly a → IsExpPoly b → IsExpPoly (.add a b)
  | sub {a b} : IsExpPoly a → IsExpPoly b → IsExpPoly (.sub a b)
  | mul {a b} : IsExpPoly a → IsExpPoly b → IsExpPoly (.mul a b)

/-- Translate a `PfaffianExpr` to a `MultiPoly 1` over `SingleExpChain`:
`exp_atom ↦ y₀` (the chain variable `eˣ`), everything else structurally.
Out-of-fragment constructors (`log_atom`/`comp`/`inv`) map to `0` — the
eval-agreement theorem is stated only under `IsExpPoly`, so they never matter. -/
noncomputable def toMP1 : MachLib.Real.PfaffianExpr → MultiPoly 1
  | .const c   => MultiPoly.const c
  | .var       => MultiPoly.varX
  | .exp_atom  => MultiPoly.varY ⟨0, by omega⟩
  | .add a b   => MultiPoly.add (toMP1 a) (toMP1 b)
  | .sub a b   => MultiPoly.sub (toMP1 a) (toMP1 b)
  | .mul a b   => MultiPoly.mul (toMP1 a) (toMP1 b)
  | .log_atom  => MultiPoly.const 0
  | .comp _ _  => MultiPoly.const 0
  | .inv _     => MultiPoly.const 0

/-- **Eval-agreement.** On the single-exp fragment, the `MultiPoly 1`
translation evaluated over `SingleExpChain`'s chain values (`y₀ = eˣ`) equals the
original `PfaffianExpr`'s evaluation. -/
theorem eval_toMP1 (e : MachLib.Real.PfaffianExpr) (he : IsExpPoly e) (x : Real) :
    MultiPoly.eval (toMP1 e) x (SingleExpChain.chainValues x) = e.eval x := by
  induction he with
  | const c => rfl
  | var => rfl
  | exp_atom => rfl
  | add a b iha ihb =>
    show MultiPoly.eval (toMP1 _) x _ + MultiPoly.eval (toMP1 _) x _ = _ + _
    rw [iha, ihb]
  | sub a b iha ihb =>
    show MultiPoly.eval (toMP1 _) x _ - MultiPoly.eval (toMP1 _) x _ = _ - _
    rw [iha, ihb]
  | mul a b iha ihb =>
    show MultiPoly.eval (toMP1 _) x _ * MultiPoly.eval (toMP1 _) x _ = _ * _
    rw [iha, ihb]

/-- The bridged PfaffianFn for a single-exp `PfaffianExpr`: `⟨1, SingleExpChain, toMP1 e⟩`. -/
noncomputable def toPfaffianFn (e : MachLib.Real.PfaffianExpr) : PfaffianFn :=
  ⟨1, SingleExpChain, toMP1 e⟩

/-- The bridged PfaffianFn evaluates to the original expression (on the fragment). -/
theorem toPfaffianFn_eval (e : MachLib.Real.PfaffianExpr) (he : IsExpPoly e) (x : Real) :
    (toPfaffianFn e).eval x = e.eval x :=
  eval_toMP1 e he x

/-- **Axiom-clean Khovanskii zero bound for single-exponential `PfaffianFunction`s.**
For `f = ⟨e⟩` with `e` in the exp fragment, the zeros of `f` on `(a, b)` are
bounded — obtained from `singleExp_khovanskii_bound_unconditional` via the bridge,
with NO dependence on `zero_count_bound_classical`.

`terminal_nonzero` is the genuine non-triviality side condition inherited from
`khovanskii_bound_full` (the reduction's chain-length-0 endpoint is not
identically zero). -/
theorem expPoly_pfaffianFunction_zero_bound
    (e : MachLib.Real.PfaffianExpr) (he : IsExpPoly e)
    (a b : Real) (hab : a < b)
    (terminal_nonzero :
       ∀ g k, g.n = 0 →
         PfaffianFn.IsKhovanskiiReducible (toPfaffianFn e) g k →
         ∃ x : Real, g.eval x ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (⟨e⟩ : MachLib.Real.PfaffianFunction).eval z = 0) →
      zeros.length ≤ N := by
  obtain ⟨N, hN⟩ :=
    MachLib.ChainExp2PathC.singleExp_khovanskii_bound_unconditional
      (toMP1 e) a b hab terminal_nonzero
  refine ⟨N, ?_⟩
  intro zeros hnodup hzeros
  apply hN zeros hnodup
  intro z hz
  obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
  refine ⟨haz, hzb, ?_⟩
  -- `(⟨1, SingleExpChain, toMP1 e⟩).eval z = e.eval z = (⟨e⟩ : PfaffianFunction).eval z`
  show (toPfaffianFn e).eval z = 0
  rw [toPfaffianFn_eval e he z]
  exact hfz

end PfaffianExprSingleExpBridge
end MachLib
