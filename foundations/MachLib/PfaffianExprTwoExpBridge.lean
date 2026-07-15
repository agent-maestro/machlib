import MachLib.ChainExp2Unconditional
import MachLib.Pfaffian

/-!
# MachLib.PfaffianExprTwoExpBridge — `PfaffianExpr` → chain-2, nested two-exp fragment

Extends `PfaffianExprSingleExpBridge` one level up the tower. Bridges the
**nested two-exponential fragment** of `PfaffianExpr` — polynomials in
`(x, eˣ, e^(eˣ))` — to a `MultiPoly 2` over `IterExpChain 2` (whose chain values
are `y₀ = eˣ`, `y₁ = e^(eˣ)`), and derives an **axiom-clean** Khovanskii zero
bound for such `PfaffianFunction`s via `chain2_khovanskii_bound_unconditional`.

`e^(eˣ)` is `PfaffianExpr.comp exp_atom exp_atom` (`comp f g` evals to
`f ∘ g`). Everything else is structural. This continues reducing the real
footprint of `zero_count_bound_classical` (the sin/cos-not-in-EML consumers)
onto the constructive pipeline, now for the depth-2 exp fragment.

Remaining: `log_atom`/`inv`, deeper towers, and independent (non-nested)
exponentials — see AXIOM_AUDIT_V2.md §2c.
-/

namespace MachLib
namespace PfaffianExprTwoExpBridge

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.IterExpChainMod
open MachLib.ChainExp2Bound

/-- The nested two-exponential fragment of `PfaffianExpr`: polynomials in
`x`, `eˣ` (`exp_atom`), and `e^(eˣ)` (`comp exp_atom exp_atom`). -/
inductive IsExpExpPoly : MachLib.Real.PfaffianExpr → Prop
  | const (c : MachLib.Real) : IsExpExpPoly (.const c)
  | var : IsExpExpPoly .var
  | exp_atom : IsExpExpPoly .exp_atom
  | expexp : IsExpExpPoly (.comp .exp_atom .exp_atom)
  | add {a b} : IsExpExpPoly a → IsExpExpPoly b → IsExpExpPoly (.add a b)
  | sub {a b} : IsExpExpPoly a → IsExpExpPoly b → IsExpExpPoly (.sub a b)
  | mul {a b} : IsExpExpPoly a → IsExpExpPoly b → IsExpExpPoly (.mul a b)

/-- Translate to `MultiPoly 2` over `IterExpChain 2`: `eˣ ↦ y₀`,
`e^(eˣ) ↦ y₁`, else structural. Out-of-fragment constructors map to `0`. -/
noncomputable def toMP2 : MachLib.Real.PfaffianExpr → MultiPoly 2
  | .const c   => MultiPoly.const c
  | .var       => MultiPoly.varX
  | .exp_atom  => MultiPoly.varY ⟨0, by omega⟩
  | .comp .exp_atom .exp_atom => MultiPoly.varY ⟨1, by omega⟩
  | .add a b   => MultiPoly.add (toMP2 a) (toMP2 b)
  | .sub a b   => MultiPoly.sub (toMP2 a) (toMP2 b)
  | .mul a b   => MultiPoly.mul (toMP2 a) (toMP2 b)
  | .comp _ _  => MultiPoly.const 0
  | .log_atom  => MultiPoly.const 0
  | .inv _     => MultiPoly.const 0

/-- **Eval-agreement.** On the nested two-exp fragment, `toMP2 e` evaluated over
`IterExpChain 2`'s chain values (`y₀ = eˣ`, `y₁ = e^(eˣ)`) equals `e.eval`. -/
theorem eval_toMP2 (e : MachLib.Real.PfaffianExpr) (he : IsExpExpPoly e) (x : Real) :
    MultiPoly.eval (toMP2 e) x ((IterExpChain 2).chainValues x) = e.eval x := by
  induction he with
  | const c => rfl
  | var => rfl
  | exp_atom => rfl
  | expexp => rfl
  | add a b iha ihb =>
    show MultiPoly.eval (toMP2 _) x _ + MultiPoly.eval (toMP2 _) x _ = _ + _
    rw [iha, ihb]
  | sub a b iha ihb =>
    show MultiPoly.eval (toMP2 _) x _ - MultiPoly.eval (toMP2 _) x _ = _ - _
    rw [iha, ihb]
  | mul a b iha ihb =>
    show MultiPoly.eval (toMP2 _) x _ * MultiPoly.eval (toMP2 _) x _ = _ * _
    rw [iha, ihb]

/-- **Axiom-clean Khovanskii zero bound for nested two-exponential
`PfaffianFunction`s.** For `f = ⟨e⟩` with `e` in the nested two-exp fragment,
the zeros of `f` on `(a, b)` are finitely bounded — via
`chain2_khovanskii_bound_unconditional` through the bridge, with NO dependence
on `zero_count_bound_classical`. The bound is conditioned on the genuine terminal
non-vanishing condition inherited from the chain-2 bound (about the reduction's
`y₁`-free single-exp reduct `g`). -/
theorem expExpPoly_pfaffianFunction_zero_bound
    (e : MachLib.Real.PfaffianExpr) (he : IsExpExpPoly e)
    (a b : Real) (hab : a < b) :
    ∃ (g : MultiPoly 2) (k : Nat), MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0 ∧
      ((∀ g' j, g'.n = 0 →
         PfaffianFn.IsKhovanskiiReducible
           (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' j →
         ∃ x : Real, g'.eval x ≠ 0) →
       ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
         (∀ z ∈ zeros, a < z ∧ z < b ∧
           (⟨e⟩ : MachLib.Real.PfaffianFunction).eval z = 0) →
         zeros.length ≤ N) := by
  obtain ⟨g, k, hg, hbound⟩ :=
    MachLib.ChainExp2Capstone.chain2_khovanskii_bound_unconditional (toMP2 e) a b hab
  refine ⟨g, k, hg, fun h_term => ?_⟩
  obtain ⟨N, hN⟩ := hbound h_term
  refine ⟨N, ?_⟩
  intro zeros hnodup hzeros
  apply hN zeros hnodup
  intro z hz
  obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
  refine ⟨haz, hzb, ?_⟩
  -- `(chain2Fn (toMP2 e)).eval z = e.eval z = (⟨e⟩ : PfaffianFunction).eval z`
  rw [chain2Fn_eval, eval_toMP2 e he z]
  exact hfz

end PfaffianExprTwoExpBridge
end MachLib
