import MachLib.EMLKhovanskiiConstructive
import MachLib.EMLPfaffian
import MachLib.PfaffianExprTwoExpBridge

/-!
# MachLib.EMLDepth1Fragment — fragment-path pilot: axiom-clean bound for depth-1 leaf EML trees

First landable brick of the log-free-exponent "fragment-path" (AXIOM_AUDIT_V2.md
§2c(2)). For a depth-1 EML tree `eml t1 t2` with **leaf** children
(`t1, t2 ∈ {const, var}`), the log-elimination step reaches an exp-only form in one
move: on the validity domain `t2 > 0`,

    zeros(exp(t1) − log(t2))  =  zeros(t2 − exp(exp(t1)))    (elim_top_log)

and `t2 − exp(exp(t1))` is a **nested two-exponential** expression — exactly the
`IsExpExpPoly` fragment bridged in `PfaffianExprTwoExpBridge`. Citing the
now-unconditional chain-2 bound gives an **axiom-clean** Khovanskii zero bound for
`eml_pfaffian (eml t1 t2)`, with NO `zero_count_bound_classical`.

This is a genuine *partial* discharge of the axiom's real footprint (the
`eml_pfaffian` consumers), for the depth-1 leaf fragment. The general
log-free-exponent case needs the re-association driver that isolates logs from
nested positions (the deeper trees where `t2` itself is an `eml` node); the
buried-log case (`eml`-node exponent contains a log) is the separate b-path.
-/

namespace MachLib
namespace EMLDepth1Fragment

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianExprTwoExpBridge

/-- A leaf EML tree: `const` or `var` (no `eml` node). -/
def EMLLeaf : EMLTree → Prop
  | .const _ => True
  | .var     => True
  | .eml _ _ => False

/-- The leaf as a `PfaffianExpr` (`const c ↦ const c`, `var ↦ var`). -/
noncomputable def leafE : EMLTree → MachLib.Real.PfaffianExpr
  | .const c => .const c
  | .var     => .var
  | .eml _ _ => .const 0

/-- `exp(exp(leaf))` as a `PfaffianExpr`: for `var`, `e^(eˣ) = comp exp_atom
exp_atom`; for `const c`, the constant `e^(e^c)`. -/
noncomputable def expExpLeafE : EMLTree → MachLib.Real.PfaffianExpr
  | .const c => .const (Real.exp (Real.exp c))
  | .var     => .comp .exp_atom .exp_atom
  | .eml _ _ => .const 0

/-- The one-step reduct of `eml t1 t2` (leaf children): `t2 − exp(exp(t1))`. -/
noncomputable def reducedE (t1 t2 : EMLTree) : MachLib.Real.PfaffianExpr :=
  .sub (leafE t2) (expExpLeafE t1)

/-- The reduct is in the nested two-exponential fragment. -/
theorem isExpExp_reducedE (t1 t2 : EMLTree) (h1 : EMLLeaf t1) (h2 : EMLLeaf t2) :
    IsExpExpPoly (reducedE t1 t2) := by
  apply IsExpExpPoly.sub
  · cases t2 with
    | const c => exact IsExpExpPoly.const c
    | var => exact IsExpExpPoly.var
    | eml _ _ => exact h2.elim
  · cases t1 with
    | const c => exact IsExpExpPoly.const _
    | var => exact IsExpExpPoly.expexp
    | eml _ _ => exact h1.elim

/-- The reduct evaluates to `t2 − exp(exp(t1))`. -/
theorem reducedE_eval (t1 t2 : EMLTree) (h1 : EMLLeaf t1) (h2 : EMLLeaf t2) (x : Real) :
    (reducedE t1 t2).eval x = t2.eval x - Real.exp (Real.exp (t1.eval x)) := by
  show (leafE t2).eval x - (expExpLeafE t1).eval x
     = t2.eval x - Real.exp (Real.exp (t1.eval x))
  congr 1
  · cases t2 with
    | const c => rfl
    | var => rfl
    | eml _ _ => exact h2.elim
  · cases t1 with
    | const c => rfl
    | var => rfl
    | eml _ _ => exact h1.elim

/-- **The reduction (zeros preserved).** On `t2 > 0`, `eml t1 t2` and its reduct
`t2 − exp(exp(t1))` vanish at the same points. -/
theorem eml_reducedE_same_zeros (t1 t2 : EMLTree) (h1 : EMLLeaf t1) (h2 : EMLLeaf t2)
    (x : Real) (hpos : 0 < t2.eval x) :
    (EMLTree.eml t1 t2).eval x = 0 ↔ (reducedE t1 t2).eval x = 0 := by
  rw [reducedE_eval t1 t2 h1 h2]
  show Real.exp (t1.eval x) - Real.log (t2.eval x) = 0
     ↔ t2.eval x - Real.exp (Real.exp (t1.eval x)) = 0
  rw [MachLib.Real.sub_log_zero_iff (Real.exp (t1.eval x)) (t2.eval x) hpos,
      MachLib.Real.sub_eq_zero_iff (t2.eval x) (Real.exp (Real.exp (t1.eval x)))]

/-- **Axiom-clean Khovanskii zero bound for depth-1 leaf EML trees.** For
`eml t1 t2` with leaf children, on a domain where `t2 > 0`, the zeros of
`eml_pfaffian (eml t1 t2)` are finitely bounded — via the two-exp bridge and
`chain2_khovanskii_bound_unconditional`, with NO `zero_count_bound_classical`.
`h_term` is the genuine terminal non-vanishing condition inherited from the
chain-2 bound. -/
theorem eml_depth1_pfaffian_zero_bound
    (t1 t2 : EMLTree) (h1 : EMLLeaf t1) (h2 : EMLLeaf t2)
    (a b : Real) (hab : a < b)
    (hpos : ∀ x : Real, a < x → x < b → 0 < t2.eval x) :
    ∃ (g : MultiPoly 2) (k : Nat), MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0 ∧
      ((∀ g' j, g'.n = 0 →
         PfaffianFn.IsKhovanskiiReducible
           (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' j →
         ∃ x : Real, g'.eval x ≠ 0) →
       ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
         (∀ z ∈ zeros, a < z ∧ z < b ∧
           (eml_pfaffian (EMLTree.eml t1 t2)).eval z = 0) →
         zeros.length ≤ N) := by
  obtain ⟨g, k, hg, hbound⟩ :=
    expExpPoly_pfaffianFunction_zero_bound (reducedE t1 t2)
      (isExpExp_reducedE t1 t2 h1 h2) a b hab
  refine ⟨g, k, hg, fun h_term => ?_⟩
  obtain ⟨N, hN⟩ := hbound h_term
  refine ⟨N, ?_⟩
  intro zeros hnodup hzeros
  apply hN zeros hnodup
  intro z hz
  obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
  refine ⟨haz, hzb, ?_⟩
  -- transfer: eml_pfaffian zero → EMLTree zero → reduct zero → ⟨reduct⟩ PfaffianFunction zero
  show (⟨reducedE t1 t2⟩ : MachLib.Real.PfaffianFunction).eval z = 0
  have hz_eml : (EMLTree.eml t1 t2).eval z = 0 := by
    rw [← eml_pfaffian_eval (EMLTree.eml t1 t2) z]; exact hfz
  exact (eml_reducedE_same_zeros t1 t2 h1 h2 z (hpos z haz hzb)).mp hz_eml

/-- **Framework-facing form.** The same depth-1 bound phrased against the
project's own `EMLPfaffianValidOn` predicate — for a leaf-children `eml t1 t2`,
`EMLPfaffianValidOn (eml t1 t2) a b` is exactly the positivity of `t2` (its first
two conjuncts, on leaves, are `True`). So the depth-1 fragment plugs directly into
the domain condition every non-trivial `PfaffianFunction.zero_bound` application
must already discharge. -/
theorem eml_depth1_pfaffian_zero_bound_validOn
    (t1 t2 : EMLTree) (h1 : EMLLeaf t1) (h2 : EMLLeaf t2)
    (a b : Real) (hab : a < b)
    (hvalid : EMLPfaffianValidOn (EMLTree.eml t1 t2) a b) :
    ∃ (g : MultiPoly 2) (k : Nat), MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0 ∧
      ((∀ g' j, g'.n = 0 →
         PfaffianFn.IsKhovanskiiReducible
           (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' j →
         ∃ x : Real, g'.eval x ≠ 0) →
       ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
         (∀ z ∈ zeros, a < z ∧ z < b ∧
           (eml_pfaffian (EMLTree.eml t1 t2)).eval z = 0) →
         zeros.length ≤ N) :=
  eml_depth1_pfaffian_zero_bound t1 t2 h1 h2 a b hab hvalid.2.2

end EMLDepth1Fragment
end MachLib
