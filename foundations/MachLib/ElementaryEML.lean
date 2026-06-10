import MachLib.Exp
import MachLib.Log
import MachLib.EML
import MachLib.SinNotInEML

/-!
# `ElementaryEML` — the EML + ring-arithmetic AST for the universality theorem

The pure `EMLTree` AST (in `MachLib.SinNotInEML`) has only three
constructors: `const`, `var`, `eml`. EML's universality theorem requires
that every elementary function rewrites to "a finite tree of `eml`, `+`,
`*`, and constants" — so `+` and `*` are additional primitives, not
expressible in pure `EMLTree`.

This file introduces `ElementaryEML` as a wrapper AST that combines
`EMLTree` leaves with `add` and `mul` constructors. The pure-EML
barrier theorems (`sin_not_in_eml_depth_le_1`, `cos_not_in_eml_depth_le_1`,
`exp_exp_not_in_eml_1`, `EML_0 ⊊ EML_1`, `EML_1 ⊊ EML_2`) continue to
hold on the pure `EMLTree` side unchanged. The universality theorem
(`forthcoming`) will be stated against `ElementaryEML`.

This is **Chunk 1** of the universality program. Chunk 2 (polynomial
embedding) and beyond build on top of this AST. Strategic context:
`monogate-research/exploration/universality_first_chunk_scoping_2026_06_10/FINDINGS.md`.

This file does not depend on Mathlib.
-/

namespace MachLib

/-! ### AST -/

/-- AST for elementary functions in EML's universality target form:
`eml`, `+`, `*`, and constants, plus the variable `x`.

The `pure` constructor lifts a pure-EML `EMLTree` into `ElementaryEML`,
so any positive embedding already provable for `EMLTree` lifts trivially.
The `add` and `mul` constructors introduce ring arithmetic. -/
inductive ElementaryEML : Type where
  | pure : EMLTree → ElementaryEML
  | add  : ElementaryEML → ElementaryEML → ElementaryEML
  | mul  : ElementaryEML → ElementaryEML → ElementaryEML

namespace ElementaryEML

/-- Real evaluation: `pure` evaluates via `EMLTree.eval`; `add` and `mul`
distribute pointwise. -/
noncomputable def eval (e : ElementaryEML) (x : Real) : Real :=
  match e with
  | pure t   => t.eval x
  | add a b  => a.eval x + b.eval x
  | mul a b  => a.eval x * b.eval x

end ElementaryEML

/-! ### Base positive embeddings

These are the trivial existence lemmas the universality theorem will
inductively build on. Each says "this canonical function is realized by
some `ElementaryEML` expression". They are the analogues of `EMLTree`'s
`exp_in_eml_1` lifted into `ElementaryEML`. -/

/-- `Real.exp` is realized by an `ElementaryEML` expression. -/
theorem exp_in_elementary :
    ∃ e : ElementaryEML, ∀ x : Real, Real.exp x = e.eval x := by
  refine ⟨ElementaryEML.pure (EMLTree.eml .var (.const 1)), ?_⟩
  intro x
  simp [ElementaryEML.eval, EMLTree.eval, Real.log_one,
        MachLib.Real.sub_zero]

/-- The identity function (the variable `x`) is realized by an
`ElementaryEML` expression. -/
theorem id_in_elementary :
    ∃ e : ElementaryEML, ∀ x : Real, x = e.eval x := by
  refine ⟨ElementaryEML.pure .var, ?_⟩
  intro x
  rfl

/-- Every constant function is realized by an `ElementaryEML` expression. -/
theorem const_in_elementary (c : Real) :
    ∃ e : ElementaryEML, ∀ x : Real, c = e.eval x := by
  refine ⟨ElementaryEML.pure (.const c), ?_⟩
  intro x
  rfl

/-! ### Forthcoming: `log_in_elementary`

`Real.log x` is structurally expressible as `1 - eml(0, x)` (since
`eml(0, x) = exp 0 - log x = 1 - log x`), but extracting `log x` from
that requires encoding subtraction as `add` + scalar multiplication
in `ElementaryEML` (i.e., `log x = (-1) * (1 - log x) + 1`). The
algebraic verification needs MachLib's distribution / negation
identities and is left for a follow-up artifact. The pure `EMLTree`
representation `eml(0, var)` does evaluate to `1 - log x`, so log is
"morally" in `ElementaryEML` via this representation. -/

end MachLib
