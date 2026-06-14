import MachLib.MultiPoly
import MachLib.PolynomialEvidence
import MachLib.PolynomialRootCount

/-!
# MachLib.MultiPolyToPoly — base case substrate for the constructive
Khovanskii bound (Item 4)

When a PfaffianFn has chain length 0, its underlying polynomial is a
`MultiPoly 0` — multivariate in (x, y_1, ..., y_n) with n = 0, hence
univariate in x alone. The chain variables are vacuous because
`Fin 0` is empty.

This module converts `MultiPoly 0 → Poly` (the univariate polynomial
AST in `MachLib.PolynomialEvidence`) and proves eval and degree
preservation. Combined with `PolynomialRootCount.poly_root_count_bound`,
this gives the **base case** zero bound for the Khovanskii iteration:

  PfaffianFn f with f.n = 0  ⟹  zeros(f) on (a,b) ≤ degreeX(f.poly)

This is the "step k = 0" target for `zero_count_iter_bound` from
`KhovanskiiReduction.lean`.

## Design choice: env-parametric conversion

We define `toPolyAt env : MultiPoly n → Poly` for arbitrary `n` and a
chain-value environment `env : Fin n → Real`. The conversion
substitutes each `varY i` with the constant `env i`. For `n = 0`,
the env is the unique empty function, the `varY` case never fires,
and the conversion is genuinely env-independent.

The general `toPolyAt` is more useful than a specialized `n = 0`
version because it lets us evaluate any `MultiPoly` at a fixed
chain-value snapshot — useful in future Khovanskii proof steps where
we freeze the chain at a particular point.
-/

namespace MachLib
namespace MultiPolyToPoly

open MachLib.MultiPolyMod
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

/-! ## The conversion -/

/-- Convert a `MultiPoly n` to a univariate `Poly` by substituting
each `varY i` with the constant `env i`. -/
noncomputable def toPolyAt {n : Nat} (env : Fin n → Real) :
    MultiPoly n → Poly
  | MultiPoly.const c => Poly.const c
  | MultiPoly.varX => Poly.var
  | MultiPoly.varY i => Poly.const (env i)
  | MultiPoly.add p q => Poly.add (toPolyAt env p) (toPolyAt env q)
  | MultiPoly.sub p q => Poly.sub (toPolyAt env p) (toPolyAt env q)
  | MultiPoly.mul p q => Poly.mul (toPolyAt env p) (toPolyAt env q)

/-! ## Eval equivalence -/

/-- The converted `Poly` evaluates to the same value as the original
`MultiPoly` at the given x and environment. -/
theorem eval_toPolyAt {n : Nat} (p : MultiPoly n) (env : Fin n → Real)
    (x : Real) :
    Poly.eval (toPolyAt env p) x = MultiPoly.eval p x env := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY i => rfl
  | add p q ihp ihq =>
    show Poly.eval (toPolyAt env p) x + Poly.eval (toPolyAt env q) x
       = MultiPoly.eval p x env + MultiPoly.eval q x env
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Poly.eval (toPolyAt env p) x - Poly.eval (toPolyAt env q) x
       = MultiPoly.eval p x env - MultiPoly.eval q x env
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show Poly.eval (toPolyAt env p) x * Poly.eval (toPolyAt env q) x
       = MultiPoly.eval p x env * MultiPoly.eval q x env
    rw [ihp, ihq]

/-! ## Degree equivalence -/

/-- The converted polynomial has the same x-degree (`degreeUpper`)
as the original's `degreeX`. Holds for any `n` and any environment,
because both definitions match structurally: `const → 0`, `varX → 1`,
`varY → 0`, `add/sub → max`, `mul → +`. -/
theorem degreeUpper_toPolyAt {n : Nat} (p : MultiPoly n) (env : Fin n → Real) :
    degreeUpper (toPolyAt env p) = MultiPoly.degreeX p := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY i => rfl
  | add p q ihp ihq =>
    show Nat.max (degreeUpper (toPolyAt env p)) (degreeUpper (toPolyAt env q))
       = Nat.max (MultiPoly.degreeX p) (MultiPoly.degreeX q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (degreeUpper (toPolyAt env p)) (degreeUpper (toPolyAt env q))
       = Nat.max (MultiPoly.degreeX p) (MultiPoly.degreeX q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show degreeUpper (toPolyAt env p) + degreeUpper (toPolyAt env q)
       = MultiPoly.degreeX p + MultiPoly.degreeX q
    rw [ihp, ihq]

/-! ## Base case zero bound for MultiPoly

For a `MultiPoly n` evaluated against a FIXED environment `env`, zero
count on `(a, b)` is bounded by `degreeX p`. This specializes to the
chain-length-0 PfaffianFn case (where the environment is the chain
values at one fixed point — which doesn't matter for `n = 0` since
the env is vacuous).

**Important caveat**: this bound holds only when `env` is constant in
`x`. For `n > 0`, a real PfaffianFn's chain values DO vary with x, so
this lemma isn't useful directly at higher chain lengths — there, the
multivariate evaluation depends nontrivially on x via the chain. -/

theorem multiPoly_root_count_bound_at_fixed_env
    {n : Nat} (p : MultiPoly n) (env : Fin n → Real)
    (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, MultiPoly.eval p x env ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ MultiPoly.eval p z env = 0) →
      zeros.length ≤ MultiPoly.degreeX p := by
  intro zeros hnodup hzeros
  -- Bridge MultiPoly.eval ↔ Poly.eval via eval_toPolyAt.
  have hne_poly : ∃ x : Real, Poly.eval (toPolyAt env p) x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    rw [eval_toPolyAt]
    exact hx
  have hzeros_poly : ∀ z ∈ zeros,
                       a < z ∧ z < b ∧ Poly.eval (toPolyAt env p) z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hpz⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    rw [eval_toPolyAt]
    exact hpz
  have hbound := poly_root_count_bound (toPolyAt env p) a b hab hne_poly
                   zeros hnodup hzeros_poly
  -- Replace degreeUpper with degreeX via degreeUpper_toPolyAt.
  rw [degreeUpper_toPolyAt] at hbound
  exact hbound

/-! ## Environment invariance for chain length 0

When `n = 0`, the env is vacuous (`Fin 0 → Real` is a subsingleton in
the obvious sense — every `varY i` case has `i : Fin 0` impossible).
Concretely, the eval of a `MultiPoly n` doesn't depend on env when
`n = 0`. This is the bridge needed to apply
`multiPoly_root_count_bound_at_fixed_env` to a PfaffianFn whose
`chainValues` varies with x — for chainLength 0, the variation doesn't
matter. -/

theorem multiPoly_eval_env_invariant_n_zero
    {n : Nat} (hn : n = 0) (p : MultiPoly n) (x : Real)
    (env₁ env₂ : Fin n → Real) :
    MultiPoly.eval p x env₁ = MultiPoly.eval p x env₂ := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY i =>
    -- i : Fin n with n = 0 is impossible.
    exfalso
    have hlt : i.val < n := i.isLt
    omega
  | add p q ihp ihq =>
    show MultiPoly.eval p x env₁ + MultiPoly.eval q x env₁
       = MultiPoly.eval p x env₂ + MultiPoly.eval q x env₂
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show MultiPoly.eval p x env₁ - MultiPoly.eval q x env₁
       = MultiPoly.eval p x env₂ - MultiPoly.eval q x env₂
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.eval p x env₁ * MultiPoly.eval q x env₁
       = MultiPoly.eval p x env₂ * MultiPoly.eval q x env₂
    rw [ihp, ihq]

end MultiPolyToPoly
end MachLib
