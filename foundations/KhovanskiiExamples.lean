import MachLib.SingleExpKhovanskii

/-!
# Concrete applications of the constructive Khovanskii bound

Demonstrates the framework's usage on specific polynomials. Each
example shows how to apply one of the three resolution paths:
  * Path (i): auto-bound via `expPoly_auto_bound_with_propagation_aux`.
  * Path (iii): parametric capstone via `expPoly_khovanskii_bound`
    with hand-constructed witness.

The examples verify the bound type-checks; the user adapts the pattern
for their specific polynomial.
-/

namespace MachLib
namespace SingleExpKhovanskii
namespace ExpPoly
namespace Examples

open MachLib.Real
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

/-! ## Example 1: `f(x) = 1` — the constant function

The simplest case: `ep = ⟨[Poly.const 1]⟩` represents `f(x) = 1`.
No zeros anywhere. Bound: `degreeUpper (polySimplify (Poly.const 1)) = 0`.

This applies the length-1 auto-bound directly. -/

example (a b : Real) (hab : a < b)
    (zeros : List Real) (hnodup : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, a < z ∧ z < b ∧
              (⟨[Poly.const 1]⟩ : ExpPoly).eval z = 0) :
    zeros.length ≤ 0 := by
  -- Length-1 auto-bound bounds zeros by `degreeUpper (polySimplify (Poly.const 1)) = 0`.
  -- expPolyAutoBound ⟨[Poly.const 1]⟩ = 1 + degreeUpper (polySimplify (Poly.const 1))
  --                                  = 1 + 0 = 1.
  -- But zeros for f ≡ 1 are 0 (no zeros).
  -- Apply the bound and use that const 1 has no roots.
  -- For this concrete case: zeros must be empty (since 1 ≠ 0 always).
  cases zeros with
  | nil => exact Nat.zero_le _
  | cons z _ =>
    -- zeros has z, but (⟨[Poly.const 1]⟩).eval z = 1 ≠ 0, contradicting hzeros.
    have h := hzeros z (List.mem_cons_self _ _)
    obtain ⟨_, _, h_ev⟩ := h
    -- h_ev : (⟨[Poly.const 1]⟩).eval z = 0, but eval = 1.
    exfalso
    have h_ev' : (⟨[Poly.const 1]⟩ : ExpPoly).eval z = 1 := by
      show evalAux [Poly.const 1] 0 z = 1
      show Poly.eval (Poly.const 1) z * Real.exp ((natCast 0) * z)
           + evalAux [] (0 + 1) z = 1
      show (1 : Real) * Real.exp ((natCast 0) * z) + 0 = 1
      rw [show (natCast 0 : Real) = 0 from natCast_zero, zero_mul, exp_zero,
          mul_one_ax, add_zero]
    rw [h_ev'] at h_ev
    exact zero_ne_one_ax h_ev.symm

/-! ## Example 2: `f(x) = x` — the identity polynomial in x

`ep = ⟨[Poly.var]⟩` represents `f(x) = x` (a polynomial in x only,
not involving e^x). One zero at x = 0.

Length-1 auto-bound: `1 + degreeUpper (polySimplify Poly.var) = 1 + 1 = 2`.
So `expPolyAutoBound = 2`. Actual zero count ≤ 1 (just x = 0).
The bound is loose but holds. -/

example (a b : Real) (hab : a < b)
    (hne : ∃ x, (⟨[Poly.var]⟩ : ExpPoly).eval x ≠ 0)
    (zeros : List Real) (hnodup : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, a < z ∧ z < b ∧
              (⟨[Poly.var]⟩ : ExpPoly).eval z = 0) :
    zeros.length ≤ expPolyAutoBound ⟨[Poly.var]⟩ :=
  expPoly_zero_count_auto_bound_length_one Poly.var a b hab hne
    zeros hnodup hzeros

/-! ## Example 3: parametric capstone for length-2 polynomial

For `f(x) = p₀(x) + p₁(x) · e^x` (length-2 ExpPoly), the parametric
capstone `expPoly_khovanskii_bound` requires the user to construct
an `IsKhovanskiiReducibleExp` witness.

This example demonstrates the witness shape (for documentation; the
actual witness must be supplied by the user for their specific case). -/

example (p₀ p₁ : Poly) (a b : Real) (hab : a < b)
    (target : Poly) (k : Nat)
    (h_iter : IsKhovanskiiReducibleExp ⟨[p₀, p₁]⟩ ⟨[target]⟩ k)
    (hne : ∃ x, (⟨[target]⟩ : ExpPoly).eval x ≠ 0)
    (zeros : List Real) (hnodup : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, a < z ∧ z < b ∧
              (⟨[p₀, p₁]⟩ : ExpPoly).eval z = 0) :
    zeros.length ≤ degreeUpper target + k :=
  expPoly_khovanskii_bound ⟨[p₀, p₁]⟩ target k h_iter a b hab hne
    zeros hnodup hzeros

end Examples
end ExpPoly
end SingleExpKhovanskii
end MachLib
