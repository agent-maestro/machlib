import MachLib.Geometry.Apollonius.SymmetricTriple

/-!
# The flagship configuration

Three unit circles centred at `(0,0)`, `(4,0)`, `(0,4)` — a right isosceles arrangement, chosen
because a visitor understands it instantly and because it is *checked* to be generic rather than
assumed to be.

Everything here is an **instantiation**: the theorems live in `SymmetricTriple` over symbolic `d`
and `ρ`, and this file supplies one pair of values and discharges the general-position hypothesis.
Numeral plumbing stays below the generic development, never above it.

**No `natCast` was needed.** The flagship's constants are `4`, `8` and `16`, small enough that the
unary `(1+1)` encoding closes each obligation directly. That is worth recording next to the earlier
failures: the numeral wall was never about *input* size, it was about the constants the class
*quadratic* generates — which reached `1.4 × 10⁴` for the scaled configuration and choked the
normaliser. Inputs this size cost nothing.
-/

namespace MachLib
namespace Geometry
namespace Apollonius
namespace Examples

open Real
open SymmetricTriple

private theorem ne_of_sub_pos {a b : Real} (h : 0 < a - b) : a ≠ b := by
  intro he
  rw [he] at h
  have z : b - b = 0 := by mach_ring
  rw [z] at h
  exact lt_irrefl_ax 0 h

/-- Centre separation of the flagship: `d = 4`. -/
noncomputable def flagD : Real := (1 + 1) * (1 + 1)

/-- Common radius of the flagship: `ρ = 1`. -/
noncomputable def flagRho : Real := 1

/-- **The flagship is in general position** — separated, and off the degree-drop locus.

Both conjuncts are *checked*, which matters: `d² = 8ρ²` would need `d ≈ 2.83`, and `d = 4` clears it,
but nothing about the picture makes that obvious. An aesthetically convenient configuration is not
automatically a generic one. -/
theorem flagship_gp : SymmetricGeneralPosition flagD flagRho := by
  refine ⟨zero_lt_one_ax, ?_, ?_⟩
  · -- `2ρ < d`, i.e. `2 < 4`
    refine ?_
    have hgap : (0 : Real) < flagD - (1 + 1) * flagRho := by
      have e : flagD - (1 + 1) * flagRho = 1 + 1 := by
        unfold flagD flagRho; mach_mpoly [] <;> mach_ring
      rw [e]; exact add_pos zero_lt_one_ax zero_lt_one_ax
    have v := add_lt_add_left hgap ((1 + 1) * flagRho)
    have l : (1 + 1) * flagRho + 0 = (1 + 1) * flagRho := by mach_ring
    have rr : (1 + 1) * flagRho + (flagD - (1 + 1) * flagRho) = flagD := by mach_ring
    rw [l, rr] at v; exact v
  · -- `d² ≠ 8ρ²`, i.e. `16 ≠ 8`
    refine ne_of_sub_pos ?_
    have e : flagD * flagD - (1 + 1) * ((1 + 1) * ((1 + 1) * (flagRho * flagRho)))
        = (1 + 1) * ((1 + 1) * (1 + 1)) := by
      unfold flagD flagRho; mach_mpoly [] <;> mach_ring
    rw [e]
    exact mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
      (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) (add_pos zero_lt_one_ax zero_lt_one_ax))

/-- **The flagship's three input circles**, as `Circle`s. -/
noncomputable def flagA : Circle := cA flagRho (gp_rho_pos flagD flagRho flagship_gp)
noncomputable def flagB : Circle := cB flagD flagRho (gp_rho_pos flagD flagRho flagship_gp)
noncomputable def flagC : Circle := cC flagD flagRho (gp_rho_pos flagD flagRho flagship_gp)

/-- **Every mode of the flagship has exactly two signed solutions** — attained, and no more.

The whole symbolic development, instantiated at one configuration. With the antipodal law this is
the eight: sixteen signed solutions in eight antipodal pairs, one member of each pair carrying a
positive radius. -/
theorem flagship_exactly_two_per_mode (m : Mode) :
    (∃ x₁ y₁ r₁ x₂ y₂ r₂ : Real, r₁ ≠ r₂
        ∧ SolvesMode flagA flagB flagC m x₁ y₁ r₁
        ∧ SolvesMode flagA flagB flagC m x₂ y₂ r₂)
    ∧ (∀ x₁ y₁ r₁ x₂ y₂ r₂ x₃ y₃ r₃ : Real,
        SolvesMode flagA flagB flagC m x₁ y₁ r₁ →
        SolvesMode flagA flagB flagC m x₂ y₂ r₂ →
        SolvesMode flagA flagB flagC m x₃ y₃ r₃ →
        (x₁ = x₂ ∧ y₁ = y₂ ∧ r₁ = r₂)
        ∨ (x₁ = x₃ ∧ y₁ = y₃ ∧ r₁ = r₃)
        ∨ (x₂ = x₃ ∧ y₂ = y₃ ∧ r₂ = r₃)) :=
  exactly_two_signed_solutions_per_mode flagD flagRho flagship_gp m

/-- **Every root of the flagship is nonzero and its mode is determined** — the decode obligations
at the concrete configuration. -/
theorem flagship_mode_unique (m m' : Mode) (x y r : Real)
    (h : SolvesMode flagA flagB flagC m x y r)
    (h' : SolvesMode flagA flagB flagC m' x y r) : m = m' :=
  mode_unique_of_gp flagD flagRho flagship_gp m m' x y r h h'

end Examples
end Apollonius
end Geometry
end MachLib
