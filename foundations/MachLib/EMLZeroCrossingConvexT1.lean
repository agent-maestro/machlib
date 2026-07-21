import MachLib.EMLZeroCrossingBothCompoundDeeper

/-!
# The `P`-side finding, generalized: convex `t1` makes `exp(t1eval)·t1deriv` increasing

`EMLZeroCrossingBothCompoundDeeper.lean` found that `P(z) := exp(t1eval z)·t1deriv z` is strictly
increasing wherever `t1deriv`'s OWN derivative is positive — i.e. wherever `t1` is CONVEX —
REGARDLESS of `t1deriv z`'s own sign (the bracket `(t1deriv z)² + t1deriv'(z)` is a square plus a
positive term, positive either way). That finding was proved only for the one concrete instance
(`t1 = eml var var`). This file distills it into a standalone, `t1`-agnostic lemma: a genuine
real-analysis fact, useful for ANY future compound `t1` whose derivative is itself increasing, not
just this one shape.

**Sanity check**: `EMLZeroCrossingBothCompoundDeeper.lean`'s `P_deriv_pos` re-derived as a
corollary, confirming the generalization is equivalent to the hand-built fact.
-/

namespace MachLib
namespace Real

/-- `P(x) := exp(t1eval x)·t1deriv x`'s raw derivative at a point, via chain rule (for
`exp∘t1eval`) then product rule (with `t1deriv`'s own derivative `t1deriv2`). -/
theorem hasDerivAt_expMulDeriv (t1eval t1deriv t1deriv2 : Real → Real) (z : Real)
    (ht1 : HasDerivAt t1eval (t1deriv z) z) (ht1' : HasDerivAt t1deriv (t1deriv2 z) z) :
    HasDerivAt (fun x => Real.exp (t1eval x) * t1deriv x)
      (Real.exp (t1eval z) * t1deriv z * t1deriv z + Real.exp (t1eval z) * t1deriv2 z) z := by
  have hexp_t1 : HasDerivAt (fun x => Real.exp (t1eval x)) (Real.exp (t1eval z) * t1deriv z) z :=
    HasDerivAt_comp Real.exp t1eval (t1deriv z) (Real.exp (t1eval z)) z ht1 (HasDerivAt_exp _)
  exact HasDerivAt_mul (fun x => Real.exp (t1eval x)) t1deriv
    (Real.exp (t1eval z) * t1deriv z) (t1deriv2 z) z hexp_t1 ht1'

/-- **Convexity alone makes `P`'s derivative positive, regardless of `t1deriv z`'s own sign.**
The raw derivative factors as `exp(t1eval z) · [(t1deriv z)² + t1deriv2 z]` — a square plus
`t1deriv2 z` (positive by the `hconvex` hypothesis, i.e. `t1` convex at `z`). -/
theorem expMulDeriv_pos_of_convex (t1eval t1deriv t1deriv2 : Real → Real) (z : Real)
    (hconvex : 0 < t1deriv2 z) :
    0 < Real.exp (t1eval z) * t1deriv z * t1deriv z + Real.exp (t1eval z) * t1deriv2 z := by
  have hexp_pos : 0 < Real.exp (t1eval z) := Real.exp_pos _
  have hsq : 0 ≤ t1deriv z * t1deriv z := mul_self_nonneg _
  have hbracket : 0 < t1deriv z * t1deriv z + t1deriv2 z := by
    have hle : t1deriv2 z ≤ t1deriv z * t1deriv z + t1deriv2 z := by
      have h := add_le_add_left hsq (t1deriv2 z)
      have e1 : t1deriv2 z + 0 = t1deriv2 z := add_zero _
      have e2 : t1deriv2 z + t1deriv z * t1deriv z
          = t1deriv z * t1deriv z + t1deriv2 z := by mach_ring
      rw [e1, e2] at h
      exact h
    exact lt_of_lt_of_le hconvex hle
  have e : Real.exp (t1eval z) * t1deriv z * t1deriv z + Real.exp (t1eval z) * t1deriv2 z
      = Real.exp (t1eval z) * (t1deriv z * t1deriv z + t1deriv2 z) := by mach_ring
  rw [e]
  exact mul_pos hexp_pos hbracket

/-- **`P` has at most one zero on `(c, d)` whenever `t1` is convex there** (`t1deriv` itself
differentiable with positive derivative) — strict monotonicity from `expMulDeriv_pos_of_convex`,
via `strictMono_of_deriv_pos` + `atMostOneZero_of_strictMono`. No assumption on `t1deriv`'s own
sign anywhere — the mechanism this whole file exists to isolate. -/
theorem expMul_atMostOneZero_of_convex (t1eval t1deriv t1deriv2 : Real → Real) (c d : Real)
    (ht1 : ∀ x : Real, c < x → x < d → HasDerivAt t1eval (t1deriv x) x)
    (ht1' : ∀ x : Real, c < x → x < d → HasDerivAt t1deriv (t1deriv2 x) x)
    (hconvex : ∀ x : Real, c < x → x < d → 0 < t1deriv2 x) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, c < z ∧ z < d ∧ Real.exp (t1eval z) * t1deriv z = 0) →
      zeros.length ≤ 1 := by
  apply atMostOneZero_of_strictMono
  intro x y hxc hxd hyc hyd hxy
  apply strictMono_of_deriv_pos (fun w => Real.exp (t1eval w) * t1deriv w) x y hxy
  · intro w hxw hwy
    have hwc : c < w := lt_of_lt_of_le hxc hxw
    have hwd : w < d := lt_of_le_of_lt hwy hyd
    exact ⟨_, hasDerivAt_expMulDeriv t1eval t1deriv t1deriv2 w (ht1 w hwc hwd)
      (ht1' w hwc hwd)⟩
  · intro w f' hxw hwy hderiv
    have hwc : c < w := lt_of_lt_of_le hxc hxw
    have hwd : w < d := lt_of_le_of_lt hwy hyd
    rw [HasDerivAt_unique _ _ _ w hderiv
      (hasDerivAt_expMulDeriv t1eval t1deriv t1deriv2 w (ht1 w hwc hwd) (ht1' w hwc hwd))]
    exact expMulDeriv_pos_of_convex t1eval t1deriv t1deriv2 w (hconvex w hwc hwd)

/-- **Sanity check**: `EMLZeroCrossingBothCompoundDeeper.lean`'s `P_deriv_pos` re-derived from
`expMulDeriv_pos_of_convex`, instantiating `t1eval = exp - log`, `t1deriv = fun x => exp x -
1/x`, `t1deriv2 = fun x => exp x - (-1/(x*x))` (`t1deriv`'s own derivative, `exp_sub_inv_deriv_pos`
supplies the convexity fact). Confirms the generalization is equivalent to, not just similar to,
the hand-built instance. -/
theorem P_deriv_pos_via_general (z : Real) (hz : 0 < z) :
    0 < Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) * (Real.exp z - 1 / z)
        + Real.exp (Real.exp z - Real.log z) * (Real.exp z - (-1 / (z * z))) :=
  expMulDeriv_pos_of_convex (fun x => Real.exp x - Real.log x) (fun x => Real.exp x - 1 / x)
    (fun x => Real.exp x - (-1 / (x * x))) z (exp_sub_inv_deriv_pos z hz)

end Real
end MachLib
