import MachLib.IterExpDepth3Descent
import MachLib.ChainExp2NoZeros

/-!
# Depth-3 vehicle no-zeros: `reduct ≡ 0 ⇒ chain3Fn has no zeros`

The terminal case of an unconditional depth-3 Khovanskii bound (pure exponentials hit it). The
integrating-factor vehicle for the graded depth-3 reduce `R(p) = p' − m·p`,
`m = d₂·y₀y₁ + d₁·y₀ + c` (`d₂ = degreeY₂ p`, `d₁ = degreeY₁(lcY₂ p)`):

  `V(x) = f(x) · exp(−(d₂·y₁ + d₁·y₀ + c·x))`,  `y₀ = eˣ = iterExp 0`,  `y₁ = e^{eˣ} = iterExp 1`.

Since `∫m dx = d₂·log y₂ + d₁·log y₁ + c·x = d₂·y₁ + d₁·y₀ + c·x` (using `(log y₂)' = y₀y₁`,
`(log y₁)' = y₀`), the factor `exp(−∫m) = y₂^{−d₂}·y₁^{−d₁}·e^{−cx}` is never 0, and `V' = E·(reduct)`.
So `reduct ≡ 0 ⇒ V' ≡ 0 ⇒ V` constant (MVT) ⇒ `f` nonzero wherever it is nonzero at one point.
Mirrors chain-2's `ChainExp2NoZeros.chain2Fn_no_zeros_of_reduct_zero`, one level up. Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3Vehicle

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepth3Descent

/-- The depth-3 Pfaffian function wrapping a `MultiPoly 3` over `IterExpChain 3`. -/
noncomputable def chain3Fn (p : MultiPoly 3) : PfaffianFn :=
  { n := 3, chain := IterExpChain 3, poly := p }

/-- The depth-3 Rolle vehicle: `f.eval x · exp(−(d₂·y₁ + d₁·y₀ + c·x))`, sign folded in. -/
noncomputable def vehicleM3 (f : PfaffianFn) (d2 d1 : Nat) (c : Real) : Real → Real :=
  fun x => f.eval x * Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 x
    + (-MachLib.Real.natCast d1) * iterExp 0 x + (-c) * x)

/-- **Same-zero-set:** the vehicle vanishes exactly where `f` does. -/
theorem vehicleM3_zero_iff (f : PfaffianFn) (d2 d1 : Nat) (c : Real) (x : Real) :
    vehicleM3 f d2 d1 c x = 0 ↔ f.eval x = 0 := by
  show f.eval x * Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 x
      + (-MachLib.Real.natCast d1) * iterExp 0 x + (-c) * x) = 0 ↔ f.eval x = 0
  constructor
  · intro h
    have hexp_ne : Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 x
        + (-MachLib.Real.natCast d1) * iterExp 0 x + (-c) * x) ≠ 0 := exp_ne_zero _
    rw [mul_comm] at h
    exact mul_eq_zero_of_factor_ne_zero hexp_ne h
  · intro h; rw [h, zero_mul]

/-- **HasDerivAt for the depth-3 vehicle (raw product-rule form).** -/
theorem hasDerivAt_vehicleM3 (f : PfaffianFn) (d2 d1 : Nat) (c : Real) (z : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z) :
    HasDerivAt (vehicleM3 f d2 d1 c)
      (f.chainTotalDerivative.eval z
          * Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
              + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
        + f.eval z
          * (Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
                + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
             * ((-MachLib.Real.natCast d2) * (iterExp 0 z * iterExp 1 z)
                + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c))))
      z := by
  -- derivatives of iterExp 1 (= y₀·y₁) and iterExp 0 (= y₀).
  have h1 : HasDerivAt (iterExp 1) (iterExp 0 z * iterExp 1 z) z := @HasDerivAt_iterExp 2 1 (by omega) z
  have h0 : HasDerivAt (iterExp 0) (iterExp 0 z) z := @HasDerivAt_iterExp 2 0 (by omega) z
  -- term1 = (−d₂)·iterExp1, term2 = (−d₁)·iterExp0, term3 = (−c)·x.
  have hT1 := HasDerivAt_mul (fun _ => -MachLib.Real.natCast d2) (iterExp 1)
              0 (iterExp 0 z * iterExp 1 z) z (HasDerivAt_const _ z) h1
  have hT2 := HasDerivAt_mul (fun _ => -MachLib.Real.natCast d1) (iterExp 0)
              0 (iterExp 0 z) z (HasDerivAt_const _ z) h0
  have hT12 := HasDerivAt_add (fun y => (-MachLib.Real.natCast d2) * iterExp 1 y)
              (fun y => (-MachLib.Real.natCast d1) * iterExp 0 y) _ _ z hT1 hT2
  have hT3 := HasDerivAt_mul (fun _ => -c) (fun x => x) 0 1 z (HasDerivAt_const _ z) (HasDerivAt_id z)
  have hu := HasDerivAt_add
              (fun y => (-MachLib.Real.natCast d2) * iterExp 1 y + (-MachLib.Real.natCast d1) * iterExp 0 y)
              (fun y => (-c) * y) _ _ z hT12 hT3
  have hu_eq :
      ((0 * iterExp 1 z + (-MachLib.Real.natCast d2) * (iterExp 0 z * iterExp 1 z))
        + (0 * iterExp 0 z + (-MachLib.Real.natCast d1) * iterExp 0 z)) + (0 * z + (-c) * 1)
      = (-MachLib.Real.natCast d2) * (iterExp 0 z * iterExp 1 z)
        + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) := by mach_ring
  rw [hu_eq] at hu
  have hE := HasDerivAt_comp Real.exp
              (fun x => (-MachLib.Real.natCast d2) * iterExp 1 x
                + (-MachLib.Real.natCast d1) * iterExp 0 x + (-c) * x)
              ((-MachLib.Real.natCast d2) * (iterExp 0 z * iterExp 1 z)
                + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c))
              (Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
                + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z))
              z hu (HasDerivAt_exp _)
  exact HasDerivAt_mul f.eval
          (fun x => Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 x
            + (-MachLib.Real.natCast d1) * iterExp 0 x + (-c) * x))
          (f.chainTotalDerivative.eval z)
          (Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
              + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
            * ((-MachLib.Real.natCast d2) * (iterExp 0 z * iterExp 1 z)
               + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c)))
          z hf hE

/-- **Algebraic factoring** of the raw derivative: `A·E + P·(E·U) = E·(A − M·P)`, `U = −M`,
`M = d₂·(Y₀·Y₁) + d₁·Y₀ + c`. -/
theorem vehicle3_deriv_factor (A P E D2 D1 Y0 Y1 c : Real) :
    A * E + P * (E * ((-D2) * (Y0 * Y1) + (-D1) * Y0 + (-c)))
    = E * (A - (D2 * (Y0 * Y1) + D1 * Y0 + c) * P) := by
  mach_mpoly [A, P, E, D2, D1, Y0, Y1, c]

/-- **The reduce eval-identity.** Along `IterExpChain 3`, `chain3Reduce c p` evaluates to the graded
poly-multiplier reduce value `cTD(p) − (d₂·y₀y₁ + d₁·y₀ + c)·p`. -/
theorem chain3Fn_chain3Reduce_eval (c : Real) (p : MultiPoly 3) (z : Real) :
    (chain3Fn (chain3Reduce c p)).eval z
    = (chain3Fn p).chainTotalDerivative.eval z
      - (MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
          * (iterExp 0 z * iterExp 1 z)
         + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3)
             (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) * iterExp 0 z
         + c)
        * (chain3Fn p).eval z := by
  show MultiPoly.eval (chain3Reduce c p) z ((IterExpChain 3).chainValues z)
     = MultiPoly.eval (chainTotalDeriv (IterExpChain 3) p) z ((IterExpChain 3).chainValues z)
       - (MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
            * (iterExp 0 z * iterExp 1 z)
          + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) * iterExp 0 z
          + c)
         * MultiPoly.eval p z ((IterExpChain 3).chainValues z)
  unfold chain3Reduce mult3
  have hey0 : MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 3)) z ((IterExpChain 3).chainValues z)
      = iterExp 0 z := rfl
  have hey1 : MultiPoly.eval (MultiPoly.varY (⟨1, by omega⟩ : Fin 3)) z ((IterExpChain 3).chainValues z)
      = iterExp 1 z := rfl
  simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add, MultiPoly.eval_const,
    hey0, hey1]

set_option maxHeartbeats 1600000 in
/-- **The depth-3 vehicle no-zeros lemma.** If the graded reduce value is `≡ 0` on `(a,b)` and
`chain3Fn p` is nonzero at some `z₀ ∈ (a,b)`, then `chain3Fn p` has no zeros on `(a,b)`. -/
theorem chain3Fn_no_zeros_of_reduct_zero (p : MultiPoly 3) (c : Real) (a b : Real) (hab : a < b)
    (h_reduct : ∀ z, a < z → z < b → (chain3Fn (chain3Reduce c p)).eval z = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : (chain3Fn p).eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → (chain3Fn p).eval z ≠ 0 := by
  let d2 := MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
  let d1 := MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)
  let V := vehicleM3 (chain3Fn p) d2 d1 c
  have hVderiv : ∀ z, a < z → z < b → HasDerivAt V 0 z := by
    intro z hza hzb
    have hf : HasDerivAt (chain3Fn p).eval ((chain3Fn p).chainTotalDerivative.eval z) z :=
      hasDerivAt_eval_natural (chain3Fn p) z (IterExpChain_isCoherentAt 3 z)
    have hvm := hasDerivAt_vehicleM3 (chain3Fn p) d2 d1 c z hf
    have hred_z : (chain3Fn p).chainTotalDerivative.eval z
                    - (MachLib.Real.natCast d2 * (iterExp 0 z * iterExp 1 z)
                       + MachLib.Real.natCast d1 * iterExp 0 z + c) * (chain3Fn p).eval z = 0 := by
      have h := h_reduct z hza hzb
      rw [chain3Fn_chain3Reduce_eval] at h; exact h
    have hD0 : (chain3Fn p).chainTotalDerivative.eval z
                 * Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
                     + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
               + (chain3Fn p).eval z
                 * (Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
                       + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
                    * ((-MachLib.Real.natCast d2) * (iterExp 0 z * iterExp 1 z)
                       + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c))) = 0 := by
      rw [vehicle3_deriv_factor ((chain3Fn p).chainTotalDerivative.eval z) ((chain3Fn p).eval z)
            (Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
              + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z))
            (MachLib.Real.natCast d2) (MachLib.Real.natCast d1) (iterExp 0 z) (iterExp 1 z) c,
          hred_z, MachLib.Real.mul_zero]
    rwa [hD0] at hvm
  have hVeq : ∀ z₁ z₂, a < z₁ → z₂ < b → z₁ < z₂ → V z₁ = V z₂ := by
    intro z₁ z₂ hz₁a hz₂b hz₁z₂
    obtain ⟨cc, f', hcc1, hcc2, hderiv_cc, hmvt⟩ :=
      mean_value_theorem V z₁ z₂ hz₁z₂
        (fun c' hc'1 hc'2 => ⟨0, hVderiv c' (lt_trans_ax hz₁a hc'1) (lt_trans_ax hc'2 hz₂b)⟩)
    have hf'0 : f' = 0 :=
      HasDerivAt_unique V f' 0 cc hderiv_cc
        (hVderiv cc (lt_trans_ax hz₁a hcc1) (lt_trans_ax hcc2 hz₂b))
    rw [hf'0, zero_mul] at hmvt
    revert hmvt
    generalize V z₁ = v1
    generalize V z₂ = v2
    intro hmvt
    calc v1 = v2 - (v2 - v1) := by mach_ring
      _ = v2 - 0 := by rw [hmvt]
      _ = v2 := by mach_ring
  have hVz₀ : V z₀ ≠ 0 := fun h => hne₀ ((vehicleM3_zero_iff (chain3Fn p) d2 d1 c z₀).mp h)
  intro z hza hzb hz_zero
  have hVz : V z = 0 := (vehicleM3_zero_iff (chain3Fn p) d2 d1 c z).mpr hz_zero
  rcases lt_total z z₀ with hlt | heq | hgt
  · rw [hVeq z z₀ hza hz₀b hlt] at hVz; exact hVz₀ hVz
  · rw [heq] at hVz; exact hVz₀ hVz
  · rw [← hVeq z₀ z hz₀a hzb hgt] at hVz; exact hVz₀ hVz

end MachLib.IterExpDepth3Vehicle
