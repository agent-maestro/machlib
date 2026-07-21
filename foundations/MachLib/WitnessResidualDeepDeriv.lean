import MachLib.WitnessResidualDeepGSignControl
import MachLib.WitnessResidualGrowthCompetitionDeriv

/-! # `growthCompetitionWitnessDeep`'s real derivative, cleared to match the `g`-sign-control tool

Mirrors `WitnessResidualGrowthCompetitionDeriv.lean`'s role for `growthCompetitionWitness`, but
with one extra layer of `exp` composition (since `T_D := exp(exp(A)) - exp(B)`, not `exp(A) - B`)
and a genuinely transcendental term (`U := exp(exp(A(z))) = exp(E/(E-p))`) that survives the
clearing instead of canceling out.

**The composition** (`growthCompetitionWitnessDeep_hasDerivAt`): built via `HasDerivAt_comp`
applied THREE times (once for `exp(A)`, once more for `exp(exp(A))`, once for `exp(B)`) then
`HasDerivAt_sub`, reusing `boundedNonConstantWitness_hasDerivAt` unchanged for both `A` and `B`.
One new wrinkle versus `growthCompetitionWitness`'s own composition: `HasDerivAt_comp`'s natural
output associates the derivative VALUE as `b·a` where `a` is itself already a product from the
previous composition step — producing `b·(a₁·a₂)`, not `(b·a₁)·a₂`. Rather than fighting this at
each step, `HasDerivAt_of_eq` re-anchors the function AND the value to a clean, uniformly-shaped
form immediately after each composition, so associativity mismatches never compound across
multiple layers.

**The clearing identity** (`growthCompetitionWitnessDeep_deriv_clear_denom`): `T_D'(z)·(E-p)²·
(E-q)² = exp(z)·E·[q·(E-p)² - U·p·(E-q)²]`, `U := exp(E/(E-p))`. Verified numerically (random
substitution respecting the four defining constraints, then against a finite-difference ground
truth for the concrete `c1=1.5,c2=2.0` instance) before any of the Lean below. Built via an
ABSTRACT lemma (`deep_clear_denom_identity`) mirroring `clear_denom_identity`'s technique exactly
— `U` stays an opaque atom throughout (genuinely can't be cleared, being transcendental), while
`expA, Ap, expB, Bp` (standing for `exp(A(z))`, `A'(z)`, `exp(B(z))`, `B'(z)`) get substituted out
via their own multiplied-out facts (`exp_A_mul_denom`, `deriv_A_mul_denom`, both already proven
for `growthCompetitionWitness` and reused here unchanged). Needed `set_option maxHeartbeats
1000000` — a genuine complexity increase over `growthCompetitionWitness`'s own identity (one
extra layer of substitution pushes the intermediate polynomial past `mach_mpoly`'s default
budget). One new piece needed that `growthCompetitionWitness` never did:
`exp_A_eq_ratio` isolates `exp(A(z)) = E/(E-p)` via division (not just the multiplied form),
needed to express `U = exp(exp(A(z))) = exp(E/(E-p))` explicitly. -/

namespace MachLib
namespace Real

theorem growthCompetitionWitnessDeep_hasDerivAt (c1 c2 z : Real)
    (hApos : 0 < Real.exp (Real.exp z) - Real.log c1)
    (hBpos : 0 < Real.exp (Real.exp z) - Real.log c2) :
    HasDerivAt
      (fun w => Real.exp (Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c1)))
        - Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c2)))
      (Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
          * Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
          * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
        - Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c2))
          * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z)))
      z := by
  have hA := boundedNonConstantWitness_hasDerivAt c1 z hApos
  have hB := boundedNonConstantWitness_hasDerivAt c2 z hBpos
  have hExpA_raw := HasDerivAt_comp Real.exp
    (fun w => Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c1))
    (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
    (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
    z hA (HasDerivAt_exp _)
  have hExpA : HasDerivAt (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c1)))
      (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z)))
      z := HasDerivAt_of_eq _ _ _ z (fun y => rfl) hExpA_raw
  have hExpExpA_raw := HasDerivAt_comp Real.exp
    (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c1)))
    (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
      * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z)))
    (Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))))
    z hExpA (HasDerivAt_exp _)
  have hExpExpA : HasDerivAt
      (fun w => Real.exp (Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c1))))
      (Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
        * (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
          * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))))
      z := HasDerivAt_of_eq _ _ _ z (fun y => rfl) hExpExpA_raw
  have hExpB_raw := HasDerivAt_comp Real.exp
    (fun w => Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c2))
    (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z))
    (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c2)))
    z hB (HasDerivAt_exp _)
  have hExpB : HasDerivAt (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c2)))
      (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c2))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z)))
      z := HasDerivAt_of_eq _ _ _ z (fun y => rfl) hExpB_raw
  have hSub := HasDerivAt_sub _ _ _ _ z hExpExpA hExpB
  have hfinal : Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
        * (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
          * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z)))
      - Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c2))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z))
      = Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
          * Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
          * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
        - Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c2))
          * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z)) := by
    rw [mul_assoc]
  rwa [hfinal] at hSub

set_option maxHeartbeats 1000000 in
/-- Abstract clearing identity for `growthCompetitionWitnessDeep`'s raw derivative, mirroring
`clear_denom_identity`'s role but with `U` (standing for `exp(exp(A(z)))`) staying as an opaque
atom throughout, since it's genuinely transcendental here — no amount of clearing removes it. -/
theorem deep_clear_denom_identity {U expA Ap expB Bp E p q ez : Real}
    (hexpAmul : expA * (E - p) = E)
    (hApmul : Ap * (E - p) = -(ez * p))
    (hexpBmul : expB * (E - q) = E)
    (hBpmul : Bp * (E - q) = -(ez * q)) :
    (U * expA * Ap - expB * Bp) * (E - p) * (E - p) * (E - q) * (E - q)
      = ez * E * (q * (E - p) * (E - p) - U * p * (E - q) * (E - q)) := by
  have step1 : (U * expA * Ap - expB * Bp) * (E - p)
      = U * (expA * (E - p)) * Ap - expB * Bp * (E - p) := by
    mach_mpoly [U, expA, Ap, expB, Bp, E, p]
  rw [hexpAmul] at step1
  have step2 : (U * expA * Ap - expB * Bp) * (E - p) * (E - p)
      = U * E * (Ap * (E - p)) - expB * Bp * (E - p) * (E - p) := by
    rw [step1]; mach_mpoly [U, E, Ap, expB, Bp, p]
  rw [hApmul] at step2
  have step3 : (U * expA * Ap - expB * Bp) * (E - p) * (E - p) * (E - q)
      = U * E * (-(ez * p)) * (E - q) - (expB * (E - q)) * Bp * (E - p) * (E - p) := by
    rw [step2]; mach_mpoly [U, E, ez, p, expB, Bp, q]
  rw [hexpBmul] at step3
  have step4 : (U * expA * Ap - expB * Bp) * (E - p) * (E - p) * (E - q) * (E - q)
      = U * E * (-(ez * p)) * (E - q) * (E - q) - E * (Bp * (E - q)) * (E - p) * (E - p) := by
    rw [step3]; mach_mpoly [U, E, ez, p, q, Bp]
  rw [hBpmul] at step4
  rw [step4]
  mach_mpoly [U, E, ez, p, q]

/-- `exp(A(z)) = E/(E-p)`, isolating `exp_A_mul_denom`'s multiplied form via division. -/
theorem exp_A_eq_ratio (c z : Real) (hpos : 0 < Real.exp (Real.exp z) - Real.log c) :
    Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c))
      = Real.exp (Real.exp z) / (Real.exp (Real.exp z) - Real.log c) := by
  have hmul := exp_A_mul_denom c z hpos
  have hne : Real.exp (Real.exp z) - Real.log c ≠ 0 := ne_of_gt hpos
  have hinv : (Real.exp (Real.exp z) - Real.log c) * (1 / (Real.exp (Real.exp z) - Real.log c)) = 1 :=
    mul_inv _ hne
  have h1 : Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c))
        * (Real.exp (Real.exp z) - Real.log c) * (1 / (Real.exp (Real.exp z) - Real.log c))
      = Real.exp (Real.exp z) * (1 / (Real.exp (Real.exp z) - Real.log c)) := by rw [hmul]
  rw [mul_assoc, hinv, mul_one_ax] at h1
  rw [h1]
  exact (div_def _ _ hne).symm

/-- **The full cleared-denominator identity for `growthCompetitionWitnessDeep`'s raw derivative.**
`T_D'(z)·(E-p)²·(E-q)² = exp(z)·E·[q·(E-p)² - U·p·(E-q)²]`, `U := exp(E/(E-p)) = exp(exp(A(z)))`. -/
theorem growthCompetitionWitnessDeep_deriv_clear_denom (c1 c2 z : Real)
    (hApos : 0 < Real.exp (Real.exp z) - Real.log c1)
    (hBpos : 0 < Real.exp (Real.exp z) - Real.log c2) :
    (Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
        * Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
      - Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c2))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z)))
      * (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) - Real.log c1)
      * (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2)
      = Real.exp z * Real.exp (Real.exp z)
        * (Real.log c2 * (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) - Real.log c1)
          - Real.exp (Real.exp (Real.exp z) / (Real.exp (Real.exp z) - Real.log c1)) * Real.log c1
            * (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2)) := by
  have hU : Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
      = Real.exp (Real.exp (Real.exp z) / (Real.exp (Real.exp z) - Real.log c1)) := by
    rw [exp_A_eq_ratio c1 z hApos]
  rw [hU]
  exact deep_clear_denom_identity (exp_A_mul_denom c1 z hApos) (deriv_A_mul_denom c1 z hApos)
    (exp_A_mul_denom c2 z hBpos) (deriv_A_mul_denom c2 z hBpos)

/-- **The sign bridge, negative side.** Divides the cleared identity back out through the
known-positive `(E-p)²·(E-q)²` — same technique as `growthCompetitionWitness_deriv_neg_of_quad_neg`,
reusing `neg_of_mul_neg_pos` (`WitnessResidualGrowthCompetitionDeriv.lean`) unchanged. -/
theorem growthCompetitionWitnessDeep_deriv_neg_of_quad_neg (c1 c2 z : Real)
    (hApos : 0 < Real.exp (Real.exp z) - Real.log c1)
    (hBpos : 0 < Real.exp (Real.exp z) - Real.log c2)
    (hquad : Real.log c2 * (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) - Real.log c1)
        - Real.exp (Real.exp (Real.exp z) / (Real.exp (Real.exp z) - Real.log c1)) * Real.log c1
          * (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2) < 0) :
    Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
        * Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
      - Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c2))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z))
      < 0 := by
  have hident := growthCompetitionWitnessDeep_deriv_clear_denom c1 c2 z hApos hBpos
  have hrhs_neg := mul_neg_of_pos_of_neg_local
    (mul_pos (Real.exp_pos z) (Real.exp_pos (Real.exp z))) hquad
  rw [← hident] at hrhs_neg
  have hBpossq : 0 < (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2) :=
    mul_pos hBpos hBpos
  have hdenom_pos : 0 < (Real.exp (Real.exp z) - Real.log c1)
      * ((Real.exp (Real.exp z) - Real.log c1)
        * ((Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2))) :=
    mul_pos hApos (mul_pos hApos hBpossq)
  rw [mul_assoc, mul_assoc, mul_assoc] at hrhs_neg
  exact neg_of_mul_neg_pos hrhs_neg hdenom_pos

/-- **The sign bridge, positive side.** Mirror of the above, for `strictMono_of_deriv_pos`. -/
theorem growthCompetitionWitnessDeep_deriv_pos_of_quad_pos (c1 c2 z : Real)
    (hApos : 0 < Real.exp (Real.exp z) - Real.log c1)
    (hBpos : 0 < Real.exp (Real.exp z) - Real.log c2)
    (hquad : 0 < Real.log c2 * (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) - Real.log c1)
        - Real.exp (Real.exp (Real.exp z) / (Real.exp (Real.exp z) - Real.log c1)) * Real.log c1
          * (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2)) :
    0 < Real.exp (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
        * Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
      - Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c2))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z)) := by
  have hident := growthCompetitionWitnessDeep_deriv_clear_denom c1 c2 z hApos hBpos
  have hrhs_pos : 0 < Real.exp z * Real.exp (Real.exp z)
      * (Real.log c2 * (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) - Real.log c1)
        - Real.exp (Real.exp (Real.exp z) / (Real.exp (Real.exp z) - Real.log c1)) * Real.log c1
          * (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2)) :=
    mul_pos (mul_pos (Real.exp_pos z) (Real.exp_pos (Real.exp z))) hquad
  rw [← hident] at hrhs_pos
  have hBpossq : 0 < (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2) :=
    mul_pos hBpos hBpos
  have hdenom_pos : 0 < (Real.exp (Real.exp z) - Real.log c1)
      * ((Real.exp (Real.exp z) - Real.log c1)
        * ((Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) - Real.log c2))) :=
    mul_pos hApos (mul_pos hApos hBpossq)
  rw [mul_assoc, mul_assoc, mul_assoc] at hrhs_pos
  exact pos_of_mul_pos_right hrhs_pos hdenom_pos

end Real
end MachLib
