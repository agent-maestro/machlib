import MachLib.WitnessResidualCancellationGeneral
import MachLib.EMLZeroCrossingDomainSplit

/-!
# The "bounded ⟹ constant" conjecture is FALSE: an explicit counterexample

The previous file asked whether every bounded (above) EML tree is necessarily constant — if true,
this would close the whole witness-finding residual (hence the axiom) vacuously. Worked out on
paper first, then checked numerically before formalizing (per this project's established
discipline): it's FALSE. This file exhibits an explicit, bounded, genuinely non-constant EML tree.

**The construction.** `T1 := eml var (eml (eml var (const 1)) (const c))`, for `1 < c` and
`log c < 1` (equivalently `1 < c < e`). Unfolding: `T1.eval x = exp(x) - log(exp(exp(x)) -
log c)`.

**Why it's bounded — the key algebraic trick.** Write `w := exp(exp(x))`, always `> 1` (since
`exp(x) > 0`). Both bounds reduce, via applying `exp` (strictly increasing) to a candidate
inequality and using `exp∘log = id`, to trivial facts:
- **Lower bound `T1.eval x > 0`**: equivalent to `exp(exp(x)) > exp(exp(x)) - log c`, i.e.
  `0 > -log c`, i.e. `log c > 0` — true since `c > 1`.
- **Upper bound `T1.eval x < -log(1 - log c)`**: equivalent (after multiplying through by
  `exp(exp(x))` and using `exp(log(1-log c)) = 1 - log c`) to `log c < exp(exp(x)) · log c`, i.e.
  `1 < exp(exp(x))`, i.e. `0 < exp(x)` — always true.

Neither bound needed `x` to range over any restricted set — both hold for EVERY real `x`, giving a
UNIFORM bound, not an asymptotic one. Numerically checked before formalizing (`c=2`: values
range from `≈1.166` at `x=-5` down toward `0` at `x=+∞`, staying below the bound `≈1.181`).

**Why it's non-constant — strictly, in fact.** `T1`'s derivative works out (chain + quotient rule)
to `-exp(x)·log(c) / (exp(exp(x)) - log c)` — strictly NEGATIVE everywhere. `T1` is strictly
DECREASING on all of `ℝ`.

**What this settles.** The witness-finding residual's hypothesis ("`T1` bounded above and
non-constant") is NOT vacuous — genuine examples exist. The conjecture from the previous entry is
refuted.

**A `mach_ring` gotcha found while building this, worth recording precisely.** `mach_ring` fails
— not merely "sometimes needs a patch" as noted twice before, but reliably — on goals where a
single sub-expression (a bare variable OR a product) needs to be recognized as the SAME quantity
after appearing multiplied into a LARGER product on one side and standing separately on the
other, e.g. `a*b + (-b + -(a*b)) = -b` (fails) vs. the identical-looking `X + (-b + -X) = -b` with
`X` a genuinely free variable (succeeds) — even `generalize a*b = X` first does NOT fix it (the
post-`generalize` goal LOOKS identical to the free-variable version but still fails). The reliable
fix throughout this file: never let `mach_ring` see a repeated non-atomic sub-term inside a
multi-term sum or a multiply-then-regroup identity — instead perform the regrouping via explicit
`rw [mul_comm, mul_assoc, ...]` first, leaving `mach_ring` only pure distribution or 2-term
cancellation (both of which it handles correctly).
-/

namespace MachLib
namespace Real

/-- `a < b → -b < -a`. Built locally via `add_comm`/`add_assoc`/`add_neg`/`zero_add` only —
deliberately avoiding `mach_ring` for this shape (see the module docstring's gotcha). -/
theorem neg_lt_neg_local {a b : Real} (h : a < b) : -b < -a := by
  have h2 := add_lt_add_left h (-a + -b)
  have e1 : (-a + -b) + a = -b := by
    rw [add_assoc, add_comm (-b) a, ← add_assoc, add_comm (-a) a, add_neg, zero_add]
  have e2 : (-a + -b) + b = -a := by
    rw [add_assoc, add_comm (-b) b, add_neg, add_zero]
  rwa [e1, e2] at h2

/-- `a < b → c - b < c - a` — subtracting a larger amount from the same base gives a smaller
result. Derived from `neg_lt_neg_local`. -/
theorem sub_lt_sub_left_local {a b : Real} (c : Real) (h : a < b) : c - b < c - a := by
  have h2 := add_lt_add_left (neg_lt_neg_local h) c
  have e1 : c + -b = c - b := by mach_ring
  have e2 : c + -a = c - a := by mach_ring
  rwa [e1, e2] at h2

/-- The concrete tree: `eml var (eml (eml var (const 1)) (const c))`. -/
noncomputable def boundedNonConstantWitness (c : Real) : EMLTree :=
  EMLTree.eml EMLTree.var
    (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1)) (EMLTree.const c))

/-- Structural unfolding: `T1.eval x = exp(x) - log(exp(exp(x)) - log c)`. -/
theorem boundedNonConstantWitness_eval (c x : Real) :
    (boundedNonConstantWitness c).eval x
      = Real.exp x - Real.log (Real.exp (Real.exp x) - Real.log c) := by
  show Real.exp x -
      Real.log (Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x) - Real.log c) = _
  have h1 : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  rw [h1, log_one]
  have h2 : Real.exp x - 0 = Real.exp x := sub_zero _
  rw [h2]

/-- `1 < exp(exp x)`, for any `x` — since `exp x > 0` and `exp` is strictly increasing past
`exp 0 = 1`. -/
theorem one_lt_exp_exp (x : Real) : (1 : Real) < Real.exp (Real.exp x) := by
  have h := Real.exp_lt (Real.exp_pos x)
  rwa [Real.exp_zero] at h

/-- `B.eval x := exp(exp x) - log c` is strictly positive throughout, given `log c < 1` — the
well-definedness fact keeping the whole construction in `log`'s real (non-clamped) branch. -/
theorem boundedNonConstantWitness_Bpos {c : Real} (hc1 : Real.log c < 1) (x : Real) :
    0 < Real.exp (Real.exp x) - Real.log c := by
  have h2 : Real.log c < Real.exp (Real.exp x) := lt_trans_ax hc1 (one_lt_exp_exp x)
  have e := sub_lt_sub_right_of_lt (r := Real.log c) h2
  have e2 : Real.log c - Real.log c = 0 := by mach_ring
  rwa [e2] at e

/-- **Lower bound**: `0 < T1.eval x`, for ANY `x`, given `c > 1`. Reduces (via `log_lt_log` on
`B.eval x < exp(exp x)`, then `log_exp`) to the trivial fact `0 < log c`. -/
theorem boundedNonConstantWitness_pos {c : Real} (hc : 1 < c) (hc1 : Real.log c < 1) (x : Real) :
    0 < (boundedNonConstantWitness c).eval x := by
  rw [boundedNonConstantWitness_eval]
  have hBpos : 0 < Real.exp (Real.exp x) - Real.log c := boundedNonConstantWitness_Bpos hc1 x
  have hlog_pos : 0 < Real.log c := log_pos_of_gt_one hc
  have hBlt : Real.exp (Real.exp x) - Real.log c < Real.exp (Real.exp x) := by
    have h := add_lt_add_left (neg_neg_of_pos hlog_pos) (Real.exp (Real.exp x))
    have e1 : Real.exp (Real.exp x) + -Real.log c = Real.exp (Real.exp x) - Real.log c := by
      mach_ring
    have e2 : Real.exp (Real.exp x) + 0 = Real.exp (Real.exp x) := add_zero _
    rwa [e1, e2] at h
  have hkey := log_lt_log hBpos hBlt
  rw [log_exp] at hkey
  have e := sub_lt_sub_right_of_lt (r := Real.log (Real.exp (Real.exp x) - Real.log c)) hkey
  have e2 : Real.log (Real.exp (Real.exp x) - Real.log c)
      - Real.log (Real.exp (Real.exp x) - Real.log c) = 0 := by mach_ring
  rwa [e2] at e

/-- **Upper bound**: `T1.eval x < -log(1 - log c)`, for ANY `x`, given `1 < c` and `log c < 1`.
Reduces, via `log_mul` (splitting `log(exp(exp x)·(1-log c))`) and `log_lt_log` on the algebraic
inequality `exp(exp x)·(1-log c) < B.eval x`, to the trivial fact `1 < exp(exp x)`
(`one_lt_exp_exp`). -/
theorem boundedNonConstantWitness_upper_bound {c : Real} (hc : 1 < c) (hc1 : Real.log c < 1)
    (x : Real) :
    (boundedNonConstantWitness c).eval x < -Real.log (1 - Real.log c) := by
  rw [boundedNonConstantWitness_eval]
  have hlog_pos : 0 < Real.log c := log_pos_of_gt_one hc
  have h1mlog_pos : 0 < 1 - Real.log c := sub_pos_of_lt hc1
  have hBpos : 0 < Real.exp (Real.exp x) - Real.log c := boundedNonConstantWitness_Bpos hc1 x
  have hone : (1 : Real) < Real.exp (Real.exp x) := one_lt_exp_exp x
  have hmul0 : (1 : Real) * Real.log c < Real.exp (Real.exp x) * Real.log c :=
    mul_lt_mul_of_pos_right hone hlog_pos
  have hmul : Real.log c < Real.exp (Real.exp x) * Real.log c := by
    have e : (1 : Real) * Real.log c = Real.log c := by mach_ring
    rwa [e] at hmul0
  have halg : Real.exp (Real.exp x) * (1 - Real.log c) < Real.exp (Real.exp x) - Real.log c := by
    have hd : Real.exp (Real.exp x) * (1 - Real.log c)
        = Real.exp (Real.exp x) - Real.exp (Real.exp x) * Real.log c := by mach_ring
    rw [hd]
    exact sub_lt_sub_left_local (Real.exp (Real.exp x)) hmul
  have hlogprod : Real.log (Real.exp (Real.exp x) * (1 - Real.log c))
      = Real.log (Real.exp (Real.exp x)) + Real.log (1 - Real.log c) :=
    log_mul (Real.exp_pos _) h1mlog_pos
  have hlt := log_lt_log (mul_pos (Real.exp_pos _) h1mlog_pos) halg
  rw [hlogprod, log_exp] at hlt
  have step1 : Real.exp x
      < Real.log (Real.exp (Real.exp x) - Real.log c) - Real.log (1 - Real.log c) := by
    have h := sub_lt_sub_right_of_lt (r := Real.log (1 - Real.log c)) hlt
    have e : Real.exp x + Real.log (1 - Real.log c) - Real.log (1 - Real.log c) = Real.exp x := by
      mach_ring
    rwa [e] at h
  have step2 := sub_lt_sub_right_of_lt (r := Real.log (Real.exp (Real.exp x) - Real.log c)) step1
  have e2 : Real.log (Real.exp (Real.exp x) - Real.log c) - Real.log (1 - Real.log c)
      - Real.log (Real.exp (Real.exp x) - Real.log c) = -Real.log (1 - Real.log c) := by mach_ring
  rwa [e2] at step2

/-- `B(x) := exp(exp x) - log c`'s raw derivative: `exp(exp x)·exp x` (chain rule around
`exp∘exp`, minus the constant `log c` contributing nothing). -/
theorem boundedNonConstantWitness_hasDerivAt_B (c z : Real) :
    HasDerivAt (fun x => Real.exp (Real.exp x) - Real.log c)
      (Real.exp (Real.exp z) * Real.exp z) z := by
  have hexp_exp :
      HasDerivAt (fun x => Real.exp (Real.exp x)) (Real.exp (Real.exp z) * Real.exp z) z :=
    HasDerivAt_comp Real.exp Real.exp (Real.exp z) (Real.exp (Real.exp z)) z
      (HasDerivAt_exp z) (HasDerivAt_exp _)
  have hd := HasDerivAt_sub (fun x => Real.exp (Real.exp x)) (fun _ => Real.log c)
    (Real.exp (Real.exp z) * Real.exp z) 0 z hexp_exp (HasDerivAt_const _ z)
  have e : Real.exp (Real.exp z) * Real.exp z - 0 = Real.exp (Real.exp z) * Real.exp z :=
    sub_zero _
  rwa [e] at hd

/-- `T1(x) := exp x - log(B x)`'s raw derivative: `exp x - (1/B z)·(exp(exp z)·exp z)` — chain +
sub rules, reusing `boundedNonConstantWitness_hasDerivAt_B` for `B`'s own derivative. -/
theorem boundedNonConstantWitness_hasDerivAt (c z : Real)
    (hBpos : 0 < Real.exp (Real.exp z) - Real.log c) :
    HasDerivAt (fun x => Real.exp x - Real.log (Real.exp (Real.exp x) - Real.log c))
      (Real.exp z
        - 1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z)) z := by
  have hB := boundedNonConstantWitness_hasDerivAt_B c z
  have hlogB : HasDerivAt (fun x => Real.log (Real.exp (Real.exp x) - Real.log c))
      (1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z)) z :=
    HasDerivAt_comp Real.log (fun x => Real.exp (Real.exp x) - Real.log c)
      (Real.exp (Real.exp z) * Real.exp z) (1 / (Real.exp (Real.exp z) - Real.log c)) z
      hB (HasDerivAt_log_pos _ hBpos)
  exact HasDerivAt_sub Real.exp (fun x => Real.log (Real.exp (Real.exp x) - Real.log c))
    (Real.exp z) (1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
    z (HasDerivAt_exp z) hlogB

/-- **The derivative is strictly negative**: `T1` is strictly DECREASING everywhere, given
`1 < c`. Established by showing `(raw deriv) · B(z) = -exp(z)·log c < 0` — a pure polynomial
identity (no division ambiguity, regrouped via explicit `rw` rather than `mach_ring` — see the
module docstring's gotcha) — then concluding `raw deriv < 0` since `B(z) > 0`. -/
theorem boundedNonConstantWitness_deriv_neg {c : Real} (hc : 1 < c) (z : Real)
    (hBpos : 0 < Real.exp (Real.exp z) - Real.log c) :
    Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z)
      < 0 := by
  have hlog_pos : 0 < Real.log c := log_pos_of_gt_one hc
  have hBne : Real.exp (Real.exp z) - Real.log c ≠ 0 := ne_of_gt hBpos
  have hinv : (1 / (Real.exp (Real.exp z) - Real.log c))
      * (Real.exp (Real.exp z) - Real.log c) = 1 := by
    rw [mul_comm]; exact mul_inv _ hBne
  have hprod : (Real.exp z
        - 1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
      * (Real.exp (Real.exp z) - Real.log c) = -(Real.exp z * Real.log c) := by
    have step1 : (Real.exp z
          - 1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
        * (Real.exp (Real.exp z) - Real.log c)
        = Real.exp z * (Real.exp (Real.exp z) - Real.log c)
          - (1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
            * (Real.exp (Real.exp z) - Real.log c) := by mach_ring
    rw [step1]
    have step2 : (1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
        * (Real.exp (Real.exp z) - Real.log c)
        = (1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) - Real.log c))
          * (Real.exp (Real.exp z) * Real.exp z) := by
      rw [mul_assoc, mul_comm (Real.exp (Real.exp z) * Real.exp z)
        (Real.exp (Real.exp z) - Real.log c), ← mul_assoc]
    rw [step2, hinv]
    have step3 : Real.exp z * (Real.exp (Real.exp z) - Real.log c) - 1 * (Real.exp (Real.exp z) * Real.exp z)
        = -(Real.exp z * Real.log c) := by mach_ring
    exact step3
  have hnumneg : -(Real.exp z * Real.log c) < 0 :=
    neg_neg_of_pos (mul_pos (Real.exp_pos z) hlog_pos)
  rw [← hprod] at hnumneg
  rcases lt_total
      (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
      0 with h | h | h
  · exact h
  · exfalso
    rw [h] at hnumneg
    have e0 : (0 : Real) * (Real.exp (Real.exp z) - Real.log c) = 0 := by mach_ring
    rw [e0] at hnumneg
    exact lt_irrefl_ax 0 hnumneg
  · exfalso
    have hpos := mul_pos h hBpos
    exact lt_irrefl_ax 0 (lt_trans_ax hpos hnumneg)

/-- **`T1` is strictly decreasing on all of `ℝ`**, hence in particular NON-CONSTANT and
INJECTIVE — via `strictAnti_of_deriv_neg` (MVT-based) fed `boundedNonConstantWitness_deriv_neg`. -/
theorem boundedNonConstantWitness_strictAnti {c : Real} (hc : 1 < c) (hc1 : Real.log c < 1)
    (x y : Real) (hxy : x < y) :
    (boundedNonConstantWitness c).eval y < (boundedNonConstantWitness c).eval x := by
  have heq : ∀ w, (boundedNonConstantWitness c).eval w
      = Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c) := boundedNonConstantWitness_eval c
  rw [heq, heq]
  apply strictAnti_of_deriv_neg
    (fun w => Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c)) x y hxy
  · intro w _ _
    exact ⟨_, boundedNonConstantWitness_hasDerivAt c w (boundedNonConstantWitness_Bpos hc1 w)⟩
  · intro w f' _ _ hderiv
    rw [HasDerivAt_unique _ _ _ w hderiv
      (boundedNonConstantWitness_hasDerivAt c w (boundedNonConstantWitness_Bpos hc1 w))]
    exact boundedNonConstantWitness_deriv_neg hc w (boundedNonConstantWitness_Bpos hc1 w)

/-- **Non-constant**: `T1.eval 0 ≠ T1.eval 1` — immediate from strict monotonicity. -/
theorem boundedNonConstantWitness_not_constant {c : Real} (hc : 1 < c) (hc1 : Real.log c < 1) :
    ∃ x y : Real, (boundedNonConstantWitness c).eval x ≠ (boundedNonConstantWitness c).eval y := by
  refine ⟨0, 1, ?_⟩
  intro heq
  have h := boundedNonConstantWitness_strictAnti hc hc1 0 1 (by
    have hh := add_lt_add_left zero_lt_one_ax (0 : Real)
    have e1 : (0 : Real) + 0 = 0 := add_zero _
    have e2 : (0 : Real) + 1 = 1 := zero_add _
    rwa [e1, e2] at hh)
  rw [heq] at h
  exact lt_irrefl_ax _ h

/-- **The counterexample, packaged.** For `1 < c < e`, `boundedNonConstantWitness c` is bounded
above (`< -log(1-log c)`) and non-constant. Refutes "every bounded EML tree is constant". -/
theorem bounded_nonconstant_eml_tree_exists (c : Real) (hc : 1 < c) (hc1 : Real.log c < 1) :
    (∀ x, (boundedNonConstantWitness c).eval x < -Real.log (1 - Real.log c)) ∧
    (∃ x y, (boundedNonConstantWitness c).eval x ≠ (boundedNonConstantWitness c).eval y) :=
  ⟨fun x => boundedNonConstantWitness_upper_bound hc hc1 x,
   boundedNonConstantWitness_not_constant hc hc1⟩

end Real
end MachLib
