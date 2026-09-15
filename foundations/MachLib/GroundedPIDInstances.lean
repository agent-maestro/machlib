import MachLib.GroundedInstanceArith

/-!
# The PID certificates, instantiated on the literal, libm-finiteness and `u + u ≤ 1` axioms

`FPGrounding.lean`'s `pid_grounded` and `pid_<prim>_grounded` take the float side conditions `hsafe : FloatSafe …` of the
PID law `1.5·e + 0.4·i + 0.05·d` and, for some primitives, a finite primitive result. Until 2026-09-14 none of them could be
instantiated: no axiom said a `Float` literal was finite or what its real value was, nothing concluded a runtime `exp`,
`sinh` or `cosh` result finite, and `u < 1` gave no lower bound on a gain's real value, so no `gain × input` product was
provably `0` or at least `DBL_MIN`. The owner approved the facts that were missing, each measured or witnessed first:
`float_lit_1_5`, `float_lit_0_4`, `float_lit_0_05`, `real_exp_finite`, `real_sinh_finite`, `real_cosh_finite` and
`u_le_half`. This module instantiates the certificates on stated input domains, and every instance has a specimen.

## The domains, in words

  * `PIDInputDomain env B δ`: the channels `e`, `i`, `d` are finite floats whose real values are at most `B` in magnitude
    and each `0` or at least `δ` in magnitude, with `DBL_MIN ≤ 0.025·δ` and `60·B ≤ DBL_MAX`. On it the PID law's computed
    value and its exact value are both at most `60·B` in magnitude (`pidRawEML_domain_facts`).
  * `PIDPositiveDomain env B δ`: that, with every channel's real value at least `δ > 0`. On it both values are at least
    `0.0125·δ` (`pidRawEML_lower`).
  * The primitives with a symmetric range take `R` with `60·B ≤ R`, and: `R < 1` (`asin`, `acos`); `R ≤ 0.5`, which is
    below `π/2` (`tan`); `R ≤ 710` (`sinh`, `cosh`); `R ≤ 500`, which keeps `exp R` finite and `exp (−R)` at least
    `DBL_MIN` (`exp`). `log`, `sqrt` and `log10` use the positive domain, on `[0.0125·δ, 60·B]`.

`pidSpecimenEnv` sets every input to `floatOfR 0.004`, which reads back between `0.002` and `0.008`, and
`pidSpecimen_domain` shows it is in the positive domain at `B = 0.008`, `δ = 0.002`. Every specimen below uses it (with
`R = 0.5`). Its inputs are nonzero, so each product meets `ProductsNormal` through the `DBL_MIN` branch, not the zero branch.

## What is not instantiated here

  * `pid_log_cosh_grounded` needs `lo ≤ realToR (cosh of the PID law's float)` with `0 < lo`. `real_cosh_rounds` puts that
    value no lower than `cosh x − 4u·cosh R`, and `u + u ≤ 1` allows `4u = 2`, so no positive `lo` follows for any `R`.
    It needs a smaller bound on `u` (for instance `u ≤ 1/8` with `R ≤ 1/2`) or a measured lower bound on the runtime
    `cosh`'s read-back value; neither was approved.
  * The `LibmBudget` restatements (`pid_sin_at_budget` and siblings): their `hsafe` now discharges, but `RuntimeLibmBudget B`
    needs `real_abs_eps = 0`, and no axiom constrains `real_abs_eps` at all (nor `real_sin_eps`, `real_cos_eps`,
    `real_atan_eps` beyond being bounds).
-/

namespace Certcom

open MachLib MachLib.Real

/-! ## 1. The domains -/

/-- **The PID instances' input domain.** The three channels `e`, `i`, `d` are finite floats; each real value is at most `B`
in magnitude and is `0` or at least `δ` in magnitude; `0 ≤ δ` and `DBL_MIN ≤ 0.025·δ`; and `60·B ≤ DBL_MAX`. The constants
come from the gains: each reads back between `0.025` and `3.0`, so a `gain × input` product is `0` or at least `DBL_MIN`,
and every node of the law stays within `DBL_MAX` with a factor `2` to spare per rounding. -/
structure PIDInputDomain (env : Env) (B δ : MachLib.Real) : Prop where
  fin_e : (env "e").toF.isFinite = true
  fin_i : (env "i").toF.isFinite = true
  fin_d : (env "d").toF.isFinite = true
  bound_e : abs (realToR (env "e").toF) ≤ B
  bound_i : abs (realToR (env "i").toF) ≤ B
  bound_d : abs (realToR (env "d").toF) ≤ B
  floor_e : realToR (env "e").toF = 0 ∨ δ ≤ abs (realToR (env "e").toF)
  floor_i : realToR (env "i").toF = 0 ∨ δ ≤ abs (realToR (env "i").toF)
  floor_d : realToR (env "d").toF = 0 ∨ δ ≤ abs (realToR (env "d").toF)
  delta_nonneg : 0 ≤ δ
  floor_min : dblMin ≤ 0.025 * δ
  size : 60.0 * B ≤ dblMax

/-- **The positive input domain**, for `log`, `sqrt` and `log10`: the PID domain with every channel's real value at least
`δ > 0`. -/
structure PIDPositiveDomain (env : Env) (B δ : MachLib.Real) : Prop extends PIDInputDomain env B δ where
  delta_pos : 0 < δ
  pos_e : δ ≤ realToR (env "e").toF
  pos_i : δ ≤ realToR (env "i").toF
  pos_d : δ ≤ realToR (env "d").toF

/-! ## 2. The nodes of the PID law -/

theorem zero_le_point_zero_two_five : (0 : MachLib.Real) ≤ 0.025 := le_of_lt (realOfScientific_pos 25 true 3 (by decide))

theorem one_le_natCast_of {n : Nat} (h : 1 ≤ n) : (1 : MachLib.Real) ≤ natCast n := by
  have h1 := natCast_le_natCast_of_nat_le h
  rw [natCast_one] at h1
  exact h1

/-- `c·B + d·B = s·B` when `c + d = s`. -/
theorem decimal_mul_add_mul {B : MachLib.Real} (c d s : MachLib.Real) (h : c + d = s) : c * B + d * B = s * B := by
  rw [← h]; mach_ring

/-- One `gain × input` node: finite, its exact product `0` or at least `DBL_MIN`, the exact product at most `3·B` and the
computed one at most `6·B` in magnitude, and the rounding fact. -/
theorem pid_product_facts {g v : Float} {B δ : MachLib.Real}
    (hg : g.isFinite = true ∧ (0.025 : MachLib.Real) ≤ realToR g ∧ realToR g ≤ 3.0)
    (hv : v.isFinite = true) (hvB : abs (realToR v) ≤ B) (hvf : realToR v = 0 ∨ δ ≤ abs (realToR v))
    (hδ : 0 ≤ δ) (hmin : dblMin ≤ 0.025 * δ) (hsize : 60.0 * B ≤ dblMax) :
    (g * v).isFinite = true ∧
    (realToR g * realToR v = 0 ∨ dblMin ≤ abs (realToR g * realToR v)) ∧
    abs (realToR g * realToR v) ≤ 3.0 * B ∧
    abs (realToR (g * v)) ≤ 6.0 * B ∧
    RoundsW u (realToR (g * v)) (realToR g * realToR v) := by
  obtain ⟨hgf, hglo, hghi⟩ := hg
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hvB
  have hg0 : 0 ≤ realToR g := le_trans zero_le_point_zero_two_five hglo
  have habsg : abs (realToR g) = realToR g := abs_of_nonneg hg0
  have hexact : abs (realToR g * realToR v) ≤ 3.0 * B := by
    rw [abs_mul, habsg]; exact mul_le_mul' hg0 hghi (abs_nonneg _) hvB
  have h3B : 3.0 * B ≤ dblMax := le_trans (mul_le_mul_of_nonneg_right (by grounded_decimal) hB0) hsize
  have hfin := real_fpfinite.mul _ _ hgf hv (le_trans hexact h3B)
  have hnorm : realToR g * realToR v = 0 ∨ dblMin ≤ abs (realToR g * realToR v) :=
    mul_normal_of_floors zero_le_point_zero_two_five hδ hmin (Or.inr (by rw [habsg]; exact hglo)) hvf
  have hr := real_fpbridge.mul _ _ hfin hnorm
  have hflt : abs (realToR (g * v)) ≤ (1 + u) * abs (realToR g * realToR v) := abs_le_one_add (roundsW_abs hr)
  have h2 : (1 + u) * abs (realToR g * realToR v) ≤ 2.0 * (3.0 * B) :=
    mul_le_mul' one_add_u_nonneg one_add_u_le_two_point_zero (abs_nonneg _) hexact
  have e : (2.0 : MachLib.Real) * (3.0 * B) = 6.0 * B := by
    rw [← mul_assoc, show (2.0 : MachLib.Real) * 3.0 = 6.0 from by grounded_decimal]
  exact ⟨hfin, hnorm, hexact, le_trans hflt (le_trans h2 (le_of_eq e)), hr⟩

/-- One sum node: finite when its exact sum is at most `DBL_MAX`, and the computed sum at most twice that bound. -/
theorem pid_sum_facts {a b : Float} {X Y : MachLib.Real} (ha : a.isFinite = true) (hb : b.isFinite = true)
    (haX : abs (realToR a) ≤ X) (hbY : abs (realToR b) ≤ Y) (hsize : X + Y ≤ dblMax) :
    (a + b).isFinite = true ∧ abs (realToR (a + b)) ≤ 2.0 * (X + Y) ∧
    RoundsW u (realToR (a + b)) (realToR a + realToR b) := by
  have hex : abs (realToR a + realToR b) ≤ X + Y := le_trans (abs_add _ _) (add_le_add haX hbY)
  have hfin := real_fpfinite.add _ _ ha hb (le_trans hex hsize)
  have hr := real_fpbridge.add _ _ hfin
  exact ⟨hfin, le_trans (abs_le_one_add (roundsW_abs hr))
    (mul_le_mul' one_add_u_nonneg one_add_u_le_two_point_zero (abs_nonneg _) hex), hr⟩

/-- **Every node of the PID law on its domain**: the three products and two sums compute finite floats, each product is
`0` or at least `DBL_MIN`, the rounding facts, and the computed and exact values are at most `60·B` in magnitude. -/
theorem pid_nodes {env : Env} {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    ((1.5 : Float) * (env "e").toF).isFinite = true ∧
    (realToR 1.5 * realToR (env "e").toF = 0 ∨ dblMin ≤ abs (realToR 1.5 * realToR (env "e").toF)) ∧
    RoundsW u (realToR ((1.5 : Float) * (env "e").toF)) (realToR 1.5 * realToR (env "e").toF) ∧
    ((0.4 : Float) * (env "i").toF).isFinite = true ∧
    (realToR 0.4 * realToR (env "i").toF = 0 ∨ dblMin ≤ abs (realToR 0.4 * realToR (env "i").toF)) ∧
    RoundsW u (realToR ((0.4 : Float) * (env "i").toF)) (realToR 0.4 * realToR (env "i").toF) ∧
    ((0.05 : Float) * (env "d").toF).isFinite = true ∧
    (realToR 0.05 * realToR (env "d").toF = 0 ∨ dblMin ≤ abs (realToR 0.05 * realToR (env "d").toF)) ∧
    RoundsW u (realToR ((0.05 : Float) * (env "d").toF)) (realToR 0.05 * realToR (env "d").toF) ∧
    ((1.5 : Float) * (env "e").toF + (0.4 : Float) * (env "i").toF).isFinite = true ∧
    RoundsW u (realToR ((1.5 : Float) * (env "e").toF + (0.4 : Float) * (env "i").toF))
      (realToR ((1.5 : Float) * (env "e").toF) + realToR ((0.4 : Float) * (env "i").toF)) ∧
    ((1.5 : Float) * (env "e").toF + (0.4 : Float) * (env "i").toF + (0.05 : Float) * (env "d").toF).isFinite = true ∧
    RoundsW u (realToR ((1.5 : Float) * (env "e").toF + (0.4 : Float) * (env "i").toF + (0.05 : Float) * (env "d").toF))
      (realToR ((1.5 : Float) * (env "e").toF + (0.4 : Float) * (env "i").toF)
        + realToR ((0.05 : Float) * (env "d").toF)) ∧
    abs (realToR ((1.5 : Float) * (env "e").toF + (0.4 : Float) * (env "i").toF + (0.05 : Float) * (env "d").toF))
      ≤ 60.0 * B ∧
    abs (realToR 1.5 * realToR (env "e").toF + realToR 0.4 * realToR (env "i").toF
      + realToR 0.05 * realToR (env "d").toF) ≤ 60.0 * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) h.bound_e
  obtain ⟨f1, n1, x1, p1, r1⟩ :=
    pid_product_facts gain_1_5_facts h.fin_e h.bound_e h.floor_e h.delta_nonneg h.floor_min h.size
  obtain ⟨f2, n2, x2, p2, r2⟩ :=
    pid_product_facts gain_0_4_facts h.fin_i h.bound_i h.floor_i h.delta_nonneg h.floor_min h.size
  obtain ⟨f3, n3, x3, p3, r3⟩ :=
    pid_product_facts gain_0_05_facts h.fin_d h.bound_d h.floor_d h.delta_nonneg h.floor_min h.size
  have e12 : 6.0 * B + 6.0 * B = 12.0 * B := decimal_mul_add_mul 6.0 6.0 12.0 (by grounded_decimal)
  have hs1size : 6.0 * B + 6.0 * B ≤ dblMax := by
    rw [e12]; exact le_trans (mul_le_mul_of_nonneg_right (by grounded_decimal) hB0) h.size
  obtain ⟨fs1, s1, rs1⟩ := pid_sum_facts f1 f2 p1 p2 hs1size
  have e24 : (2.0 : MachLib.Real) * (6.0 * B + 6.0 * B) = 24.0 * B := by
    rw [e12, ← mul_assoc, show (2.0 : MachLib.Real) * 12.0 = 24.0 from by grounded_decimal]
  have e30 : 24.0 * B + 6.0 * B = 30.0 * B := decimal_mul_add_mul 24.0 6.0 30.0 (by grounded_decimal)
  have hs2size : 24.0 * B + 6.0 * B ≤ dblMax := by
    rw [e30]; exact le_trans (mul_le_mul_of_nonneg_right (by grounded_decimal) hB0) h.size
  obtain ⟨fs2, s2, rs2⟩ := pid_sum_facts fs1 f3 (le_trans s1 (le_of_eq e24)) p3 hs2size
  have e60 : (2.0 : MachLib.Real) * (24.0 * B + 6.0 * B) = 60.0 * B := by
    rw [e30, ← mul_assoc, show (2.0 : MachLib.Real) * 30.0 = 60.0 from by grounded_decimal]
  have e9 : 3.0 * B + 3.0 * B + 3.0 * B = 9.0 * B := by
    rw [decimal_mul_add_mul 3.0 3.0 6.0 (by grounded_decimal), decimal_mul_add_mul 6.0 3.0 9.0 (by grounded_decimal)]
  have hexR : abs (realToR 1.5 * realToR (env "e").toF + realToR 0.4 * realToR (env "i").toF
      + realToR 0.05 * realToR (env "d").toF) ≤ 60.0 * B := by
    refine le_trans (abs_add _ _) (le_trans (add_le_add (le_trans (abs_add _ _) (add_le_add x1 x2)) x3) ?_)
    rw [e9]; exact mul_le_mul_of_nonneg_right (by grounded_decimal) hB0
  exact ⟨f1, n1, r1, f2, n2, r2, f3, n3, r3, fs1, rs1, fs2, rs2, le_trans s2 (le_of_eq e60), hexR⟩

/-- **On the PID domain, `FloatSafe` holds and the PID law's computed and exact values are at most `60·B`.** -/
theorem pidRawEML_domain_facts {env : Env} {B δ : MachLib.Real} (h : PIDInputDomain env B δ)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) :
    FloatSafe realToR i1 i2 env pidRawEML ∧
    abs (realToR (evalEML i1 i2 env pidRawEML).toF) ≤ 60.0 * B ∧
    abs (exactR realToR env pidRawEML) ≤ 60.0 * B := by
  obtain ⟨f1, n1, _, f2, n2, _, f3, n3, _, fs1, _, fs2, _, hfl, hex⟩ := pid_nodes h
  exact ⟨FloatSafe.add _ _ (FloatSafe.add _ _ (FloatSafe.mul _ _ (.lit _) (.var _) f1 n1)
      (FloatSafe.mul _ _ (.lit _) (.var _) f2 n2) fs1) (FloatSafe.mul _ _ (.lit _) (.var _) f3 n3) fs2, hfl, hex⟩

/-- A value correctly rounded from a non-negative exact value is at least half of it. -/
theorem half_le_of_roundsW {fl e : MachLib.Real} (he : 0 ≤ e) (hr : RoundsW u fl e) : 0.5 * e ≤ fl := by
  have h := roundsW_abs hr
  rw [abs_of_nonneg he] at h
  exact half_le_of_close he h

/-- **On the positive domain, the PID law's computed and exact values are at least `0.0125·δ`.** Each exact product is at
least `0.025·δ`, and each rounding loses at most half (`u + u ≤ 1`). -/
theorem pidRawEML_lower {env : Env} {B δ : MachLib.Real} (h : PIDPositiveDomain env B δ)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) :
    0.0125 * δ ≤ realToR (evalEML i1 i2 env pidRawEML).toF ∧ 0.0125 * δ ≤ exactR realToR env pidRawEML := by
  obtain ⟨_, _, r1, _, _, r2, _, _, r3, _, rs1, _, rs2, _, _⟩ := pid_nodes h.toPIDInputDomain
  have hδ0 := h.delta_nonneg
  have hk0 : (0 : MachLib.Real) ≤ 0.025 * δ := mul_nonneg zero_le_point_zero_two_five hδ0
  have q1 : 0.025 * δ ≤ realToR 1.5 * realToR (env "e").toF :=
    mul_le_mul' zero_le_point_zero_two_five gain_1_5_facts.2.1 hδ0 h.pos_e
  have q2 : 0.025 * δ ≤ realToR 0.4 * realToR (env "i").toF :=
    mul_le_mul' zero_le_point_zero_two_five gain_0_4_facts.2.1 hδ0 h.pos_i
  have q3 : 0.025 * δ ≤ realToR 0.05 * realToR (env "d").toF :=
    mul_le_mul' zero_le_point_zero_two_five gain_0_05_facts.2.1 hδ0 h.pos_d
  have hhalf0 : (0 : MachLib.Real) ≤ 0.5 := le_of_lt (realOfScientific_pos 5 true 1 (by decide))
  have e125 : (0.5 : MachLib.Real) * (0.025 * δ) = 0.0125 * δ := by
    rw [← mul_assoc, show (0.5 : MachLib.Real) * 0.025 = 0.0125 from by grounded_decimal]
  have e25 : 0.0125 * δ + 0.0125 * δ = 0.025 * δ := decimal_mul_add_mul 0.0125 0.0125 0.025 (by grounded_decimal)
  have lift : ∀ {fl e : MachLib.Real}, 0.025 * δ ≤ e → RoundsW u fl e → 0.0125 * δ ≤ fl := fun hq hr =>
    le_trans (le_of_eq e125.symm)
      (le_trans (mul_le_mul_of_nonneg_left hq hhalf0) (half_le_of_roundsW (le_trans hk0 hq) hr))
  have g1 := lift q1 r1
  have g2 := lift q2 r2
  have g3 := lift q3 r3
  have gs1 := lift (le_trans (le_of_eq e25.symm) (add_le_add g1 g2)) rs1
  have gs2 := lift (le_trans (le_of_eq e25.symm) (add_le_add gs1 g3)) rs2
  have hex : 0.0125 * δ ≤ realToR 1.5 * realToR (env "e").toF + realToR 0.4 * realToR (env "i").toF
      + realToR 0.05 * realToR (env "d").toF := by
    have hlt : 0.0125 * δ ≤ 0.025 * δ := mul_le_mul_of_nonneg_right (by grounded_decimal) hδ0
    refine le_trans hlt (le_trans q1 ?_)
    refine le_trans (le_add_of_nonneg_right (le_trans hk0 q2)) (le_add_of_nonneg_right (le_trans hk0 q3))
  exact ⟨gs2, hex⟩

/-- `0 < 0.0125·δ` for `0 < δ`. -/
theorem lo_pos_of_delta {δ : MachLib.Real} (h : 0 < δ) : (0 : MachLib.Real) < 0.0125 * δ :=
  mul_pos (realOfScientific_pos 125 true 4 (by decide)) h

/-- `0 ≤ R` when `60·B ≤ R` on a PID domain. -/
theorem range_nonneg {env : Env} {B δ R : MachLib.Real} (h : PIDInputDomain env B δ) (hBR : 60.0 * B ≤ R) : 0 ≤ R :=
  le_trans (mul_nonneg (le_of_lt (realOfScientific_pos 600 true 1 (by decide))) (le_trans (abs_nonneg _) h.bound_e)) hBR

/-! ## 3. The instances -/

/-- **`pid_grounded`, instantiated** on `PIDInputDomain`. -/
theorem pid_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc (absErr realToR env pidRawEML)
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC pidRawEML)).toF)
      (exactR realToR env pidRawEML) :=
  pid_grounded env (pidRawEML_domain_facts h _ _).1

/-- **`pid_tanh_grounded`, instantiated** on `PIDInputDomain`. -/
theorem pid_tanh_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc ((u + u) + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .tanh pidRawEML))).toF)
      (tanh (exactR realToR env pidRawEML)) :=
  pid_tanh_grounded env (pidRawEML_domain_facts h _ _).1

/-- **`pid_sin_grounded`, instantiated** on `PIDInputDomain`. -/
theorem pid_sin_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc (real_sin_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sin pidRawEML))).toF)
      (sin (exactR realToR env pidRawEML)) :=
  pid_sin_grounded env (pidRawEML_domain_facts h _ _).1

/-- **`pid_cos_grounded`, instantiated** on `PIDInputDomain`. -/
theorem pid_cos_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc (real_cos_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .cos pidRawEML))).toF)
      (cos (exactR realToR env pidRawEML)) :=
  pid_cos_grounded env (pidRawEML_domain_facts h _ _).1

/-- **`pid_atan_grounded`, instantiated** on `PIDInputDomain`. -/
theorem pid_atan_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc (real_atan_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .atan pidRawEML))).toF)
      (atan (exactR realToR env pidRawEML)) :=
  pid_atan_grounded env (pidRawEML_domain_facts h _ _).1

/-- **`pid_abs_grounded`, instantiated** on `PIDInputDomain`. -/
theorem pid_abs_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc (real_abs_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .abs pidRawEML))).toF)
      (abs (exactR realToR env pidRawEML)) :=
  pid_abs_grounded env (pidRawEML_domain_facts h _ _).1

/-- **`pid_exp_grounded`, instantiated** on `PIDInputDomain`, with `60·B ≤ R ≤ 500`, at `lo = −R`, `hi = R`. `hexp` is
`real_exp_finite` (the computed PID law is at most `R ≤ 709`), and `hnorm` is `DBL_MIN ≤ exp (−R)` (`dblMin_le_exp_neg`). -/
theorem pid_exp_grounded_instantiated (env : Env) {B δ R : MachLib.Real} (h : PIDInputDomain env B δ)
    (hBR : 60.0 * B ≤ R) (hR : R ≤ natCast 500) :
    AbsEnc ((u + u) * exp R + exp R * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .exp pidRawEML))).toF)
      (exp (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨l1, u1⟩ := abs_le_iff.mp (le_trans hfl hBR)
  obtain ⟨l2, u2⟩ := abs_le_iff.mp (le_trans hex hBR)
  have hexp : (stdI1 leanPrims .exp (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF).isFinite = true :=
    real_exp_finite _ (FloatSafe.add_isFinite hs) (le_trans u1 (le_trans hR (natCast_le_natCast_of_nat_le (by decide))))
  exact pid_exp_grounded env (-R) R hs hexp (dblMin_le_exp_neg hR) l1 u1 l2 u2

/-- **`pid_log_grounded`, instantiated** on `PIDPositiveDomain`, at `lo = 0.0125·δ`, `hi = 60·B`. -/
theorem pid_log_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDPositiveDomain env B δ) :
    AbsEnc (u * (abs (log (0.0125 * δ)) + abs (log (60.0 * B))) + (1 / (0.0125 * δ)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .ln pidRawEML))).toF)
      (log (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h.toPIDInputDomain (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨lo1, lo2⟩ := pidRawEML_lower h (stdI1 leanPrims) (stdI2 leanPrims)
  exact pid_log_grounded env (0.0125 * δ) (60.0 * B) (lo_pos_of_delta h.delta_pos) hs lo1 (le_of_abs_le hfl) lo2
    (le_of_abs_le hex)

/-- **`pid_sqrt_grounded`, instantiated** on `PIDPositiveDomain`, at `lo = 0.0125·δ`, `hi = 60·B`. -/
theorem pid_sqrt_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDPositiveDomain env B δ) :
    AbsEnc (u * sqrt (60.0 * B) + (1 / (sqrt (0.0125 * δ) + sqrt (0.0125 * δ))) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sqrt pidRawEML))).toF)
      (sqrt (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h.toPIDInputDomain (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨lo1, lo2⟩ := pidRawEML_lower h (stdI1 leanPrims) (stdI2 leanPrims)
  exact pid_sqrt_grounded env (0.0125 * δ) (60.0 * B) (lo_pos_of_delta h.delta_pos) hs lo1 (le_of_abs_le hfl) lo2
    (le_of_abs_le hex)

/-- **`pid_log10_grounded`, instantiated** on `PIDPositiveDomain`, at `lo = 0.0125·δ`, `hi = 60·B`. -/
theorem pid_log10_grounded_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDPositiveDomain env B δ) :
    AbsEnc ((u + u + u) * (abs (log10 (0.0125 * δ)) + abs (log10 (60.0 * B)))
        + (1 / ((0.0125 * δ) * log (natCast 10))) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .log10 pidRawEML))).toF)
      (log10 (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h.toPIDInputDomain (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨lo1, lo2⟩ := pidRawEML_lower h (stdI1 leanPrims) (stdI2 leanPrims)
  exact pid_log10_grounded env (0.0125 * δ) (60.0 * B) (lo_pos_of_delta h.delta_pos) hs lo1 (le_of_abs_le hfl) lo2
    (le_of_abs_le hex)

/-- **`pid_asin_grounded`, instantiated** on `PIDInputDomain`, with `60·B ≤ R < 1`. -/
theorem pid_asin_grounded_instantiated (env : Env) {B δ R : MachLib.Real} (h : PIDInputDomain env B δ)
    (hBR : 60.0 * B ≤ R) (hR : R < 1) :
    AbsEnc (u * (pi / (1 + 1)) + (1 / sqrt (1 - R * R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .asin pidRawEML))).toF)
      (arcsin (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨l1, u1⟩ := abs_le_iff.mp (le_trans hfl hBR)
  obtain ⟨l2, u2⟩ := abs_le_iff.mp (le_trans hex hBR)
  exact pid_asin_grounded env R hR hs l1 u1 l2 u2

/-- **`pid_acos_grounded`, instantiated** on `PIDInputDomain`, with `60·B ≤ R < 1`. -/
theorem pid_acos_grounded_instantiated (env : Env) {B δ R : MachLib.Real} (h : PIDInputDomain env B δ)
    (hBR : 60.0 * B ≤ R) (hR : R < 1) :
    AbsEnc (u * pi + (1 / sqrt (1 - R * R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .acos pidRawEML))).toF)
      (arccos (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨l1, u1⟩ := abs_le_iff.mp (le_trans hfl hBR)
  obtain ⟨l2, u2⟩ := abs_le_iff.mp (le_trans hex hBR)
  exact pid_acos_grounded env R hR hs l1 u1 l2 u2

/-- **`pid_tan_grounded`, instantiated** on `PIDInputDomain`, with `60·B ≤ R ≤ 0.5`, which is below `π/2`. -/
theorem pid_tan_grounded_instantiated (env : Env) {B δ R : MachLib.Real} (h : PIDInputDomain env B δ)
    (hBR : 60.0 * B ≤ R) (hR : R ≤ 0.5) :
    AbsEnc ((u + u) * tan R + (1 / (cos R * cos R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .tan pidRawEML))).toF)
      (tan (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨l1, u1⟩ := abs_le_iff.mp (le_trans hfl hBR)
  obtain ⟨l2, u2⟩ := abs_le_iff.mp (le_trans hex hBR)
  exact pid_tan_grounded env R (range_nonneg h hBR) (lt_of_le_of_lt hR half_lt_pi_div_two) hs l1 u1 l2 u2

/-- **`pid_sinh_grounded`, instantiated** on `PIDInputDomain`, with `60·B ≤ R ≤ 710`. `hsinh` is `real_sinh_finite`. -/
theorem pid_sinh_grounded_instantiated (env : Env) {B δ R : MachLib.Real} (h : PIDInputDomain env B δ)
    (hBR : 60.0 * B ≤ R) (hR : R ≤ natCast 710) :
    AbsEnc ((u + u + u + u) * cosh R + cosh R * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sinh pidRawEML))).toF)
      (sinh (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨l1, u1⟩ := abs_le_iff.mp (le_trans hfl hBR)
  obtain ⟨l2, u2⟩ := abs_le_iff.mp (le_trans hex hBR)
  exact pid_sinh_grounded env R hs (real_sinh_finite _ (FloatSafe.add_isFinite hs) (le_trans (le_trans hfl hBR) hR))
    l1 u1 l2 u2

/-- **`pid_cosh_grounded`, instantiated** on `PIDInputDomain`, with `60·B ≤ R ≤ 710`. `hcosh` is `real_cosh_finite`. -/
theorem pid_cosh_grounded_instantiated (env : Env) {B δ R : MachLib.Real} (h : PIDInputDomain env B δ)
    (hBR : 60.0 * B ≤ R) (hR : R ≤ natCast 710) :
    AbsEnc ((u + u + u + u) * cosh R + sinh R * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .cosh pidRawEML))).toF)
      (cosh (exactR realToR env pidRawEML)) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h (stdI1 leanPrims) (stdI2 leanPrims)
  obtain ⟨l1, u1⟩ := abs_le_iff.mp (le_trans hfl hBR)
  obtain ⟨l2, u2⟩ := abs_le_iff.mp (le_trans hex hBR)
  exact pid_cosh_grounded env R (range_nonneg h hBR) hs
    (real_cosh_finite _ (FloatSafe.add_isFinite hs) (le_trans (le_trans hfl hBR) hR)) l1 u1 l2 u2

/-! ## 4. The specimen -/

/-- The specimen environment: every input is `floatOfR 0.004`. -/
noncomputable def pidSpecimenEnv : Env := fun _ => Val.scalar (floatOfR 0.004)

set_option exponentiation.threshold 1100 in
/-- **The positive PID domain is non-empty**: `pidSpecimenEnv` is in it at `B = 0.008`, `δ = 0.002`. Every input reads
back between `0.002` and `0.008`, so none is zero, and each `gain × input` product meets `ProductsNormal` through its
`DBL_MIN` branch. -/
theorem pidSpecimen_domain : PIDPositiveDomain pidSpecimenEnv 0.008 0.002 := by
  obtain ⟨hf, hlo, hhi⟩ := floatOfR_decimal_facts 4 3 (by decide) (by decide) (by decide)
  have hpos : (0.002 : MachLib.Real) ≤ realToR (floatOfR 0.004) := le_trans (by grounded_decimal) hlo
  have hub : realToR (floatOfR 0.004) ≤ 0.008 := le_trans hhi (by grounded_decimal)
  have hd0 : (0 : MachLib.Real) < 0.002 := realOfScientific_pos 2 true 3 (by decide)
  have habs : abs (realToR (floatOfR 0.004)) = realToR (floatOfR 0.004) := abs_of_nonneg (le_trans (le_of_lt hd0) hpos)
  have hb : abs (realToR (floatOfR 0.004)) ≤ 0.008 := by rw [habs]; exact hub
  have hfl : realToR (floatOfR 0.004) = 0 ∨ (0.002 : MachLib.Real) ≤ abs (realToR (floatOfR 0.004)) :=
    Or.inr (by rw [habs]; exact hpos)
  have hmin : dblMin ≤ 0.025 * 0.002 :=
    le_trans (dblMin_le_decimal 50 6 (by decide) (by decide)) (le_of_eq (by grounded_decimal))
  have hsize : (60.0 : MachLib.Real) * 0.008 ≤ dblMax :=
    le_trans (le_trans (by grounded_decimal : (60.0 : MachLib.Real) * 0.008 ≤ 1.0)
      (le_of_eq realOfScientific_one_dot_zero)) one_le_dblMax
  exact ⟨⟨hf, hf, hf, hb, hb, hb, hfl, hfl, hfl, le_of_lt hd0, hmin, hsize⟩, hd0, hpos, hpos, hpos⟩

theorem pidSpecimen_range : (60.0 : MachLib.Real) * 0.008 ≤ 0.5 := by grounded_decimal

theorem point_five_le_natCast {n : Nat} (h : 1 ≤ n) : (0.5 : MachLib.Real) ≤ natCast n :=
  le_trans (le_trans (by grounded_decimal : (0.5 : MachLib.Real) ≤ 1.0) (le_of_eq realOfScientific_one_dot_zero))
    (one_le_natCast_of h)

theorem point_five_lt_one : (0.5 : MachLib.Real) < 1 :=
  lt_of_lt_of_le (by grounded_decimal : (0.5 : MachLib.Real) < 1.0) (le_of_eq realOfScientific_one_dot_zero)

/-- **Specimen for `pid_grounded_instantiated`**, at `pidSpecimenEnv`: the exact PID law it bounds the computation against
is strictly positive. -/
theorem pid_grounded_specimen :
    0 < exactR realToR pidSpecimenEnv pidRawEML ∧
    AbsEnc (absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) pidSpecimenEnv (emitC pidRawEML)).toF)
      (exactR realToR pidSpecimenEnv pidRawEML) :=
  ⟨lt_of_lt_of_le (lo_pos_of_delta pidSpecimen_domain.delta_pos)
      (pidRawEML_lower pidSpecimen_domain (fun _ _ => 0) (fun _ _ _ => 0)).2,
    pid_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain⟩

/-- Specimen for `pid_tanh_grounded_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_tanh_grounded_specimen :
    AbsEnc ((u + u) + 1 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .tanh pidRawEML))).toF)
      (tanh (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_tanh_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

/-- Specimen for `pid_sin_grounded_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_sin_grounded_specimen :
    AbsEnc (real_sin_eps + 1 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .sin pidRawEML))).toF)
      (sin (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_sin_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

/-- Specimen for `pid_cos_grounded_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_cos_grounded_specimen :
    AbsEnc (real_cos_eps + 1 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .cos pidRawEML))).toF)
      (cos (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_cos_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

/-- Specimen for `pid_atan_grounded_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_atan_grounded_specimen :
    AbsEnc (real_atan_eps + 1 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .atan pidRawEML))).toF)
      (atan (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_atan_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

/-- Specimen for `pid_abs_grounded_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_abs_grounded_specimen :
    AbsEnc (real_abs_eps + 1 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .abs pidRawEML))).toF)
      (abs (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_abs_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

/-- Specimen for `pid_exp_grounded_instantiated`, at `pidSpecimenEnv` and `R = 0.5`. -/
theorem pid_exp_grounded_specimen :
    AbsEnc ((u + u) * exp 0.5 + exp 0.5 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .exp pidRawEML))).toF)
      (exp (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_exp_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain pidSpecimen_range
    (point_five_le_natCast (by decide))

/-- Specimen for `pid_log_grounded_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_log_grounded_specimen :
    AbsEnc (u * (abs (log (0.0125 * 0.002)) + abs (log (60.0 * 0.008)))
        + (1 / (0.0125 * 0.002)) * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .ln pidRawEML))).toF)
      (log (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_log_grounded_instantiated pidSpecimenEnv pidSpecimen_domain

/-- Specimen for `pid_sqrt_grounded_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_sqrt_grounded_specimen :
    AbsEnc (u * sqrt (60.0 * 0.008)
        + (1 / (sqrt (0.0125 * 0.002) + sqrt (0.0125 * 0.002))) * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .sqrt pidRawEML))).toF)
      (sqrt (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_sqrt_grounded_instantiated pidSpecimenEnv pidSpecimen_domain

/-- Specimen for `pid_log10_grounded_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_log10_grounded_specimen :
    AbsEnc ((u + u + u) * (abs (log10 (0.0125 * 0.002)) + abs (log10 (60.0 * 0.008)))
        + (1 / ((0.0125 * 0.002) * log (natCast 10))) * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .log10 pidRawEML))).toF)
      (log10 (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_log10_grounded_instantiated pidSpecimenEnv pidSpecimen_domain

/-- Specimen for `pid_asin_grounded_instantiated`, at `pidSpecimenEnv` and `R = 0.5`. -/
theorem pid_asin_grounded_specimen :
    AbsEnc (u * (pi / (1 + 1)) + (1 / sqrt (1 - 0.5 * 0.5)) * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .asin pidRawEML))).toF)
      (arcsin (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_asin_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain pidSpecimen_range point_five_lt_one

/-- Specimen for `pid_acos_grounded_instantiated`, at `pidSpecimenEnv` and `R = 0.5`. -/
theorem pid_acos_grounded_specimen :
    AbsEnc (u * pi + (1 / sqrt (1 - 0.5 * 0.5)) * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .acos pidRawEML))).toF)
      (arccos (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_acos_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain pidSpecimen_range point_five_lt_one

/-- Specimen for `pid_tan_grounded_instantiated`, at `pidSpecimenEnv` and `R = 0.5`. -/
theorem pid_tan_grounded_specimen :
    AbsEnc ((u + u) * tan 0.5 + (1 / (cos 0.5 * cos 0.5)) * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .tan pidRawEML))).toF)
      (tan (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_tan_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain pidSpecimen_range (le_refl _)

/-- Specimen for `pid_sinh_grounded_instantiated`, at `pidSpecimenEnv` and `R = 0.5`. -/
theorem pid_sinh_grounded_specimen :
    AbsEnc ((u + u + u + u) * cosh 0.5 + cosh 0.5 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .sinh pidRawEML))).toF)
      (sinh (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_sinh_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain pidSpecimen_range
    (point_five_le_natCast (by decide))

/-- Specimen for `pid_cosh_grounded_instantiated`, at `pidSpecimenEnv` and `R = 0.5`. -/
theorem pid_cosh_grounded_specimen :
    AbsEnc ((u + u + u + u) * cosh 0.5 + sinh 0.5 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .cosh pidRawEML))).toF)
      (cosh (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_cosh_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain pidSpecimen_range
    (point_five_le_natCast (by decide))

/-! ## 5. The determinant through the `DBL_MIN` branch -/

/-- The determinant specimen environment: `x` and `y` are `floatOfR 5.0`, every other input `floatOfR 1.0`. -/
noncomputable def detSpecimenEnv : Env := fun s => Val.scalar (if s = "x" ∨ s = "y" then floatOfR 5.0 else floatOfR 1.0)

set_option exponentiation.threshold 1100 in
/-- **A nonzero specimen for `pipeline_det_grounded_instantiated`, through `ProductsNormal`'s `DBL_MIN` branch.** At
`detSpecimenEnv`, with `α = 0.5` and `B = 10.0`: `X = Y = realToR (floatOfR 5.0)` lies in `[2.5, 10]` and
`Z = W = realToR (floatOfR 1.0)` in `[0.5, 2]` (`u + u ≤ 1`), so both exact products are at least `DBL_MIN` and the exact
determinant `X·Y − Z·W ≥ 6.25 − 4` is positive. `FloatSafeInstances.lean`'s specimen reached only the zero branch, because
`u < 1` gives no lower bound on a nonzero float's real value. -/
theorem pipeline_det_grounded_nonzero_specimen :
    dblMin ≤ abs (realToR (detSpecimenEnv "x").toF * realToR (detSpecimenEnv "y").toF) ∧
    dblMin ≤ abs (realToR (detSpecimenEnv "z").toF * realToR (detSpecimenEnv "w").toF) ∧
    0 < realToR (detSpecimenEnv "x").toF * realToR (detSpecimenEnv "y").toF
        - realToR (detSpecimenEnv "z").toF * realToR (detSpecimenEnv "w").toF ∧
    AbsEnc (u * (1 + 1 + u) * (abs (realToR (detSpecimenEnv "x").toF * realToR (detSpecimenEnv "y").toF)
                              + abs (realToR (detSpecimenEnv "z").toF * realToR (detSpecimenEnv "w").toF)))
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) detSpecimenEnv (emitC detEML)).toF)
      (realToR (detSpecimenEnv "x").toF * realToR (detSpecimenEnv "y").toF
        - realToR (detSpecimenEnv "z").toF * realToR (detSpecimenEnv "w").toF) := by
  have ex : (detSpecimenEnv "x").toF = floatOfR 5.0 := by
    show (if "x" = "x" ∨ "x" = "y" then floatOfR 5.0 else floatOfR 1.0) = floatOfR 5.0
    rw [if_pos (Or.inl rfl)]
  have ey : (detSpecimenEnv "y").toF = floatOfR 5.0 := by
    show (if "y" = "x" ∨ "y" = "y" then floatOfR 5.0 else floatOfR 1.0) = floatOfR 5.0
    rw [if_pos (Or.inr rfl)]
  have ez : (detSpecimenEnv "z").toF = floatOfR 1.0 := by
    show (if "z" = "x" ∨ "z" = "y" then floatOfR 5.0 else floatOfR 1.0) = floatOfR 1.0
    rw [if_neg (by decide)]
  have ew : (detSpecimenEnv "w").toF = floatOfR 1.0 := by
    show (if "w" = "x" ∨ "w" = "y" then floatOfR 5.0 else floatOfR 1.0) = floatOfR 1.0
    rw [if_neg (by decide)]
  obtain ⟨f5, lo5, hi5⟩ := floatOfR_decimal_facts 50 1 (by decide) (by decide) (by decide)
  obtain ⟨f1, lo1, hi1⟩ := floatOfR_decimal_facts 10 1 (by decide) (by decide) (by decide)
  have hX : (2.5 : MachLib.Real) ≤ realToR (floatOfR 5.0) := le_trans (by grounded_decimal) lo5
  have hXu : realToR (floatOfR 5.0) ≤ 10.0 := le_trans hi5 (by grounded_decimal)
  have hZ : (0.5 : MachLib.Real) ≤ realToR (floatOfR 1.0) := le_trans (by grounded_decimal) lo1
  have hZu : realToR (floatOfR 1.0) ≤ 2.0 := le_trans hi1 (by grounded_decimal)
  have h25 : (0 : MachLib.Real) ≤ 2.5 := le_of_lt (realOfScientific_pos 25 true 1 (by decide))
  have h05 : (0 : MachLib.Real) ≤ 0.5 := le_of_lt (realOfScientific_pos 5 true 1 (by decide))
  have hX0 : 0 ≤ realToR (floatOfR 5.0) := le_trans h25 hX
  have hZ0 : 0 ≤ realToR (floatOfR 1.0) := le_trans h05 hZ
  have hXX : (6.25 : MachLib.Real) ≤ realToR (floatOfR 5.0) * realToR (floatOfR 5.0) :=
    le_trans (le_of_eq (by grounded_decimal)) (mul_le_mul' h25 hX h25 hX)
  have hZZ : realToR (floatOfR 1.0) * realToR (floatOfR 1.0) ≤ 4.0 :=
    le_trans (mul_le_mul' hZ0 hZu hZ0 hZu) (le_of_eq (by grounded_decimal))
  have hZZlo : (0.25 : MachLib.Real) ≤ realToR (floatOfR 1.0) * realToR (floatOfR 1.0) :=
    le_trans (le_of_eq (by grounded_decimal)) (mul_le_mul' h05 hZ h05 hZ)
  have hmin25 : dblMin ≤ (0.25 : MachLib.Real) := dblMin_le_decimal 25 2 (by decide) (by decide)
  have hmin625 : dblMin ≤ (6.25 : MachLib.Real) := dblMin_le_decimal 625 2 (by decide) (by decide)
  have habsX : abs (realToR (floatOfR 5.0)) = realToR (floatOfR 5.0) := abs_of_nonneg hX0
  have habsZ : abs (realToR (floatOfR 1.0)) = realToR (floatOfR 1.0) := abs_of_nonneg hZ0
  have hpXX : abs (realToR (floatOfR 5.0) * realToR (floatOfR 5.0))
      = realToR (floatOfR 5.0) * realToR (floatOfR 5.0) := abs_of_nonneg (mul_nonneg hX0 hX0)
  have hpZZ : abs (realToR (floatOfR 1.0) * realToR (floatOfR 1.0))
      = realToR (floatOfR 1.0) * realToR (floatOfR 1.0) := abs_of_nonneg (mul_nonneg hZ0 hZ0)
  have hBmax : (1 + 1 + 1 + 1) * ((10.0 : MachLib.Real) * 10.0) ≤ dblMax := by
    have h100 : (10.0 : MachLib.Real) * 10.0 ≤ natCast 1000 :=
      le_trans (le_of_eq (by grounded_decimal)) (decimal_le_natCast 1000 1 (by decide))
    rw [← natCast_four]
    refine le_trans (mul_le_mul_of_nonneg_left h100 (Real.natCast_nonneg 4)) ?_
    rw [← natCast_mul]
    exact natCast_le_natCast_of_nat_le (by decide)
  have hα : dblMin ≤ (0.5 : MachLib.Real) * 0.5 := le_trans hmin25 (le_of_eq (by grounded_decimal))
  have hZB : realToR (floatOfR 1.0) ≤ 10.0 := le_trans hZu (by grounded_decimal)
  have hcert := pipeline_det_grounded_instantiated detSpecimenEnv (α := 0.5) (B := 10.0) h05 hα hBmax
    (by rw [ex]; exact f5) (by rw [ey]; exact f5) (by rw [ez]; exact f1) (by rw [ew]; exact f1)
    (by rw [ex, habsX]; exact hXu) (by rw [ey, habsX]; exact hXu)
    (by rw [ez, habsZ]; exact hZB) (by rw [ew, habsZ]; exact hZB)
    (Or.inr (by rw [ex, habsX]; exact le_trans (by grounded_decimal) hX))
    (Or.inr (by rw [ey, habsX]; exact le_trans (by grounded_decimal) hX))
    (Or.inr (by rw [ez, habsZ]; exact hZ)) (Or.inr (by rw [ew, habsZ]; exact hZ))
  rw [ex, ey, ez, ew] at hcert ⊢
  refine ⟨by rw [hpXX]; exact le_trans hmin625 hXX, by rw [hpZZ]; exact le_trans hmin25 hZZlo, ?_, hcert⟩
  exact sub_pos_of_lt (lt_of_le_of_lt hZZ (lt_of_lt_of_le (by grounded_decimal) hXX))

end Certcom
