import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel

/-!
# Fixed-point (Q-format) forward-error — the EML→RTL equivalence leg (Leg A)

`FPModel` proves that the `f64`/`f32` (floating-point) evaluation of a kernel
is within a derived bound of its exact `Real` value, using the *multiplicative*
standard model `fl(a∘b) = (a∘b)(1+δ)`, `|δ| ≤ u`. The FPGA datapath is not
floating-point: Forge's Verilog backend emits a **fixed-point** datapath, so the
rounding model is different and this file supplies it.

## What Forge actually emits (ground truth, read off the RTL)

From the kernels under `monogate-research/electronics_intake/.../emitted/*.v`:

* **Format: Q16.16** — signed 32-bit, 16 fractional bits. `1.0` is the integer
  `32'sd65536 = 2¹⁶`, `0.5` is `32768`, `2.0` is `131072`. The quantization step
  is therefore `s = 2⁻¹⁶`.
* **Multiply** lowers to `(a*b) >>> FRAC` (arithmetic shift right by 16) — i.e.
  truncation of the 64-bit product back to the grid, so `|fxmul a b − a·b| ≤ s`.
* **Add / sub** lower to plain integer `±` — **exact**, no rounding (and no
  overflow in the PID's regime: `|inputs| ≤ 100`, `|raw| ≤ 195 ≪ 2¹⁵`).
* **Constants** are quantized to the grid: `|c_fx − c| ≤ s`.

(The hand-written Arty A7 wrapper stub assumed **Q1.31**; the emitted RTL is
**Q16.16**. The stub's signal widths/scaling must be fixed to match — see the
write-up in `monogate-research`.)

## The rounding model here

Rather than a multiplicative `(1+δ)`, fixed-point rounding is **additive**: each
op lands within an absolute step `s` of its real result. The forward-error of
the PID datapath is then assembled exactly as in `FPModel` (decompose the sum of
products, bound each term, recombine with the triangle inequality), the new
ingredients being (a) the additive multiply/constant bounds and (b) `clamp` being
1-Lipschitz so the output saturation never amplifies error.

Mathlib-free; rests only on `MachLib`'s `Real` axioms + `abs_add`/`abs_mul`
(same base as `FPModel`). Companion: `FPModel`, `docs/cross_target_equivalence_*`.

## `quantize`/`qmul` — deriving the leaf rounding fact instead of assuming it

`fxmul_err` above takes its `s`-bound as a hypothesis. The `quantize`/`qmul_real` section
(added for the `eml_sin.v` hardware forward-error certificate, see `SinHardwareForwardError`)
*proves* that bound from `MachLib.Real`'s `floor` axiom instead: `quantize x D := floor(x·D)/D`
is the real-valued model of Verilog's `x >>> FRAC`, and `quantize_err` shows it lands within
`1/D` of the exact `x`. `qmul_err`/`qmul_err_loose` generalize `fxmul_err` to two erroneous
operands, needed once a pipeline chains `qmul` outputs into further `qmul`s.
-/

namespace MachLib.Real

/-! ## clamp -/

/-- Saturating clamp, matching the Forge emission exactly:
`pid_step = min (max raw OUT_MIN) OUT_MAX` — the lower clamp (`max … lo`) is
applied first, then the upper clamp (`min … hi`). -/
noncomputable def clamp (x lo hi : Real) : Real := min (max x lo) hi

/-! ## small order helpers -/

/-- `a ≤ b → a − b ≤ 0`. -/
theorem sub_nonpos_of_le {a b : Real} (h : a ≤ b) : a - b ≤ 0 := by
  have h1 : a - b ≤ b - b := sub_le_sub_right h b
  have h2 : b - b = 0 := by mach_ring
  rw [h2] at h1; exact h1

/-- Two one-sided bounds give an `abs` bound. The `abs` analogue of
`abs_le_of`, specialised to a difference so both sides share the bound `B`. -/
theorem abs_sub_le_of {a b B : Real} (h1 : a - b ≤ B) (h2 : b - a ≤ B) :
    abs (a - b) ≤ B := by
  apply abs_le_of h1
  have e : -(a - b) = b - a := by mach_ring
  rw [e]; exact h2

/-! ## `min` / `max` are 1-Lipschitz in their first argument

Each is proved one-sided first (two tiny case splits on the branch condition),
then the two sides are stitched into an `abs` bound. This is the
"separate discrete from continuous" decomposition: the `if` is a case split, and
each arm is an algebraic `≤`. -/

theorem max_sub_le_abs (x y c : Real) : max x c - max y c ≤ abs (x - y) := by
  by_cases hx : x ≤ c
  · have hmx : max x c = c := by unfold max; rw [if_pos hx]
    rw [hmx]
    exact le_trans (sub_nonpos_of_le (le_max_right y c)) (abs_nonneg _)
  · have hmx : max x c = x := by unfold max; rw [if_neg hx]
    rw [hmx]
    exact le_trans (sub_le_sub_left (le_max_left y c) x) (le_abs_self _)

theorem max_sub_le_abs' (x y c : Real) : max y c - max x c ≤ abs (x - y) := by
  by_cases hy : y ≤ c
  · have hmy : max y c = c := by unfold max; rw [if_pos hy]
    rw [hmy]
    exact le_trans (sub_nonpos_of_le (le_max_right x c)) (abs_nonneg _)
  · have hmy : max y c = y := by unfold max; rw [if_neg hy]
    rw [hmy]
    have h1 : y - max x c ≤ y - x := sub_le_sub_left (le_max_left x c) y
    have h2 : y - x ≤ abs (x - y) := by
      have e : y - x = -(x - y) := by mach_ring
      rw [e]; exact neg_le_abs (x - y)
    exact le_trans h1 h2

theorem max_lipschitz (x y c : Real) : abs (max x c - max y c) ≤ abs (x - y) :=
  abs_sub_le_of (max_sub_le_abs x y c) (max_sub_le_abs' x y c)

theorem min_sub_le_abs (x y c : Real) : min x c - min y c ≤ abs (x - y) := by
  by_cases hy : y ≤ c
  · have hmy : min y c = y := by unfold min; rw [if_pos hy]
    rw [hmy]
    exact le_trans (sub_le_sub_right (min_le_left x c) y) (le_abs_self _)
  · have hmy : min y c = c := by unfold min; rw [if_neg hy]
    rw [hmy]
    exact le_trans (sub_nonpos_of_le (min_le_right x c)) (abs_nonneg _)

theorem min_sub_le_abs' (x y c : Real) : min y c - min x c ≤ abs (x - y) := by
  by_cases hx : x ≤ c
  · have hmx : min x c = x := by unfold min; rw [if_pos hx]
    rw [hmx]
    have h1 : min y c - x ≤ y - x := sub_le_sub_right (min_le_left y c) x
    have h2 : y - x ≤ abs (x - y) := by
      have e : y - x = -(x - y) := by mach_ring
      rw [e]; exact neg_le_abs (x - y)
    exact le_trans h1 h2
  · have hmx : min x c = c := by unfold min; rw [if_neg hx]
    rw [hmx]
    exact le_trans (sub_nonpos_of_le (min_le_right y c)) (abs_nonneg _)

theorem min_lipschitz (x y c : Real) : abs (min x c - min y c) ≤ abs (x - y) :=
  abs_sub_le_of (min_sub_le_abs x y c) (min_sub_le_abs' x y c)

/-- **`clamp` is 1-Lipschitz** — saturation never amplifies error. This is what
lets the PID forward-error pass through the output clamp unchanged. -/
theorem clamp_lipschitz (a b lo hi : Real) :
    abs (clamp a lo hi - clamp b lo hi) ≤ abs (a - b) := by
  unfold clamp
  exact le_trans (min_lipschitz (max a lo) (max b lo) hi) (max_lipschitz a b lo)

/-! ## clamp range (closes the kernel's `pid_output_clamped` obligation) -/

theorem clamp_le_hi (x lo hi : Real) : clamp x lo hi ≤ hi := by
  unfold clamp; exact min_le_right _ _

theorem lo_le_clamp (x lo hi : Real) (h : lo ≤ hi) : lo ≤ clamp x lo hi := by
  unfold clamp; exact le_min (le_max_right x lo) h

/-! ## one fixed-point product term

`m ≈ c'·x` (truncating multiply, error ≤ s) with a quantized constant
`c' ≈ c` (error ≤ s) sits within `s·|x| + s` of the exact product `c·x`. -/
theorem fxmul_err {s c c' x m : Real}
    (hc : abs (c' - c) ≤ s) (hm : abs (m - c' * x) ≤ s) :
    abs (m - c * x) ≤ s * abs x + s := by
  have hsplit : m - c * x = (c' * x - c * x) + (m - c' * x) := by
    mach_mpoly [m, c, c', x]
  rw [hsplit]
  refine le_trans (abs_add _ _) ?_
  have hcx : abs (c' * x - c * x) ≤ s * abs x := by
    have hfac : c' * x - c * x = (c' - c) * x := by mach_mpoly [c, c', x]
    rw [hfac, abs_mul]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg x)
  exact add_le_add_both hcx hm

/-! ## deriving the leaf rounding fact from `floor`, and composing two erroneous operands

`fxmul_err` (above) takes its `s`-bounds as *hypotheses* — the caller must separately show the
RTL's truncating multiply satisfies them. `quantize` closes that gap: it is the real-valued model
of `floor(x·D)/D` (Verilog's `x >>> FRAC` on a value already scaled by `D = 2^FRAC`), built
directly from `MachLib.Real`'s `floor` axiom, and `quantize_err` *proves* — rather than assumes —
that it lands within one grid step `1/D` of the exact value. `qmul_err` then generalizes
`fxmul_err` to the case *both* factors already carry upstream error (needed when a pipeline
chains `qmul` outputs into further `qmul`s, e.g. `eml_sin.v`'s `x3 = qmul(x2, x1)` with `x2`
itself already rounded) — `fxmul_err` only covers one exact operand. `qmul_err_loose` is the
same fact loosened to clean integer-coefficient bookkeeping (`kx/D`, `ky/D`) for a bounded-input
regime (`|xe|, |ye| ≤ 1`, `D ≥ 1`), which is what makes a multi-stage composition tractable
without re-deriving the triangle-inequality algebra at every stage. -/

/-- Truncating quantization to the `1/D` grid. -/
noncomputable def quantize (x D : Real) : Real := floor (x * D) * (1 / D)

theorem quantize_le (x D : Real) (hD : 0 < D) : quantize x D ≤ x := by
  unfold quantize
  have h1 : floor (x * D) ≤ x * D := floor_le (x * D)
  have h2 : floor (x * D) * (1 / D) ≤ (x * D) * (1 / D) :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt (one_div_pos_of_pos hD))
  have h3 : (x * D) * (1 / D) = x := by
    rw [mul_assoc, mul_inv D (ne_of_gt hD), mul_one_ax]
  rwa [h3] at h2

theorem quantize_gt (x D : Real) (hD : 0 < D) : x - quantize x D < 1 / D := by
  unfold quantize
  have h1 : x * D < floor (x * D) + 1 := lt_floor_add_one (x * D)
  have h2 : (x * D) * (1/D) < (floor (x*D) + 1) * (1/D) :=
    mul_lt_mul_of_pos_right h1 (one_div_pos_of_pos hD)
  have h3 : (x * D) * (1 / D) = x := by
    rw [mul_assoc, mul_inv D (ne_of_gt hD), mul_one_ax]
  have h4 : (floor (x*D) + 1) * (1/D) = floor (x*D) * (1/D) + 1 * (1/D) := by mach_ring
  rw [h3, h4, one_mul_thm] at h2
  have h5 := add_lt_add_left h2 (-(floor (x*D) * (1/D)))
  rw [show (-(floor (x*D)*(1/D)) + (floor (x*D)*(1/D) + 1/D) : Real) = 1/D from by mach_ring] at h5
  rw [sub_def]
  rwa [show (x + -(floor (x*D)*(1/D)) : Real) = -(floor (x*D)*(1/D)) + x from by mach_ring]

/-- **Truncating quantization is within one grid step `1/D` of the exact value** — the direct
`abs`-bound form matching `fxmul_err`'s convention. -/
theorem quantize_err (x D : Real) (hD : 0 < D) : abs (quantize x D - x) ≤ 1 / D := by
  have hle : quantize x D ≤ x := quantize_le x D hD
  have hgt : x - quantize x D < 1 / D := quantize_gt x D hD
  have hnonpos : quantize x D - x ≤ 0 := sub_nonpos_of_le hle
  rw [abs_of_nonpos hnonpos]
  have heq : -(quantize x D - x) = x - quantize x D := by mach_ring
  rw [heq]
  exact le_of_lt hgt

/-- The fixed-point multiply: exact product truncated to the `1/D` grid, matching Forge's
emitted `(a*b) >>> FRAC`. -/
noncomputable def qmul_real (a b D : Real) : Real := quantize (a * b) D

/-- **Leaf rounding fact for `qmul`, derived (not assumed).** -/
theorem qmul_trunc_err (a b D : Real) (hD : 0 < D) :
    abs (qmul_real a b D - a * b) ≤ 1 / D := quantize_err (a * b) D hD

/-- **General fixed-point product composition — both operands carry pre-existing error.**
Generalizes `fxmul_err` (which fixes `x` exact) to the case both factors are themselves the
output of upstream rounded ops. -/
theorem qmul_err {s Ex Ey a b xe ye m : Real}
    (hx : abs (a - xe) ≤ Ex) (hy : abs (b - ye) ≤ Ey) (hm : abs (m - a * b) ≤ s) :
    abs (m - xe * ye) ≤ s + ((abs xe + Ex) * Ey + Ex * abs ye) := by
  have hEx : 0 ≤ Ex := le_trans (abs_nonneg _) hx
  have hsplit : m - xe * ye = (m - a * b) + (a * b - xe * ye) := by
    mach_mpoly [m, a, b, xe, ye]
  rw [hsplit]
  refine le_trans (abs_add _ _) ?_
  have hprod : abs (a * b - xe * ye) ≤ (abs xe + Ex) * Ey + Ex * abs ye := by
    have hfac : a * b - xe * ye = a * (b - ye) + (a - xe) * ye := by
      mach_mpoly [a, b, xe, ye]
    rw [hfac]
    refine le_trans (abs_add _ _) ?_
    have habound : abs a ≤ abs xe + Ex := abs_le_add_err hx
    have ha : abs (a * (b - ye)) ≤ (abs xe + Ex) * Ey := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_right habound (abs_nonneg (b - ye)))
        (mul_le_mul_of_nonneg_left hy (le_trans (abs_nonneg a) habound))
    have hb : abs ((a - xe) * ye) ≤ Ex * abs ye := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hx (abs_nonneg ye)
    exact add_le_add_both ha hb
  exact add_le_add_both hm hprod

/-- **Loosened qmul composition, in units of `1/D`.** If the exact operands lie in `[-1,1]`
(the range-reduced-input regime), and the incoming errors are `kx/D`/`ky/D` for known nonneg
coefficients `kx`/`ky`, then one more `qmul` (contributing its own `1/D` truncation) lands within
`(1+kx+ky+kx*ky)/D` of the true product. The reusable per-stage step for threading error
coefficients through a multi-stage fixed-point pipeline without re-deriving the triangle-
inequality algebra at each stage. -/
theorem qmul_err_loose {D a b xe ye m kx ky : Real}
    (hD : 0 < D) (hD1 : 1 ≤ D)
    (hxe : abs xe ≤ 1) (hye : abs ye ≤ 1)
    (hkx0 : 0 ≤ kx) (hky0 : 0 ≤ ky)
    (hx : abs (a - xe) ≤ kx * (1/D)) (hy : abs (b - ye) ≤ ky * (1/D))
    (hm : abs (m - a * b) ≤ 1/D) :
    abs (m - xe * ye) ≤ (1 + kx + ky + kx * ky) * (1/D) := by
  have hinvnn : (0:Real) ≤ 1/D := one_div_nonneg_of_pos hD
  have hDsq_le : (1/D) * (1/D) ≤ 1/D := by
    have hd1 : (1:Real)/D ≤ 1 := div_le_one_of_le_of_pos hD hD1
    have step := mul_le_mul_of_nonneg_left hd1 hinvnn
    rwa [mul_one_ax] at step
  have hraw := qmul_err hx hy hm
  have hB : (abs xe + kx*(1/D)) * (ky*(1/D)) ≤ ky*(1/D) + kx*ky*(1/D) := by
    have t1 : (abs xe + kx*(1/D)) ≤ 1 + kx*(1/D) := add_le_add_both hxe (le_refl _)
    have t2 : (abs xe + kx*(1/D)) * (ky*(1/D)) ≤ (1+kx*(1/D)) * (ky*(1/D)) :=
      mul_le_mul_of_nonneg_right t1 (mul_nonneg hky0 hinvnn)
    have t3 : (1+kx*(1/D)) * (ky*(1/D)) = ky*(1/D) + kx*ky*((1/D)*(1/D)) := by mach_ring
    have t4 : ky*(1/D) + kx*ky*((1/D)*(1/D)) ≤ ky*(1/D) + kx*ky*(1/D) :=
      add_le_add_both (le_refl _) (mul_le_mul_of_nonneg_left hDsq_le (mul_nonneg hkx0 hky0))
    rw [t3] at t2
    exact le_trans t2 t4
  have hC : kx*(1/D)*abs ye ≤ kx*(1/D) := by
    have t5 : kx*(1/D)*abs ye ≤ kx*(1/D)*1 :=
      mul_le_mul_of_nonneg_left hye (mul_nonneg hkx0 hinvnn)
    rwa [mul_one_ax] at t5
  have hcombine : 1/D + ((abs xe+kx*(1/D))*(ky*(1/D)) + kx*(1/D)*abs ye)
      ≤ 1/D + (ky*(1/D) + kx*ky*(1/D) + kx*(1/D)) :=
    add_le_add_both (le_refl (1/D)) (add_le_add_both hB hC)
  refine le_trans hraw (le_trans hcombine ?_)
  exact le_of_eq (by mach_ring)

/-! ## the PID datapath -/

/-- Collect the three per-term bounds. Pulled out so `mach_mpoly` works over
fresh atoms. -/
theorem pid_bound_collect (s ae ai ad : Real) :
    ((s * ae + s) + (s * ai + s)) + (s * ad + s) = s * (ae + ai + ad) + (s + s + s) := by
  mach_mpoly [s, ae, ai, ad]

/-- **Pre-clamp PID forward-error.** The fixed-point raw output
`(m1 + m2) + m3` (exact adds of three truncating products with quantized gains)
is within `s·(|e|+|i|+|d|) + 3s` of the exact `Kp·e + Ki·i + Kd·d`. -/
theorem pid_raw_fwd_error {s e i d Kp Ki Kd Kp' Ki' Kd' m1 m2 m3 : Real}
    (hKp : abs (Kp' - Kp) ≤ s) (hKi : abs (Ki' - Ki) ≤ s) (hKd : abs (Kd' - Kd) ≤ s)
    (hm1 : abs (m1 - Kp' * e) ≤ s) (hm2 : abs (m2 - Ki' * i) ≤ s)
    (hm3 : abs (m3 - Kd' * d) ≤ s) :
    abs (((m1 + m2) + m3) - (((Kp * e) + (Ki * i)) + (Kd * d)))
      ≤ s * (abs e + abs i + abs d) + (s + s + s) := by
  have eKp := fxmul_err hKp hm1
  have eKi := fxmul_err hKi hm2
  have eKd := fxmul_err hKd hm3
  have hsplit : ((m1 + m2) + m3) - (((Kp * e) + (Ki * i)) + (Kd * d))
      = (((m1 - Kp * e) + (m2 - Ki * i)) + (m3 - Kd * d)) := by
    mach_mpoly [m1, m2, m3, Kp, Ki, Kd, e, i, d]
  rw [hsplit]
  refine le_trans (abs_add _ _) ?_
  refine le_trans (add_le_add_both (abs_add _ _) (le_refl (abs (m3 - Kd * d)))) ?_
  refine le_trans (add_le_add_both (add_le_add_both eKp eKi) eKd) ?_
  exact le_of_eq (pid_bound_collect s (abs e) (abs i) (abs d))

/-
Binding (Leg A, pinned 2026-06-26). The real-valued side below,
`clamp (((Kp*e)+(Ki*i))+(Kd*d)) OUT_MIN OUT_MAX`, is *definitionally* the
Forge-emitted `Pid.lean`:
  `pid_step e i d = min (max (((Kp*e)+(Ki*i))+(Kd*d)) OUT_MIN) OUT_MAX`
(`clamp x lo hi := min (max x lo) hi`). The obligation is therefore pinned to
the shipped expression, whose Forge `tree_hash` is

  pid.eml :: pid_step
    tree_hash   = sha256:b15588371d568e57ad65471cb48b04fefa6c4b6554642efe7fa7f0ea33debd63
    module_hash = sha256:9a0f146613a9cad04f68e0bd16efdba2179d258ca1c24d045d44c670b77af4d8

If `pid.eml` changes, this hash changes and the binding is stale (re-derive).
Source: monogate-research/electronics_intake/kernels/pid_dual_target_v0/pid.eml
-/

/-- **PID cross-target forward-error (generic step `s`).** The complete
fixed-point PID datapath — three truncating multiplies by quantized gains, two
exact adds, then the saturating `clamp` — is within `s·(|e|+|i|+|d|) + 3s` of
the exact real-valued PID law. This is the EML→RTL equivalence statement for
`pid.eml`: `clamp` is the same emitted `min (max · lo) hi`, and the bound holds
for *any* fixed-point step `s ≥ 0`. -/
theorem pid_fx_fwd_error {s e i d Kp Ki Kd Kp' Ki' Kd' m1 m2 m3 lo hi : Real}
    (hKp : abs (Kp' - Kp) ≤ s) (hKi : abs (Ki' - Ki) ≤ s) (hKd : abs (Kd' - Kd) ≤ s)
    (hm1 : abs (m1 - Kp' * e) ≤ s) (hm2 : abs (m2 - Ki' * i) ≤ s)
    (hm3 : abs (m3 - Kd' * d) ≤ s) :
    abs (clamp ((m1 + m2) + m3) lo hi
          - clamp (((Kp * e) + (Ki * i)) + (Kd * d)) lo hi)
      ≤ s * (abs e + abs i + abs d) + (s + s + s) :=
  le_trans (clamp_lipschitz _ _ lo hi)
    (pid_raw_fwd_error hKp hKi hKd hm1 hm2 hm3)

/-! ## concrete instantiation at Q16.16 (`s = 2⁻¹⁶`) -/

/-- The Q16.16 quantization step `2⁻¹⁶`, written like `FPModel`'s `f64_u`. -/
noncomputable def q16_step : Real := 1 / npow 16 (1 + 1)

theorem q16_step_nonneg : (0 : Real) ≤ q16_step :=
  one_div_nonneg_of_pos (npow_two_pos 16)

/-- **PID forward-error on the actual Q16.16 datapath, `|inputs| ≤ 100`.**
Instantiates `pid_fx_fwd_error` at the real Forge step `s = 2⁻¹⁶` and the
`pid.eml` refinement bound `|e|,|i|,|d| ≤ 100`, giving the concrete worst-case
bound `2⁻¹⁶·300 + 3·2⁻¹⁶ = 303·2⁻¹⁶ ≈ 4.62e-3` on the `[-1,1]` control output. -/
theorem pid_q16_fwd_error {e i d Kp Ki Kd Kp' Ki' Kd' m1 m2 m3 lo hi : Real}
    (hKp : abs (Kp' - Kp) ≤ q16_step) (hKi : abs (Ki' - Ki) ≤ q16_step)
    (hKd : abs (Kd' - Kd) ≤ q16_step)
    (hm1 : abs (m1 - Kp' * e) ≤ q16_step) (hm2 : abs (m2 - Ki' * i) ≤ q16_step)
    (hm3 : abs (m3 - Kd' * d) ≤ q16_step)
    (he : abs e ≤ 100.0) (hi100 : abs i ≤ 100.0) (hd : abs d ≤ 100.0) :
    abs (clamp ((m1 + m2) + m3) lo hi
          - clamp (((Kp * e) + (Ki * i)) + (Kd * d)) lo hi)
      ≤ q16_step * (100.0 + 100.0 + 100.0) + (q16_step + q16_step + q16_step) := by
  refine le_trans (pid_fx_fwd_error hKp hKi hKd hm1 hm2 hm3) ?_
  have hsum : abs e + abs i + abs d ≤ 100.0 + 100.0 + 100.0 :=
    add_le_add_both (add_le_add_both he hi100) hd
  exact add_le_add_both (mul_le_mul_of_nonneg_left hsum q16_step_nonneg)
    (le_refl ((q16_step + q16_step + q16_step)))

end MachLib.Real
