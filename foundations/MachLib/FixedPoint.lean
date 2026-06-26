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
