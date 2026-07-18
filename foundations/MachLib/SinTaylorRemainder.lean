import MachLib.Trig
import MachLib.Forge
import MachLib.Rolle
import MachLib.Ring
import MachLib.FPModel

/-!
# The real-valued sin Taylor-remainder bound — pathfinder for hardware forward-error grounding

Forge's Verilog backend (`hardware/modules/transcendental/eml_sin.v`) implements `sin(x)` on real
FPGA silicon via a 3-term Maclaurin truncation, `sin(x) ≈ x − x³/6 + x⁵/120`, valid on `[−π/2,π/2]`,
computed in Q16.16 fixed-point. Certifying that hardware's forward error needs TWO independent
pieces: (1) how far the TRUNCATED POLYNOMIAL itself is from the true `sin`, and (2) how far Q-format
FIXED-POINT ARITHMETIC (truncating shifts, not round-to-nearest) drifts from exact real arithmetic
computing that polynomial. This file is (1) — a REAL-VALUED bound, no fixed-point yet, deliberately
isolated per the scoping note this session's earlier pass left
(`project_forge_hardware_forward_error_scoping` memory): "First derive the real-valued Taylor-
remainder bound in isolation... get that reviewed/confirmed sound on its own before touching the
Q-format quantization layer."

**Status: 3 of 6 levels closed, `sorryAx`-free.** MachLib has no general Taylor's-theorem-with-
remainder machinery (would need Cauchy's generalized MVT or an auxiliary-function/Rolle argument for
the SHARP `x⁷/7!` Lagrange bound); building that from scratch is its own multi-session arc. Instead:
a REPEATED plain-MVT chain (`abs_mvt_step` below), applied to the remainder function's own iterated
derivatives, each bounded by a CONSTANT over `[0,x]` rather than an integral. This is provably
CORRECT but LOOSER than the sharp bound (off by a factor of `~x·(k+1)` at each of the levels closed
so far) — an honest, checked bound, not a guessed or optimal one.

Closed: `R5(y) = cos y − 1` (`|R5(x)| ≤ x`), `R4(y) = sin y − y` (`|R4(x)| ≤ x²`),
`R3(y) = 1 − y²/2 − cos y` (`|R3(x)| ≤ x³`) — i.e. as far as the bound on `cos(x) − (1 − x²/2)`,
NOT yet the full degree-5 `sin(x) − (x − x³/6 + x⁵/120)` bound the actual hardware needs.

**Not yet done** (levels `R2`, `R1`, `R0`, needing the `y³`/`1/6`, `y⁴`/`1/24`, `y⁵`/`1/120`
coefficient relations — each needs its OWN `mul_inv`-based fraction lemma, `mach_ring` only handles
ring structure, not decimal-literal arithmetic like `3·(1/6) = 1/2`, confirmed by direct test). Left
open rather than rushed; see `double_half`'s docstring below for the technique to extend.
-/

open MachLib.Real

/-- Transport a `HasDerivAt` fact along a proof that its derivative VALUE equals another expression
— used throughout to clean up "raw" combinator output into the exact next-level target form. -/
theorem hasDerivAt_congr_val {f : MachLib.Real → MachLib.Real} {a b x : MachLib.Real}
    (h : HasDerivAt f a x) (hab : a = b) : HasDerivAt f b x := hab ▸ h

/-- `(y·y)' = c+c` at `c` (product rule, not yet simplified to `2c` — `mach_ring` handles that
downstream where needed). -/
theorem hD_y2 : ∀ c : MachLib.Real, HasDerivAt (fun y => y * y) (c + c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_mul (fun y => y) (fun y => y) 1 1 c (HasDerivAt_id c) (HasDerivAt_id c))
    (by mach_ring)

/-- `(y·y·y)' = c·c+c·c+c·c` at `c` (product rule on `(y·y)·y`, reusing `hD_y2`). -/
theorem hD_y3 : ∀ c : MachLib.Real, HasDerivAt (fun y => y * y * y) (c * c + c * c + c * c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_mul (fun y => y * y) (fun y => y) (c + c) 1 c (hD_y2 c) (HasDerivAt_id c))
    (by mach_ring)

theorem two_ne_zero : (1 + 1 : MachLib.Real) ≠ 0 :=
  ne_of_gt (add_pos zero_lt_one_ax zero_lt_one_ax)

/-- `1/2 + 1/2 = 1`. `mach_ring` normalizes ring structure (associativity/commutativity/
distributivity) but NOT decimal/fraction-literal arithmetic (confirmed directly: `mach_ring` alone
cannot close `0.5 + 0.5 = 1` or `1/(1+1) + 1/(1+1) = 1`) — this is the field-axiom (`mul_inv`) route
instead, the technique every further fraction-coefficient lemma in this file (and any future
extension to the `y³`/`y⁴`/`y⁵` levels) needs to reuse. -/
theorem half_add_half : (1 : MachLib.Real) / (1 + 1) + 1 / (1 + 1) = 1 := by
  have hgen : ∀ h : MachLib.Real, h + h = (1 + 1) * h := by intro h; mach_ring
  rw [hgen (1 / (1 + 1))]
  exact mul_inv (1 + 1) two_ne_zero

/-- `(c+c)·(1/2) = c` — bridges a `y·y`-derivative's raw `(c+c)` coefficient down to the clean `c`
that `y²/2`'s OWN derivative needs, via `half_add_half`. -/
theorem double_half (c : MachLib.Real) : (c + c) * (1 / (1 + 1)) = c := by
  have step : (c + c) * (1 / (1 + 1)) = c * (1 / (1 + 1) + 1 / (1 + 1)) := by mach_ring
  rw [step, half_add_half]; mach_ring

/-- **Generic MVT step.** If `f 0 = 0`, `f' = g` everywhere, and `|g(t)| ≤ B` (a CONSTANT) for all
`t ∈ [0,x]`, then `|f(x)| ≤ B·x`. The crude "constant sup times width" Lagrange-style bound — looser
than the sharp integral-based one, but needs only plain MVT (`mean_value_theorem_ct`), not
integration or Cauchy's generalized MVT. Reused at every level below. -/
theorem abs_mvt_step (f g : MachLib.Real → MachLib.Real) (x B : MachLib.Real)
    (hx0 : 0 ≤ x) (hB : 0 ≤ B)
    (hderiv : ∀ c : MachLib.Real, HasDerivAt f (g c) c)
    (hf0 : f 0 = 0)
    (hgB : ∀ t : MachLib.Real, 0 ≤ t → t ≤ x → abs (g t) ≤ B) :
    abs (f x) ≤ B * x := by
  rcases (le_iff_lt_or_eq 0 x).mp hx0 with hlt | heq
  · obtain ⟨c, f', hac, hcb, hd, hval⟩ :=
      mean_value_theorem_ct f 0 x hlt (fun c _ _ => ⟨g c, hderiv c⟩)
    rw [HasDerivAt_unique f f' (g c) c hd (hderiv c)] at hval
    rw [hf0, sub_zero, sub_zero] at hval
    have hstep : abs (f x) = abs (g c) * x := by rw [hval, abs_mul, abs_of_nonneg hx0]
    rw [hstep]
    have h1 : abs (g c) ≤ B := hgB c (le_of_lt hac) (le_of_lt hcb)
    exact mul_le_mul_of_nonneg_right h1 hx0
  · have hx0' : x = 0 := heq.symm
    rw [hx0', show f 0 = 0 from hf0, abs_zero, mul_zero]
    exact le_refl 0

/-! ## The remainder chain, from the innermost (5th) derivative down

`R5 = R4' = R3'' = ...` down to `R0`, the actual Taylor remainder `sin(y) − (y − y³/6 + y⁵/120)` —
each `Rk` vanishes at 0 by construction, and `Rk' = R(k-1)` chains the bound down. -/

/-- `R5(y) = cos y − 1`. -/
noncomputable def R5 (y : MachLib.Real) : MachLib.Real := cos y - 1

theorem R5_deriv : ∀ c : MachLib.Real, HasDerivAt R5 (-sin c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_sub cos (fun _ => 1) (-sin c) 0 c (HasDerivAt_cos c) (HasDerivAt_const 1 c))
    (by mach_ring)

theorem R5_zero : R5 0 = 0 := by unfold R5; rw [cos_zero]; mach_ring

/-- `|cos(x) − 1| ≤ x` for `x ≥ 0`. -/
theorem R5_bound (x : MachLib.Real) (hx0 : 0 ≤ x) : abs (R5 x) ≤ 1 * x := by
  apply abs_mvt_step R5 (fun c => -sin c) x 1 hx0 (le_of_lt zero_lt_one_ax) R5_deriv R5_zero
  intro t _ _
  rw [abs_neg]
  exact abs_sin_le_one t

/-- `R4(y) = sin y − y`. -/
noncomputable def R4 (y : MachLib.Real) : MachLib.Real := sin y - y

theorem R4_deriv : ∀ c : MachLib.Real, HasDerivAt R4 (R5 c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_sub sin (fun y => y) (cos c) 1 c (HasDerivAt_sin c) (HasDerivAt_id c))
    (by unfold R5; mach_ring)

theorem R4_zero : R4 0 = 0 := by unfold R4; rw [sin_zero]; mach_ring

/-- `|sin(x) − x| ≤ x²` for `x ≥ 0`. -/
theorem R4_bound (x : MachLib.Real) (hx0 : 0 ≤ x) : abs (R4 x) ≤ x * x := by
  apply abs_mvt_step R4 R5 x x hx0 hx0 R4_deriv R4_zero
  intro t ht0 htx
  have h1 : abs (R5 t) ≤ 1 * t := R5_bound t ht0
  rw [one_mul_thm] at h1
  exact le_trans h1 htx

/-- `R3(y) = 1 − y²/2 − cos y`. -/
noncomputable def R3 (y : MachLib.Real) : MachLib.Real := 1 - y * y * ((1 / (1 + 1) : MachLib.Real)) - cos y

theorem R3_deriv : ∀ c : MachLib.Real, HasDerivAt R3 (R4 c) c := by
  intro c
  have hyy2 : HasDerivAt (fun y => y * y * ((1 / (1 + 1) : MachLib.Real)))
      ((c + c) * ((1 / (1 + 1) : MachLib.Real)) + (c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y) (fun _ => (1 / (1 + 1) : MachLib.Real)) (c + c) 0 c
      (hD_y2 c) (HasDerivAt_const (1 / (1 + 1) : MachLib.Real) c)
  have hsub1 : HasDerivAt (fun y => (1 : MachLib.Real) - y * y * ((1 / (1 + 1) : MachLib.Real)))
      (0 - ((c + c) * ((1 / (1 + 1) : MachLib.Real)) + (c * c) * 0)) c :=
    HasDerivAt_sub (fun _ => 1) (fun y => y * y * ((1 / (1 + 1) : MachLib.Real))) 0 _ c
      (HasDerivAt_const 1 c) hyy2
  have hfull := HasDerivAt_sub (fun y => (1 : MachLib.Real) - y * y * (1 / (1 + 1) : MachLib.Real))
    cos _ (-sin c) c hsub1 (HasDerivAt_cos c)
  have hclean : (0 - ((c + c) * (1 / (1 + 1) : MachLib.Real) + (c * c) * 0)) - -sin c = R4 c := by
    unfold R4
    have hdh := double_half c
    have hrearr : (0 : MachLib.Real) - ((c + c) * (1 / (1 + 1)) + c * c * 0) - -sin c
        = sin c - (c + c) * (1 / (1 + 1)) := by mach_ring
    rw [hrearr, hdh]
  exact hasDerivAt_congr_val hfull hclean

theorem R3_zero : R3 0 = 0 := by unfold R3; rw [cos_zero]; mach_ring

/-- `|1 − x²/2 − cos(x)| ≤ x³` for `x ≥ 0`. As far as this session's pathfinder reaches — a genuine,
`sorryAx`-free bound, but not yet the full degree-5 `sin` remainder `eml_sin.v` needs (that requires
extending `R3_deriv`'s technique through `R2`, `R1`, `R0`, with `1/6`/`1/24`/`1/120` coefficient
lemmas analogous to `double_half`). -/
theorem R3_bound (x : MachLib.Real) (hx0 : 0 ≤ x) : abs (R3 x) ≤ (x * x) * x := by
  apply abs_mvt_step R3 R4 x (x * x) hx0 (mul_nonneg hx0 hx0) R3_deriv R3_zero
  intro t ht0 htx
  have h1 : abs (R4 t) ≤ t * t := R4_bound t ht0
  have h2 : t * t ≤ x * x :=
    le_trans (mul_le_mul_of_nonneg_right htx ht0) (mul_le_mul_of_nonneg_left htx hx0)
  exact le_trans h1 h2
