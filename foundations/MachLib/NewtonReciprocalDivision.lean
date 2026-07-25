import MachLib.FixedPointCertifier

/-!
# Newton-Raphson fixed-point division — error model (Q_n track, part 1)

Forge's Verilog backend (`hardware/hdl_gen/verilog_backend.py`, the `node.value == "/"` case) lowers
every EML `a / b` to `a * eml_reciprocal(b)`, where `eml_reciprocal.v` is a **4-stage Newton-Raphson
reciprocal**:

    y_{n+1} = y_n · (2 − b · y_n)          (NR iteration for 1/b)

Each stage does two truncating Q-format multiplies (`qmul`, i.e. `>>> FRAC`): `by = qmul(b, y)` then
`y' = qmul(y, 2 − by)`. So a division is `8` truncating multiplies (inside the reciprocal) `+ 1` (the
final `a·recip`). `FixedPointCertifier.lean` already certifies `+`, `×`, `clamp` under per-node
truncation (`FxErr`/`fx_sound`); it does NOT yet handle division. This file builds the missing
numerical core: the NR reciprocal's error, which is *not* a single truncation but a quadratically-
convergent iteration with truncation at each step.

## The math (paper-derived first, then machined here)

Work with the **scaled error** `e_n := 1 − b·y_n` (dimensionless; `e_n = b·(1/b − y_n)`, so
`y_n − 1/b = −e_n/b`). The exact NR step `nrStep b y = y·(2 − b·y)` satisfies the quadratic-
convergence identity

    1 − b·nrStep(b,y) = (1 − b·y)²     i.e.   e_{n+1} = e_n²          (`nr_convergence`)

so from a 1-bit initial estimate (`|e_0| ≤ 1/2`) the *exact* iteration reaches `|e_4| ≤ e_0^16 ≤
2⁻¹⁶` — the ~16 bits the comment in `eml_reciprocal.v` claims, one bit-doubling per stage.

The **hardware** truncates. Writing `by' = b·y + δ₁` (`|δ₁| ≤ s`, `s = 2⁻ᶠ` the Q-step) for the first
`qmul` and `y' = y·(2 − by') + δ₂` (`|δ₂| ≤ s`) for the second, a one-line expansion gives the exact
identity

    1 − b·y' = (1 − b·y)² + b·y·δ₁ − b·δ₂                              (`nr_scaled_err_identity`)

hence the one-step **truncated error recurrence**

    |1 − b·y'| ≤ (1 − b·y)² + |b·y|·s + |b|·s                          (`nr_scaled_err_bound`)

The `|b|·s` term is the honest cost of a Q16.16 reciprocal: the *absolute* error of `1/b` is ~one
ULP, but for a large divisor `|b|` the *scaled* (relative) error floor is `~|b|·s`, so the reciprocal
is only accurate to ~1 relative bit once `|b|` approaches `2^FRAC`. This is a real property of the
datapath, not a proof artifact — the division is absolute-accurate, not relative-accurate, for large
divisors.

## Status / next steps (handoff)

This file lands the two foundational lemmas (exact convergence + one-step truncated recurrence),
paper-verified then machine-checked, `sorryAx`-free, zero new axioms. The remaining Q_n work, in
order: (1) the 4-stage composition — unroll `nr_scaled_err_bound` four times under the invariant
`|e_n| ≤ 1/2` (a contraction `|e_{n+1}| ≤ |e_n|/2·|e_n| + floor`), yielding the reciprocal's total
error; (2) convert the scaled bound to the absolute reciprocal error `|recip(b) − 1/b|`; (3) a `div`
node for `FxExpr` (or a standalone `fxerr_div` combinator) composing the reciprocal error with the
final `qmul` via `fxerr_mul`. The ~135 kernels that use `÷` are then covered by `fx_sound`.
-/

namespace MachLib
namespace Real

-- Local arithmetic helpers (the triangle/monotonicity lemmas below live in modules this file does
-- not import).
private theorem abs_sub_le_l (a b : Real) : abs (a - b) ≤ abs a + abs b := by
  have h : a - b = a + -b := by mach_mpoly [a, b]
  rw [h, ← abs_neg b]; exact abs_add a (-b)
private theorem add_le_add_right_l {a b : Real} (h : a ≤ b) (c : Real) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]; exact add_le_add_left h c
private theorem add_le_add_l {a b c d : Real} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right_l h1 c) (add_le_add_left h2 b)

/-- One exact Newton-Raphson reciprocal step, `y ↦ y·(2 − b·y)` (hardware `TWO = 2` in Q-format). -/
noncomputable def nrStep (b y : Real) : Real := y * ((1 + 1) - b * y)

/-- **Exact quadratic convergence**: the scaled error squares each step, `e_{n+1} = e_n²` where
`e_n = 1 − b·y_n`. This is why 4 stages reach ~16 bits from a 1-bit start. -/
theorem nr_convergence (b y : Real) :
    1 - b * nrStep b y = (1 - b * y) * (1 - b * y) := by
  rw [nrStep]; mach_mpoly [b, y]

/-- **One-step truncated-error identity**: with `by' = b·y + δ₁` the first (truncating) `qmul` and
`y' = y·(2 − by') + δ₂` the second, the new scaled error is the exact square plus two truncation
terms. Pure algebraic identity in `b, y, by', y'`. -/
theorem nr_scaled_err_identity (b y by' y' : Real) :
    1 - b * y'
      = (1 - b * y) * (1 - b * y) + b * y * (by' - b * y)
        - b * (y' - y * ((1 + 1) - by')) := by
  mach_mpoly [b, y, by', y']

/-- **One-step truncated error recurrence**: `|e'| ≤ e² + |b·y|·s + |b|·s`. The `e²` term is NR's
quadratic convergence; the two `·s` terms are the two `qmul` truncations (`s = 2⁻ᶠ`). -/
theorem nr_scaled_err_bound (b y s by' y' : Real) (hs : 0 ≤ s)
    (h1 : abs (by' - b * y) ≤ s)
    (h2 : abs (y' - y * ((1 + 1) - by')) ≤ s) :
    abs (1 - b * y')
      ≤ (1 - b * y) * (1 - b * y) + abs (b * y) * s + abs b * s := by
  rw [nr_scaled_err_identity b y by' y']
  -- |A + B - C| ≤ |A| + |B| + |C|, with A = (1-by)² ≥ 0
  have hA : abs ((1 - b * y) * (1 - b * y)) = (1 - b * y) * (1 - b * y) :=
    abs_of_nonneg (mul_self_nonneg _)
  have hB : abs (b * y * (by' - b * y)) ≤ abs (b * y) * s := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hC : abs (b * (y' - y * ((1 + 1) - by'))) ≤ abs b * s := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have t1 : abs ((1 - b * y) * (1 - b * y) + b * y * (by' - b * y)
              - b * (y' - y * ((1 + 1) - by')))
      ≤ abs ((1 - b * y) * (1 - b * y) + b * y * (by' - b * y))
          + abs (b * (y' - y * ((1 + 1) - by'))) := abs_sub_le_l _ _
  have t2 : abs ((1 - b * y) * (1 - b * y) + b * y * (by' - b * y))
          + abs (b * (y' - y * ((1 + 1) - by')))
      ≤ (abs ((1 - b * y) * (1 - b * y)) + abs (b * y * (by' - b * y)))
          + abs (b * (y' - y * ((1 + 1) - by'))) := add_le_add_right_l (abs_add _ _) _
  have t3 : (abs ((1 - b * y) * (1 - b * y)) + abs (b * y * (by' - b * y)))
          + abs (b * (y' - y * ((1 + 1) - by')))
      ≤ ((1 - b * y) * (1 - b * y) + abs (b * y) * s) + abs b * s := by
    rw [hA]; exact add_le_add_l (add_le_add_l (le_refl _) hB) hC
  exact le_trans (le_trans t1 t2) t3

private theorem add_mul_r (X Y s : Real) : X * s + Y * s = (X + Y) * s := by mach_mpoly [X, Y, s]

/-- **The contraction step**: under the convergence invariant `|1 − b·y| ≤ 1/2`, one truncated NR
step *halves* the scaled error and adds the truncation floor:
`|1 − b·y'| ≤ |1 − b·y|/2 + (|b·y| + |b|)·s`. The halving comes from `e² ≤ |e|·(1/2)` when
`|e| ≤ 1/2`; iterating this four times drives the error to the `(|b·y|+|b|)·s` floor. -/
theorem nr_contract_step (b y s by' y' : Real) (hs : 0 ≤ s)
    (h1 : abs (by' - b * y) ≤ s) (h2 : abs (y' - y * ((1 + 1) - by')) ≤ s)
    (hinv : abs (1 - b * y) ≤ 1 / (1 + 1)) :
    abs (1 - b * y')
      ≤ abs (1 - b * y) * (1 / (1 + 1)) + (abs (b * y) + abs b) * s := by
  have hsq : (1 - b * y) * (1 - b * y) ≤ abs (1 - b * y) * (1 / (1 + 1)) := by
    have he2 : abs (1 - b * y) * abs (1 - b * y) = (1 - b * y) * (1 - b * y) := by
      rw [← abs_mul]; exact abs_of_nonneg (mul_self_nonneg _)
    rw [← he2]; exact mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
  apply le_trans (nr_scaled_err_bound b y s by' y' hs h1 h2)
  rw [← add_mul_r (abs (b * y)) (abs b) s, add_assoc]
  exact add_le_add_right_l hsq _

/-! ## §3 — the 4-stage composition and division combinator (Q_n part 3) -/

/-- **The 4-fold contraction bound**: chaining `a_{k+1} ≤ a_k·h + c` four times gives
`a_4 ≤ a_0·h⁴ + c·(1 + h + h² + h³)`. Instantiated at `h = 1/2` (the `nr_contract_step` halving)
this is `a_4 ≤ a_0/16 + (15/8)·c`; with `a_0 ≤ 1/2` (the 1-bit initial estimate) the reciprocal's
scaled error is `≤ 1/32 + (15/8)·c`, `c` the uniform truncation floor `(3/2+|b|)·s`. -/
theorem contract4_bound (a0 a1 a2 a3 a4 h c : Real) (hh : 0 ≤ h)
    (h1 : a1 ≤ a0 * h + c) (h2 : a2 ≤ a1 * h + c)
    (h3 : a3 ≤ a2 * h + c) (h4 : a4 ≤ a3 * h + c) :
    a4 ≤ a0 * (h * h * h * h) + c * (1 + h + h * h + h * h * h) := by
  have b2 : a2 ≤ (a0 * h + c) * h + c :=
    le_trans h2 (add_le_add_right_l (mul_le_mul_of_nonneg_right h1 hh) c)
  have b3 : a3 ≤ ((a0 * h + c) * h + c) * h + c :=
    le_trans h3 (add_le_add_right_l (mul_le_mul_of_nonneg_right b2 hh) c)
  have b4 : a4 ≤ (((a0 * h + c) * h + c) * h + c) * h + c :=
    le_trans h4 (add_le_add_right_l (mul_le_mul_of_nonneg_right b3 hh) c)
  rwa [show (((a0 * h + c) * h + c) * h + c) * h + c
      = a0 * (h * h * h * h) + c * (1 + h + h * h + h * h * h) from by mach_mpoly [a0, h, c]] at b4

private theorem mul_sub_l (b r inv : Real) : b * (r - inv) = b * r - b * inv := by
  mach_mpoly [b, r, inv]

/-- **Scaled → absolute reciprocal error**: `|1 − b·r| = |b|·|r − 1/b|` (`b ≠ 0`). Converts the
scaled error the NR analysis bounds into the absolute reciprocal error the division needs. -/
theorem recip_scaled_to_abs (b r : Real) (hb : b ≠ 0) :
    abs (1 - b * r) = abs b * abs (r - 1 / b) := by
  have key : 1 - b * r = -(b * (r - 1 / b)) := by
    rw [mul_sub_l b r (1 / b), mul_inv b hb]; mach_mpoly [(b * r : Real)]
  rw [key, abs_neg, abs_mul]

private theorem abs_sub_comm_l (x y : Real) : abs (x - y) = abs (y - x) := by
  rw [show x - y = -(y - x) from by mach_mpoly [x, y], abs_neg]

/-- **The NR reciprocal as an `FxErr` quantity**: given the (absolute) reciprocal error bound
`|recip_e − 1/b| ≤ Eabs`, package it in the `FixedPointCertifier` framework with exact value `1/b`
and evaluated value `recip_e`. `Eabs` is supplied by `contract4_bound` (scaled error) composed with
`recip_scaled_to_abs` (÷|b|); this is the bridge from the NR analysis to `FxErr`/`fx_sound`. -/
theorem fxerr_recip (b recip_e Eabs : Real) (habs : abs (recip_e - 1 / b) ≤ Eabs) :
    FxErr (abs recip_e) Eabs (1 / b) recip_e :=
  ⟨le_refl _, by rw [abs_sub_comm_l (1 / b) recip_e]; exact habs⟩

/-- **The fixed-point division combinator**: `a / b` is certified as `qmul(a, recip(b))` — a single
truncating multiply of the dividend by the NR reciprocal (`fxerr_recip`). This is exactly
`fxerr_mul` with the reciprocal as the second operand, so division inherits the certifier's whole
`+`/`×`/`clamp` machinery; the ~135 EML kernels that use `÷` are covered by feeding this into
`fx_sound`. `vr = 1/vb` (exact reciprocal), `rr = recip_e` (NR output). -/
theorem fxerr_div {s Mx Ex vx xe Mr Er vr rr p : Real} (hs : 0 ≤ s)
    (hx : FxErr Mx Ex vx xe) (hr : FxErr Mr Er vr rr) (hp : TruncW s p (vx * vr)) :
    FxErr (Mx * Mr) (Mx * Er + Mr * Ex + Ex * Er + s) p (xe * rr) :=
  fxerr_mul hs hx hr hp

end Real
end MachLib
