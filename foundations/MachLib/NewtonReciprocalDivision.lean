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

end Real
end MachLib
