# Fixed-point (Q-format) forward-error — EML→RTL equivalence, Leg A

*2026-06-26. Companion to `cross_target_equivalence_2026_06_26.md`. Module:
`MachLib.FixedPoint`.*

`FPModel` proved cross-target equivalence for the **floating-point** targets
(`f64`/`f32`) using the multiplicative standard model `fl(a∘b)=(a∘b)(1+δ)`,
`|δ|≤u`. The FPGA target is not floating-point — its datapath is **fixed-point**.
This module supplies the fixed-point rounding model and proves the forward-error
of a representative control kernel (a one-step PID law) against the exact
real-valued law. It is the first ("Leg A") of the two EML→RTL legs sketched in
`roadmap/eml-rtl-equivalence-sketch.md`; Leg B (gate-level / bit-vector
equivalence) is a separate, not-yet-started program.

## The rounding model (read off the emitted RTL, not assumed)

The fixed-point convention is **Q16.16** — signed 32-bit, 16 fractional bits.
In the emitted Verilog, `1.0` is the integer `65536 = 2¹⁶`, so the quantization
step is `s = 2⁻¹⁶`. The three operation classes lower as:

| op | RTL lowering | error model |
| --- | --- | --- |
| multiply | `(a*b) >>> FRAC` (arithmetic shift right = truncate to grid) | `\|fxmul a b − a·b\| ≤ s` |
| add / sub | integer `±` | **exact** (no rounding; no overflow in regime) |
| constant | quantized to grid | `\|c_fx − c\| ≤ s` |

Unlike the multiplicative FP model, the fixed-point error is **additive** (an
absolute step `s`, not a relative `(1±u)`). Adds are *exact* here (simpler than
FP); the new structural ingredient is the saturating `clamp`.

## What is proved (`MachLib.FixedPoint`, 17 theorems, `sorryAx`-free)

- **`clamp x lo hi := max lo (min x hi)`** — exactly the emitted shape
  (`max OUT_MIN (min raw OUT_MAX)`). It was `min (max x lo) hi` until 2026-09-22, when
  the proof backends were brought onto the EML language's definition of `clamp`
  (`max(lo, min(x, hi))`); the two differ only for `lo > hi`, where the old order
  returns `hi` and the language returns `lo`.
- **`max_lipschitz` / `min_lipschitz` / `clamp_lipschitz`** — `min`, `max`, and
  hence `clamp` are 1-Lipschitz: `|clamp a − clamp b| ≤ |a − b|`. Saturation
  never amplifies error. (Proved one-sided first via two branch-condition case
  splits, then stitched with `abs_sub_le_of`.)
- **`fxmul_err`** — one truncating product with a quantized gain sits within
  `s·|x| + s` of the exact product.
- **`pid_raw_fwd_error`** — the pre-clamp sum of three such products is within
  `s·(|e|+|i|+|d|) + 3s` of `Kp·e + Ki·i + Kd·d` (decompose the sum, bound each
  term, recombine by triangle — the same shape as `FPModel`'s `dot3`).
- **`pid_fx_fwd_error`** (the Leg A statement) — the *complete* datapath
  (truncating multiplies, exact adds, saturating clamp) is within
  `s·(|e|+|i|+|d|) + 3s` of the exact real PID law, for any step `s ≥ 0`.
- **`pid_q16_fwd_error`** — instantiated at the real Forge step `s = 2⁻¹⁶`
  (`q16_step`) and the kernel's `|inputs| ≤ 100` refinement bound, giving the
  concrete worst-case bound `303·2⁻¹⁶ ≈ 4.62e-3` on the `[−1,1]` output.
- **`clamp_le_hi` / `lo_le_clamp`** — the output-range bound (`OUT_MIN ≤ pid_step
  ≤ OUT_MAX`), which is the kernel's own `@verify` obligation. Since the 2026-09-22
  order swap the `lo ≤ hi` side condition sits on `clamp_le_hi` (the ceiling), not on
  `lo_le_clamp`, which is now unconditional.

`#print axioms` on every PID theorem shows only `propext`, `Classical.choice`,
`Quot.sound`, the `MachLib.Real` field axioms, and `abs_add`/`abs_mul` — the same
documented base as `FPModel`, and notably *not* the FP model's `u` axiom. No
`sorryAx`, no Mathlib.

## Why this is the moat-completing leg

The hardware lane already demonstrates cross-backend agreement *empirically*
(one source → C/ESP32 reproducing the reference bit-for-bit; Arty A7 bitstreams).
What was missing is a *proof* that the fixed-point RTL datapath computes the same
function as the source, within a stated bound. `pid_fx_fwd_error` is that proof
for the PID datapath: it turns "the FPGA agrees in our test" into "the FPGA
output is provably within `303·2⁻¹⁶` of the source's value, by construction."

## The methodology held again

This closed with the existing `FPModel` toolkit plus two new lemmas
(`clamp_lipschitz`, `fxmul_err`) — no new tactic, no nonlinear engine. The lever
was, once more, the *decomposition* (sum-of-products → triangle; saturation →
the Lipschitz *object*), per `proof_decomposition_before_automation.md`.
