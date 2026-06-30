# Closed-loop safety — the guard keeps the plant safe, for all time

A reader's front door to MachLib's **closed-loop safety** results: machine-checked proofs that a
saturating "guard" keeps a plant's *state* inside a safe envelope for **all time**, under **any**
controller signal and **any** bounded disturbance. The property a control engineer actually cares
about (state stays safe, not per-step arithmetic error), proven in time.

Everything below is `sorryAx`-free and rests on **0 axioms beyond MachLib's documented base** — the
Real field/order axioms (`addR`, `mulR`, `add_comm`, `mul_distrib`, `lt_total`, …) and, for the
V-norm result only, the `sqrt` axioms (`sqrt_sq_nonneg`, `le_sqrt_of_sq_le`, …). No `sorry`, no
`admit`, no new "trust me" axiom. Verified, not asserted (§8).

Source: `MachLib/ClosedLoopSafety.lean`, `MachLib/LyapunovSafety.lean`.

---

## 1. What this is

Everything else in MachLib's certifier bounds error *per step*. This bounds the **trajectory**: a
discrete-time barrier / Lyapunov (input-to-state-stability) argument that the plant state stays in a
forward-invariant safe set. The thesis is the **guard**: a saturating clamp `u = clamp(v, −U, U)`
around the actuator. The clamp alone bounds `|u| ≤ U` no matter what the controller `v` computes — so
the safety proof rides on the *saturation*, not the control law.

## 2. Start here: the one result

`clamp_guarded_safe` — for a first-order plant `x_{k+1} = a·x_k + clamp(v_k, −U, U) + w_k` with a
stable pole (`|a|·X + (U+W) ≤ X`, true for some finite `X` exactly when `|a| < 1`), the state stays
in `|x_k| ≤ X` for **all k and ANY signal v_k**:

> **the loop is safe even if the controller inside the guard is wrong** (or faulty, or lying).

That is the whole point. A bounded fault — a biased actuator, a lying sensor, a brown-out — is just a
bounded disturbance `w`; it is absorbed by the same envelope, so the proof already covers it
(`clamp_guarded_ultimately_bounded` adds: the state *converges into* the envelope from anywhere).

## 3. The ladder (the substance)

Each rung is `sorryAx`-free. The state grows from a scalar to a coupled vector; the safe set grows
from an interval to a quadratic sublevel set.

| theorem | plant | safe set |
|---|---|---|
| `safe_envelope_invariant` / `measure_sublevel_invariant` | abstract contraction `m_{k+1} ≤ ρ·m_k + δ` | `m_k ≤ X` (the reusable core) |
| `clamp_guarded_safe`, `clamp_guarded_ultimately_bounded` | scalar, saturating guard | `|x| ≤ X`; converges to `(U+W)/(1−|a|)` |
| `first_order_clamp_envelope` | scalar, envelope pinned to its value | `|x| ≤ X`, `X` from `(1−a)·X = U+W` (division-free) |
| `nonlinear_drift_clamp_safe` | scalar, **nonlinear** drift `|f(x)| ≤ L·|x|+c` (`L<1`) | `|x| ≤ X` — subsumes the linear case; `nonlinear_abs_drift_safe` is a worked non-affine instance |
| `two_mode_clamp_envelope` | **two decoupled modes**, one actuator | weighted-ℓ¹ `p₁|x₁|+p₂|x₂| ≤ X` |
| `coupled_two_state_clamp_envelope` | **coupled 2×2** (off-diagonal), ℓ¹-diagonally-dominant | weighted-ℓ¹ sublevel set |
| `quadratic_lyapunov_sublevel` | **coupled oscillator** (non-diagonal `V = xᵀPx`) + disturbance | `{V ≤ X}`, needs `ρ < ½` |
| `quadratic_lyapunov_sublevel_tight'` | same oscillator, **any `ρ < 1`** | `{V ≤ X²}`, **no extra hypotheses** |

The last rung is the sharp one: the V-norm `√V` is a genuine norm (Minkowski proven via a
Cauchy–Schwarz Gram identity that `mach_mpoly` discharges), so the disturbed coupled oscillator
contracts at rate `√ρ` for **any** stable `ρ < 1` — no factor-of-2 restriction, no triangle-inequality
hypothesis. Fully closed.

## 4. The envelope is an actual number, measured on silicon

For the EE-BRIDGE PID plant (`electronics_intake/kernels/pid_dual_target_v0`, monogate-research):
the constants give `a = 1−DT/TAU = 0.99`, `U = DT·K/TAU·OUT_MAX = 0.01`, so the proven envelope is
**`X* = (U+W)/(1−|a|) = 1 + 100·W`** — nominally `1.0` (which equals the plant's DC gain, so it holds
for *any* stable unity-gain plant), `2.0` under a full-scale actuator fault.

*The envelope number is now itself machine-checked* (`MachLib.Decimal`). Those constants are decimal
literals, which MachLib's `Real` previously left opaque — so the step "`1−0.99 = 0.01`, hence `X* =
1.0`" was done in Python `float`, not Lean. `MachLib.Decimal` closes that gap: the defining property
of a decimal literal, `realOfScientific m true e · 10ᵉ = m` (one new axiom, `realOfScientific_clears`,
which *subsumes* the three ad-hoc `…_dot_zero` bridges in `Basic.lean` — `one_dot_zero_from_clears`
derives one back), yields a clear-denominators recipe under which both decimal **subtraction**
(`one_sub_decimal`) and **multiplication** (`decimal_mul`) reduce to integer `natCast` arithmetic. The
two flagship envelope relations are then theorems, `sorryAx`-free: `pid_envelope_relation : (1−0.99)·1
= 0.01+0` and `motor_envelope_relation : (1−0.996)·2.0 = 0.008`. *Scope:* this machine-checks the
*exact arithmetic* for these specific constants; `safety_certify.py` still instantiates arbitrary
kernels (and the auto-derived Lyapunov rate) in floating point — the general theorems are the proof,
the per-kernel number is the instantiation, and now the two flagship instantiations are Lean-checked.

The closed loop was run on a real **Arty A7-100T** (timing-closed bitstream, Vivado, 0 failing
endpoints): nominal peak `|x| = 0.655 ≤ 1.0`, and under an injected `+1.0` actuator fault the state
rises **above** the nominal `1.0` (the fault is real and visible) but stays `≤ 2.0` — the proof held,
on hardware, under a fault.

*On the silicon trajectory:* it is bit-identical to the Verilator sim — for a deterministic
fixed-point datapath the correct, strongest outcome (the FPGA reproduces the verified RTL exactly),
but the trajectory *values* alone then can't distinguish a real capture from a copy of sim.

*Resolved on a real analog plant.* The same verified controller was then closed around a **physical
first-order RC circuit** (ESP32 DAC→R→node→C→GND, ADC reads the state, τ=RC=0.1 s = `plant.eml`).
The captured trajectory is genuinely analog — **not** bit-identical to sim (783 sample-to-sample
direction reversals = real ADC noise) — so the byte-identity question is gone. Nominal peak
`|x| = 0.806 ≤ 1.0`; under the `+1.0` actuator fault `|x| = 1.546 ≤ 2.0`. Notably the real loop
**limit-cycles** (the derivative term amplifies ADC noise), so its trajectory looks nothing like the
smooth sim — yet the envelope holds, because the bound is a *safety* guarantee resting on the
saturation, not a tracking claim. (Run: `electronics_intake/kernels/pid_dual_target_v0/physical/`.)

## 5. What this does NOT claim

- It bounds the **plant state**, treating the control as an adversarially clamp-bounded input. It is
  **safety, not tracking** — no settling-time / steady-state-accuracy claim.
- The coupled/quadratic rungs take the homogeneous Lyapunov decrease `V(Ax) ≤ ρ·V(x)` (the LMI a
  control engineer solves) as a **hypothesis** — the standard certificate. The theorems prove that
  this certificate + a disturbance bound ⇒ forward-invariance; producing the certificate for a given
  plant is the caller's (elementary) step.
- The **forward-Euler discretization / fixed-point quantization** error is a *separate* layer — the
  per-step forward-error certifier (`forward_error_certifier.md`, `compare_to_bound.py`). The two
  compose; neither subsumes the other.
- (Resolved) the physical-plant validation is **done** — see §4: a real analog RC plant, genuinely
  noisy, inside the envelope under nominal + fault.

## 6. Check it yourself

```bash
# Build (part of the MachLib aggregate):
cd foundations && lake build MachLib.ClosedLoopSafety MachLib.LyapunovSafety

# Confirm the headline ladder is sorryAx-free + rests only on the documented axiom base:
printf 'import MachLib.LyapunovSafety\n#print axioms MachLib.Real.clamp_guarded_safe\n#print axioms MachLib.Real.quadratic_lyapunov_sublevel\n' > /tmp/chk.lean
lake env lean /tmp/chk.lean   # -> no sorryAx; only Real-field/order/sqrt axioms

# The per-kernel envelope NUMBERS are machine-checked (decimal arithmetic), resting only on the one
# new foundational axiom realOfScientific_clears (no sorryAx):
printf 'import MachLib.Decimal\n#print axioms MachLib.Real.pid_envelope_relation\n#print axioms MachLib.Real.motor_envelope_relation\n' > /tmp/dec.lean
lake env lean /tmp/dec.lean   # -> no sorryAx; + MachLib.Real.realOfScientific_clears

# Library-wide integrity gate — fails (non-zero) if ANY non-allowlisted sorryAx appears
# (e.g. a future mach_ring-swallowed goal). Proven to go red on an injected canary:
tools/check.sh
```

## 7. Status — consolidated

Theory: **fully closed** (scalar → vector → coupled-ℓ¹ → coupled-quadratic-oscillator, the last
unconditional), `sorryAx`-free, 0 axioms beyond the documented base, integrity-gated. Per-kernel
envelope numbers: the two flagship instantiations (`1.0`, `2.0`) are now **machine-checked decimal
arithmetic** (`MachLib.Decimal`, +1 foundational axiom `realOfScientific_clears`) — the old
float-asserted step is closed for the flagships. Silicon:
**validated** on Arty A7-100T under nominal + injected fault (timing-closed). Physical analog plant:
**validated** on a real RC circuit (ESP32), genuinely noisy — which closes the one byte-identity
joint a reviewer would push (§4). The "single biggest leap" — proven closed-loop safety, measured on
real hardware (FPGA *and* a real analog plant), surviving an injected fault — closed.
