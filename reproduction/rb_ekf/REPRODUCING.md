# Reproducing the rb-EKF trail

**One trail, five steps.** A range-bearing radar EKF, from a symbolic Jacobian the compiler derives,
through a normalized form, a certified fixed-point lowering, emitted RTL, and replay against silicon
captures.

> **Every command on this page was executed on 2026-08-01 in a fresh `debian:bookworm-slim`
> container, as a newly created user, with no host checkouts, no home-directory config, no
> preinstalled toolchains, and anonymous access to public remotes only.** Nothing here is
> reconstructed from a developer's machine. `GIT_TERMINAL_PROMPT=0` was set throughout, so a
> credential prompt would have been a failure rather than a pause.
>
> **All five steps completed. The results below are what that container printed.**

**Disclosed limits.** The walk ran on **arm64** and has not been repeated on x86-64. The silicon
captures are committed artifacts: checking them establishes consistency with the golden and with the
physics, **not** that they came off a die.

## What the grades mean

| grade | what you need | what a pass establishes |
|---|---|---|
| **`MACHINE_CHECKABLE`** | the repo and a toolchain | the result is **re-derived from source**; nothing is taken on trust |
| **`ARTIFACT_VERIFICATION`** | the repo | the result is **consistent with a committed artifact**. It does **not** establish that artifact's provenance — different question, different word |
| **`HARDWARE_REQUIRED`** | an FPGA board | the result is **re-measured from the physical world**. Optional here, always |

---

## Setup — 14 seconds

```bash
git clone https://github.com/agent-maestro/machlib.git
python3 -m venv venv
./venv/bin/pip install monogate-forge eml-cost pytest
cd machlib/reproduction/rb_ekf
```

**`eml-cost` is not optional.** Without it the profiler once returned a sentinel that silently halved
the emitted datapath from Q16.16 to Q8.8 — no error, no warning. That now refuses rather than
guessing, but the dependency is real.

> **Use `monogate-forge >= 0.14.3`.** `0.14.0` was a stale build whose Verilog backend could not lower
> this kernel; `0.14.1` could not compile its own emitted C. Both are superseded.

**First, check you got what we published:**

```bash
python3 check_manifest.py
```

> `MANIFEST PASS — every file present and byte-identical to its record.` · exit `0`

---

## Step 1 — Emit the rb kernel and diff against the pinned emission

**Grade: `MACHINE_CHECKABLE`** · **measured: under 1 second**

```python
import hashlib
from hardware.allocator import FPGAAllocator
from hardware.hdl_gen.verilog_backend import VerilogBackend, EMISSION_FAILURES
from lang.parser import parse_source
from lang.profiler import Profiler
from lang.optimizer import autodiff

mod = parse_source(open("kernel/ekf_range_bearing.eml").read(), "ekf_range_bearing.eml")
Profiler().profile_module(mod)
v = VerilogBackend().compile(mod, FPGAAllocator().allocate(mod))
print(len(v.splitlines()), hashlib.sha256(v.encode()).hexdigest())
print(len(autodiff.NORMALISE_FALLBACKS), EMISSION_FAILURES)
```

**Committed expected result:**

```
786  f47f6c8181723a2878fad488cec5486fb4322fe46b630a36bb8f1df188d51998
0    []
```

The compiler derives `H = ∂h/∂x` symbolically through `sqrt`, a fractional power, a division and
`atan`. No hand-written Jacobian is involved, which is the claim this step exists to let you check.

> ### ⚠ `eml-stdlib` ships a *different* kernel under the same filename
>
> `eml_stdlib/control/ekf_range_bearing.eml` is a robot-pose EKF-SLAM model — 60 lines, state
> `(x, y, θ)` against a landmark. **This** kernel is 28 lines and tracks a 2-D radar target:
> `track(x0, x1) → (sqrt(x0² + x1²), atan(x1 / x0))`. Emitting the other file produces a clean,
> valid, *wrong* result and nothing errors. Use the copy in `kernel/`, sha256 `31c4eedd44307984…`
> (LF); upstream `forge/examples/ekf_range_bearing.eml`.

---

## Step 2 — Normalization soundness suite

**Grade: `MACHINE_CHECKABLE`** · **measured: 0.6 s, or 5.9 s with Lean**

```bash
./venv/bin/python -m pytest normalization/ -q
```

**Committed expected result: `16 passed, 3 skipped`.** The three skips are Lean-dependent and say so
(`needs lean + MachLib`). To run them, complete step 3a's toolchain setup and then:

```bash
MACHLIB_ROOT=/path/to/machlib ./venv/bin/python -m pytest normalization/ -q
```

> `19 passed`

**A skip here is honest, not a pass.** If your Lean install does not match the one that built
MachLib, these report as skipped rather than as failed proofs — a distinction that cost us 47
misattributed test failures before it was fixed.

---

## Step 3 — The two certificates

### 3a — the reciprocal certificate · **`MACHINE_CHECKABLE`** · **measured: 4 m 17 s (build) + under 1 s**

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain "$(cat /path/to/machlib/foundations/lean-toolchain)"
export PATH="$HOME/.elan/bin:$PATH"
cd /path/to/machlib/foundations && lake build        # 575 jobs, ZERO Mathlib dependency

printf 'import MachLib.ReciprocalFormatInstantiation\n#print axioms MachLib.nr_reciprocal_2stage_at_format\n' > /tmp/r.lean
lake env lean /tmp/r.lean
```

**Committed expected result:** exit `0`, and the printed axiom footprint contains **zero**
occurrences of `sorryAx`. The footprint is 33 names — `propext`, `Classical.choice`, `Quot.sound`,
and 30 `MachLib.Real.*`.

**Pin the toolchain from `lean-toolchain`, as above.** A `lean` of a different version reads the
oleans as `incompatible header`.

### 3b — the atan **enumeration** certificate · **`MACHINE_CHECKABLE`** · **measured: 0.7 s**

```bash
./venv/bin/python -m pytest certificate/ -q
```

> `8 passed`

This is the exhaustive sweep over the fixed-point domain that yields the **6.16e-02 rad** worst case
at the band edge.

> **Do not substitute the analytic theorem for it.** `MachLib.Real.eml_atan_full_fwd_error` is public
> and re-derives `sorryAx`-free with the step-3a commands. It is the Taylor-remainder result — a
> *different artifact*. Checking it does not check the enumeration. Flagged because the substitution
> is convincing and we nearly made it.

---

## Step 4 — Replay the golden against the silicon captures

**Grade: `ARTIFACT_VERIFICATION`** · **measured: under 1 second, no dependencies**

```bash
python3 silicon/scripts/analyze_rb_ekf_anchor.py silicon/evidence/rb_ekf_trace.jsonl
```

**Committed expected result:** `ACCEPTANCE: PASS`, exit `0` — 8 steps, every one `OK`, and:

```
--- PHYSICS GATE (reference-free, on the SILICON trace) ---
    P positive-semidefinite / P symmetric / trace(P) non-increasing
    bounded predict-growth on valid=0 / error monotone on constant z
    PHYSICS GATE: PASS
```

Error decreases monotonically across all eight steps, `0.30621 → 0.03246`.

**Why a physics gate as well as bit-exactness, and why it runs on the trace and never on the golden.**
On 2026-07-27 the golden and the RTL agreed **bit-for-bit on a sign-inverted gain for three rounds**.
Bit-exactness passed while the physics was wrong, because a golden and its RTL share arithmetic
ancestry by construction. The gate asserts things about the *mathematics* — covariance stays PSD,
error falls on constant input — and it is what would have caught that on round one.

### Step 4-HW — re-measure on silicon · **`HARDWARE_REQUIRED`, and OPTIONAL**

**Verifying the captures needs no hardware. Re-measuring them does** — that is why these are two
rungs. Re-measurement needs a **Digilent Arty A7-100T** (`xc7a100tcsg324-1`, ≈ **$130**) plus Vivado
for the bitstream. **Nothing else on this page depends on owning one.**

---

## Step 5 — Re-derive the headline axiom footprints

**Grade: `MACHINE_CHECKABLE`** · **measured: 4.0 s after step 3a's build**

```bash
cd /path/to/machlib
python3 foundations/tools/axiom_ledger/check_ledger.py
```

**Committed expected result:**

```
AXIOM-LEDGER PASS  242 axioms pinned, 57 headline footprints ⊆ trusted.
```

exit `0`. **Read the exit code — it distinguishes three different facts:**

| exit | meaning |
|---|---|
| `0` | the trust boundary was checked and holds |
| `1` | the trust boundary was checked and **drifted** |
| `2` | **`UNAVAILABLE`** — it was **not checked**, because `lake` is not on your PATH |

`2` exists because this step failed for us the first time: without a Lean toolchain the runner used
to die with a `FileNotFoundError` traceback and exit `1` — **the same code as a drifted boundary.**

---

## Summary — 5 of 5

| step | grade | wall time |
|---|---|---|
| setup — clone, venv, pip | — | 14 s |
| 1 · emit and diff `f47f6c81…` | **`MACHINE_CHECKABLE`** | < 1 s |
| 2 · normalization soundness | **`MACHINE_CHECKABLE`** | 0.6 s (5.9 s with Lean) |
| 3a · reciprocal certificate | **`MACHINE_CHECKABLE`** | 4 m 17 s + < 1 s |
| 3b · atan enumeration certificate | **`MACHINE_CHECKABLE`** | 0.7 s |
| 4 · replay vs silicon captures | **`ARTIFACT_VERIFICATION`** | < 1 s |
| 4-HW · re-measure on silicon | **`HARDWARE_REQUIRED`**, optional | Arty A7-100T ≈ $130 |
| 5 · 57 headline axiom footprints | **`MACHINE_CHECKABLE`** | 4.0 s |

**Under five minutes end to end, and the Lean build is four of them.**

## What this page is not

* **It is not a claim that the captures came off a die.** Step 4 is `ARTIFACT_VERIFICATION` and that
  is the whole point of giving it a separate word.
* **It is not a proof that the filter is optimal.** The rb-EKF is first-order, so MMSE-optimality does
  not carry and is not claimed.
* **It does not cover the compiler's source history.** `forge` is a private repository; the compiler
  is publicly installable, which is what every step above needs. Reading its history is a different
  question and no step here depends on it.

## If your output differs

> **If your output differs from the committed result at any step, that divergence is a finding — file
> it here:**
>
> ### **https://github.com/agent-maestro/machlib/issues**

Include the step, the exact command, the expected value from this page, what you got, and your OS and
architecture. **This walk ran on arm64 only**, so an architecture-dependent divergence is a result we
do not have and would want.

**A divergence is useful even if it turns out to be your environment.** Walking this trail as a
stranger produced fourteen findings and eight shipped fixes — a compiler that reported failed
emission as success, a published wheel whose bits did not match its version, a wheel that could not
compile its own output, and 47 test failures that were an instrument defect and had been explained
away twice. **Every one of them was invisible from inside the project.**
