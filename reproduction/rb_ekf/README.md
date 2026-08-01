# rb-EKF reproduction evidence package

**The artifacts a stranger needs to check the range-bearing radar EKF trail, published because a
reproduction claim that withholds its evidence is not a reproduction claim.**

Published 2026-08-01 in response to the project's first external reproducer, who asked whether the
trail is reconstructible from public artifacts. **It was 2-of-5. This package is four of the three
gaps closed** — the fifth (the compiler) was already public on PyPI and needed a corrected release
rather than a publication.

Every file is listed with its sha256 in [`MANIFEST.sha256`](MANIFEST.sha256), **computed on
LF-normalised bytes**. That normalisation is not fussiness: this package draws from two repositories
that check out with different line endings, and the original evidence packet shipped one hash in the
wrong normalisation for exactly that reason.

## What each directory is, and what it proves

| directory | artifact | what checking it establishes |
|---|---|---|
| `kernel/` | `ekf_range_bearing.eml`, 28 lines | **the trail's actual source.** See the warning below. |
| `normalization/` | 3 test modules | the derivative normalisation pass is sound, and its fallback is gated rather than silent |
| `certificate/` | `test_eml_atan_wide_certificate.py` | the **enumerated** atan certificate — an exhaustive sweep over the fixed-point domain, worst case **6.16e-02 rad** |
| `silicon/` | captures + golden + analyzer + anchor RTL | the silicon trace reproduces the golden bit-for-bit, and passes a reference-free physics gate |
| `tools/` | `physics_gate.py` | the third oracle — assertions about the mathematics, not about another implementation |

> ## ⚠ Read this before you go looking for the kernel yourself
>
> **`eml-stdlib` publicly ships a file also named `ekf_range_bearing.eml`. It is a different
> kernel.** That one is 60 lines and models a robot pose `(x, y, θ)` observing a landmark. **This**
> one is 28 lines and models a 2-D radar target:
>
> ```
> track(x0, x1) → (sqrt(x0² + x1²), atan(x1 / x0))
> ```
>
> They share a filename and nothing else. Emitting the other file will not reproduce this trail's
> RTL, and the mismatch will not tell you why. Upstream identity of the file in this package:
>
> **`forge/examples/ekf_range_bearing.eml` @ `18c3851`, sha256 `31c4eedd44307984…` (LF)**

## Running the evidence

### Silicon-capture replay — no hardware required

```bash
python3 silicon/scripts/analyze_rb_ekf_anchor.py silicon/evidence/rb_ekf_trace.jsonl
```

**Expected:** `ACCEPTANCE: PASS`, exit **0**. 8 steps, every one `OK`, and:

```
--- PHYSICS GATE (reference-free, on the SILICON trace) ---
    P positive-semidefinite / P symmetric / trace(P) non-increasing
    bounded predict-growth on valid=0 / error monotone on constant z
    PHYSICS GATE: PASS
```

Pure Python, no dependencies, seconds. **This verifies a committed capture against the golden — it
does not re-measure silicon.** Different claim, and the distinction is deliberate: see
`REPRODUCING.md` on `ARTIFACT_VERIFICATION` versus `HARDWARE_REQUIRED`.

**Why there is a physics gate at all, and why it runs on the trace and never on the golden.** On
2026-07-27 the golden and the RTL agreed **bit-for-bit on a sign-inverted gain for three rounds**.
Bit-exactness passed while the physics was wrong, because a golden and its RTL share arithmetic
ancestry by construction. The gate asserts things about the *mathematics* — covariance stays PSD,
error decreases on constant input — and it is what would have caught that defect on round one.

### The normalization suite and the atan certificate

Both need the compiler:

```bash
pip install monogate-forge eml-cost
python3 -m pytest normalization/ certificate/ -q
```

**`eml-cost` is not optional.** Without it the profiler used to return a sentinel that silently
halved the emitted datapath from Q16.16 to Q8.8 — no error, no warning. That is fixed (it now
refuses), but the dependency is real.

> **Version note.** `monogate-forge==0.14.0` on PyPI is a **stale build** whose Verilog backend
> cannot lower this kernel. Use **0.14.1 or later**.

## What this package does NOT contain

**Stated plainly, because a package that quietly omits things is worse than one that lists them.**

* **The compiler source.** `forge` remains a private repository. The compiler is publicly
  installable from PyPI, which is what reproducing the emission requires; reading its history is a
  separate question and is not needed for any rung.
* **The bitstream and the build TCL.** Re-measuring on hardware needs a Digilent Arty A7-100T
  (`xc7a100tcsg324-1`, ≈ $130) and Vivado. **Nothing here is contingent on you owning one.**
* **A guarantee that these captures came off silicon.** They are committed artifacts. Checking them
  establishes internal consistency with the golden and with the physics — it does not establish
  provenance, and this package does not claim it does.

## If your output differs

**That divergence is a finding — file it at
<https://github.com/agent-maestro/machlib/issues>.** Include the file, the command, the expected
value from `MANIFEST.sha256`, what you got, and your OS and architecture.
