import MachLib.KalmanUpdateFixedPoint

/-!
# The representability precondition the fixed-point certificates leave implicit

**Occasioned by a hardware measurement, not by a proof gap that anyone had noticed.**
`monogate-research/exploration/joint_texture_2026_08_05/` swept `operand × state` for the Q8.8
Kalman kernel — 1,073,676,289 + 2,147,418,112 points, real RTL and an independent integer model
bit-identical on every one — and found **110,935,140 + 7,225,349** points where the certificate's
bound is violated *with every status bit silent*. The mechanism is that two `WIDTH`-bit quantities
wrap: `S = P⁻ + R` and `innov = z − x`.

## What the corpus says about those two operations

`FixedPoint.lean` states the condition, **parenthetically and scoped to one kernel**:

> *"**Add / sub** lower to plain integer `±` — **exact**, no rounding (and no overflow in the
> PID's regime: `|inputs| ≤ 100`, `|raw| ≤ 195 ≪ 2¹⁵`)."*

`KalmanUpdateFixedPoint.lean` inherits the claim and **drops the caveat** — *"`s_den = p + r`
— exact"*, *"`d = z − x` — exact"* — while its `p, r, z, x` are **unbounded free variables**.

> **The theorems are not wrong.** They quantify over `Real`, which does not wrap, and they are
> sound there. **What was missing is the hypothesis that licenses instantiating them at the die.**

## Why this file is not just "add a hypothesis"

**Bolting `abs (p+r) ≤ M` onto a theorem over `Real` would be VACUOUS** — nothing in a real-valued
proof can consume it, so the theorem would be strictly weaker for nothing while *looking* like the
gap had closed. **That is a worse outcome than leaving it open.**

So the content here is a **bridge**: `WrapAdd`, an abstract model of an add that *can* wrap, and
theorems relating it to the real sum. Every hypothesis added below is consumed by a proof about
the wrapping model.

**The result that matters is `wrap_error_catastrophic`: out of range, the discrepancy is at least
a full span.** Overflow is therefore **not** a small additive error that a wider `Erec` could
absorb — which is exactly why `mon_fire_range` is a separate status bit and not a looser bound.

No new axioms. No `sorry`.
-/

namespace MachLib
namespace Real

/-- `Fits M v` — the real quantity `v` lies within the format's representable magnitude `M`.

**Parametric in `M` on purpose.** `MachLib.Real` has no `OfNat` instance, so a literal cannot
leak into a statement even by accident; the corpus's no-numerals architecture is inherited here
rather than fought. `M` is the format's max magnitude (`(2^(WIDTH-1) − 1)·s` at the instantiation
site), and every theorem below is proved for all `M`. -/
def Fits (M v : Real) : Prop := abs v ≤ M

/-- **The wrapping add.** `WrapAdd Span M a b w` says `w` is what a `WIDTH`-bit register holds
after adding `a` and `b`, where `Span` is the register's modulus:

* **in range** — `w` is exactly the real sum, and
* **out of range** — `w` differs from the real sum by a *nonzero whole number of spans*.

The out-of-range branch is what makes this a model of hardware rather than of `Real`. It is stated
with `1 ≤ abs n` rather than `n ≠ 0` because that is the fact the hardware supplies (a wrap moves
the value by at least one full modulus) and it is what `wrap_error_catastrophic` consumes. -/
def WrapAdd (Span M a b w : Real) : Prop :=
  (Fits M (a + b) ∧ w = a + b) ∨
  (¬ Fits M (a + b) ∧ ∃ n : Real, 1 ≤ abs n ∧ w = a + b - n * Span)

/-- **R2 — in range, the machine add IS the real add.** This is the theorem that licenses
`KalmanUpdateFixedPoint`'s *"the two adds are exact"*, and it is the precondition that sentence
was missing. -/
theorem wrap_exact_of_fits {Span M a b w : Real}
    (hw : WrapAdd Span M a b w) (hfit : Fits M (a + b)) : w = a + b := by
  rcases hw with ⟨_, he⟩ | ⟨hnf, _⟩
  · exact he
  · exact absurd hfit hnf

/-- **R3 — out of range, the error is at least a FULL SPAN.**

This is the load-bearing result. An overflow is **not** a small perturbation that a larger `Erec`
could absorb: the machine's value is displaced by at least the whole register modulus. It is the
formal counterpart of the measured one-LSB cliff, where `S = 32767 → 32768` flips `x_out` from
`+216` to `−434` against an exact `+433.9`. -/
theorem wrap_error_catastrophic {Span M a b w : Real}
    (hw : WrapAdd Span M a b w) (hnf : ¬ Fits M (a + b)) (hs : 0 ≤ Span) :
    Span ≤ abs (w - (a + b)) := by
  rcases hw with ⟨hfit, _⟩ | ⟨_, n, hn, he⟩
  · exact absurd hfit hnf
  · have e : w - (a + b) = -(n * Span) := by rw [he]; mach_mpoly [a, b, n, Span]
    rw [e, abs_neg, abs_mul, abs_of_nonneg hs]
    have h1 : (1 : Real) * Span ≤ abs n * Span := mul_le_mul_of_nonneg_right hn hs
    have e1 : (1 : Real) * Span = Span := by mach_mpoly [Span]
    rw [e1] at h1
    exact h1

/-- **The two adds of the Kalman datapath, discharged.** Given that both `p + r` and `z − x` fit,
the machine's `s_den` and `d` are the real ones — so the reciprocal really does see the exact
`p + r`, which is what `kalman_update_1d_fwd_error`'s hypotheses assume. -/
theorem kalman_adds_exact_of_fits {Span M p r z x s_den d : Real}
    (hS : WrapAdd Span M p r s_den) (hd : WrapAdd Span M z (-x) d)
    (hfS : Fits M (p + r)) (hfd : Fits M (z - x)) :
    s_den = p + r ∧ d = z - x := by
  refine ⟨wrap_exact_of_fits hS hfS, ?_⟩
  have hz : z + -x = z - x := by mach_mpoly [z, x]
  have := wrap_exact_of_fits hd (by rw [hz]; exact hfd)
  rw [hz] at this; exact this

/-- **The certificate is UNPROVABLE by this route once `S` wraps** — not merely unproven.

`kalman_update_1d_fwd_error` needs `abs (recip_e − 1/(p+r)) ≤ Erec`. The hardware's reciprocal is
computed on what the register actually holds, `s_den`, and the NR certificate bounds it against
`1/s_den` (hypothesis `hnr`). The two errors must therefore straddle the gap between the two
reciprocals:

    |1/s_den − 1/(p+r)|  ≤  E_nr + Erec        i.e.   Erec ≥ |1/s_den − 1/(p+r)| − E_nr

**When `s_den ≠ p + r` those are different numbers, so a small `Erec` is not merely unproven — it
is REFUTED**, and the refutation is quantitative: the gap is a lower bound on how loose the Kalman
hypothesis has to be. This is what `mon_fire_range` protects, and the reason overflow needs a bit
of its own rather than a looser bound.

Stated in additive form (`≤ Enr + Erec`) rather than with a subtraction on the left: it is the
same content, and it keeps the proof inside the corpus's `abs`/`add` idiom instead of routing a
rearrangement through `sub_def`. -/
theorem recip_gap_le_errors
    {p r s_den recip_e Erec Enr : Real}
    (hnr : abs (recip_e - 1 / s_den) ≤ Enr)
    (hkal : abs (recip_e - 1 / (p + r)) ≤ Erec) :
    abs (1 / s_den - 1 / (p + r)) ≤ Enr + Erec := by
  have hsplit : (1 : Real) / s_den - 1 / (p + r)
      = -(recip_e - 1 / s_den) + (recip_e - 1 / (p + r)) := by
    mach_mpoly [recip_e, 1 / s_den, 1 / (p + r)]
  have htri : abs (1 / s_den - 1 / (p + r))
      ≤ abs (recip_e - 1 / s_den) + abs (recip_e - 1 / (p + r)) := by
    rw [hsplit]
    refine le_trans (abs_add _ _) ?_
    exact le_of_eq (by rw [abs_neg])
  exact le_trans htri (add_le_add_both hnr hkal)

/-- **The restatement.** `kalman_update_1d_fwd_error`, with the two adds' exactness *derived* from
representability rather than assumed in prose. Every hypothesis is consumed: `hS`/`hd` and
`hfS`/`hfd` are used to rewrite the machine values to the real ones before the original bound is
applied.

**This is the version a die can discharge**: `Fits` is checkable at run time — it is precisely what
`mon_fire_range` computes (`chip2/rtl/kalman_update.v`). -/
theorem kalman_update_1d_fwd_error_representable
    {Span M x p z r s_den d recip_e k_hw kd_hw s Erec : Real}
    (hS : WrapAdd Span M p r s_den) (hd : WrapAdd Span M z (-x) d)
    (hfS : Fits M (p + r)) (hfd : Fits M (z - x))
    (hpr : s_den ≠ 0)
    (hrec : abs (recip_e - 1 / s_den) ≤ Erec)
    (hk : abs (k_hw - p * recip_e) ≤ s)
    (hkd : abs (kd_hw - k_hw * d) ≤ s) :
    abs ((x + kd_hw) - (x + p / (p + r) * (z - x)))
      ≤ s + abs (z - x) * (s + abs p * Erec) := by
  obtain ⟨heS, hed⟩ := kalman_adds_exact_of_fits hS hd hfS hfd
  rw [heS] at hpr hrec
  rw [hed] at hkd
  exact kalman_update_1d_fwd_error hpr hrec hk hkd

end Real
end MachLib
