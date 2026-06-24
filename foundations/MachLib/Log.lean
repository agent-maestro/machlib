import MachLib.Exp

/-
MachLib.Log — the real natural logarithm.

`log` is the inverse of `exp` on the positive reals. We define it
classically via the surjectivity axiom of `exp` (every positive
real has a unique preimage under `exp`). Outside its natural
domain — at zero and on the negative reals — `log` returns `0`,
matching the convention used throughout MachLib's symbolic
manipulation primitives.

The convention `log x = 0 for x ≤ 0` is a CHOICE, not a theorem.
Downstream code must guard arguments with `0 < x` to get
mathematically meaningful results. The same convention is used in
GNU libc (`log(0) → -∞` is the IEEE behaviour, but we deliberately
use `0` here so that algebraic rewrites do not silently
introduce `-∞`).
-/

namespace MachLib
namespace Real

/-- `log x` is the real natural logarithm of `x` for `x > 0`, and
`0` otherwise. -/
noncomputable def log (x : Real) : Real :=
  if h : 0 < x then
    Classical.choose (exp_surj x h)
  else
    0

/-! ### Specification lemmas: what `log` returns on positive inputs -/

theorem exp_log {x : Real} (hx : 0 < x) : exp (log x) = x := by
  unfold log
  simp [hx]
  exact Classical.choose_spec (exp_surj x hx)

theorem log_exp (x : Real) : log (exp x) = x := by
  have hpos : 0 < exp x := exp_pos x
  have key : exp (log (exp x)) = exp x := exp_log hpos
  exact exp_injective key

/-- `log x = 0` for `x ≤ 0`. Direct from MachLib's clamped-log
convention (the definition's else-branch). Used by downstream EML
expressiveness arguments where the clamped log triggers
asymptotically. -/
theorem log_nonpos {x : Real} (hx : x ≤ 0) : log x = 0 := by
  unfold log
  have hnot : ¬ (0 < x) := by
    intro h
    -- 0 < x ≤ 0: case-split on ≤ via le_iff_lt_or_eq.
    rcases (le_iff_lt_or_eq x 0).mp hx with hxlt | hxeq
    · -- x < 0 and 0 < x: chain to 0 < 0 via lt_trans_ax.
      exact lt_irrefl_ax 0 (lt_trans_ax h hxlt)
    · -- x = 0 and 0 < x: substitute to get 0 < 0.
      rw [hxeq] at h
      exact lt_irrefl_ax 0 h
  simp [hnot]

theorem log_one : log 1 = 0 := by
  have : log (exp 0) = 0 := log_exp 0
  rw [exp_zero] at this
  exact this

theorem log_pos_def {x : Real} (hx : 0 < x) :
    exp (log x) = x ∧ log x = Classical.choose (exp_surj x hx) := by
  refine ⟨exp_log hx, ?_⟩
  unfold log
  simp [hx]

/-! ### log_mul -/

theorem log_mul {x y : Real} (hx : 0 < x) (hy : 0 < y) :
    log (x * y) = log x + log y := by
  have step : exp (log x + log y) = x * y := by
    rw [exp_add, exp_log hx, exp_log hy]
  -- Apply exp_injective: log(x*y) and log x + log y both map to x*y.
  have hxy : 0 < x * y := mul_pos hx hy
  have hxy_log : exp (log (x * y)) = x * y := exp_log hxy
  have eq : exp (log (x * y)) = exp (log x + log y) := by
    rw [hxy_log, ← step]
  exact exp_injective eq

/-! ### Monotonicity -/

theorem log_lt_log {x y : Real} (hx : 0 < x) (hxy : x < y) :
    log x < log y := by
  have hy : 0 < y := lt_trans_ax hx hxy
  -- log is the inverse of exp on positives; exp is strictly monotone;
  -- hence log is strictly monotone on positives.
  cases lt_total (log x) (log y) with
  | inl hlt => exact hlt
  | inr h =>
    cases h with
    | inl heq =>
      -- log x = log y ⇒ exp(log x) = exp(log y) ⇒ x = y, contra hxy
      have : exp (log x) = exp (log y) := by rw [heq]
      rw [exp_log hx, exp_log hy] at this
      exact (ne_of_lt hxy this).elim
    | inr hgt =>
      -- log y < log x ⇒ exp(log y) < exp(log x) ⇒ y < x, contra hxy
      have step : exp (log y) < exp (log x) := exp_lt hgt
      rw [exp_log hy, exp_log hx] at step
      exact (lt_irrefl_ax x (lt_trans_ax hxy step)).elim

/-- `log x < 0` for `0 < x < 1`. The strict-monotonicity corollary at the
unit boundary: since `log 1 = 0` and `log` is increasing, sub-unit arguments
have negative log. Closes the `reverb_t60_positive` denominator sign
(`-log feedback > 0` from `0 < feedback < 1`) and any decay-time kernel whose
time-constant divides by `-log(feedback)`. PROVED from `log_lt_log` + `log_one`,
no new axioms. -/
theorem log_neg_of_lt_one {x : Real} (hx : 0 < x) (hx1 : x < 1) : log x < 0 := by
  have h := log_lt_log hx hx1
  rwa [log_one] at h

/-- On the positive reals minus the singleton {1}, `log` is non-zero.
This guards EDL self-map definitions where dividing by `log x` must
be meaningful. -/
theorem log_ne_zero_of_pos_of_ne_one {x : Real}
    (hx : 0 < x) (hx1 : x ≠ 1) : log x ≠ 0 := by
  intro h
  -- log x = 0 ⇒ exp(log x) = exp 0 ⇒ x = 1, contradicting hx1.
  have hpair : exp (log x) = exp 0 := by rw [h]
  rw [exp_log hx, exp_zero] at hpair
  exact hx1 hpair

/-! ### Common-log / common-anti-log axioms

`log10 x = log x / log 10` and `exp10 x = exp (x * log 10)` on
positive inputs. We axiomatise rather than define here because
the downstream Forge kernels (pH chemistry, Tafel electro-
chemistry, distillation) only need the *symbol* and the linking
identity, not the analytic construction. -/

axiom log10 : Real → Real
axiom exp10 : Real → Real

axiom log10_zero : log10 1 = 0
axiom exp10_zero : exp10 0 = 1
axiom log10_def  (x : Real) :
    0 < x → exp (log10 x * log (natCast 10)) = x
axiom exp10_def  (x : Real) : exp10 x = exp (x * log (natCast 10))
axiom exp10_log10_inverse (x : Real) : 0 < x → exp10 (log10 x) = x

end Real
end MachLib
