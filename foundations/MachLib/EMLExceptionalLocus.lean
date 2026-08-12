import MachLib.EMLConstantFree

/-!
# T3, first artifact: an exceptional locus solved for exactly

This arm keeps producing **exceptional sets** by accident — parameter values where a family's
qualitative behaviour changes, sitting on a transcendental locus that generic reasoning walks past.
It has already cost something: a grid search over 12,208 samples reported non-existence and missed a
witness living on exactly such a set.

The repair is to solve for these loci **deliberately**. This module does it for the one the arm
knows best, the depth-4 reciprocal family `invX4gen c₀ c₁`.

`EMLDepth2InvX` supplies the *sufficient* direction (`invX4gen_eval`: the relation implies the tree
computes `1/x`) and *existence* (`invX4gen_witness_for_any_c1`). Neither says the relation is
**necessary**, and without that there is no locus — only a supply of witnesses.

* **`invX4gen_iff`** — the tree computes `1/x` **if and only if** `exp(exp c₀) − exp(exp c₁) = 1`.
  The forward direction needs a **single point**, `x = 1`, where `log 1 = 0` collapses both branches.
* **`invX4gen_locus_unique`** — for each `c₁` at most one `c₀` works, so the locus is a **graph**.
* **`invX4gen_locus_solved`** — and exactly one does, namely `c₀ = log (log (1 + exp (exp c₁)))`.
  The locus is that explicit transcendental curve, nothing more and nothing less.
* **`invX4gen_off_locus`** — every other `(c₀, c₁)` fails. This is the statement that makes the grid
  failure inevitable rather than unlucky: the good set is a graph over one parameter, so sampling
  `c₀` independently misses it unless the sample lands on the curve exactly.

The template generalises: for a parameterised family, prove the behaviour is **equivalent** to an
equation, then solve the equation. "Here is a witness" is not a locus; "here is precisely the set" is.
-/

namespace MachLib

open Real

/-- The family's value at `x = 1`, where `log 1 = 0` collapses every branch. This single point is the
whole forward direction. -/
theorem invX4gen_eval_at_one (c0 c1 : Real) :
    (invX4gen c0 c1).eval 1 = exp (exp c0) - exp (exp c1) := by
  show exp ((EMLTree.eml (EMLTree.const c0) EMLTree.var).eval 1)
      - log ((EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var)
          (EMLTree.const 1)) (EMLTree.const 1)).eval 1) = _
  show exp (exp c0 - log (1 : Real))
      - log (exp ((EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var)
          (EMLTree.const 1)).eval 1) - log ((EMLTree.const (1 : Real)).eval 1)) = _
  show exp (exp c0 - log (1 : Real))
      - log (exp (exp ((EMLTree.eml (EMLTree.const c1) EMLTree.var).eval 1)
          - log ((EMLTree.const (1 : Real)).eval 1)) - log (1 : Real)) = _
  show exp (exp c0 - log (1 : Real))
      - log (exp (exp (exp c1 - log (1 : Real)) - log (1 : Real)) - log (1 : Real)) = _
  rw [log_one]
  have e0 : exp c0 - (0 : Real) = exp c0 := by mach_mpoly [exp c0]
  have e1 : exp c1 - (0 : Real) = exp c1 := by mach_mpoly [exp c1]
  rw [e0, e1]
  have e2 : exp (exp c1) - (0 : Real) = exp (exp c1) := by mach_mpoly [exp (exp c1)]
  rw [e2]
  have e3 : exp (exp (exp c1)) - (0 : Real) = exp (exp (exp c1)) := by
    mach_mpoly [exp (exp (exp c1))]
  rw [e3, log_exp]

/-- **The locus, exactly.** The relation is not merely sufficient — it is equivalent. -/
theorem invX4gen_iff (c0 c1 : Real) :
    (∀ x : Real, 0 < x → (invX4gen c0 c1).eval x = 1 / x)
      ↔ exp (exp c0) - exp (exp c1) = 1 := by
  constructor
  · intro h
    have h1 := h 1 zero_lt_one_ax
    rw [invX4gen_eval_at_one] at h1
    have hone : (1 : Real) / 1 = 1 := by
      have hv := mul_inv (1 : Real) (ne_of_gt zero_lt_one_ax)
      have l : (1 : Real) * (1 / 1) = 1 / 1 := by mach_mpoly [(1 / 1 : Real)]
      rw [l] at hv; exact hv
    rw [hone] at h1; exact h1
  · intro hfam; exact invX4gen_eval hfam

/-- **At most one `c₀` per `c₁`**: the locus is a graph, not a region. -/
theorem invX4gen_locus_unique {c1 c0 c0' : Real}
    (h : exp (exp c0) - exp (exp c1) = 1) (h' : exp (exp c0') - exp (exp c1) = 1) :
    c0 = c0' := by
  have heq : exp (exp c0) = exp (exp c0') := by
    have u : exp (exp c0) - exp (exp c1) + exp (exp c1)
        = exp (exp c0') - exp (exp c1) + exp (exp c1) := by rw [h, h']
    have l : exp (exp c0) - exp (exp c1) + exp (exp c1) = exp (exp c0) := by
      mach_mpoly [exp (exp c0), exp (exp c1)]
    have r : exp (exp c0') - exp (exp c1) + exp (exp c1) = exp (exp c0') := by
      mach_mpoly [exp (exp c0'), exp (exp c1)]
    rw [l, r] at u; exact u
  have h1 : exp c0 = exp c0' := by
    have u : log (exp (exp c0)) = log (exp (exp c0')) := by rw [heq]
    rw [log_exp, log_exp] at u; exact u
  have u : log (exp c0) = log (exp c0') := by rw [h1]
  rw [log_exp, log_exp] at u; exact u

/-- **And exactly one does.** The locus is the explicit transcendental curve
`c₀ = log (log (1 + exp (exp c₁)))`. -/
theorem invX4gen_locus_solved (c1 : Real) :
    exp (exp (log (log (1 + exp (exp c1))))) - exp (exp c1) = 1 := by
  have hK : (0 : Real) < exp (exp c1) := exp_pos _
  have h1K : (1 : Real) < 1 + exp (exp c1) := by
    have u := add_lt_add_left hK 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have hpos : (0 : Real) < 1 + exp (exp c1) := lt_trans_ax zero_lt_one_ax h1K
  have hlogpos : (0 : Real) < log (1 + exp (exp c1)) := by
    have hm := log_lt_log zero_lt_one_ax h1K
    rw [log_one] at hm; exact hm
  rw [exp_log hlogpos, exp_log hpos]
  mach_mpoly [exp (exp c1)]

/-- **Every other parameter pair fails.** The good set is a graph over `c₁`, so an independent sweep
of `c₀` misses it unless a sample lands on the curve exactly — which is why a grid found nothing. -/
theorem invX4gen_off_locus (c0 c1 : Real) (h : exp (exp c0) - exp (exp c1) ≠ 1) :
    ¬ (∀ x : Real, 0 < x → (invX4gen c0 c1).eval x = 1 / x) :=
  fun hc => h ((invX4gen_iff c0 c1).mp hc)

/-- The locus, packaged: for every `c₁` there is a **unique** `c₀`, given explicitly, and it is
exactly the set of parameters for which the depth-4 family computes `1/x`. -/
theorem invX4gen_locus_is_a_graph (c1 : Real) :
    (∀ x : Real, 0 < x →
        (invX4gen (log (log (1 + exp (exp c1)))) c1).eval x = 1 / x)
    ∧ ∀ c0 : Real, (∀ x : Real, 0 < x → (invX4gen c0 c1).eval x = 1 / x)
        → c0 = log (log (1 + exp (exp c1))) :=
  ⟨(invX4gen_iff _ c1).mpr (invX4gen_locus_solved c1),
   fun c0 hc => invX4gen_locus_unique ((invX4gen_iff c0 c1).mp hc) (invX4gen_locus_solved c1)⟩

end MachLib
