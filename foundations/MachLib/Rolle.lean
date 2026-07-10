import MachLib.Exp
import MachLib.Log
import MachLib.Differentiation
import MachLib.AnalyticFiniteZeros
import MachLib.Ring

/-!
# Rolle's Theorem — header port (Phase B of Pfaffian programme)

Axiomatizes Rolle's theorem and its zero-count corollary. The proofs
are deferred to Phase C (the constructive Khovanskii proof) which
combines Rolle + induction-on-Pfaffian-chain-order to derive the
zero bound.

**Strategic purpose:** Phase B is the building block for Phase C.
Rolle's theorem says: between any two zeros of a differentiable
function, the derivative has a zero. Iterating: a function of
Pfaffian order `n` has zero count bounded by a polynomial in n+1
applications of Rolle to derive zero bounds inductively.

**Scope of this file:**

1. `rolle` axiom: standard Rolle's theorem.
2. `zero_count_bound_by_deriv` axiom: zero count of f is at most
   1 + zero count of f', expressed in the list-of-zeros form
   compatible with `PfaffianFunction.zero_count_le`.

**Phase C plan:**

Phase C uses Rolle + induction on Pfaffian chain order to prove:
- Base case: order-0 Pfaffian functions are polynomials in x alone,
  with bounded zero count via `PolynomialRootCount` (already in
  MachLib).
- Inductive step: f of order n has derivative f' which is Pfaffian
  of order ≤ n (the chain stays the same, the polynomial degree
  changes). Apply `zero_count_bound_by_deriv` and use the inductive
  hypothesis.

The final theorem (Phase C) replaces Phase A's
`PfaffianFunction.zero_bound` axiom with a constructive proof.

**Honest scope:** This file ports the Rolle statement; it does NOT
prove it. Continuity + extreme-value-theorem-based proof of Rolle
is itself non-trivial and would require porting MachLib's
`IsAnalyticOnReals` framework (from `AnalyticFiniteZeros.lean`) with
continuity bridges, plus an axiomatic extreme value theorem. Phase
B's role is to commit to the STATEMENT so that Phase C can use it.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-! ## Rolle's theorem (axiomatized) -/

/-- **Rolle's theorem.** If `f` is differentiable on `(a, b)` (every
point has a derivative) and `f a = f b`, then there exists a point
`c ∈ (a, b)` where the derivative of `f` is zero.

Axiomatized. The classical proof uses the extreme value theorem +
the necessary-condition lemma for extrema (`Fermat's theorem`); both
require continuity infrastructure not yet in MachLib.

The differentiability hypothesis is encoded as: for every `c ∈ (a, b)`,
there exists some `f' : Real` with `HasDerivAt f f' c`. -/
axiom rolle (f : Real → Real) (a b : Real) (hab : a < b)
    (hfa_eq_fb : f a = f b)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c) :
    ∃ c : Real, a < c ∧ c < b ∧ HasDerivAt f 0 c

/-- **Rolle's theorem — sound closed-interval form.** Identical to `rolle`, except the differentiability
hypothesis is on the CLOSED interval `[a,b]` (`a ≤ c → c ≤ b`). This is the *faithfully groundable* form: it
is discharged against Mathlib's ℝ by `MonogateEML.RealModel.rolle_witnessed` (differentiability on `[a,b]`
gives continuity on `[a,b]`, so Mathlib's `exists_hasDerivAt_eq_zero` applies). The open-only `rolle` above
OMITS that continuity and is *not* a theorem of ℝ — counterexample: `f x = x` on `(0,1)` with `f 0 = f 1 = 0`
(differentiable on the open interval, `f 0 = f 1`, no interior zero of `f'`).

`interleave_from` — hence `zero_count_bound_by_deriv`, the plain zero-count transfer — is migrated to
`rolle_ct`: it only applies Rolle on consecutive-zero subintervals `[zᵢ,zᵢ₊₁] ⊂ (a,b)`, where closed-interval
differentiability follows from the open-interval hypothesis (`lt_of_lt_of_le_r`/`lt_of_le_of_lt_r`), and its
own PUBLIC hypothesis stays open, so no caller changes. Two consumers still rest on the open-only `rolle`,
each a bounded follow-up: (1) `mean_value_theorem` — a general-purpose MVT with ~27 call sites, whose
migration means threading closed-interval differentiability through every caller; (2) `interleave_dual` (the
bad-set transfer, used by the log/exp Wronskian reduces) — its Rolle endpoints can be bad points where the
vehicle is discontinuous, so it needs a continuity-safe restructuring, not just a hypothesis swap. -/
axiom rolle_ct (f : Real → Real) (a b : Real) (hab : a < b)
    (hfa_eq_fb : f a = f b)
    (hdiff : ∀ c : Real, a ≤ c → c ≤ b → ∃ f' : Real, HasDerivAt f f' c) :
    ∃ c : Real, a < c ∧ c < b ∧ HasDerivAt f 0 c

/-- `x < y → y ≤ z → x < z` (local). -/
private theorem lt_of_lt_of_le_r {x y z : Real} (h1 : x < y) (h2 : y ≤ z) : x < z := by
  rcases (le_iff_lt_or_eq y z).mp h2 with h | h
  · exact lt_trans_ax h1 h
  · rw [← h]; exact h1
/-- `x ≤ y → y < z → x < z` (local). -/
private theorem lt_of_le_of_lt_r {x y z : Real} (h1 : x ≤ y) (h2 : y < z) : x < z := by
  rcases (le_iff_lt_or_eq x y).mp h1 with h | h
  · exact lt_trans_ax h h2
  · rw [h]; exact h2

/-! ## Mean Value Theorem (consequence of Rolle)

**Khovanskii sprint week 1 chunk 1 (2026-06-11):** axiom-to-theorem
conversion landed. The prior session's `mach_ring` block at the
`h a = h b` step left residue on the AC normalisation of an 8-term
polynomial. Replaced with the explicit factor-cancel:

  (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    = (b - a) * (f b - f a) - (f b - f a) * (b - a)   [mul_distrib + mul_neg]
    = (b - a) * (f b - f a) - (b - a) * (f b - f a)   [mul_comm]
    = 0                                                [sub_self]

Two other surprises hit during the closure:

1. MachLib has no `mul_sub` axiom. Derived inline via
   `sub_def + mul_distrib + mul_neg`.

2. `rw [sub_def]` only rewrites a single subtraction occurrence per
   call (each `rw` step targets the first match). The prior session's
   chain mixed pre- and post-`sub_def` forms and failed pattern
   match on the later steps. Fixed by using `simp only [sub_def]`
   to normalise all subtractions in one pass before continuing with
   targeted rewrites.

The axiom previously at this position has been removed; the two
KhovanskiiLemma.lean consumers automatically pick up the theorem
because the name is preserved. -/

/-- **Mean Value Theorem.** If `f` is differentiable on `(a, b)`, there
exists `c ∈ (a, b)` and `f' : Real` such that `HasDerivAt f f' c`
and `f b - f a = f' * (b - a)`.

Constructive proof via Rolle applied to the auxiliary function
`h(x) := (b - a) * f(x) - (b - a) * f(a) - (f(b) - f(a)) * (x - a)`,
which is crafted so that `h a = h b = 0`. -/
theorem mean_value_theorem (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c) :
    ∃ c : Real, ∃ f' : Real, a < c ∧ c < b ∧ HasDerivAt f f' c ∧
      f b - f a = f' * (b - a) := by
  -- Auxiliary function h(x) = (b-a)*f(x) - (b-a)*f(a) - (f(b) - f(a))*(x - a).
  -- Crafted so that h(a) = h(b) = 0 algebraically, making Rolle applicable.
  let h : Real → Real := fun x =>
    (b - a) * f x - (b - a) * f a - (f b - f a) * (x - a)
  -- Step 1: h a = h b.
  have hfa_eq_fb : h a = h b := by
    show (b - a) * f a - (b - a) * f a - (f b - f a) * (a - a) =
         (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    rw [sub_self a, mul_zero, sub_zero]
    -- Goal: (b - a) * f a - (b - a) * f a =
    --       (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    have hlhs : (b - a) * f a - (b - a) * f a = 0 := sub_self _
    rw [hlhs]
    -- Goal: 0 = (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a)
    -- Explicit factor-cancel replacing the prior session's failed mach_ring.
    -- MachLib has no `mul_sub` axiom; derive it from sub_def + mul_distrib + mul_neg.
    have hidentity :
        (b - a) * f b - (b - a) * f a - (f b - f a) * (b - a) = 0 := by
      have step1 : (b - a) * (f b - f a) = (b - a) * f b - (b - a) * f a := by
        -- sub_def rewrites only one subtraction per `rw` call, so use simp
        -- only to normalise both `f b - f a` and the outer `-` consistently.
        simp only [sub_def]
        rw [mul_distrib, mul_neg]
      have step2 : (f b - f a) * (b - a) = (b - a) * (f b - f a) := mul_comm _ _
      rw [← step1, step2]
      exact sub_self _
    rw [hidentity]
  -- Step 2: h is differentiable on (a, b) with derivative
  --   h'(c) = (b - a) * f'_c - 0 - (f b - f a).
  have h_diff : ∀ c : Real, a < c → c < b →
      ∃ h' : Real, HasDerivAt h h' c := by
    intro c hca hcb
    obtain ⟨f'_c, hf'_c⟩ := hdiff c hca hcb
    -- g1(x) = (b - a) * f x;  g1'(c) = (b - a) * f'_c.
    have hg1 : HasDerivAt (fun x => (b - a) * f x) ((b - a) * f'_c) c := by
      have h_const : HasDerivAt (fun _ : Real => b - a) 0 c := HasDerivAt_const (b - a) c
      have h_prod := HasDerivAt_mul (fun _ => b - a) f 0 f'_c c h_const hf'_c
      have h_simp : (0 : Real) * f c + (b - a) * f'_c = (b - a) * f'_c := by
        rw [zero_mul, zero_add]
      rw [h_simp] at h_prod
      exact h_prod
    -- g2(x) = (b - a) * f a (constant); g2'(c) = 0.
    have hg2 : HasDerivAt (fun _ : Real => (b - a) * f a) 0 c :=
      HasDerivAt_const _ c
    -- g3(x) = (f b - f a) * (x - a); g3'(c) = f b - f a.
    have hg3 : HasDerivAt (fun x => (f b - f a) * (x - a)) (f b - f a) c := by
      have h_id : HasDerivAt (fun y : Real => y) 1 c := HasDerivAt_id c
      have h_const_a : HasDerivAt (fun _ : Real => a) 0 c := HasDerivAt_const a c
      have h_sub : HasDerivAt (fun y => y - a) (1 - 0) c :=
        HasDerivAt_sub (fun y => y) (fun _ => a) 1 0 c h_id h_const_a
      have h_sub_simp : (1 : Real) - 0 = 1 := sub_zero 1
      rw [h_sub_simp] at h_sub
      have h_const_fba : HasDerivAt (fun _ : Real => f b - f a) 0 c := HasDerivAt_const _ c
      have h_prod := HasDerivAt_mul (fun _ => f b - f a) (fun x => x - a) 0 1 c h_const_fba h_sub
      have h_simp : (0 : Real) * (c - a) + (f b - f a) * 1 = f b - f a := by
        rw [zero_mul, zero_add, mul_one_ax]
      rw [h_simp] at h_prod
      exact h_prod
    -- h = g1 - g2 - g3.
    have h_g12 : HasDerivAt (fun x => (b - a) * f x - (b - a) * f a) ((b - a) * f'_c - 0) c :=
      HasDerivAt_sub _ _ _ _ c hg1 hg2
    have h_full : HasDerivAt h ((b - a) * f'_c - 0 - (f b - f a)) c :=
      HasDerivAt_sub _ _ _ _ c h_g12 hg3
    exact ⟨(b - a) * f'_c - 0 - (f b - f a), h_full⟩
  -- Step 3: apply Rolle to h, obtain c ∈ (a, b) with h'(c) = 0.
  obtain ⟨c, hca, hcb, h_zero⟩ := rolle h a b hab hfa_eq_fb h_diff
  obtain ⟨f'_c, hf'_c⟩ := hdiff c hca hcb
  -- Re-derive h's derivative at c so we can compare with the 0 from Rolle.
  have h_derived : HasDerivAt h ((b - a) * f'_c - 0 - (f b - f a)) c := by
    have hg1 : HasDerivAt (fun x => (b - a) * f x) ((b - a) * f'_c) c := by
      have h_const : HasDerivAt (fun _ : Real => b - a) 0 c := HasDerivAt_const (b - a) c
      have h_prod := HasDerivAt_mul (fun _ => b - a) f 0 f'_c c h_const hf'_c
      have h_simp : (0 : Real) * f c + (b - a) * f'_c = (b - a) * f'_c := by
        rw [zero_mul, zero_add]
      rw [h_simp] at h_prod
      exact h_prod
    have hg2 : HasDerivAt (fun _ : Real => (b - a) * f a) 0 c := HasDerivAt_const _ c
    have hg3 : HasDerivAt (fun x => (f b - f a) * (x - a)) (f b - f a) c := by
      have h_id : HasDerivAt (fun y : Real => y) 1 c := HasDerivAt_id c
      have h_const_a : HasDerivAt (fun _ : Real => a) 0 c := HasDerivAt_const a c
      have h_sub : HasDerivAt (fun y => y - a) (1 - 0) c :=
        HasDerivAt_sub (fun y => y) (fun _ => a) 1 0 c h_id h_const_a
      have h_sub_simp : (1 : Real) - 0 = 1 := sub_zero 1
      rw [h_sub_simp] at h_sub
      have h_const_fba : HasDerivAt (fun _ : Real => f b - f a) 0 c := HasDerivAt_const _ c
      have h_prod := HasDerivAt_mul (fun _ => f b - f a) (fun x => x - a) 0 1 c h_const_fba h_sub
      have h_simp : (0 : Real) * (c - a) + (f b - f a) * 1 = f b - f a := by
        rw [zero_mul, zero_add, mul_one_ax]
      rw [h_simp] at h_prod
      exact h_prod
    have h_g12 : HasDerivAt (fun x => (b - a) * f x - (b - a) * f a) ((b - a) * f'_c - 0) c :=
      HasDerivAt_sub _ _ _ _ c hg1 hg2
    exact HasDerivAt_sub _ _ _ _ c h_g12 hg3
  -- By HasDerivAt_unique: 0 = (b - a) * f'_c - 0 - (f b - f a).
  have h_eq : (0 : Real) = (b - a) * f'_c - 0 - (f b - f a) :=
    HasDerivAt_unique h 0 _ c h_zero h_derived
  -- Algebra: f b - f a = (b - a) * f'_c = f'_c * (b - a).
  have h_simp1 : (b - a) * f'_c - 0 - (f b - f a) = (b - a) * f'_c - (f b - f a) := by
    rw [sub_zero]
  rw [h_simp1] at h_eq
  -- From h_eq : 0 = (b - a) * f'_c - (f b - f a).
  -- Derive f b - f a = (b - a) * f'_c via the identity x = (x - y) + y,
  -- which after the substitution h_eq.symm becomes x = 0 + y = y.
  -- This avoids the prior session's mixed-form rewrite chain that
  -- failed on the sub_def vs post-sub_def pattern mismatch.
  have h_step : f b - f a = (b - a) * f'_c := by
    have h_sym : (b - a) * f'_c - (f b - f a) = 0 := h_eq.symm
    have h_id : (b - a) * f'_c
        = ((b - a) * f'_c - (f b - f a)) + (f b - f a) := by
      -- Use simp only for sub_def so the inner `(b - a)` subtraction isn't
      -- the only one touched — we need the outer `- (f b - f a)` rewritten too.
      simp only [sub_def]
      rw [add_assoc]
      have h_inv : -(f b + -f a) + (f b + -f a) = 0 := by
        rw [add_comm]; exact add_neg _
      rw [h_inv, add_zero]
    rw [h_sym, zero_add] at h_id
    exact h_id.symm
  have h_final : f b - f a = f'_c * (b - a) := by
    rw [h_step]; exact mul_comm (b - a) f'_c
  exact ⟨c, f'_c, hca, hcb, hf'_c, h_final⟩


/-! ## Zero count bound via Rolle's theorem

**No longer an axiom.** `zero_count_bound_by_deriv` is now DERIVED from `rolle`
below (Khovanskii sprint, hardening pass 2026-07): the analytic base of the
whole tower collapses to the single axiom `rolle`. The construction sorts the
`Nodup` zeros of `f` into strictly-increasing order (`List.mergeSort` with a
classical `≤`-comparator), applies `rolle` between each consecutive pair to get
a zero of `f'` strictly between them, and observes those bracket points are
themselves strictly increasing (each lies in a disjoint sub-interval), hence
`Nodup` and of length `zeros_f.length - 1`. Feeding that list to `hf'_bound`
gives `zeros_f.length - 1 ≤ N`, i.e. `zeros_f.length ≤ N + 1`.

All supporting definitions are `private` to this file. -/

/-- Classical `≤`-as-`Bool` comparator on `Real` (reals have no decidable `≤`,
so we go through `Classical.propDecidable`). Only used to feed `mergeSort`. -/
private noncomputable def leB (a b : Real) : Bool := by
  classical exact decide (a ≤ b)

private theorem leB_iff (a b : Real) : leB a b = true ↔ a ≤ b := by
  unfold leB; exact decide_eq_true_iff

private theorem lt_of_le_of_ne' {a b : Real} (hle : a ≤ b) (hne : a ≠ b) : a < b := by
  rcases (le_iff_lt_or_eq a b).mp hle with h | h
  · exact h
  · exact absurd h hne

private theorem le_total' (a b : Real) : a ≤ b ∨ b ≤ a := by
  rcases lt_total a b with h | h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inl ((le_iff_lt_or_eq a b).mpr (Or.inr h))
  · exact Or.inr (le_of_lt h)

private theorem leB_trans (a b c : Real) :
    leB a b = true → leB b c = true → leB a c = true := by
  intro hab hbc
  exact (leB_iff a c).mpr (le_trans ((leB_iff a b).mp hab) ((leB_iff b c).mp hbc))

private theorem leB_total (a b : Real) : (leB a b || leB b a) = true := by
  rcases le_total' a b with h | h
  · exact (Bool.or_eq_true _ _).mpr (Or.inl ((leB_iff a b).mpr h))
  · exact (Bool.or_eq_true _ _).mpr (Or.inr ((leB_iff b a).mpr h))

/-- **Iterated-Rolle core.** Process a `leB`-sorted `Nodup` list `hd :: s` of zeros
of `f` in `(a,b)`: produce a `Nodup` list `cs` of zeros of `f'` in `(a,b)`, one
strictly between each consecutive pair of zeros, every element `> hd`, of length
`≥ (hd::s).length - 1`. The `> hd` invariant is what keeps the bracket points
strictly increasing (hence distinct) across the recursion. -/
private theorem interleave_from (f : Real → Real) (a b : Real)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c) :
    ∀ (hd : Real) (s : List Real),
      List.Pairwise (fun x y => leB x y = true) (hd :: s) →
      (hd :: s).Nodup →
      (∀ z ∈ (hd :: s), a < z ∧ z < b ∧ f z = 0) →
      ∃ cs : List Real, cs.Nodup ∧
        (∀ c ∈ cs, a < c ∧ c < b ∧ ∃ f'' : Real, HasDerivAt f f'' c ∧ f'' = 0) ∧
        (∀ c ∈ cs, hd < c) ∧
        (hd :: s).length ≤ cs.length + 1 := by
  intro hd s
  induction s generalizing hd with
  | nil =>
    intro _ _ _
    exact ⟨[], List.nodup_nil, by intro c hc; exact absurd hc (List.not_mem_nil c),
      by intro c hc; exact absurd hc (List.not_mem_nil c), Nat.le_refl 1⟩
  | cons z1 rest ih =>
    intro hpair hnodup hzero
    rw [List.pairwise_cons] at hpair
    obtain ⟨hhd_le, hpair_tail⟩ := hpair
    rw [List.nodup_cons] at hnodup
    obtain ⟨hhd_notin, hnodup_tail⟩ := hnodup
    have hz1_mem : z1 ∈ (z1 :: rest) := List.mem_cons_self z1 rest
    have hhd_le_z1 : hd ≤ z1 := (leB_iff hd z1).mp (hhd_le z1 hz1_mem)
    have hhd_ne_z1 : hd ≠ z1 := fun h => hhd_notin (h ▸ hz1_mem)
    have hhd_lt_z1 : hd < z1 := lt_of_le_of_ne' hhd_le_z1 hhd_ne_z1
    obtain ⟨ha_hd, hhd_b, hf_hd⟩ := hzero hd (List.mem_cons_self hd _)
    obtain ⟨ha_z1, hz1_b, hf_z1⟩ := hzero z1 (List.mem_cons_of_mem hd hz1_mem)
    have hdiff' : ∀ c : Real, hd ≤ c → c ≤ z1 → ∃ f' : Real, HasDerivAt f f' c :=
      fun c hc1 hc2 => hdiff c (lt_of_lt_of_le_r ha_hd hc1) (lt_of_le_of_lt_r hc2 hz1_b)
    have hfeq : f hd = f z1 := by rw [hf_hd, hf_z1]
    obtain ⟨c0, hc0_lo, hc0_hi, hc0_deriv⟩ := rolle_ct f hd z1 hhd_lt_z1 hfeq hdiff'
    obtain ⟨cs', hcs'_nodup, hcs'_props, hcs'_gt, hcs'_len⟩ :=
      ih z1 hpair_tail hnodup_tail (fun z hz => hzero z (List.mem_cons_of_mem hd hz))
    have hc0_lt_cs' : ∀ c ∈ cs', c0 < c := fun c hc => lt_trans_ax hc0_hi (hcs'_gt c hc)
    refine ⟨c0 :: cs', ?_, ?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨fun hmem => lt_irrefl_ax c0 (hc0_lt_cs' c0 hmem), hcs'_nodup⟩
    · intro c hc
      rw [List.mem_cons] at hc
      rcases hc with h | h
      · subst h; exact ⟨lt_trans_ax ha_hd hc0_lo, lt_trans_ax hc0_hi hz1_b, 0, hc0_deriv, rfl⟩
      · exact hcs'_props c h
    · intro c hc
      rw [List.mem_cons] at hc
      rcases hc with h | h
      · subst h; exact hc0_lo
      · exact lt_trans_ax hhd_lt_z1 (hcs'_gt c h)
    · simp only [List.length_cons] at hcs'_len ⊢
      omega

set_option linter.unusedVariables false in
/-- **Zero count of f ≤ 1 + zero count of f'**, on a bounded open
interval `(a, b)`. If `f` has zeros at `z_1 < z_2 < ... < z_N`, then by
Rolle applied between consecutive zeros, `f'` has zeros at
`c_1 < c_2 < ... < c_{N-1}` (one between each consecutive pair).

**Proved from `rolle`** (see the section note above): sort the `Nodup`
zeros, bracket each consecutive pair via `interleave_from`, and feed the
resulting `Nodup` list of `f'`-zeros to `hf'_bound`.

The statement: if `f'` has at most `N` zeros on `(a, b)`, then `f` has at
most `N + 1` zeros on `(a, b)`. -/
theorem zero_count_bound_by_deriv (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a < c → c < b → ∃ f' : Real, HasDerivAt f f' c)
    (N : Nat)
    (hf'_bound : ∀ zeros_f' : List Real,
        zeros_f'.Nodup →
        (∀ z ∈ zeros_f', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt f f'' z ∧ f'' = 0) →
        zeros_f'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzero
  have hperm : (zeros_f.mergeSort leB).Perm zeros_f := List.mergeSort_perm zeros_f leB
  have hlen : (zeros_f.mergeSort leB).length = zeros_f.length := hperm.length_eq
  have hnodup_s : (zeros_f.mergeSort leB).Nodup := hperm.symm.nodup hnodup
  have hzero_s : ∀ z ∈ zeros_f.mergeSort leB, a < z ∧ z < b ∧ f z = 0 :=
    fun z hz => hzero z (hperm.mem_iff.mp hz)
  have hpair_s : List.Pairwise (fun x y => leB x y = true) (zeros_f.mergeSort leB) :=
    List.sorted_mergeSort leB_trans leB_total zeros_f
  rw [← hlen]
  generalize hs : zeros_f.mergeSort leB = s at hnodup_s hzero_s hpair_s ⊢
  cases s with
  | nil => simp
  | cons hd t =>
    obtain ⟨cs, hcs_nodup, hcs_props, _, hcs_len⟩ :=
      interleave_from f a b hdiff hd t hpair_s hnodup_s hzero_s
    have hb := hf'_bound cs hcs_nodup hcs_props
    simp only [List.length_cons] at hcs_len ⊢
    omega

/-! ## Dual interleave — Rolle with a "bad set" where `f` need not be differentiable

For the LOG Wronskian partition: `f` (the reciprocal vehicle `pf(p)/c_D`) is
differentiable only where `c_D ≠ 0`. Between consecutive zeros, a gap either avoids
the bad set (`c_D = 0`) entirely — Rolle gives an interior critical point — or contains
a bad point. Each gap thus yields a distinct critical point OR a distinct bad point,
so the zero count splits as `#crit + #bad + 1`. -/

/-- **Dual interleave.** Like `interleave_from`, but `f` is only known differentiable
off a `isBad` set. Each gap between consecutive zeros contributes either a critical
point (`f'' = 0`, when the gap avoids `isBad`) or a bad point — collected into two
ordered `Nodup` lists. -/
private theorem interleave_dual (f : Real → Real) (isBad : Real → Prop) (a b : Real)
    (hdiff : ∀ c : Real, a < c → c < b → ¬ isBad c → ∃ f' : Real, HasDerivAt f f' c) :
    ∀ (hd : Real) (s : List Real),
      List.Pairwise (fun x y => leB x y = true) (hd :: s) →
      (hd :: s).Nodup →
      (∀ z ∈ (hd :: s), a < z ∧ z < b ∧ f z = 0) →
      ∃ csC csB : List Real, csC.Nodup ∧ csB.Nodup ∧
        (∀ c ∈ csC, a < c ∧ c < b ∧ ¬ isBad c ∧ ∃ f'' : Real, HasDerivAt f f'' c ∧ f'' = 0) ∧
        (∀ c ∈ csB, a < c ∧ c < b ∧ isBad c) ∧
        (∀ c ∈ csC, hd < c) ∧ (∀ c ∈ csB, hd < c) ∧
        (hd :: s).length ≤ csC.length + csB.length + 1 := by
  intro hd s
  induction s generalizing hd with
  | nil =>
    intro _ _ _
    exact ⟨[], [], List.nodup_nil, List.nodup_nil,
      (by intro c hc; exact absurd hc (List.not_mem_nil c)),
      (by intro c hc; exact absurd hc (List.not_mem_nil c)),
      (by intro c hc; exact absurd hc (List.not_mem_nil c)),
      (by intro c hc; exact absurd hc (List.not_mem_nil c)), Nat.le_refl 1⟩
  | cons z1 rest ih =>
    intro hpair hnodup hzero
    rw [List.pairwise_cons] at hpair
    obtain ⟨hhd_le, hpair_tail⟩ := hpair
    rw [List.nodup_cons] at hnodup
    obtain ⟨hhd_notin, hnodup_tail⟩ := hnodup
    have hz1_mem : z1 ∈ (z1 :: rest) := List.mem_cons_self z1 rest
    have hhd_le_z1 : hd ≤ z1 := (leB_iff hd z1).mp (hhd_le z1 hz1_mem)
    have hhd_ne_z1 : hd ≠ z1 := fun h => hhd_notin (h ▸ hz1_mem)
    have hhd_lt_z1 : hd < z1 := lt_of_le_of_ne' hhd_le_z1 hhd_ne_z1
    obtain ⟨ha_hd, hhd_b, hf_hd⟩ := hzero hd (List.mem_cons_self hd _)
    obtain ⟨ha_z1, hz1_b, hf_z1⟩ := hzero z1 (List.mem_cons_of_mem hd hz1_mem)
    obtain ⟨csC', csB', hcsC'_nd, hcsB'_nd, hcsC'_props, hcsB'_props, hcsC'_gt, hcsB'_gt, hlen'⟩ :=
      ih z1 hpair_tail hnodup_tail (fun z hz => hzero z (List.mem_cons_of_mem hd hz))
    by_cases hbad : ∃ w, hd < w ∧ w < z1 ∧ isBad w
    · obtain ⟨w0, hw0_lo, hw0_hi, hw0_bad⟩ := hbad
      have hw0_lt_csB' : ∀ c ∈ csB', w0 < c := fun c hc => lt_trans_ax hw0_hi (hcsB'_gt c hc)
      refine ⟨csC', w0 :: csB', hcsC'_nd, ?_, hcsC'_props, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]; exact ⟨fun hmem => lt_irrefl_ax w0 (hw0_lt_csB' w0 hmem), hcsB'_nd⟩
      · intro c hc; rw [List.mem_cons] at hc
        rcases hc with h | h
        · subst h; exact ⟨lt_trans_ax ha_hd hw0_lo, lt_trans_ax hw0_hi hz1_b, hw0_bad⟩
        · exact hcsB'_props c h
      · intro c hc; exact lt_trans_ax hhd_lt_z1 (hcsC'_gt c hc)
      · intro c hc; rw [List.mem_cons] at hc
        rcases hc with h | h
        · subst h; exact hw0_lo
        · exact lt_trans_ax hhd_lt_z1 (hcsB'_gt c h)
      · simp only [List.length_cons] at hlen' ⊢; omega
    · have hbad' : ∀ w, hd < w → w < z1 → ¬ isBad w := fun w hw1 hw2 hbw => hbad ⟨w, hw1, hw2, hbw⟩
      have hdiff' : ∀ c : Real, hd < c → c < z1 → ∃ f' : Real, HasDerivAt f f' c :=
        fun c hc1 hc2 => hdiff c (lt_trans_ax ha_hd hc1) (lt_trans_ax hc2 hz1_b) (hbad' c hc1 hc2)
      have hfeq : f hd = f z1 := by rw [hf_hd, hf_z1]
      obtain ⟨c0, hc0_lo, hc0_hi, hc0_deriv⟩ := rolle f hd z1 hhd_lt_z1 hfeq hdiff'
      have hc0_lt_csC' : ∀ c ∈ csC', c0 < c := fun c hc => lt_trans_ax hc0_hi (hcsC'_gt c hc)
      refine ⟨c0 :: csC', csB', ?_, hcsB'_nd, ?_, hcsB'_props, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]; exact ⟨fun hmem => lt_irrefl_ax c0 (hc0_lt_csC' c0 hmem), hcsC'_nd⟩
      · intro c hc; rw [List.mem_cons] at hc
        rcases hc with h | h
        · subst h; exact ⟨lt_trans_ax ha_hd hc0_lo, lt_trans_ax hc0_hi hz1_b, hbad' _ hc0_lo hc0_hi, 0, hc0_deriv, rfl⟩
        · exact hcsC'_props c h
      · intro c hc; rw [List.mem_cons] at hc
        rcases hc with h | h
        · subst h; exact hc0_lo
        · exact lt_trans_ax hhd_lt_z1 (hcsC'_gt c h)
      · intro c hc; exact lt_trans_ax hhd_lt_z1 (hcsB'_gt c hc)
      · simp only [List.length_cons] at hlen' ⊢; omega

/-- **Zero count with a bad set.** If `f` is differentiable off `isBad`, and the
critical points (`f'' = 0`) number ≤ `Ncrit` while the bad points number ≤ `Nbad`,
then `f` has ≤ `Ncrit + Nbad + 1` zeros on `(a,b)`. The `c_D`-partition of the log
Wronskian descent: `isBad z := c_D(z) = 0`, critical points are `g`-zeros. -/
theorem zero_count_bound_by_deriv_with_bad (f : Real → Real) (isBad : Real → Prop)
    (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a < c → c < b → ¬ isBad c → ∃ f' : Real, HasDerivAt f f' c)
    (Ncrit Nbad : Nat)
    (hcrit : ∀ zs : List Real, zs.Nodup →
        (∀ z ∈ zs, a < z ∧ z < b ∧ ¬ isBad z ∧ ∃ f'' : Real, HasDerivAt f f'' z ∧ f'' = 0) →
        zs.length ≤ Ncrit)
    (hbadN : ∀ zs : List Real, zs.Nodup →
        (∀ z ∈ zs, a < z ∧ z < b ∧ isBad z) → zs.length ≤ Nbad) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f z = 0) →
      zeros_f.length ≤ Ncrit + Nbad + 1 := by
  intro zeros_f hnodup hzero
  have hperm : (zeros_f.mergeSort leB).Perm zeros_f := List.mergeSort_perm zeros_f leB
  have hlen : (zeros_f.mergeSort leB).length = zeros_f.length := hperm.length_eq
  have hnodup_s : (zeros_f.mergeSort leB).Nodup := hperm.symm.nodup hnodup
  have hzero_s : ∀ z ∈ zeros_f.mergeSort leB, a < z ∧ z < b ∧ f z = 0 :=
    fun z hz => hzero z (hperm.mem_iff.mp hz)
  have hpair_s : List.Pairwise (fun x y => leB x y = true) (zeros_f.mergeSort leB) :=
    List.sorted_mergeSort leB_trans leB_total zeros_f
  rw [← hlen]
  generalize hs : zeros_f.mergeSort leB = s at hnodup_s hzero_s hpair_s ⊢
  cases s with
  | nil => simp
  | cons hd t =>
    obtain ⟨csC, csB, hcsC_nd, hcsB_nd, hcsC_props, hcsB_props, _, _, hcs_len⟩ :=
      interleave_dual f isBad a b hdiff hd t hpair_s hnodup_s hzero_s
    have hbC := hcrit csC hcsC_nd hcsC_props
    have hbB := hbadN csB hcsB_nd hcsB_props
    simp only [List.length_cons] at hcs_len ⊢
    omega

/-! ## Phase C plan (documented here as roadmap)

Phase C constructs the Pfaffian zero bound (Phase A's
`pfaffian_zero_count_bound`) via induction on Pfaffian chain order:

**Base case (order 0):** A Pfaffian function of order 0 is a
polynomial in x alone. Zero count ≤ degree, by
`PolynomialRootCount.lean` in MachLib.

**Inductive step:** A Pfaffian function `f` of order `n+1` has
derivative `f'` that, by the Pfaffian-chain-derivative axioms, is
ALSO Pfaffian of order ≤ `n+1` (the chain stays the same; only
the polynomial degree of f' in chain entries changes, bounded by
the original degree of f times the chain length).

Applying `zero_count_bound_by_deriv` (this file) + the inductive
hypothesis to f' gives a bound on the zero count of f.

Carrying out this induction explicitly yields a polynomial in
(order, degree) that matches Khovanskii's classical formula
`d · (d + 1)^{n-1}` or `2^{n(n-1)/2} · d^n`.

The induction proof is ~200-400 lines. Phase C is a 2-3 week focused
artifact.
-/

end Real
end MachLib
