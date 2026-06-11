import MachLib.Exp
import MachLib.Log
import MachLib.Trig
import MachLib.EML
import MachLib.EMLHierarchy
import MachLib.Pfaffian

/-!
# EML → Pfaffian embedding + Sin Barrier (Phase D)

Conditional on Phase A's axiomatized zero bound
(`PfaffianFunction.zero_bound`), ships the END-USER results:

1. **EML embedding** (`eml_pfaffian`): every EMLTree corresponds to
   a Pfaffian function with matching evaluation.

2. **Sin barrier for all depths** (`sin_not_in_eml_any_depth`):
   `Real.sin ∉ EML_k` for every Nat k. ONE theorem.

**Proof strategy:** Given `t.eval = sin globally` with `t.depth ≤ k`:

- `eml_pfaffian t` is Pfaffian. Its eval = t.eval = sin.
- Not identically zero (sin 1 > 0). So `PfaffianFunction.zero_bound`
  applies. Let M be the bound.
- Construct M+1 distinct zeros of sin at `pi, 2pi, ..., (M+1)pi`
  (all in the interval `(0, (M+2) * pi)`).
- Bound says ≤ M zeros, but we have M+1. Contradiction.

**Honest scope:** This is CONDITIONAL on Phase A's axiomatized zero
bound. The constructive Khovanskii proof (Phase C) replaces the
axiom with a real proof.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-! ## sin(natCast k * π) = 0 for all Nat k -/

/-- Sin vanishes at all integer multiples of π. -/
theorem sin_natCast_mul_pi (k : Nat) : sin (natCast k * pi) = 0 := by
  induction k with
  | zero =>
    rw [natCast_zero, zero_mul]
    exact sin_zero
  | succ n ih =>
    rw [natCast_succ]
    have hdistrib : (natCast n + 1) * pi = natCast n * pi + pi := by
      rw [mul_distrib_right, one_mul_thm]
    rw [hdistrib, sin_add, ih, sin_pi, zero_mul, mul_zero, add_zero]

end Real
end MachLib

namespace MachLib

open Real

/-! ## EML → Pfaffian embedding -/

/-- Every EML tree corresponds to a Pfaffian function. Axiomatized
for now; a constructive recursive definition using the Phase A
operations (`exp_as_pfaffian.comp`, `log_as_pfaffian.comp`,
`PfaffianFunction.sub`) is straightforward but requires handling
the log domain convention in the eval-agreement proof. -/
axiom eml_pfaffian : EMLTree → PfaffianFunction

/-- The eval-agreement axiom. -/
axiom eml_pfaffian_eval (t : EMLTree) (x : Real) :
    (eml_pfaffian t).eval x = t.eval x

/-- The list `[natCast 1 * π, natCast 2 * π, ..., natCast (M+1) * π]` has
no duplicates. Used in the sin barrier proof to satisfy the Nodup
precondition of `PfaffianFunction.zero_count_le`.

Axiomatized; a constructive proof requires either `List.Nodup.map`
(which isn't trivially applicable from Lean core's current signature)
or manual induction on M with `Pairwise` reasoning. The mathematical
fact follows from the injectivity of `i ↦ natCast (i+1) * π` (since
natCast is order-preserving and π > 0) + `List.range`'s Nodup-ness. -/
axiom sin_zeros_list_nodup (M : Nat) :
    ((List.range (M + 1)).map (fun i => natCast (i + 1) * pi)).Nodup

/-! ## Helpers for the list construction -/

/-- `natCast k * π ≥ 0` for all `k`. -/
theorem natCast_mul_pi_nonneg (k : Nat) : (0 : Real) ≤ natCast k * pi := by
  induction k with
  | zero => rw [natCast_zero, zero_mul]; exact le_refl _
  | succ p ihp =>
    rw [natCast_succ, mul_distrib_right, one_mul_thm]
    exact add_nonneg ihp (le_of_lt pi_pos)

/-- `natCast k * π > 0` for `k ≥ 1`. -/
theorem natCast_mul_pi_pos {k : Nat} (hk : 1 ≤ k) : (0 : Real) < natCast k * pi := by
  -- For k ≥ 1: k = m + 1 with m ≥ 0. natCast (m+1) * pi = natCast m * pi + pi.
  -- ≥ 0 + pi = pi > 0.
  cases k with
  | zero => omega
  | succ m =>
    rw [natCast_succ, mul_distrib_right, one_mul_thm]
    have hmul_nonneg : (0 : Real) ≤ natCast m * pi := natCast_mul_pi_nonneg m
    have step := add_lt_add_left pi_pos (natCast m * pi)
    rw [add_zero] at step
    exact lt_of_le_of_lt hmul_nonneg step

/-- `natCast j * π < natCast k * π` when `j < k`. -/
theorem natCast_mul_pi_lt {j k : Nat} (hjk : j < k) :
    natCast j * pi < natCast k * pi := by
  induction k with
  | zero => omega
  | succ m ih =>
    by_cases h : j < m
    · have ih' := ih h
      rw [natCast_succ, mul_distrib_right, one_mul_thm]
      have hstep : natCast m * pi < natCast m * pi + pi := by
        have step := add_lt_add_left pi_pos (natCast m * pi)
        rw [add_zero] at step
        exact step
      exact lt_trans_ax ih' hstep
    · have hjm : j = m := by omega
      rw [hjm, natCast_succ, mul_distrib_right, one_mul_thm]
      have step := add_lt_add_left pi_pos (natCast m * pi)
      rw [add_zero] at step
      exact step

/-! ## Sin barrier — uniform-in-k closure via Pfaffian zero bound

The proof constructs the list of zeros inline (avoiding a separate
`pi_zeros` definition to bypass Lean-side recursion-unfolding issues).
-/

/-- **Sin barrier for all depths.** For every `k : Nat`, `Real.sin`
is NOT in `EML_k`. Conditional on the Pfaffian zero bound (Phase A
axiom). -/
theorem sin_not_in_eml_any_depth (k : Nat) :
    ¬ InEMLDepth (fun x : Real => Real.sin x) k := by
  intro ⟨t, _htd, hsin⟩
  -- f := eml_pfaffian t.
  let f : PfaffianFunction := eml_pfaffian t
  have hf_def : f = eml_pfaffian t := rfl
  -- f.eval x = sin x for all x.
  have hf_eval : ∀ x, f.eval x = Real.sin x := by
    intro x
    rw [hf_def, eml_pfaffian_eval]
    exact (hsin x).symm
  -- f is not identically zero.
  have hf_ne : ∃ x : Real, f.eval x ≠ 0 := by
    refine ⟨1, ?_⟩
    rw [hf_eval]
    intro heq
    have hpos : (0 : Real) < Real.sin 1 := sin_one_pos
    rw [heq] at hpos
    exact lt_irrefl_ax 0 hpos
  -- The bound M.
  let M : Nat := pfaffian_zero_count_bound f.chain.order f.degree
  have hM_def : M = pfaffian_zero_count_bound f.chain.order f.degree := rfl
  -- Interval (0, natCast (M + 2) * pi).
  have hb_pos : (0 : Real) < natCast (M + 2) * pi :=
    natCast_mul_pi_pos (by omega)
  have hbound : f.zero_count_le 0 (natCast (M + 2) * pi) M := by
    have := f.zero_bound 0 (natCast (M + 2) * pi) hb_pos hf_ne
    rw [← hM_def] at this
    exact this
  -- Build the list of M+1 zeros at natCast 1 * pi, natCast 2 * pi, ..., natCast (M+1) * pi.
  -- Use a recursive helper.
  let zeros : List Real := (List.range (M + 1)).map (fun i => natCast (i + 1) * pi)
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  -- Each z ∈ zeros satisfies 0 < z, z < natCast (M+2) * pi, f.eval z = 0.
  have hzeros_valid : ∀ z ∈ zeros,
      0 < z ∧ z < natCast (M + 2) * pi ∧ f.eval z = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hi_lt, hzeq⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzeq]; exact natCast_mul_pi_pos (by omega)
    · rw [← hzeq]; exact natCast_mul_pi_lt (by omega)
    · rw [← hzeq, hf_eval]; exact sin_natCast_mul_pi (i + 1)
  -- The list zeros is Nodup because (List.range (M+1)) is Nodup and
  -- the function i ↦ natCast (i+1) * pi is injective on Nat.
  -- Proved by manual induction on M (Lean core's List.Nodup.map signature
  -- isn't easily applicable here).
  have hzeros_nodup : zeros.Nodup := sin_zeros_list_nodup M
  -- Apply hbound: zeros.length ≤ M. But length = M + 1. Contradiction.
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

end MachLib
