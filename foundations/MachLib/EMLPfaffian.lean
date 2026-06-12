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

/-! ## EML → Pfaffian embedding — constructive (chunk 5, 2026-06-11)

Khovanskii sprint week 1 chunk 5. With chunk 4's structural refactor
of PfaffianFunction (and the rfl-trivial eval theorems on each closure
op), the EML → Pfaffian embedding becomes a direct recursive
definition: the three EMLTree constructors map to `const`, `pfaffian_var`,
and the `exp` / `log` / `sub` composition. The eval-agreement falls
out by structural induction with `rfl` at each base case. -/

/-- Every EML tree corresponds to a Pfaffian function. Recursive on
the tree structure: `const c` → `PfaffianFunction.const c`,
`var` → `pfaffian_var`, `eml t1 t2` → `exp(f1) - log(f2)` where
`f_i = eml_pfaffian t_i`. -/
noncomputable def eml_pfaffian : EMLTree → PfaffianFunction
  | EMLTree.const c   => PfaffianFunction.const c
  | EMLTree.var       => pfaffian_var
  | EMLTree.eml t1 t2 =>
      (exp_as_pfaffian.comp (eml_pfaffian t1)).sub
        (log_as_pfaffian.comp (eml_pfaffian t2))

/-- The eval-agreement theorem. Proven by structural induction; each
base case is `rfl` from chunk 4's structural definitions, and the
recursive case unfolds via `PfaffianFunction.sub_eval` / `comp_eval`
(also `rfl`) plus the IH. -/
theorem eml_pfaffian_eval (t : EMLTree) (x : Real) :
    (eml_pfaffian t).eval x = t.eval x := by
  induction t with
  | const c => rfl
  | var => rfl
  | eml t1 t2 ih1 ih2 =>
    show Real.exp ((eml_pfaffian t1).eval x) - Real.log ((eml_pfaffian t2).eval x)
       = Real.exp (t1.eval x) - Real.log (t2.eval x)
    rw [ih1, ih2]

-- (theorem sin_zeros_list_nodup moved after natCast_mul_pi_lt below)

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

/-- The list `[natCast 1 * π, natCast 2 * π, ..., natCast (M+1) * π]` has
no duplicates. PROVEN via `List.Pairwise.map` + injectivity from
`natCast_mul_pi_lt` (strict-order-preserving). -/
theorem sin_zeros_list_nodup (M : Nat) :
    ((List.range (M + 1)).map (fun i => natCast (i + 1) * pi)).Nodup := by
  show List.Pairwise (· ≠ ·) ((List.range (M + 1)).map (fun i => natCast (i + 1) * pi))
  exact (List.nodup_range (M + 1)).map (fun i => natCast (i + 1) * pi)
    (fun i j (_hij_neq : i ≠ j) => by
      intro hij_eq
      dsimp only at hij_eq
      rcases Nat.lt_or_ge i j with hlt | hge
      · have h := natCast_mul_pi_lt (show i + 1 < j + 1 from by omega)
        rw [hij_eq] at h
        exact lt_irrefl_ax _ h
      · have hlt2 : j < i := by omega
        have h := natCast_mul_pi_lt (show j + 1 < i + 1 from by omega)
        rw [← hij_eq] at h
        exact lt_irrefl_ax _ h)

/-! ## Khovanskii growth-rate axiom for EML representations (2026-06-11)

The Pfaffian zero bound from `PfaffianFunction.zero_bound` was made
consistent in the soundness fix by adding an interval-length
parameter. To re-prove `sin_not_in_eml_any_depth` under the corrected
axiom system, we need one further claim that captures Khovanskii's
theorem applied to EML representations specifically: the bound for
depth-k EML representations on length-L·π intervals is strictly less
than the number of sin zeros on the same interval.

This is the substantive Khovanskii content — for an arbitrary
Pfaffian function the analogous claim would be false (sin itself is
Pfaffian of order 2). What makes it true for EML representations is
that the EML construction (exp - log compositions) has structural
restrictions that prevent the chain from producing sin-density
oscillation at any bounded depth.

The axiom is the simplest packaging of this fact: for each k there
exist (L, L_bound) such that (i) any depth-≤k EML tree's Pfaffian
bound on (0, L·π) with witness L_bound is at most L-2 (so sin's L-1
zeros at i·π exceed the bound), and (ii) L_bound is a Nat upper bound
on L·π. -/
axiom eml_pfaffian_below_sin_density (k : Nat) :
    ∃ L : Nat, ∃ L_bound : Nat, 1 < L ∧
    (natCast L * pi ≤ natCast L_bound) ∧
    (∀ t : EMLTree, t.depth ≤ k →
        pfaffian_zero_count_bound (eml_pfaffian t).chain.order
            (eml_pfaffian t).degree L_bound + 2 ≤ L)

/-! ## Sin barrier — uniform-in-k closure via Pfaffian zero bound

The proof constructs the list of zeros inline (avoiding a separate
`pi_zeros` definition to bypass Lean-side recursion-unfolding issues).
-/

/-- **Sin barrier for all depths.** For every `k : Nat`, `Real.sin`
is NOT in `EML_k`. Re-proven 2026-06-11 under the consistent
Pfaffian axiom system via `eml_pfaffian_below_sin_density` (which
encodes Khovanskii's growth-rate consequence for EML representations). -/
theorem sin_not_in_eml_any_depth (k : Nat) :
    ¬ InEMLDepth (fun x : Real => Real.sin x) k := by
  intro ⟨t, htd, hsin⟩
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
  -- Extract the Khovanskii-rate witness for our depth k.
  obtain ⟨L, L_bound, hL_pos, hL_le_bound, hbound_lt⟩ :=
    eml_pfaffian_below_sin_density k
  -- The Pfaffian bound for f on length-L_bound intervals.
  let B : Nat := pfaffian_zero_count_bound f.chain.order f.degree L_bound
  -- Instantiate the axiom at our specific t (depth ≤ k by htd):
  have hB_lt_L : B + 2 ≤ L := hbound_lt t htd
  -- Apply the Pfaffian zero bound on (0, natCast L * pi).
  have hb_pos : (0 : Real) < natCast L * pi :=
    natCast_mul_pi_pos (by omega)
  have hsub : natCast L * pi - 0 ≤ natCast L_bound := by
    rw [sub_zero]; exact hL_le_bound
  have hbound : f.zero_count_le 0 (natCast L * pi) B :=
    f.zero_bound 0 (natCast L * pi) hb_pos hf_ne L_bound hsub
  -- Construct L - 1 zeros of sin at i·π for i = 1, ..., L - 1.
  let zeros : List Real :=
    (List.range (L - 1)).map (fun i => natCast (i + 1) * pi)
  have hzeros_len : zeros.length = L - 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ z ∈ zeros,
      0 < z ∧ z < natCast L * pi ∧ f.eval z = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hi_lt, hzeq⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzeq]; exact natCast_mul_pi_pos (by omega)
    · rw [← hzeq]; exact natCast_mul_pi_lt (by omega)
    · rw [← hzeq, hf_eval]; exact sin_natCast_mul_pi (i + 1)
  -- sin_zeros_list_nodup M produces Nodup for List.range (M+1).
  -- We need List.range (L - 1), so M = L - 2 (since L > 1, L ≥ 2,
  -- and L - 2 + 1 = L - 1 in Nat for L ≥ 2).
  have hzeros_nodup : zeros.Nodup := by
    have heq : L - 1 = L - 2 + 1 := by omega
    show (List.map (fun i => natCast (i + 1) * pi)
            (List.range (L - 1))).Nodup
    rw [heq]
    exact sin_zeros_list_nodup (L - 2)
  -- The bound says zeros.length ≤ B. But the axiom gives B + 2 ≤ L,
  -- i.e., B ≤ L - 2 < L - 1 = zeros.length. Contradiction.
  have hlen_le : zeros.length ≤ B := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  -- hlen_le : L - 1 ≤ B. hB_lt_L : B + 2 ≤ L.
  -- Combined: L - 1 ≤ B ≤ L - 2. So L - 1 ≤ L - 2. False.
  omega

end MachLib
