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
  -- ⚠ 2026-06-11: This proof was originally written against an
  -- INCONSISTENT version of PfaffianFunction.zero_bound whose bound
  -- was interval-length-independent. The corrected axiom now takes
  -- an `L : Nat` parameter with `b - a ≤ natCast L`, so the bound
  -- `pfaffian_zero_count_bound n d L` is allowed to grow with L.
  --
  -- The original proof structure (pick M = bound, construct M+1 zeros
  -- in (0, (M+2)·π)) is now circular: M = pfaffian_zero_count_bound n d L
  -- where L must be ≥ (M+2)·π, so M depends on L which depends on M.
  --
  -- A correct proof requires a different structure. One approach:
  --   1. Choose L : Nat as a free parameter (to be picked at the end).
  --   2. Set M(L) := pfaffian_zero_count_bound n d L.
  --   3. Construct N(L) zeros where N(L) > M(L) for some choice of L.
  --      The construction must produce zeros in (0, L) — sin has
  --      ⌊L/π⌋ zeros at i·π for i = 1, ..., ⌊L/π⌋.
  --   4. For contradiction: need ⌊L/π⌋ > pfaffian_zero_count_bound n d L
  --      for some L. This requires Khovanskii's actual growth rate
  --      bound (which isn't yet axiomatized in MachLib).
  --
  -- This is a substantive mathematical claim about the rate of growth
  -- of the Pfaffian bound. Marked `sorry` until the right axiom
  -- (Khovanskii's actual rate-of-growth statement) is added in a
  -- future sprint.
  --
  -- The mathematical conclusion (sin ∉ EML_k) is still correct; what's
  -- missing is the formal proof under the now-consistent axiom system.
  -- The prior proof was VALID under the old INCONSISTENT axiom (any
  -- conclusion follows from inconsistency) but is no longer derivable.
  sorry

end MachLib
