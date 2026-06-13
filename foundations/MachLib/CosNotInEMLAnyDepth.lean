import MachLib.EMLPfaffian
import MachLib.CosNotInEML

/-!
# `cos ∉ EML_k(ℝ)` for ALL depths

Mirror of `sin_not_in_eml_any_depth` (in `EMLPfaffian.lean`) for cosine.
Both proofs use the same `eml_pfaffian` envelope + Khovanskii zero bound;
the only difference is the set of zeros used to overrun the bound:

  - sin's zeros at `i * π` for `i = 1, 2, ..., M+1` (in
    `EMLPfaffian.sin_not_in_eml_any_depth`).
  - cos's zeros at `i·π + π/2` for `i = 0, 1, ..., M` (this file).

## New axioms introduced (3, all classical-true)

1. `eml_pfaffian_validon_from_cos_equality` — exact analog of the sin
   side axiom. Same classical smoothness-preservation argument; cos is
   smooth everywhere just like sin. A Smoothness module would discharge
   this and its sin sibling together.

2. `pi_div_one_plus_one_pos : 0 < pi/(1+1)` — trivial classical fact.
   Would be derivable in ~20 lines if MachLib had `div_pos`; lifted
   here as a small classical-citation axiom.

3. `pi_div_one_plus_one_lt_pi : pi/(1+1) < pi` — trivial classical
   fact (`pi/2 < pi`). Same discharge path as #2.

Net axiom delta: +3. The constructive infrastructure (cos zeros at
half-odd-pi, distinct-list, witness chain) is proven directly.

## What this does NOT do

- Does not modify `Trig.lean` or any pre-existing file.
- Does not introduce any new sorry.
- Does not change the sin barrier or any other prior proof.
-/

namespace MachLib

open Real

/-! ## Two small classical-citation lemmas about π/2 -/

/-- `0 < π/2`. Classically trivial (positive divided by positive).
Lifted as an axiom since MachLib doesn't yet have a general
`div_pos`. Same discharge path as
`pi_div_one_plus_one_lt_pi` below — both fall out once div-ordering
lemmas land in `Ring.lean`. -/
axiom pi_div_one_plus_one_pos : (0 : Real) < pi / (1 + 1)

/-- `π/2 < π`. Classically trivial (half of positive < whole).
Same lifting rationale as `pi_div_one_plus_one_pos`. -/
axiom pi_div_one_plus_one_lt_pi : pi / (1 + 1) < pi

/-! ## cos(k·π + π/2) = 0 for all Nat k -/

/-- Cos vanishes at all half-odd multiples of π. Proof by induction on
`k`, using `cos_add` together with the standing values
`cos(π/2) = 0` (CosNotInEML), `cos(π) = -1` and `sin(π) = 0` (Trig). -/
theorem cos_at_half_odd_pi (k : Nat) :
    cos (natCast k * pi + pi / (1 + 1)) = 0 := by
  induction k with
  | zero =>
    rw [natCast_zero, zero_mul, zero_add]
    exact cos_pi_div_two
  | succ n ih =>
    -- (natCast (n+1)) * pi + pi/(1+1)
    --   = (natCast n + 1) * pi + pi/(1+1)
    --   = natCast n * pi + pi + pi/(1+1)
    --   = (natCast n * pi + pi/(1+1)) + pi
    rw [natCast_succ]
    have hdistrib : (natCast n + 1) * pi = natCast n * pi + pi := by
      rw [mul_distrib_right, one_mul_thm]
    rw [hdistrib]
    have hassoc : natCast n * pi + pi + pi / (1 + 1)
                = (natCast n * pi + pi / (1 + 1)) + pi := by
      rw [add_assoc, add_comm pi (pi / (1 + 1)), ← add_assoc]
    rw [hassoc]
    -- cos((x + pi)) = cos x * cos pi - sin x * sin pi
    --              = cos x * (-1) - sin x * 0 = -cos x
    -- And IH says cos x = 0 for x = natCast n * pi + pi/(1+1), so:
    rw [cos_add, cos_pi, sin_pi, ih, mul_zero, sub_zero, zero_mul]

/-! ## Strict order on the half-odd-pi list -/

/-- The half-odd-pi expressions `natCast j * pi + pi/(1+1)` and
`natCast k * pi + pi/(1+1)` are strictly ordered when `j < k`.
Direct consequence of `natCast_mul_pi_lt` with the same offset added
to both sides. -/
theorem cos_half_odd_pi_lt {j k : Nat} (hjk : j < k) :
    natCast j * pi + pi / (1 + 1) < natCast k * pi + pi / (1 + 1) := by
  have h := natCast_mul_pi_lt hjk
  -- MachLib has add_lt_add_left only; commute to use it.
  have hL := add_lt_add_left h (pi / (1 + 1))
  -- hL : pi/(1+1) + natCast j * pi < pi/(1+1) + natCast k * pi
  rw [add_comm (pi / (1 + 1)) (natCast j * pi),
      add_comm (pi / (1 + 1)) (natCast k * pi)] at hL
  exact hL

/-- The list `[0·π + π/2, 1·π + π/2, …, M·π + π/2]` has no
duplicates. Same `List.Pairwise.map` + strict-order-injectivity pattern
as `sin_zeros_list_nodup`. -/
theorem cos_zeros_list_nodup (M : Nat) :
    ((List.range (M + 1)).map (fun i => natCast i * pi + pi / (1 + 1))).Nodup := by
  show List.Pairwise (· ≠ ·)
    ((List.range (M + 1)).map (fun i => natCast i * pi + pi / (1 + 1)))
  exact (List.nodup_range (M + 1)).map (fun i => natCast i * pi + pi / (1 + 1))
    (fun i j (_hij_neq : i ≠ j) => by
      intro hij_eq
      dsimp only at hij_eq
      rcases Nat.lt_or_ge i j with hlt | hge
      · have h := cos_half_odd_pi_lt hlt
        rw [hij_eq] at h
        exact lt_irrefl_ax _ h
      · have hlt2 : j < i := by omega
        have h := cos_half_odd_pi_lt hlt2
        rw [← hij_eq] at h
        exact lt_irrefl_ax _ h)

/-! ## Cos-equality forces validity (classical, same justification as sin)

If `t.eval x = cos x` for all `x : Real`, then `EMLPfaffianValidOn t 0 b`
holds for every `b > 0`. Same classical smoothness-preservation argument
as the sin side; see the docstring of
`eml_pfaffian_validon_from_sin_equality` in `EMLPfaffian.lean` for the
full reasoning (the same argument applies verbatim with cos in place
of sin, since both functions are globally smooth and the connectivity
argument is phase-independent).

Closure path: a Smoothness module would discharge both this axiom and
its sin sibling together; ~300-500 lines, multi-session. -/
axiom eml_pfaffian_validon_from_cos_equality
    (t : EMLTree) (hcos : ∀ x : Real, t.eval x = Real.cos x)
    (b : Real) (_hb_pos : 0 < b) :
    EMLPfaffianValidOn t 0 b

/-! ## Main theorem -/

/-- **Cos barrier for all depths.** For every `k : Nat`, `Real.cos` is
NOT in `EML_k`. Structurally parallel to `sin_not_in_eml_any_depth`:
the eml_pfaffian envelope's Khovanskii zero bound `M` is overrun by
the M+1 distinct cos zeros at `i·π + π/2` for `i = 0, 1, ..., M`.

Witness for "f is not identically zero" is `x = π`, where
`cos π = -1 ≠ 0` (derived constructively below from `cos_pi` and
`zero_lt_one_ax`). -/
theorem cos_not_in_eml_any_depth (k : Nat) :
    ¬ InEMLDepth (fun x : Real => Real.cos x) k := by
  intro ⟨t, htd, hcos⟩
  let f : PfaffianFunction := eml_pfaffian t
  have hf_def : f = eml_pfaffian t := rfl
  have hf_eval : ∀ x, f.eval x = Real.cos x := by
    intro x
    rw [hf_def, eml_pfaffian_eval]
    exact (hcos x).symm
  -- `-1 ≠ 0` constructively (no new axiom).
  -- If -1 = 0, then 1 = -(-1) = -0 = 0, contradicting zero_lt_one_ax.
  have neg_one_ne_zero : (-1 : Real) ≠ 0 := by
    intro h
    have h1 : (1 : Real) = 0 := by
      have step : -(- (1 : Real)) = -(0 : Real) := by rw [h]
      rw [neg_neg_helper, neg_zero] at step
      exact step
    -- Materialize zero_lt_one_ax as a local fact, then rewrite.
    have hz : (0 : Real) < 1 := zero_lt_one_ax
    rw [h1] at hz
    exact lt_irrefl_ax 0 hz
  -- f is not identically zero (cos π = -1 ≠ 0).
  have hf_ne : ∃ x : Real, f.eval x ≠ 0 := by
    refine ⟨pi, ?_⟩
    rw [hf_eval, cos_pi]
    exact neg_one_ne_zero
  -- The Pfaffian bound M (uniform in interval).
  let M : Nat := pfaffian_zero_count_bound f.chain.order f.degree
  have hM_def : M = pfaffian_zero_count_bound f.chain.order f.degree := rfl
  -- Apply the bound on the interval (0, natCast (M + 2) * pi).
  have hb_pos : (0 : Real) < natCast (M + 2) * pi :=
    natCast_mul_pi_pos (by omega)
  -- Witness IN the interval: x = π. cos π = -1 ≠ 0.
  have hne_in : ∃ x : Real, (0 : Real) < x ∧ x < natCast (M + 2) * pi ∧
                f.eval x ≠ 0 := by
    refine ⟨pi, pi_pos, ?_, ?_⟩
    · -- pi < natCast (M + 2) * pi: same chain as sin's proof.
      have h1_lt : (1 : Nat) < M + 2 := by omega
      have h_chain : natCast 1 * pi < natCast (M + 2) * pi :=
        natCast_mul_pi_lt h1_lt
      have h_natCast1 : natCast 1 = (1 : Real) := by
        rw [show (1 : Nat) = 0 + 1 by rfl, natCast_succ, natCast_zero,
            zero_add]
      rw [h_natCast1, one_mul_thm] at h_chain
      exact h_chain
    · rw [hf_eval, cos_pi]
      exact neg_one_ne_zero
  have h_valid : ∀ x : Real, (0 : Real) < x → x < natCast (M + 2) * pi →
                  f.expr.IsValidAt x := by
    have hcos' : ∀ x : Real, t.eval x = Real.cos x := fun x => (hcos x).symm
    have hvalidon : EMLPfaffianValidOn t 0 (natCast (M + 2) * pi) :=
      eml_pfaffian_validon_from_cos_equality t hcos'
        (natCast (M + 2) * pi) hb_pos
    show ∀ x, (0 : Real) < x → x < natCast (M + 2) * pi →
          (eml_pfaffian t).expr.IsValidAt x
    exact eml_pfaffian_isvalidat_of_validon t 0
            (natCast (M + 2) * pi) hvalidon
  have hbound : f.zero_count_le 0 (natCast (M + 2) * pi) M := by
    have := f.zero_bound 0 (natCast (M + 2) * pi) hb_pos h_valid hne_in
    rw [← hM_def] at this
    exact this
  -- Construct M + 1 zeros of cos at i·π + π/2 for i = 0, 1, ..., M.
  let zeros : List Real :=
    (List.range (M + 1)).map (fun i => natCast i * pi + pi / (1 + 1))
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ z ∈ zeros,
      0 < z ∧ z < natCast (M + 2) * pi ∧ f.eval z = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hi_lt, hzeq⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · -- 0 < natCast i * pi + pi/(1+1).
      -- Decompose: 0 + 0 < natCast i * pi + pi/(1+1) via
      --   pi/(1+1) > 0 (strict) + natCast i * pi ≥ 0 (nonneg).
      rw [← hzeq]
      have hi_nonneg : (0 : Real) ≤ natCast i * pi := natCast_mul_pi_nonneg i
      have hpi_half_pos : (0 : Real) < pi / (1 + 1) := pi_div_one_plus_one_pos
      -- Strict version: add the strict bound on the right.
      have hstep1 : (0 : Real) < (0 : Real) + pi / (1 + 1) := by
        rw [zero_add]; exact hpi_half_pos
      -- Now bump the left to natCast i * pi (preserving < via ≤).
      -- Use add_lt_add_left with the ≤ side handled by le_trans.
      have hstep2 : (0 : Real) + pi / (1 + 1) ≤
                    natCast i * pi + pi / (1 + 1) := by
        -- Goal: 0 + x ≤ y + x for 0 ≤ y. Rewrite via zero_add and
        -- a + x = a + x to reduce to 0 ≤ y.
        rw [zero_add]
        -- Goal: pi/(1+1) ≤ natCast i * pi + pi/(1+1).
        -- That's 0 + pi/(1+1) ≤ natCast i * pi + pi/(1+1) after rewriting.
        -- Use add_lt_add_left with hi_nonneg: ≤ case from add_le_add_right_helper.
        -- MachLib has add_lt_add_left for strict; for ≤ use le_iff.
        -- Simpler: 0 + pi/(1+1) = pi/(1+1) ≤ natCast i * pi + pi/(1+1)
        -- via add_le_add_right (need to derive from add_lt_add_left).
        rcases le_iff_lt_or_eq 0 (natCast i * pi) |>.mp hi_nonneg with hlt | heq
        · have := add_lt_add_left hlt (pi / (1 + 1))
          -- this : pi/(1+1) + 0 < pi/(1+1) + natCast i * pi
          rw [add_zero, add_comm (pi / (1 + 1)) (natCast i * pi)] at this
          exact le_of_lt this
        · rw [← heq, zero_add]
          exact le_refl _
      -- Combine: 0 < 0 + pi/(1+1) ≤ natCast i * pi + pi/(1+1).
      exact lt_of_lt_of_le hstep1 hstep2
    · -- natCast i * pi + pi/(1+1) < natCast (M+2) * pi.
      -- Chain: natCast i * pi + pi/(1+1) < natCast i * pi + pi
      --                                 = natCast (i+1) * pi
      --                                 < natCast (M+2) * pi  (since i+1 < M+2 = i+1+(M-i)+1, given i ≤ M).
      rw [← hzeq]
      have hhalf_lt_pi : pi / (1 + 1) < pi := pi_div_one_plus_one_lt_pi
      have step1 : natCast i * pi + pi / (1 + 1) < natCast i * pi + pi :=
        add_lt_add_left hhalf_lt_pi (natCast i * pi)
      have step2 : natCast i * pi + pi = natCast (i + 1) * pi := by
        rw [natCast_succ, mul_distrib_right, one_mul_thm]
      rw [step2] at step1
      have step3 : natCast (i + 1) * pi < natCast (M + 2) * pi :=
        natCast_mul_pi_lt (by omega)
      exact lt_trans_ax step1 step3
    · -- f.eval z = cos z = 0 via cos_at_half_odd_pi.
      rw [← hzeq, hf_eval]; exact cos_at_half_odd_pi i
  have hzeros_nodup : zeros.Nodup := cos_zeros_list_nodup M
  -- The bound says zeros.length ≤ M, but length = M + 1. Contradiction.
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

end MachLib
