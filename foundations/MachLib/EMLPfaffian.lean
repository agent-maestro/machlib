import MachLib.Exp
import MachLib.Log
import MachLib.Trig
import MachLib.EML
import MachLib.EMLHierarchy
import MachLib.Pfaffian
import MachLib.KhovanskiiLemma

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
`f_i = eml_pfaffian t_i`.

⚠ **Domain qualification (2026-06-12 step 2):** The construction
produces a `PfaffianFunction` (a Lean structure) for *any* EMLTree,
but the resulting function is GENUINELY Pfaffian (in the
classical-Khovanskii sense) only on intervals where every log-
subargument stays strictly positive. This is because MachLib's
`Real.log` is clamped at 0 for `x ≤ 0` (a piecewise-total function),
and piecewise functions are not analytic, hence not Pfaffian.

A correct downstream application of `PfaffianFunction.zero_bound`
to `eml_pfaffian t` on `(a, b)` therefore requires verifying:

  for every `eml t1 t2` subtree of `t`, the inner function
  `t2.eval` is strictly positive on `(a, b)`.

The predicate `EMLPfaffianValidOn` (below) captures this domain
condition explicitly. Downstream consumers should require it as a
precondition.

For the headline `sin_not_in_eml_any_depth`, the domain condition is
*forced* by the hypothesis: if `t.eval = sin` globally, then for any
`eml` subtree on the interval `(0, (M+2)·π)`, the inner `t2.eval`
must stay positive — because sin takes negative values on `(π, 2π)`,
and `exp(t1.eval x) - log(t2.eval x) = sin x` with negative sin
forces `log(t2.eval x)` to be the analytic (positive-domain) value,
which forces `t2.eval x > 0`. So the sin-barrier proof's domain
condition is satisfied implicitly by its hypothesis — no explicit
precondition needed for that specific theorem. -/
noncomputable def eml_pfaffian : EMLTree → PfaffianFunction
  | EMLTree.const c   => PfaffianFunction.const c
  | EMLTree.var       => pfaffian_var
  | EMLTree.eml t1 t2 =>
      (exp_as_pfaffian.comp (eml_pfaffian t1)).sub
        (log_as_pfaffian.comp (eml_pfaffian t2))

/-- Domain-validity predicate for `eml_pfaffian` on `(a, b)`. The
construction is genuinely Pfaffian on `(a, b)` iff all log subargument
sub-evaluations stay strictly positive throughout the interval.

This predicate is the load-bearing precondition that any non-trivial
application of `PfaffianFunction.zero_bound` to `eml_pfaffian t`
must verify. -/
def EMLPfaffianValidOn : EMLTree → Real → Real → Prop
  | EMLTree.const _,    _, _ => True
  | EMLTree.var,        _, _ => True
  | EMLTree.eml t1 t2,  a, b =>
      EMLPfaffianValidOn t1 a b ∧
      EMLPfaffianValidOn t2 a b ∧
      (∀ x : Real, a < x → x < b → 0 < t2.eval x)

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

/-! ## Bridge: EMLPfaffianValidOn → PfaffianExpr.IsValidAt

The `EMLPfaffianValidOn t a b` predicate (defined above) captures the
EMLTree-level domain condition: every `eml t1 t2` subtree has
`t2.eval > 0` on `(a, b)`. The `PfaffianExpr.IsValidAt` predicate
(defined in `KhovanskiiLemma.lean`) is its Pfaffian-side counterpart.
This theorem bridges the two. Proven by structural induction on
`EMLTree`. -/
theorem eml_pfaffian_isvalidat_of_validon (t : EMLTree) (a b : Real)
    (hvalidon : EMLPfaffianValidOn t a b) :
    ∀ x : Real, a < x → x < b → (eml_pfaffian t).expr.IsValidAt x := by
  intro x hxa hxb
  induction t with
  | const c =>
    -- eml_pfaffian (const c) = ⟨const c⟩; IsValidAt = True.
    trivial
  | var =>
    -- eml_pfaffian var = ⟨var⟩; IsValidAt = True.
    trivial
  | eml t1 t2 ih1 ih2 =>
    -- EMLPfaffianValidOn (eml t1 t2) a b = validon t1 ∧ validon t2 ∧ (∀ x, ..., 0 < t2.eval x)
    obtain ⟨hv1, hv2, hpos⟩ := hvalidon
    -- (eml_pfaffian (eml t1 t2)).expr.IsValidAt x: triplet from sub/comp/comp structure.
    refine ⟨?_, ?_⟩
    · -- First subtree: comp exp_atom (eml_pfaffian t1).expr
      refine ⟨ih1 hv1, ?_⟩
      -- exp_atom.IsValidAt _ = True
      trivial
    · -- Second subtree: comp log_atom (eml_pfaffian t2).expr
      refine ⟨ih2 hv2, ?_⟩
      -- log_atom.IsValidAt ((eml_pfaffian t2).expr.eval x) = 0 < t2.eval x
      show (0 : Real) < (eml_pfaffian t2).expr.eval x
      have := hpos x hxa hxb
      -- (eml_pfaffian t2).expr.eval x = (eml_pfaffian t2).eval x = t2.eval x
      show (0 : Real) < (eml_pfaffian t2).eval x
      rw [eml_pfaffian_eval t2 x]
      exact this

/-! ## Sin-equality forces validity (axiomatized analytic argument)

If `t.eval x = sin x` for all `x : Real`, then `EMLPfaffianValidOn t 0 b`
holds for every `b > 0`. The classical argument:

1. `t.eval` equals `sin`, hence is smooth (sin is smooth everywhere).
2. For any `eml t1 t2` subtree of `t`, the eval is
   `exp(t1.eval x) - log_clamped(t2.eval x)`. Since `exp` is smooth,
   smoothness of the whole forces `log_clamped(t2.eval x)` to be smooth.
3. `log_clamped` is discontinuous at `0` (jumps from 0 to the analytic
   log). For its composition with `t2.eval` to be smooth, `t2.eval`
   must not cross 0 anywhere `t.eval = sin` is smooth — which is
   everywhere.
4. At any zero of `sin` (`x = i·π`), if `t = eml t1 t2`, then
   `t.eval = exp - log_clamped(t2) = 0` forces `log_clamped(t2) > 0`
   (since `exp > 0`), hence `t2 > 0` (since log_clamped(t2) = 0 when
   t2 ≤ 0).
5. By connectivity of `(0, b)` and `t2` not crossing 0 plus `t2 > 0`
   at any sin-zero in the interval (if any exists), `t2 > 0` throughout.

The argument requires formalizing smoothness preservation, continuity,
and connectivity — none of which MachLib currently has. Axiomatized
here as a single load-bearing analytic claim, named so reviewers can
locate it as a single auditable item. Closure path: add a Smoothness
module with `IsSmoothOn`, `IsSmoothOn_of_eq`, `Continuous_of_HasDerivAt`,
and a connectivity argument; ~300-500 lines, multi-session. -/
axiom eml_pfaffian_validon_from_sin_equality
    (t : EMLTree) (hsin : ∀ x : Real, t.eval x = Real.sin x)
    (b : Real) (_hb_pos : 0 < b) :
    EMLPfaffianValidOn t 0 b

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

/-! ## 2026-06-12 sprint week-2 step 1 — sin barrier under consistent axioms

The 2026-06-11 reproof attempt added an `eml_pfaffian_below_sin_density`
axiom that turned out to be inconsistent (same root cause as the
original Pfaffian zero bound: sin/cos couldn't be distinguished from
EML functions at the same (n, d)).

The operator's diagnosis on 2026-06-12 identified that sin/cos were
themselves the source of the inconsistency: they had been axiomatized
as globally Pfaffian (chain.order=2, degree=1), but classical
Khovanskii requires triangular Pfaffian chains, and the sin/cos
chain sin' = cos, cos' = -sin is circular. Removing `sin_as_pfaffian`
and `cos_as_pfaffian` from Pfaffian.lean restored consistency of the
original interval-uniform bound axiom.

With the original axiom signature restored and sin/cos no longer in
the Pfaffian family, the sin barrier proof works as originally
structured (commit pre-086e464). No additional Khovanskii-rate axiom
is needed. -/

/-! ## Sin barrier — moved (2026-07-15)

`sin_not_in_eml_any_depth` used to live here, applying `PfaffianFunction.zero_bound`
(the axiom `zero_count_bound_classical`'s thin wrapper). Both have been deleted —
see `KhovanskiiLemma.lean`'s removal notes. The theorem now lives in
`EMLExplicitBoundSinBarrier.lean` (same name, re-proven via the constructive
`EMLExplicitBound.enc_combinedBound`), which imports this file for `eml_pfaffian`,
`EMLPfaffianValidOn`, and `eml_pfaffian_validon_from_sin_equality` — kept here since
they're still needed and moving them would risk an import cycle (that file necessarily
imports this one). -/

end MachLib
