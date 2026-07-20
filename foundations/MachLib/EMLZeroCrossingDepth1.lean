import MachLib.MonotoneFromDeriv
import MachLib.SinNotInEML
import MachLib.Log
import MachLib.Linarith
import MachLib.FieldLemmas
import MachLib.MultiVarBucket

/-!
# The zero-crossing induction, base case: `eml var var`, with NO validity assumption

Continuation of path (1) (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). The strategy traced in
`EMLExplicitBoundGlue.lean` needs a strong induction on tree depth bounding zero-CROSSINGS of an
arbitrary tree, without assuming its own `EMLPfaffianValidOn`. This file attempts the base case:
depth-1 trees, where the classic Pfaffian-chain encoder isn't needed at all — elementary
calculus (Rolle/MVT, both already in the codebase) suffices directly, because a depth-1 tree's
right child is a bare leaf, so its sign pattern is either constant (`const`) or a single
crossing at `x=0` (`var`) — known in closed form, not something that itself needs a recursive
validity argument.

**The hardest of the four depth-1 shapes, worked through completely.** `t = eml var var`:
`t.eval x = exp(x) - log(x)` for `x>0` (clamps to `exp(x)` for `x≤0`, where it's `>0` always, so
zero-free there). On `x>0`: `t`'s derivative is `exp(x) - 1/x`; THAT function's own derivative is
`exp(x) + 1/x²`, manifestly positive, so `exp(x)-1/x` is strictly monotonic
(`strictMono_of_deriv_pos`, MVT-based, already in `MonotoneFromDeriv.lean`) — hence injective,
hence has at most one zero. Feed that into `zero_count_bound_by_deriv` (Rolle's theorem,
`Rolle.lean`) to get: `exp(x)-log(x)` has at most `1+1=2` zeros on any `(0,B)`. Combined with
"zero zeros on `x≤0`" (trivial), `eml var var`'s full evaluation has boundedly many zeros on ANY
interval — proved WITHOUT ever invoking `EMLPfaffianValidOn`, `LogArgPosOn`, or the Pfaffian-chain
encoder at all.

**Scope, honestly.** This is the base case of a depth-based induction, for the single hardest of
four depth-1 shapes (the other three — both leaves constant, or one leaf `var`/one `const` — are
easier variants of the same technique: injectivity of `exp` or `log` alone, no second-derivative
step needed). The INDUCTIVE STEP — compound `t1`/`t2`, needing the full "split by every internal
log-node's sign, recurse" strategy sketched in `EMLExplicitBoundGlue.lean` — is not attempted
here. This is one confirmed brick of a foundation, not the foundation.
-/

namespace MachLib
namespace Real

/-- **At most one zero from pairwise strict monotonicity on an open interval.** If `f x < f y`
whenever `c < x < y < d`, any nodup list of `f`'s zeros in `(c,d)` has length `≤ 1` — two
distinct zeros would force `f` of one to be less than `f` of the other, contradicting both being
`0`. -/
theorem atMostOneZero_of_strictMono {f : Real → Real} {c d : Real}
    (hmono : ∀ x y : Real, c < x → x < d → c < y → y < d → x < y → f x < f y) :
    ∀ zeros : List Real, zeros.Nodup → (∀ z ∈ zeros, c < z ∧ z < d ∧ f z = 0) → zeros.length ≤ 1
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: ys, hnd, hz => by
      exfalso
      have hxin := hz x (List.mem_cons_self _ _)
      have hyin := hz y (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
      have hxney : x ≠ y := by
        have h := List.nodup_cons.mp hnd
        exact fun h' => h.1 (h' ▸ List.mem_cons_self _ _)
      rcases lt_total x y with hlt | heq | hgt
      · have hlt' := hmono x y hxin.1 hxin.2.1 hyin.1 hyin.2.1 hlt
        rw [hxin.2.2, hyin.2.2] at hlt'
        exact lt_irrefl_ax 0 hlt'
      · exact hxney heq
      · have hlt' := hmono y x hyin.1 hyin.2.1 hxin.1 hxin.2.1 hgt
        rw [hxin.2.2, hyin.2.2] at hlt'
        exact lt_irrefl_ax 0 hlt'

/-- `(fun y => exp y - 1/y)`'s derivative at any `x > 0` is `exp x - (-1/(x*x))` — via
`HasDerivAt_inv` on the identity function for the `1/y` piece. -/
theorem hasDerivAt_exp_sub_inv (x : Real) (hx : 0 < x) :
    HasDerivAt (fun y => Real.exp y - 1 / y) (Real.exp x - (-1 / (x * x))) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hinv : HasDerivAt (fun y => 1 / y) (-1 / (x * x)) x := by
    have h := HasDerivAt_inv (fun y => y) 1 x hxne (HasDerivAt_id x)
    have e : -1 / (x * x) = -(1 : Real) / (x * x) := by mach_ring
    rw [e]; exact h
  exact HasDerivAt_sub Real.exp (fun y => 1 / y) (Real.exp x) (-1 / (x * x)) x
    (HasDerivAt_exp x) hinv

/-- The derivative value `exp x - (-1/(x*x))` is strictly positive for `x > 0` — it equals
`exp x + 1/(x*x)`, a sum of two positives. -/
theorem exp_sub_inv_deriv_pos (x : Real) (hx : 0 < x) :
    0 < Real.exp x - (-1 / (x * x)) := by
  have hxx : (0 : Real) < x * x := mul_pos hx hx
  have hxxne : x * x ≠ 0 := ne_of_gt hxx
  have hinv_pos : (0 : Real) < 1 / (x * x) := div_pos_of_pos_pos zero_lt_one_ax hxx
  have e : (-1 : Real) / (x * x) = -(1 / (x * x)) := (neg_div hxxne).symm
  have e2 : Real.exp x - (-1 / (x * x)) = Real.exp x + 1 / (x * x) := by
    rw [e]; mach_ring
  rw [e2]
  exact add_pos (Real.exp_pos x) hinv_pos

/-- **`exp x - 1/x` has at most one zero on any `(0,B)`.** Its own derivative is manifestly
positive throughout `(0,∞)`, so it is strictly monotonic (MVT) hence injective hence has at
most one zero. -/
theorem exp_sub_inv_atMostOneZero (B : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, 0 < z ∧ z < B ∧ Real.exp z - 1 / z = 0) → zeros.length ≤ 1 := by
  apply atMostOneZero_of_strictMono
  intro x y _hx0 _hxB hy0 _hyB hxy
  apply strictMono_of_deriv_pos (fun y => Real.exp y - 1 / y) x y hxy
  · intro c hxc hcy
    have hc0 : 0 < c := lt_of_lt_of_le _hx0 hxc
    exact ⟨_, hasDerivAt_exp_sub_inv c hc0⟩
  · intro c f' hxc hcy hderiv
    have hc0 : 0 < c := lt_of_lt_of_le _hx0 hxc
    rw [HasDerivAt_unique _ _ _ c hderiv (hasDerivAt_exp_sub_inv c hc0)]
    exact exp_sub_inv_deriv_pos c hc0

/-- **`exp x - log x` has at most two zeros on any `(0,B)`.** Rolle's theorem (`zero_count_bound_by_deriv`)
applied to the derivative bound above. -/
theorem exp_sub_log_atMostTwoZeros_pos (B : Real) (hB : 0 < B) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, 0 < z ∧ z < B ∧ Real.exp z - Real.log z = 0) → zeros.length ≤ 2 := by
  apply zero_count_bound_by_deriv (fun y => Real.exp y - Real.log y) 0 B hB
  · intro c hc0 hcB
    exact ⟨Real.exp c - 1 / c, HasDerivAt_sub Real.exp Real.log (Real.exp c) (1 / c) c
      (HasDerivAt_exp c) (HasDerivAt_log_pos c hc0)⟩
  · intro zeros_f' hnd hzf'
    apply exp_sub_inv_atMostOneZero B zeros_f' hnd
    intro z hzmem
    obtain ⟨hz0, hzB, f'', hderiv, hf''0⟩ := hzf' z hzmem
    have hderiv_eq : HasDerivAt (fun y => Real.exp y - Real.log y)
        (Real.exp z - 1 / z) z := HasDerivAt_sub Real.exp Real.log (Real.exp z) (1 / z) z
      (HasDerivAt_exp z) (HasDerivAt_log_pos z hz0)
    rw [HasDerivAt_unique _ _ _ z hderiv hderiv_eq] at hf''0
    exact ⟨hz0, hzB, hf''0⟩

/-- **`(eml var var).eval` has boundedly many zeros (`≤ 3`) on ANY interval `(a,b)`, with NO
`EMLPfaffianValidOn`/`LogArgPosOn` hypothesis at all.** Splits at `x=0`: zero zeros on `x ≤ 0`
(the clamp forces `eval = exp x > 0` there, unconditionally); at most two on `x>0` (the lemma
above); glued (`+1` for `x=0` itself, matching `BoundedZerosBy.glue`'s shape from
`EMLExplicitBoundGlue.lean`, inlined here since this file works with raw functions rather than
`PfaffianFn`). The concrete demonstration that the induction's base case does not need the
Pfaffian-chain machinery at all. -/
theorem eml_var_var_boundedZeros (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (EMLTree.eml EMLTree.var EMLTree.var).eval z = 0) →
      zeros.length ≤ 3 := by
  intro zeros hnd hz
  haveI : DecidableEq Real := fun x y => Classical.propDecidable (x = y)
  have hle_bound : (zeros.filter (fun z => decide (z ≤ 0))).length ≤ 0 := by
    have hempty : zeros.filter (fun z => decide (z ≤ 0)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hzmem hzle
      have hzle' : z ≤ 0 := of_decide_eq_true hzle
      obtain ⟨_, _, hfz⟩ := hz z hzmem
      have hcl : (EMLTree.eml EMLTree.var EMLTree.var).eval z = Real.exp z := by
        show Real.exp z - Real.log z = Real.exp z
        rw [Real.log_nonpos hzle']; exact sub_zero _
      rw [hcl] at hfz
      exact lt_irrefl_ax 0 (hfz ▸ Real.exp_pos z)
    rw [hempty]; simp
  have hnd_hi : (zeros.filter (fun z => !decide (z ≤ 0))).Nodup := hnd.filter _
  have hgt_bound : (zeros.filter (fun z => !decide (z ≤ 0))).length ≤ 2 := by
    rcases lt_total 0 b with hb | hb | hb
    · apply exp_sub_log_atMostTwoZeros_pos b hb _ hnd_hi
      intro z hzmem
      rw [List.mem_filter] at hzmem
      obtain ⟨hzz, hzgt⟩ := hzmem
      have hzgt' : 0 < z := by
        have := of_decide_eq_false (show decide (z ≤ 0) = false by simpa using hzgt)
        rcases lt_total z 0 with h | h | h
        · exact absurd (le_of_lt h) this
        · exact absurd (h ▸ le_refl (0:Real)) this
        · exact h
      obtain ⟨_, hzb, hfz⟩ := hz z hzz
      exact ⟨hzgt', hzb, hfz⟩
    · have hempty : zeros.filter (fun z => !decide (z ≤ 0)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hzmem hzgt
        obtain ⟨_, hzb, _⟩ := hz z hzmem
        have : z < 0 := hb ▸ hzb
        have hzle : z ≤ 0 := le_of_lt this
        have : decide (z ≤ 0) = true := decide_eq_true hzle
        simp [this] at hzgt
      rw [hempty]; simp
    · have hempty : zeros.filter (fun z => !decide (z ≤ 0)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hzmem hzgt
        obtain ⟨_, hzb, _⟩ := hz z hzmem
        have hzlt0 : z < 0 := lt_trans_ax hzb hb
        have hzle : z ≤ 0 := le_of_lt hzlt0
        have : decide (z ≤ 0) = true := decide_eq_true hzle
        simp [this] at hzgt
      rw [hempty]; simp
  have hpart : (zeros.filter (fun z => decide (z ≤ 0))).length
      + (zeros.filter (fun z => !decide (z ≤ 0))).length = zeros.length :=
    MultiVarMod.length_filter_partition (fun z => decide (z ≤ 0)) zeros
  omega

end Real
end MachLib
