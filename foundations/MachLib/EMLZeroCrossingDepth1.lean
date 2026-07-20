import MachLib.MonotoneFromDeriv
import MachLib.SinNotInEML
import MachLib.Log
import MachLib.Linarith
import MachLib.FieldLemmas
import MachLib.MultiVarBucket

/-!
# The zero-crossing induction, base case COMPLETE: all four depth-1 shapes, NO validity assumption

Continuation of path (1) (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). The strategy traced in
`EMLExplicitBoundGlue.lean` needs a strong induction on tree depth bounding zero-CROSSINGS of an
arbitrary tree, without assuming its own `EMLPfaffianValidOn`. This file closes the base case:
depth-1 trees, where the classic Pfaffian-chain encoder isn't needed at all — elementary
calculus suffices directly, because a depth-1 tree's right child is a bare leaf, so its sign
pattern is either constant (`const`) or a single crossing at `x=0` (`var`) — known in closed
form, not something that itself needs a recursive validity argument.

**All four depth-1 shapes, worked through completely.**
- `eml var var` (the hardest): `t.eval x = exp(x) - log(x)` for `x>0` (clamps to `exp(x) > 0` for
  `x≤0`, zero-free there). On `x>0`, the derivative `exp(x)-1/x` has its OWN derivative
  `exp(x)+1/x²` manifestly positive, so it is strictly monotonic (`strictMono_of_deriv_pos`, MVT-
  based, already in `MonotoneFromDeriv.lean`) hence injective hence at most one zero; Rolle's
  theorem (`zero_count_bound_by_deriv`, `Rolle.lean`) lifts that to at most `2` zeros for
  `exp(x)-log(x)` itself. Glued with the `x≤0` region: `≤3` total.
- `eml (const c1) (const c2)`: a genuine constant (`exp c1 - log c2`, no clamp-region split at
  all — `log c2`'s value doesn't depend on `x`); given non-degeneracy, `0` zeros.
- `eml var (const c2)`: `exp(x) - log(c2)`, again no clamp split; `exp`'s own injectivity
  (`exp_lt`) gives at most `1` zero, no derivative work needed.
- `eml (const c1) var`: `exp(c1) - log(x)` for `x>0` (clamps to `exp(c1) > 0` for `x≤0`); `log`'s
  own injectivity on positives (`log_lt_log`) gives at most `1` zero there, `≤3` total after the
  same clamp-region glue as `eml var var`.

Each of the last three needed only injectivity of `exp` or `log` (both already axioms/theorems in
the codebase) — no second-derivative argument, no new machinery — confirming the base case really
was as tractable as the first (`eml var var`) case suggested.

**Scope, honestly.** This closes ALL of depth-1 — a complete base case, not one illustrative
shape. The INDUCTIVE STEP — compound `t1`/`t2`, needing the full "split by every internal
log-node's sign, recurse" strategy sketched in `EMLExplicitBoundGlue.lean` — is not attempted
here. This is a complete foundation for an induction, not the induction itself.
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

/-- **At most one zero from pairwise injectivity on an open interval.** Generalizes
`atMostOneZero_of_strictMono` to `f x ≠ f y` directly (not requiring a fixed direction of
inequality) — covers both increasing and decreasing functions uniformly, needed for the depth-1
shapes below where the natural witness is `exp`/`log` injectivity, not a derivative-sign
argument. -/
theorem atMostOneZero_of_injOn {f : Real → Real} {c d : Real}
    (hinj : ∀ x y : Real, c < x → x < d → c < y → y < d → x < y → f x ≠ f y) :
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
      have hfeq : f x = f y := hxin.2.2.trans hyin.2.2.symm
      rcases lt_total x y with hlt | heq | hgt
      · exact (hinj x y hxin.1 hxin.2.1 hyin.1 hyin.2.1 hlt) hfeq
      · exact hxney heq
      · exact (hinj y x hyin.1 hyin.2.1 hxin.1 hxin.2.1 hgt) hfeq.symm

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

/-! ## The other three depth-1 shapes — no derivative work needed, `exp`/`log` injectivity alone -/

/-- **`eml (const c1) (const c2)`: zero or infinitely many zeros, no in-between.** A constant
function — `t.eval x = exp c1 - log c2` for every `x`, no clamp-region splitting at all (`log
c2`'s value, clamped or not, doesn't depend on `x`). Given the non-degenerate case
(`exp c1 ≠ log c2`), the constant is never `0`: zero zeros anywhere. -/
theorem eml_const_const_boundedZeros (c1 c2 : Real) (hne : Real.exp c1 ≠ Real.log c2)
    (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.const c1) (EMLTree.const c2)).eval z = 0) →
      zeros.length ≤ 0 := by
  intro zeros hnd hz
  match zeros with
  | [] => simp
  | x :: xs =>
      exfalso
      obtain ⟨_, _, hfx⟩ := hz x (List.mem_cons_self _ _)
      have hfx' : Real.exp c1 - Real.log c2 = 0 := hfx
      apply hne
      have e : Real.exp c1 = (Real.exp c1 - Real.log c2) + Real.log c2 := by mach_ring
      rw [hfx'] at e
      have e2 : (0 : Real) + Real.log c2 = Real.log c2 := by mach_ring
      rw [e2] at e
      exact e

/-- **`eml var (const c2)`: at most one zero, anywhere, via `exp`'s own injectivity.** `t.eval x
= exp(x) - log(c2)` for every `x` — again no clamp-region split (`log c2` is `x`-independent).
`exp` is strictly monotonic (`exp_lt`) hence injective, so `exp(x) = log(c2)` has at most one
solution. -/
theorem eml_var_const_boundedZeros (c2 : Real) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (EMLTree.eml EMLTree.var (EMLTree.const c2)).eval z = 0) →
      zeros.length ≤ 1 := by
  apply atMostOneZero_of_injOn
  intro x y _hxa _hxb _hya _hyb hxy hEq
  have hEq' : Real.exp x - Real.log c2 = Real.exp y - Real.log c2 := hEq
  have hExpEq : Real.exp x = Real.exp y := by
    have e1 : Real.exp x = (Real.exp x - Real.log c2) + Real.log c2 := by mach_ring
    have e2 : Real.exp y = (Real.exp y - Real.log c2) + Real.log c2 := by mach_ring
    rw [e1, e2, hEq']
  have hlt : Real.exp x < Real.exp y := Real.exp_lt hxy
  rw [hExpEq] at hlt
  exact lt_irrefl_ax _ hlt

/-- **`eml (const c1) var`: at most three zeros, via `log`'s own injectivity plus the same
clamp-region split as `eml var var`.** `t.eval x = exp(c1) - log(x)` for `x>0` (clamps to
`exp(c1) > 0`, never zero, for `x≤0`). `log` is strictly monotonic on positives (`log_lt_log`)
hence injective there, so `log(x) = exp(c1)` has at most one solution on `x>0`. -/
theorem eml_const_var_boundedZeros (c1 : Real) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (EMLTree.eml (EMLTree.const c1) EMLTree.var).eval z = 0) →
      zeros.length ≤ 3 := by
  intro zeros hnd hz
  haveI : DecidableEq Real := fun x y => Classical.propDecidable (x = y)
  have hle_empty : zeros.filter (fun z => decide (z ≤ 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro z hzmem hzle
    have hzle' : z ≤ 0 := of_decide_eq_true hzle
    obtain ⟨_, _, hfz⟩ := hz z hzmem
    have hcl : (EMLTree.eml (EMLTree.const c1) EMLTree.var).eval z = Real.exp c1 := by
      show Real.exp c1 - Real.log z = Real.exp c1
      rw [Real.log_nonpos hzle']; exact sub_zero _
    rw [hcl] at hfz
    exact lt_irrefl_ax 0 (hfz ▸ Real.exp_pos c1)
  have hnd_hi : (zeros.filter (fun z => !decide (z ≤ 0))).Nodup := hnd.filter _
  have hgt_bound : (zeros.filter (fun z => !decide (z ≤ 0))).length ≤ 1 := by
    apply atMostOneZero_of_injOn (c := 0) (d := b)
    · intro x y hx0 _hxb hy0 _hyb hxy hEq
      have hEq' : Real.exp c1 - Real.log x = Real.exp c1 - Real.log y := hEq
      have hLogEq : Real.log x = Real.log y := by
        have e1 : Real.log x = Real.exp c1 - (Real.exp c1 - Real.log x) := by mach_ring
        have e2 : Real.log y = Real.exp c1 - (Real.exp c1 - Real.log y) := by mach_ring
        rw [e1, e2, hEq']
      have hlt : Real.log x < Real.log y := log_lt_log hx0 hxy
      rw [hLogEq] at hlt
      exact lt_irrefl_ax _ hlt
    · exact hnd_hi
    · intro z hzmem
      rw [List.mem_filter] at hzmem
      obtain ⟨hzz, hzgt⟩ := hzmem
      have hzgt' : 0 < z := by
        have hne0 := of_decide_eq_false (show decide (z ≤ 0) = false by simpa using hzgt)
        rcases lt_total z 0 with h | h | h
        · exact absurd (le_of_lt h) hne0
        · exact absurd (h ▸ le_refl (0 : Real)) hne0
        · exact h
      obtain ⟨_, hzb, hfz⟩ := hz z hzz
      exact ⟨hzgt', hzb, hfz⟩
  have hpart : (zeros.filter (fun z => decide (z ≤ 0))).length
      + (zeros.filter (fun z => !decide (z ≤ 0))).length = zeros.length :=
    MultiVarMod.length_filter_partition (fun z => decide (z ≤ 0)) zeros
  rw [hle_empty] at hpart
  have hlen_nil : ([] : List Real).length = 0 := rfl
  rw [hlen_nil] at hpart
  omega

end Real
end MachLib
