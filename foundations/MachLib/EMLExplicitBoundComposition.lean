import MachLib.EMLExplicitBoundExpArm
import MachLib.EMLExplicitBoundLogArm
import MachLib.PfaffianExpLogRecipDescent
import MachLib.PfaffianAnalytic

/-!
# Explicit-K composition — threading exp/log/recip arms across chain depth

`combined_descent_3` (`PfaffianExpLogRecipDescent.lean`) assembles the base case, the exp/log arms,
and the (already-proven) reciprocal arm into one descent over the WHOLE chain depth `N`, dispatching
per level via the existential `IsExpLogRecipW c a b`. That existential is *parametrized by `(a, b)`* —
its recip-level witness `v`'s positivity (`hvcoh`/`hvpos`) genuinely depends on the interval — so
extracting witnesses from it via `Classical.choice` inside a `Nat`-valued bound definition would risk
making the resulting bound secretly interval-dependent, defeating the entire point of the explicit-K
refactor (this is exactly why `∃K` wasn't enough for `sin/cos_not_in_eml` in the first place).

The fix: don't consume `IsExpLogRecipW` for the explicit path. The CONCRETE encoder (`EMLEncoder.lean`,
`enc`/`encEmlStepR`/`stepCC`/`stepCD`) already builds its chain — and every level's type/witness data —
purely from the EML tree, with NO `(a, b)` dependence anywhere in the chain's construction; only the
*validity* certificates (coherence, positivity, `LogArgPos`) are re-derived per interval. So the natural
explicit interface takes the per-level type tag and witness as EXPLICIT STRUCTURAL data (`ChainTypeTag`/
`ChainTags`, mirroring exactly how `exp_step_general_explicit`/`log_step_general_explicit` already take
`G`/`h_reltop` as plain hypotheses rather than existentials) — which is also a direct match for how `enc`
will eventually supply this data once this file re-routes onto it.

Triangularity is threaded via the chain-wide, `(a,b)`-independent `PfaffianChain.IsTriangular` (already in
`PfaffianChain.lean`) rather than per-level, since the recip arm's `recip_arm_explicit` doesn't need a
relation-shape fact at all (only `v`'s own properties) — its zero-count reduction is a pure
change-of-variables that never inspects `c.relations top`'s syntax.
-/

namespace MachLib.EMLExplicitBound

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpRecip
open MachLib.PfaffianExpRecipW
open MachLib.PolynomialRootCount

/-! ## Structural chain typing (explicit, `(a,b)`-independent witnesses) -/

/-- The top level's type: exponential (witness `G`, relation `G · y_top`), logarithmic (no witness,
relation top-free), or reciprocal (witness `v`, the eval-reciprocal companion — `recip_arm_explicit`'s
zero-count reduction needs only `v`'s own properties, not the relation's shape). -/
inductive ChainTypeTag (k : Nat) : Type
  | expTag (G : MultiPoly (k + 1)) : ChainTypeTag k
  | logTag : ChainTypeTag k
  | recipTag (v : MultiPoly (k + 1)) : ChainTypeTag k

/-- A full stack of type tags, one per level from depth `N` down to `1` (depth `0` needs none). -/
def ChainTags : Nat → Type
  | 0 => Unit
  | k + 1 => ChainTypeTag k × ChainTags k

/-- The `(a,b)`-INDEPENDENT structural facts a tag must satisfy: for `expTag`, the relation shape and
`G`'s own top-freedom; for `logTag`, the relation's top-freedom; for `recipTag`, `v`'s top-freedom
(`hvtf`, degree `0` at and above the top index). -/
def ChainTagValid {k : Nat} (c : PfaffianChain (k + 1)) : ChainTypeTag k → Prop
  | .expTag G => MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) G = 0
      ∧ c.relations (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
          = MultiPoly.mul G (MultiPoly.varY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)))
  | .logTag => MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
      (c.relations (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))) = 0
  | .recipTag v => ∀ j : Fin (k + 1), k ≤ j.val → MultiPoly.degreeY j v = 0

/-- The `(a,b)`-DEPENDENT eval facts a tag must satisfy on `(a,b)`: for `expTag`, the top variable is
non-vanishing (`hyt`); for `logTag`, nothing further; for `recipTag`, the reciprocal identity (`hvcoh`)
and positivity (`hvpos`). -/
def ChainTagValidAB {k : Nat} (c : PfaffianChain (k + 1)) (a b : Real) : ChainTypeTag k → Prop
  | .expTag _ => ∀ z, a < z → z < b →
      MultiPoly.eval (MultiPoly.varY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))) z (c.chainValues z) ≠ 0
  | .logTag => True
  | .recipTag v =>
      (∀ x : Real, a < x → x < b →
        c.evals (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) x * MultiPoly.eval v x (c.chainValues x) = 1)
      ∧ (∀ x : Real, a < x → x < b → 0 < MultiPoly.eval v x (c.chainValues x))

/-- All levels' structural validity, recursively down to depth `0`. -/
def ChainTagsValid : ∀ (N : Nat), PfaffianChain N → ChainTags N → Prop
  | 0, _, _ => True
  | _ + 1, c, (tag, tags) => ChainTagValid c tag ∧ ChainTagsValid _ (chainRestrict c) tags

/-- All levels' `(a,b)`-dependent validity, recursively down to depth `0`. -/
def ChainTagsValidAB : ∀ (N : Nat), PfaffianChain N → Real → Real → ChainTags N → Prop
  | 0, _, _, _, _ => True
  | _ + 1, c, a, b, (tag, tags) => ChainTagValidAB c a b tag ∧ ChainTagsValidAB _ (chainRestrict c) a b tags

/-! ## Structural lemmas: triangularity and coherence descend to `chainRestrict` -/

/-- **Triangularity descends to `chainRestrict`.** `(chainRestrict c).relations i = dropLastY
(c.relations ⟨i⟩)`, and `degreeY_dropLastY_le` never increases the degree at any OTHER index, so
`c`'s triangularity at the lifted indices transfers directly. -/
theorem chainRestrict_isTriangular {N : Nat} (c : PfaffianChain (N + 1))
    (hTri : c.IsTriangular) : (chainRestrict c).IsTriangular := by
  intro i j hij
  show MultiPoly.degreeY j (MultiPoly.dropLastY
      (c.relations (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)))) = 0
  have hle := MultiPoly.degreeY_dropLastY_le
    (c.relations (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1))) j
  have h0 := hTri (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1))
    (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (N + 1)) hij
  omega

/-- **Coherence descends to `chainRestrict`, given only triangularity** (not `IsExpChain`). Verbatim
`PfaffianGeneralReduce.chainRestrict_isCoherentOn`, but sourcing the top-freedom fact from
`c.IsTriangular` directly instead of an `IsExpChain` witness — the recip arm's zero-count reduction
never needs the relation's shape, so the composition should not need `IsExpChain` either. -/
theorem chainRestrict_isCoherentOn_tri {N : Nat} (c : PfaffianChain (N + 1))
    (hTri : c.IsTriangular) (a b : Real) (hcoh : c.IsCoherentOn a b) :
    (chainRestrict c).IsCoherentOn a b := by
  intro x hax hxb i
  show HasDerivAt (c.evals ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (MultiPoly.eval (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) x
      ((chainRestrict c).chainValues x)) x
  have hc := hcoh x hax hxb ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  have htop : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
      (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = 0 :=
    hTri ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) i.isLt
  have heval : MultiPoly.eval (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) x
        ((chainRestrict c).chainValues x)
      = MultiPoly.eval (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) x (c.chainValues x) := by
    have hrestrict : (chainRestrict c).chainValues x
        = (fun j => (c.chainValues x) ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) := by
      funext j; exact chainRestrict_chainValues c x j
    rw [hrestrict, MultiPoly.eval_dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) htop x
      (c.chainValues x)]
  rw [heval]; exact hc

/-! ## The explicit composed bound -/

/-- **The explicit composed bound.** Structural recursion on the chain depth `N`, dispatching on the
(literal, non-`Prop`) tag at each level: `expTag`/`logTag` invoke `expBoundE`/`logBoundE` at fuel
`degreeY_top p` (trivially `≤`-reflexive) over the depth-below combinator; `recipTag` passes straight
through to the restricted chain at `clearTop (dropLastY v) p` — the reciprocal arm is bound-preserving,
so no new term is added. Depth `0` is the base case's syntactic degree bound. -/
noncomputable def combinedBoundE : ∀ (N : Nat), PfaffianChain N → ChainTags N → MultiPoly N → Nat
  | 0, _, _, p => degreeUpper (mpoly0ToPoly p)
  | k + 1, c, (tag, tags), p =>
      match tag with
      | .expTag G =>
          expBoundE c G (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
            (fun r => combinedBoundE k (chainRestrict c) tags r)
            (MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) p) p
      | .logTag =>
          logBoundE c (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
            (fun r => combinedBoundE k (chainRestrict c) tags r)
            (MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) p) p
      | .recipTag v =>
          combinedBoundE k (chainRestrict c) tags
            (clearTop (MultiPoly.dropLastY v) p)

/-! ## The explicit three-way combined descent -/

set_option maxHeartbeats 4000000 in
/-- **The explicit three-way combined descent.** Explicit-`K` analog of
`PfaffianExpLogRecip.combined_descent_3`: induction on the chain depth `N`, dispatching per level on the
STRUCTURAL tag (not the existential `IsExpLogRecipW`) to `exp_step_general_explicit`,
`log_step_general_explicit`, or `recip_arm_explicit` — each producing EXACTLY `combinedBoundE`'s value at
that branch (by definitional unfolding of the `match` inside `combinedBoundE` itself), so every case
closes by `exact`, no `.mono`/domination needed. -/
theorem combined_descent_3_explicit (a b : Real) (hab : a < b) :
    ∀ (N : Nat) (c : PfaffianChain N) (tags : ChainTags N),
      ChainTagsValid N c tags → ChainTagsValidAB N c a b tags →
      c.IsTriangular → c.IsCoherentOn a b →
      (∀ r : MultiPoly N, IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) →
      ∀ (p : MultiPoly N),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn c p) a b (combinedBoundE N c tags p) := by
  intro N
  induction N with
  | zero =>
    intro c _tags _ _ _ _ _ p hne
    exact base_case_explicit a b hab c p hne
  | succ k ih =>
    intro c tags hValid hValidAB hTri hcoh hAn p hne
    obtain ⟨tag, tags'⟩ := tags
    obtain ⟨hTagValid, hTagsValid'⟩ := hValid
    obtain ⟨hTagValidAB, hTagsValidAB'⟩ := hValidAB
    have hTriR := chainRestrict_isTriangular c hTri
    have hcohR := chainRestrict_isCoherentOn_tri c hTri a b hcoh
    have hAnR := pfaffianChainFn_analytic_chainRestrict c (Icc a b) hAn
    have IH_ex : ∀ r : MultiPoly k,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn (chainRestrict c) r) a b
          (combinedBoundE k (chainRestrict c) tags' r) :=
      fun r hner => ih (chainRestrict c) tags' hTagsValid' hTagsValidAB' hTriR hcohR hAnR r hner
    have h_tri : ∀ j : Fin (k + 1), j ≠ (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) →
        MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) (c.relations j) = 0 := by
      intro j hj
      have hjlt : j.val < k := by
        rcases Nat.lt_or_ge j.val k with h' | h'
        · exact h'
        · exact absurd (Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp j.isLt) h')) hj
      exact hTri j (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) hjlt
    match tag, hTagValid, hTagValidAB with
    | .expTag G, ⟨hG, hrel⟩, hyt =>
      exact exp_step_general_explicit c a b hab hcoh G hrel hG h_tri hyt
        (fun r => combinedBoundE k (chainRestrict c) tags' r) IH_ex hAn
        (MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) p) p (Nat.le_refl _) hne
    | .logTag, h_top, _ =>
      exact log_step_general_explicit c a b hab hcoh h_top h_tri
        (fun r => combinedBoundE k (chainRestrict c) tags' r) IH_ex hAn
        (MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) p) p (Nat.le_refl _) hne
    | .recipTag v, hvtf, ⟨hvcoh, hvpos⟩ =>
      have hvN : MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) v = 0 :=
        hvtf (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) (Nat.le_refl k)
      have heval : ∀ x : Real, MultiPoly.eval (MultiPoly.dropLastY v) x
            ((chainRestrict c).chainValues x) = MultiPoly.eval v x (c.chainValues x) :=
        fun x => MultiPoly.eval_dropLastY v hvN x (c.chainValues x)
      have hvpos_r : ∀ x : Real, a < x → x < b →
          0 < MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) :=
        fun x hxa hxb => by rw [heval x]; exact hvpos x hxa hxb
      have hwitness : ∀ x : Real, a < x → x < b →
          c.chainValues x (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
            = 1 / MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) := by
        intro x hxa hxb
        have hw := ne_of_gt (hvpos_r x hxa hxb)
        have hcoh1 : c.evals (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) x
            * MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) = 1 := by
          rw [heval x]; exact hvcoh x hxa hxb
        show c.evals (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) x
            = 1 / MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x)
        rw [← hcoh1, mul_comm, mul_div_cancel_left' hw]
      have hnv := clearTop_nonvanishing c (MultiPoly.dropLastY v) a b hwitness hvpos_r p hne
      exact recip_arm_explicit c a b v hvtf hvcoh hvpos p _ (IH_ex (clearTop (MultiPoly.dropLastY v) p) hnv)

end MachLib.EMLExplicitBound
