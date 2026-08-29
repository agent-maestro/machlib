import MachLib.AnalyticFiniteZerosReal
import MachLib.EMLAnalyticDischarge

/-!
# Vanishing on one subinterval of a ray forces vanishing on the whole ray

The shared gap under `EMLQueryGermTerm` and `EMLQueryGermNegBranch`. Both produce an
**interval-local** zero bound, because `encBound_bounds` needs a nonzero witness *inside* `(a,b)`,
and `¬ EvZeroF` gives non-vanishing only eventually — arbitrarily far out, not inside a nominated
bounded interval. Composing them into `UniformZeroBoundFrom` needs the missing direction:

> if the tree vanishes identically on **some** subinterval of the ray, it is `EvZeroF`.

Contrapositively: `¬ EvZeroF` plus log-positivity on the ray gives a nonzero point in **every**
subinterval, which is exactly the per-interval witness both branches were assuming.

## The axiom cost, measured rather than assumed

`analytic_zero_on_subinterval_imp_zero` (`AnalyticFiniteZerosReal`) is a **theorem**, derived from
`analytic_finite_zeros_compact` — not a fresh analytic assumption. Good.

**But this is not free for the query-germ branches, and I first wrote that it was.** Measured
footprints:

```
exists_nonzero_in_subinterval   analytic_finite_zeros_compact, eml_tree_analytic_on_interval
queryTerm_zero_bound            analytic_finite_zeros_compact, analytic_ne_zero_nbhd, rolle_ct
```

`eml_tree_analytic_on_interval` is **not** in the positive branch's footprint. It is a pinned corpus
axiom, used elsewhere in this lane (`EMLAnalyticDischarge`), but composing this lemma with either
branch will **add one axiom to that branch's footprint**. The total pinned count does not move — 243
is unchanged — but the *branch* gets strictly more trusting, and that is the number a reader of those
theorems cares about.

Stated because I claimed the opposite before checking, which is this arc's recurring error in its
smallest form: an optimistic guess about cost, one `#print axioms` away from being settled.

## The argument

Suppose `t` vanishes on `(p, q)` with `X ≤ p < q`. For any `x ≥ q`, take the interval `(p, x + 2)`:
log-positivity holds there (it holds on every interval at or beyond `X`), so `t.eval` is analytic on
`Icc m (x+1)` for any `m` strictly inside. Choose `m` strictly between `p` and `q`
(`exists_between`); then `t` vanishes on `Ioo m q`, a nonempty subinterval of `Icc m (x+1)`, so the
identity theorem gives vanishing on all of `Ioo m (x+1)` — which contains `x`.

The `+2`/`+1` are not slack: `eml_tree_analytic_on_interval` is stated **strictly inside** the
interval it is given, because analyticity at a point needs a neighbourhood while `LogArgPos` only
controls the open interval. So the analytic window has to be opened wider than the point being
reached.
-/

namespace MachLib

open Real

/-- `a < a + 1`. **A fifth private copy**, and worth a line of complaint: `EMLZeroBoundRay`,
`EMLAnalyticDischarge`, `EMLDepthTameness` (as `lt_succ_self`) and `EMLZeroBoundAssembly` each carry
their own, all `private`, so none can be reused. A lemma this trivial being re-proved five times is
not a cost worth chasing — but it is a small standing argument for making such helpers public, since
`private` guarantees the next module writes it again. -/
private theorem lt_add_one' (a : Real) : a < a + 1 := by
  have v := add_lt_add_left zero_lt_one_ax a
  have e : a + (0 : Real) = a := by mach_ring
  rw [e] at v; exact v

/-- **The ray identity theorem for EML trees.** Vanishing on one subinterval of a ray forces
`EvZeroF`. -/
theorem evZeroF_of_vanishes_on_subinterval (t : EMLTree) (X : Real) (hX1 : 1 ≤ X)
    (hpos : ∀ a b : Real, X ≤ a → a < b → LogArgPos t a b)
    (p q : Real) (hXp : X ≤ p) (hpq : p < q)
    (hzero : ∀ x : Real, p < x → x < q → t.eval x = 0) :
    EvZeroF t.eval := by
  obtain ⟨m, hpm, hmq⟩ := exists_between p q hpq
  refine ⟨q, le_trans hX1 (le_trans hXp (le_of_lt hpq)), ?_⟩
  intro x hxq
  -- open the analytic window strictly wider than `x`
  have hx1 : x < x + 1 := lt_add_one' x
  have hx2 : x + 1 < x + 1 + 1 := lt_add_one' (x + 1)
  have hpx2 : p < x + 1 + 1 :=
    lt_of_lt_of_le hpq (le_trans hxq (le_trans (le_of_lt hx1) (le_of_lt hx2)))
  have hlog : LogArgPos t p (x + 1 + 1) := hpos p (x + 1 + 1) hXp hpx2
  have hanalytic : IsAnalyticOnReals t.eval (Icc m (x + 1)) :=
    eml_tree_analytic_on_interval t p (x + 1 + 1) hlog m (x + 1) hpm hx2
  -- `t` vanishes on `Ioo m q`, a nonempty subinterval of `Icc m (x+1)`
  have hmx1 : m < x + 1 := lt_of_lt_of_le hmq (le_trans hxq (le_of_lt hx1))
  have hqx1 : q ≤ x + 1 := le_trans hxq (le_of_lt hx1)
  have hsub : ∀ y : Real, Ioo m q y → t.eval y = 0 := by
    intro y hy
    exact hzero y (lt_trans_ax hpm hy.1) hy.2
  have hall := analytic_zero_on_subinterval_imp_zero t.eval m (x + 1) m q
    (le_refl m) hqx1 hmq hmx1 hanalytic hsub
  exact hall x ⟨lt_of_lt_of_le hmq hxq, hx1⟩

/-- **The contrapositive, in the form the query-germ branches need.** A tree that is not eventually
zero has a nonzero point in **every** subinterval of the ray — which is precisely the per-interval
witness `encBound_bounds` demands and `¬ EvZeroF` does not directly give. -/
theorem exists_nonzero_in_subinterval (t : EMLTree) (X : Real) (hX1 : 1 ≤ X)
    (hpos : ∀ a b : Real, X ≤ a → a < b → LogArgPos t a b)
    (hne : ¬ EvZeroF t.eval)
    (p q : Real) (hXp : X ≤ p) (hpq : p < q) :
    ∃ z : Real, p < z ∧ z < q ∧ t.eval z ≠ 0 := by
  rcases Classical.em (∃ z : Real, p < z ∧ z < q ∧ t.eval z ≠ 0) with h | h
  · exact h
  · exact absurd (evZeroF_of_vanishes_on_subinterval t X hX1 hpos p q hXp hpq
      (fun y h1 h2 => by
        rcases Classical.em (t.eval y = 0) with hy | hy
        · exact hy
        · exact absurd ⟨y, h1, h2, hy⟩ h)) hne

end MachLib
