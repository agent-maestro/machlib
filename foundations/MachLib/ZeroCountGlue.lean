import MachLib.MultiVarBucket

/-!
# Counting zeros in an interval, and gluing the counts

Three of this corpus's zero-counting predicates are the same statement wearing different types:

```
BoundedZerosBy f a b K    (EMLExplicitBound)   -- f : PfaffianFn, one interval
UniformZeroBound f N      (EMLZeroBoundRay)    -- f : Real → Real, EVERY interval
UniformZeroBoundFrom f R N                     -- f : Real → Real, every interval past R
```

All three unfold to *"every duplicate-free list of points in the interval at which a predicate holds
is at most `K` long"*. `ZeroCountOn` is that statement with the predicate left abstract, so a lemma
proved once here serves all three — `BoundedZerosBy f a b K` is `ZeroCountOn (f.eval · = 0) a b K`
definitionally, and `UniformZeroBound f N` is `∀ a b, a < b → ZeroCountOn (f · = 0) a b N`.

## The glue, and why the `+ 1` is not slack

`ZeroCountOn.glue` splits a zero list at a midpoint into `< m`, `= m` and `> m`. The middle slice has
at most one element by `Nodup`, and it is genuinely needed: `m` itself lies in neither open piece, so
a zero sitting exactly on a cut is invisible to both and must be paid for once per cut. Over `n`
cuts that is `(n + 1) * K + n`, and the `+ n` is that payment.

The proof is the one `EMLExplicitBound.BoundedZerosBy.glue` carried, generalised beside it rather
than restated: `length_filter_partition` (`MultiVarBucket`) does the counting, and nothing here
touches analysis, Pfaffian chains or `EMLTree`. This module imports `MultiVarBucket` and nothing
else.

## What the cut list is for

`OneQueryLevelSet` needs a bound on *every* interval for a germ whose defining tree changes at the
poles of its rational argument. Those poles are finitely many and computed from the germ alone, so
they are the cut list, and `glueList` is what turns per-piece bounds into the interval-independent
one. `PiecesBounded` is deliberately the *weak* hypothesis — a bound on each named piece, not on
every interval — and `piecesBounded_is_weaker_than_the_conclusion` pins that difference with a
witness, because the first draft of `glueList` assumed the strong form and was therefore vacuous.
-/

namespace MachLib

open Real
open MachLib.MultiVarMod

/-- Zeros of a *predicate* in an open interval, counted. `BoundedZerosBy` is the `PfaffianFn`
instance of this and `UniformZeroBound` is the all-intervals quantification of it. -/
def ZeroCountOn (p : Real → Prop) (a b : Real) (K : Nat) : Prop :=
  ∀ zeros : List Real, zeros.Nodup →
    (∀ z ∈ zeros, a < z ∧ z < b ∧ p z) → zeros.length ≤ K

private theorem lt_add_one_r' (a : Real) : a < a + 1 := by
  have v := add_lt_add_left zero_lt_one_ax a
  have e : a + 0 = a := by mach_ring
  rw [e] at v; exact v

private theorem length_le_one_of_forall_eq' {v : Real} :
    ∀ l : List Real, l.Nodup → (∀ x ∈ l, x = v) → l.length ≤ 1
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: ys, hnd, hmem => by
      exfalso
      have hx : x = v := hmem x (List.mem_cons_self)
      have hy : y = v := hmem y (List.mem_cons_of_mem _ (List.mem_cons_self))
      have hxy : x = y := hx.trans hy.symm
      have hxney : x ≠ y := by
        have := List.nodup_cons.mp hnd
        exact fun h => this.1 (h ▸ List.mem_cons_self)
      exact hxney hxy

/-- **Gluing a zero count across a midpoint, for an arbitrary predicate.** -/
theorem ZeroCountOn.glue {p : Real → Prop} {a m b : Real} {K1 K2 : Nat}
    (hK1 : ZeroCountOn p a m K1) (hK2 : ZeroCountOn p m b K2) :
    ZeroCountOn p a b (K1 + K2 + 1) := by
  haveI : DecidableEq Real := fun x y => Classical.propDecidable (x = y)
  intro zeros hnd hz
  have hlo_bound : (zeros.filter (fun z => decide (z < m))).length ≤ K1 := by
    apply hK1 _ (hnd.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    obtain ⟨hzz, hzlt⟩ := hzmem
    obtain ⟨hza, _, hfz⟩ := hz z hzz
    exact ⟨hza, of_decide_eq_true hzlt, hfz⟩
  have hnd_hi : (zeros.filter (fun z => !decide (z < m))).Nodup := hnd.filter _
  have heqm_bound :
      ((zeros.filter (fun z => !decide (z < m))).filter (fun z => decide (z = m))).length ≤ 1 := by
    apply length_le_one_of_forall_eq' _ (hnd_hi.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    exact of_decide_eq_true hzmem.2
  have hgtm_bound : ((zeros.filter (fun z => !decide (z < m))).filter
      (fun z => !decide (z = m))).length ≤ K2 := by
    apply hK2 _ (hnd_hi.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    obtain ⟨hzhi, hzne⟩ := hzmem
    rw [List.mem_filter] at hzhi
    obtain ⟨hzz, hzge⟩ := hzhi
    obtain ⟨_, hzb, hfz⟩ := hz z hzz
    have hzgem : ¬ z < m := of_decide_eq_false (by simpa using hzge)
    have hzneqm : z ≠ m := of_decide_eq_false (by simpa using hzne)
    have hzgtm : m < z := by
      rcases lt_total m z with h | h | h
      · exact h
      · exact absurd h.symm hzneqm
      · exact absurd h hzgem
    exact ⟨hzgtm, hzb, hfz⟩
  have hpart_lo : (zeros.filter (fun z => decide (z < m))).length
      + (zeros.filter (fun z => !decide (z < m))).length = zeros.length :=
    length_filter_partition (fun z => decide (z < m)) zeros
  have hpart_hi : ((zeros.filter (fun z => !decide (z < m))).filter (fun z => decide (z = m))).length
      + ((zeros.filter (fun z => !decide (z < m))).filter (fun z => !decide (z = m))).length
      = (zeros.filter (fun z => !decide (z < m))).length :=
    length_filter_partition (fun z => decide (z = m)) (zeros.filter (fun z => !decide (z < m)))
  omega

/-- A wider interval's count bounds a narrower one's. -/
theorem ZeroCountOn.mono {p : Real → Prop} {a b a' b' : Real} {K : Nat}
    (ha : a ≤ a') (hb : b' ≤ b) (h : ZeroCountOn p a b K) : ZeroCountOn p a' b' K :=
  fun zeros hnd hz => h zeros hnd (fun z hzm =>
    ⟨lt_of_le_of_lt ha (hz z hzm).1, lt_of_lt_of_le (hz z hzm).2.1 hb, (hz z hzm).2.2⟩)

/-- **The pieces of `a < m₁ < … < b` are bounded, one by one.** The hypothesis a gluing theorem
actually needs: a bound on *each consecutive piece*, not on every interval.

Stating it as a recursion rather than as indexed access keeps the induction below free of any
sortedness or length bookkeeping — the chain structure *is* the list structure. -/
def PiecesBounded (p : Real → Prop) (K : Nat) : Real → List Real → Real → Prop
  | a, [],       b => ZeroCountOn p a b K
  | a, m :: rest, b => ZeroCountOn p a m K ∧ PiecesBounded p K m rest b

/-- **Gluing along a whole list of cut points.** `K` per piece over `n` cuts gives
`(n + 1) * K + n` overall: `n + 1` pieces, plus one for each cut point itself, which no open piece
counts.

The `+ n` is not slack. Each cut is a point the two adjacent open intervals both exclude, and a zero
can sit exactly there — `ZeroCountOn.glue`'s `+ 1` is that point, and it accumulates once per cut. -/
theorem ZeroCountOn.glueList {p : Real → Prop} {K : Nat} :
    ∀ (cuts : List Real) (a b : Real), PiecesBounded p K a cuts b →
      ZeroCountOn p a b ((cuts.length + 1) * K + cuts.length)
  | [], a, b, h => by
      have e : (([] : List Real).length + 1) * K + ([] : List Real).length = K := by simp
      rw [e]; exact h
  | m :: rest, a, b, h => by
      have hg := ZeroCountOn.glue h.1 (ZeroCountOn.glueList rest m b h.2)
      have hm : ((m :: rest).length + 1) * K = (rest.length + 1) * K + K := by
        rw [List.length_cons]
        exact Nat.succ_mul (rest.length + 1) K
      have e : K + ((rest.length + 1) * K + rest.length) + 1
             = ((m :: rest).length + 1) * K + (m :: rest).length := by
        rw [hm, List.length_cons]
        omega
      rw [← e]; exact hg

/-- **Discrimination: the hypothesis is strictly weaker than the conclusion.**

`PiecesBounded` over `n` cuts constrains `n + 1` *named* intervals; `ZeroCountOn p a b N` constrains
the whole of `(a,b)`, which contains intervals straddling every cut. A first draft of `glueList`
assumed `∀ u v, ZeroCountOn p u v K` instead — a bound on every interval, which is exactly
`UniformZeroBound` — so its hypothesis already implied its conclusion and the theorem said nothing.

This specimen makes that mistake un-repeatable: it exhibits a `PiecesBounded` at `K = 1` that holds
while `ZeroCountOn p a b 1` **fails**, so the two are not interchangeable and the draft's hypothesis
cannot be reintroduced without this failing to compile.

The predicate is the zero set of `(x - 1)·(x - 2)`, written directly as a predicate because only the
counting matters. Cut at `1`: the piece `(0,1)` holds no zero, `(1,3)` holds one, and `(0,3)` holds
two. -/
theorem piecesBounded_is_weaker_than_the_conclusion :
    ∃ (p : Real → Prop) (a m b : Real) (K : Nat),
      PiecesBounded p K a [m] b ∧ ¬ ZeroCountOn p a b K := by
  have h1 : (1 : Real) < 1 + 1 := lt_add_one_r' 1
  have h2 : (1 : Real) + 1 < 1 + 1 + 1 := lt_add_one_r' (1 + 1)
  have hne : (1 : Real) ≠ 1 + 1 := by
    intro h
    rw [← h] at h1
    exact lt_irrefl_ax 1 h1
  refine ⟨fun z => z = 1 ∨ z = 1 + 1, 0, 1, 1 + 1 + 1, 1, ⟨?_, ?_⟩, ?_⟩
  · -- `(0,1)` holds no zero at all
    intro zeros hnd hz
    cases zeros with
    | nil => exact Nat.zero_le 1
    | cons x _ =>
        exfalso
        obtain ⟨_, hx1, hp⟩ := hz x List.mem_cons_self
        rcases hp with h | h
        · have hlt : (1 : Real) < 1 := by rw [h] at hx1; exact hx1
          exact lt_irrefl_ax 1 hlt
        · have hlt : (1 : Real) + 1 < 1 := by rw [h] at hx1; exact hx1
          exact lt_irrefl_ax 1 (lt_trans_ax h1 hlt)
  · -- `(1,3)` holds only `2`
    intro zeros hnd hz
    refine length_le_one_of_forall_eq' (v := (1 : Real) + 1) zeros hnd (fun x hx => ?_)
    obtain ⟨h1x, _, hp⟩ := hz x hx
    rcases hp with h | h
    · have hlt : (1 : Real) < 1 := by rw [h] at h1x; exact h1x
      exact absurd hlt (lt_irrefl_ax 1)
    · exact h
  · -- but `(0,3)` holds both
    intro hbad
    have hmem : ∀ z ∈ [(1 : Real), 1 + 1], (0 : Real) < z ∧ z < 1 + 1 + 1 ∧ (z = 1 ∨ z = 1 + 1) := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact ⟨zero_lt_one_ax, lt_trans_ax h1 h2, Or.inl rfl⟩
      · rcases List.mem_cons.mp hz' with rfl | hz'' 
        · exact ⟨lt_trans_ax zero_lt_one_ax h1, h2, Or.inr rfl⟩
        · exact absurd hz'' (List.not_mem_nil)
    have hnd : ([(1 : Real), 1 + 1]).Nodup :=
      List.nodup_cons.mpr ⟨fun hm => by
        rcases List.mem_cons.mp hm with h | h
        · exact hne h
        · exact absurd h (List.not_mem_nil), List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩
    have := hbad [(1 : Real), 1 + 1] hnd hmem
    simp at this

end MachLib
