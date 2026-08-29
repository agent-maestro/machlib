import MachLib.EMLQueryGermUniform
import MachLib.EMLSignNotZeroQuery
import MachLib.PolynomialCanonical
import MachLib.EMLQueryGermAntecedent
import MachLib.ZeroCountGlue

/-!
# From a uniform zero bound to an explicit finite zero list

`UniformZeroBound f N` says every interval holds at most `N` distinct zeros. `OneQueryLevelSet` —
and every other "the level set is finite" statement in this corpus — wants something one step
stronger in *form* though not in content: an actual `List Real` containing every zero, because a
`List` is how this corpus spells "finite".

Nothing bridged the two. An exhaustive search (`grep -rn ': UniformZeroBound '` over all of
`MachLib/`, not a truncated one) finds exactly one theorem *concluding* the global form, and it is a
specimen: `uniformZeroBound_specimen` for `x - 1`. So there is **no producer**.

Consumers do exist, and the distinction matters — `eventually_nonzero_of_uniformZeroBound`
(`EMLZeroBoundRay`) and `uniformZeroBoundFrom_mono` (`EMLDeclampUniform`) both take a bound as a
hypothesis. What was missing was never "anything that uses a bound"; it was specifically the step
from a bound to a **list**.

## Why the bound does not hand you the list

`UniformZeroBound` quantifies over lists that *happen* to be zeros; it never exhibits one. Going the
other way needs a **maximal** such list, and maximality is where the work is: pick a nodup zero list
of the greatest length the bound permits, and any zero outside it would extend it past that length.

The greatest length exists because `nat_least_element` (`PolynomialCanonical`) is exactly
well-ordering in the form this corpus carries it — the least `n` for which no zero list of length `n`
exists. That `n` is at most `N + 1`, so the predicate is inhabited and the least element is real.

## The shape of the result

Both rays and the whole line are covered, because the ray form is what today's `divClamp` work
actually produces (`queryGerm_pos_branch_uniform`, `queryGerm_neg_branch_uniform` both give
`UniformZeroBoundFrom`), while the global form is what a level-set theorem consumes.

This module proves no dichotomy and assumes no analyticity. It is pure order and list combinatorics
over `UniformZeroBound*`, in the same spirit as `eventually_nonzero_of_uniformZeroBound` — which
cannot be wrong for chain-shape reasons and so serves any future zero-counting result.
-/

namespace MachLib

open Real

/-! ## Zero lists -/

/-- A duplicate-free list of zeros of `f`, all strictly beyond `R`. -/
def ZeroListFrom (f : Real → Real) (R : Real) (l : List Real) : Prop :=
  l.Nodup ∧ ∀ z ∈ l, R < z ∧ f z = 0

/-- `f` has a duplicate-free list of exactly `n` zeros beyond `R`. -/
def HasZeroListFrom (f : Real → Real) (R : Real) (n : Nat) : Prop :=
  ∃ l : List Real, ZeroListFrom f R l ∧ l.length = n

/-- The empty list always witnesses length `0`, which is what makes the least failing length
positive — and hence gives a predecessor to take the maximal list at. -/
theorem hasZeroListFrom_zero (f : Real → Real) (R : Real) : HasZeroListFrom f R 0 :=
  ⟨[], ⟨List.nodup_nil, fun _ hz => by cases hz⟩, rfl⟩

private theorem lt_add_one_r (a : Real) : a < a + 1 := by
  have v := add_lt_add_left zero_lt_one_ax a
  have e : a + 0 = a := by mach_ring
  rw [e] at v; exact v

/-- **The bound caps the lengths.** A zero list one longer than the bound cannot exist: it is
contained in a single interval — `(R, B + 1)` for `B` the two-sided bound of the list — and that is
an interval the hypothesis speaks about.

The list being nonempty is used, and is exactly why the statement is about `N + 1` rather than about
an arbitrary length: the interval's right endpoint is built from a member. -/
theorem not_hasZeroListFrom_succ (f : Real → Real) (R : Real) (N : Nat)
    (h : UniformZeroBoundFrom f R N) : ¬ HasZeroListFrom f R (N + 1) := by
  rintro ⟨l, ⟨hnd, hmem⟩, hlen⟩
  obtain ⟨B, _, hball⟩ := list_two_sided_bound l
  have hne : ∃ z, z ∈ l := by
    cases l with
    | nil => exact absurd hlen.symm (Nat.succ_ne_zero N)
    | cons a t => exact ⟨a, List.mem_cons_self⟩
  obtain ⟨z0, hz0⟩ := hne
  have hRb : R < B + 1 :=
    lt_of_lt_of_le (hmem z0 hz0).1 (le_trans (hball z0 hz0).2 (le_of_lt (lt_add_one_r B)))
  have hcap := h R (B + 1) (le_refl R) hRb l hnd (fun z hz =>
    ⟨(hmem z hz).1, lt_of_le_of_lt (hball z hz).2 (lt_add_one_r B), (hmem z hz).2⟩)
  rw [hlen] at hcap
  omega

/-! ## The same, without a ray -/

/-- A duplicate-free list of zeros of `f`, anywhere on the line. -/
def ZeroListGlobal (f : Real → Real) (l : List Real) : Prop :=
  l.Nodup ∧ ∀ z ∈ l, f z = 0

/-- `f` has a duplicate-free list of exactly `n` zeros. -/
def HasZeroListGlobal (f : Real → Real) (n : Nat) : Prop :=
  ∃ l : List Real, ZeroListGlobal f l ∧ l.length = n

theorem hasZeroListGlobal_zero (f : Real → Real) : HasZeroListGlobal f 0 :=
  ⟨[], ⟨List.nodup_nil, fun _ hz => by cases hz⟩, rfl⟩

private theorem sub_one_lt_r (a : Real) : a - 1 < a := by
  have v := add_lt_add_left zero_lt_one_ax (a - 1)
  have l : a - 1 + 0 = a - 1 := by mach_ring
  have r : a - 1 + 1 = a := by mach_ring
  rw [l, r] at v; exact v

/-- **The global cap.** Same argument as `not_hasZeroListFrom_succ`, with the left endpoint built
from the list's *lower* two-sided bound instead of from the ray. The interval's two endpoints are
compared through a member of the list, so nonemptiness is used once for each. -/
theorem not_hasZeroListGlobal_succ (f : Real → Real) (N : Nat)
    (h : UniformZeroBound f N) : ¬ HasZeroListGlobal f (N + 1) := by
  rintro ⟨l, ⟨hnd, hmem⟩, hlen⟩
  obtain ⟨B, _, hball⟩ := list_two_sided_bound l
  have hne : ∃ z, z ∈ l := by
    cases l with
    | nil => exact absurd hlen.symm (Nat.succ_ne_zero N)
    | cons a t => exact ⟨a, List.mem_cons_self⟩
  obtain ⟨z0, hz0⟩ := hne
  have hlo : ∀ z, z ∈ l → (0 - B) - 1 < z :=
    fun z hz => lt_of_lt_of_le (sub_one_lt_r (0 - B)) (hball z hz).1
  have hhi : ∀ z, z ∈ l → z < B + 1 :=
    fun z hz => lt_of_le_of_lt (hball z hz).2 (lt_add_one_r B)
  have hab : (0 - B) - 1 < B + 1 := lt_trans_ax (hlo z0 hz0) (hhi z0 hz0)
  have hcap := h ((0 - B) - 1) (B + 1) hab l hnd
    (fun z hz => ⟨hlo z hz, hhi z hz, (hmem z hz)⟩)
  rw [hlen] at hcap
  omega

/-! ## The bridge -/

/-- **A uniform zero bound on a ray gives an explicit finite list of the zeros on that ray.**

The list is the *maximal* zero list the bound permits. Any zero beyond `R` outside it would cons onto
it — `List.nodup_cons` needs exactly non-membership, which is the assumption for contradiction — and
produce a zero list of the least *impossible* length.

No analyticity, no dichotomy, no `EvZeroF`: this is the order-theoretic half, and it holds for every
`f` whatever. -/
theorem zeroList_of_uniformZeroBoundFrom (f : Real → Real) (R : Real) (N : Nat)
    (h : UniformZeroBoundFrom f R N) :
    ∃ E : List Real, ∀ x : Real, R < x → f x = 0 → x ∈ E := by
  obtain ⟨m, hm, hlt⟩ :=
    PolynomialCanonical.nat_least_element (fun n => ¬ HasZeroListFrom f R n)
      ⟨N + 1, not_hasZeroListFrom_succ f R N h⟩
  -- `m ≠ 0`, since the empty list witnesses length `0`
  have hm0 : m ≠ 0 := by
    intro h0
    exact hm (h0 ▸ hasZeroListFrom_zero f R)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    cases m with
    | zero => exact absurd rfl hm0
    | succ k => exact ⟨k, rfl⟩
  -- the predecessor is achievable, and its witness is the list
  have hpred : HasZeroListFrom f R m' := by
    have := hlt m' (Nat.lt_succ_self m')
    exact Classical.byContradiction (fun hc => this hc)
  obtain ⟨E, ⟨hnd, hmem⟩, hlen⟩ := hpred
  refine ⟨E, fun x hxR hx0 => ?_⟩
  refine Classical.byContradiction (fun hxE => ?_)
  refine hm ⟨x :: E, ⟨List.nodup_cons.mpr ⟨hxE, hnd⟩, ?_⟩, ?_⟩
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hzE
    · exact ⟨hxR, hx0⟩
    · exact hmem z hzE
  · rw [List.length_cons, hlen]

/-- **The same, globally.** A bound on every interval bounds the zeros on the whole line, because a
finite list of zeros is contained in a single interval in both directions. -/
theorem zeroList_of_uniformZeroBound (f : Real → Real) (N : Nat)
    (h : UniformZeroBound f N) :
    ∃ E : List Real, ∀ x : Real, f x = 0 → x ∈ E := by
  obtain ⟨m, hm, hlt⟩ :=
    PolynomialCanonical.nat_least_element (fun n => ¬ HasZeroListGlobal f n) ⟨N + 1, not_hasZeroListGlobal_succ f N h⟩
  have hm0 : m ≠ 0 := by
    intro h0
    exact hm (h0 ▸ hasZeroListGlobal_zero f)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    cases m with
    | zero => exact absurd rfl hm0
    | succ k => exact ⟨k, rfl⟩
  have hpred : HasZeroListGlobal f m' :=
    Classical.byContradiction (fun hc => hlt m' (Nat.lt_succ_self m') hc)
  obtain ⟨E, ⟨hnd, hmem⟩, hlen⟩ := hpred
  refine ⟨E, fun x hx0 => ?_⟩
  refine Classical.byContradiction (fun hxE => ?_)
  refine hm ⟨x :: E, ⟨List.nodup_cons.mpr ⟨hxE, hnd⟩, ?_⟩, ?_⟩
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hzE
    · exact hx0
    · exact hmem z hzE
  · rw [List.length_cons, hlen]

/-! ## Specimen -/

/-- **The bridge fires, on the corpus's own uniform-bound specimen.**

`uniformZeroBound_specimen : UniformZeroBound (fun x => x - 1) 1` is the only `UniformZeroBound` the
corpus proves, so it is the only thing that can show this bridge is not a theorem about an empty
hypothesis. The conclusion is exhibited with a *member*: `E` provably contains `1`, so the list is
not the empty one and the quantifier is doing work.

Both halves matter. Without the hypothesis being satisfiable the theorem is vacuous
(`a_theorem_can_be_vacuous_and_all_gates_pass`); without a member the produced `E` could be `[]` and
the statement would still typecheck. -/
theorem zeroList_specimen :
    ∃ E : List Real, (1 : Real) ∈ E ∧ ∀ x : Real, x - 1 = 0 → x ∈ E := by
  obtain ⟨E, hE⟩ := zeroList_of_uniformZeroBound (fun x => x - 1) 1 uniformZeroBound_specimen
  have hE' : ∀ x : Real, x - 1 = 0 → x ∈ E := hE
  have h1 : (1 : Real) - 1 = 0 := by mach_ring
  exact ⟨E, hE' 1 h1, hE'⟩

/-! ## What it buys, immediately -/

/-- **A one-query germ that is not eventually zero has FINITELY MANY zeros on a ray — and the list is
exhibited.**

This is the first statement in the corpus to say *finite* about a level-1 germ rather than
*eventually non-zero*. `queryGerm_ratUniformBounds` supplies the interval-independent bound through
all three sign regimes; the bridge above turns it into a list.

It is exactly half of what `OneQueryLevelSet` needs. The other half is the bounded region below `R`,
where a germ can vanish identically on one analyticity component without vanishing on the next —
`Fbasis` is discontinuous where its argument crosses `0` upward, so no identity theorem carries an
identity across such a crossing. That half is open, and this theorem must not be mistaken for it. -/
theorem queryGerm_finite_zeros_on_ray (N : List (List Real)) (P Q : List Real)
    (X : Real) (hX1 : 1 ≤ X) (hQ : ∀ x : Real, X ≤ x → pev Q x ≠ 0)
    (hne : ¬ EvZeroF (fun x => bipev N x (Fbasis (pev P x / pev Q x)))) :
    ∃ (R : Real) (E : List Real),
      ∀ x : Real, R < x → bipev N x (Fbasis (pev P x / pev Q x)) = 0 → x ∈ E := by
  obtain ⟨K, R, hb⟩ := queryGerm_ratUniformBounds N P Q X hX1 hQ hne
  obtain ⟨E, hE⟩ := zeroList_of_uniformZeroBoundFrom _ R K hb
  have hE' : ∀ x : Real, R < x → bipev N x (Fbasis (pev P x / pev Q x)) = 0 → x ∈ E := hE
  exact ⟨R, E, hE'⟩

/-! ## The same predicate, three types -/

/-- `UniformZeroBound` is `ZeroCountOn` quantified over every interval — definitionally, so the glue
lemmas in `ZeroCountGlue` apply to it without translation. -/
theorem uniformZeroBound_iff_zeroCountOn (f : Real → Real) (N : Nat) :
    UniformZeroBound f N ↔ ∀ a b : Real, a < b → ZeroCountOn (fun z => f z = 0) a b N :=
  Iff.rfl

/-- The ray-relative form, likewise. -/
theorem uniformZeroBoundFrom_iff_zeroCountOn (f : Real → Real) (R : Real) (N : Nat) :
    UniformZeroBoundFrom f R N ↔
      ∀ a b : Real, R ≤ a → a < b → ZeroCountOn (fun z => f z = 0) a b N :=
  Iff.rfl

end MachLib
