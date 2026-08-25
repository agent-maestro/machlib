import MachLib.EMLOneQueryNormalForm

/-!
# From a uniform zero bound to eventual non-vanishing

`bipolyDichotomy_iff_noOscillation` showed that `OneQueryDichotomy` is, after the normal form,
exactly a **no-infinite-oscillation** statement: not eventually zero must imply eventually nonzero.
That is a finite-zeros question, and this corpus has a zero-counting arc for those.

But the arc's bounds are the wrong *shape*, and this module supplies the missing bridge.

## The shape mismatch

`chain2_khovanskii_bound_unconditional` and its siblings read

```
∀ (a b : Real), a < b → … → ∃ N, ∀ zeros, zeros.Nodup → (∀ z ∈ zeros, a < z ∧ z < b ∧ f z = 0) →
  zeros.length ≤ N
```

— a bound on a **bounded interval**, with `N` quantified *inside* `a b`, so as written it may depend
on the interval. `BipolyNoOscillation` needs non-vanishing on a **ray**. A per-interval bound does
not give that: zeros could accumulate towards infinity with finitely many in each compact piece.

## What actually bridges it

**Uniformity in the interval is the whole difference.** If one `N` works for *every* interval, then a
function that keeps returning to zero can be milked for `N + 1` distinct zeros — and they all sit
inside a single interval, contradicting the bound. So:

```
UniformZeroBound f N → ∃ Y, 1 ≤ Y ∧ ∀ x, Y ≤ x → f x ≠ 0
```

This is pure order and combinatorics: no analyticity, no Pfaffian chain, no transcendence, and
nothing about `f` beyond the bound. It therefore cannot be wrong for chain-shape reasons, which is
why it is worth having separately from any particular zero-counting theorem.

## What it does **not** do

It does not prove any `UniformZeroBound`. Establishing one for `N(x, F(P/Q))` is the open work, and
the Khovanskii statements would first have to be strengthened to quantify `N` **before** the
interval. That reordering is a statement-level gap rather than a gap in the mathematics — Khovanskii
bounds are uniform in nature — but it is not what the corpus currently proves, and assuming
otherwise is the kind of step that survives every gate here.
-/

namespace MachLib

open Real

/-- One bound `N` on the number of distinct zeros in **every** interval. -/
def UniformZeroBound (f : Real → Real) (N : Nat) : Prop :=
  ∀ a b : Real, a < b → ∀ zeros : List Real, zeros.Nodup →
    (∀ z ∈ zeros, a < z ∧ z < b ∧ f z = 0) → zeros.length ≤ N

private theorem lt_add_one' (a : Real) : a < a + 1 := by
  have v := add_lt_add_left zero_lt_one_ax a
  have e : a + 0 = a := by mach_ring
  rw [e] at v; exact v

private theorem sub_one_lt' (a : Real) : a - 1 < a := by
  have v := add_lt_add_left zero_lt_one_ax (a - 1)
  have l : a - 1 + 0 = a - 1 := by mach_ring
  have r : a - 1 + 1 = a := by mach_ring
  rw [l, r] at v; exact v

/-! ## Milking a cofinal zero set -/

/-- A strictly increasing sequence of zeros, from the assumption that zeros are cofinal. -/
private noncomputable def pickZero (f : Real → Real)
    (hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0) : Nat → Real
  | 0     => Classical.choose (hz 1)
  | n + 1 => Classical.choose (hz (pickZero f hz n + 1))

private theorem pickZero_spec (f : Real → Real)
    (hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0) :
    ∀ n : Nat, 1 ≤ pickZero f hz n ∧ f (pickZero f hz n) = 0 := by
  intro n
  cases n with
  | zero => exact ⟨(Classical.choose_spec (hz 1)).2.1, (Classical.choose_spec (hz 1)).2.2⟩
  | succ k =>
      exact ⟨(Classical.choose_spec (hz (pickZero f hz k + 1))).2.1,
             (Classical.choose_spec (hz (pickZero f hz k + 1))).2.2⟩

private theorem pickZero_succ_gt (f : Real → Real)
    (hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0) :
    ∀ n : Nat, pickZero f hz n < pickZero f hz (n + 1) := by
  intro n
  have hge : pickZero f hz n + 1 ≤ pickZero f hz (n + 1) :=
    (Classical.choose_spec (hz (pickZero f hz n + 1))).1
  exact lt_of_lt_of_le (lt_add_one' _) hge

private theorem pickZero_mono (f : Real → Real)
    (hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0) :
    ∀ i j : Nat, i < j → pickZero f hz i < pickZero f hz j := by
  intro i j
  induction j with
  | zero => intro h; exact absurd h (Nat.not_lt_zero i)
  | succ k ih =>
      intro h
      rcases Nat.lt_or_ge i k with hlt | hge
      · exact lt_of_lt_of_le (ih hlt) (le_of_lt (pickZero_succ_gt f hz k))
      · have hik : i = k := Nat.le_antisymm (by omega) hge
        rw [hik]; exact pickZero_succ_gt f hz k

/-! ## The witness list -/

private noncomputable def zlist (f : Real → Real)
    (hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0) : Nat → List Real
  | 0     => [pickZero f hz 0]
  | k + 1 => pickZero f hz (k + 1) :: zlist f hz k

private theorem zlist_length (f : Real → Real)
    (hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0) :
    ∀ k : Nat, (zlist f hz k).length = k + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ m ih => show (zlist f hz m).length + 1 = m + 1 + 1; rw [ih]

private theorem zlist_bounds (f : Real → Real)
    (hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0) :
    ∀ (k : Nat) (z : Real), z ∈ zlist f hz k →
      pickZero f hz 0 ≤ z ∧ z ≤ pickZero f hz k ∧ f z = 0 := by
  intro k
  induction k with
  | zero =>
      intro z hzm
      have : z = pickZero f hz 0 := by simpa [zlist] using hzm
      rw [this]
      exact ⟨le_refl _, le_refl _, (pickZero_spec f hz 0).2⟩
  | succ m ih =>
      intro z hzm
      rcases List.mem_cons.mp hzm with hhead | htail
      · rw [hhead]
        refine ⟨le_of_lt (pickZero_mono f hz 0 (m + 1) (by omega)), le_refl _, ?_⟩
        exact (pickZero_spec f hz (m + 1)).2
      · obtain ⟨h0, hm, hf⟩ := ih z htail
        exact ⟨h0, le_trans hm (le_of_lt (pickZero_succ_gt f hz m)), hf⟩

private theorem zlist_nodup (f : Real → Real)
    (hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0) :
    ∀ k : Nat, (zlist f hz k).Nodup := by
  intro k
  induction k with
  | zero => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | succ m ih =>
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hmem
      obtain ⟨_, hle, _⟩ := zlist_bounds f hz m _ hmem
      exact (ne_of_lt (lt_of_lt_of_le (pickZero_succ_gt f hz m) hle)) rfl

/-! ## The bridge -/

/-- **A uniform interval bound gives eventual non-vanishing.** Pure order and combinatorics: no
analyticity, no Pfaffian chain, nothing about `f` beyond the bound. -/
theorem eventually_nonzero_of_uniformZeroBound {f : Real → Real} {N : Nat}
    (h : UniformZeroBound f N) : ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x → f x ≠ 0 := by
  rcases Classical.em (∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x → f x ≠ 0) with hy | hy
  · exact hy
  · exfalso
    have base : ∀ Z : Real, 1 ≤ Z → ∃ x : Real, Z ≤ x ∧ f x = 0 := by
      intro Z hZ
      rcases Classical.em (∃ x : Real, Z ≤ x ∧ f x = 0) with hx | hx
      · exact hx
      · exact absurd ⟨Z, hZ, fun x hxZ hfx => hx ⟨x, hxZ, hfx⟩⟩ hy
    have hz : ∀ Y : Real, ∃ x : Real, Y ≤ x ∧ 1 ≤ x ∧ f x = 0 := by
      intro Y
      rcases lt_total Y 1 with hlt | heq | hgt
      · obtain ⟨x, hx1, hfx⟩ := base 1 (le_refl 1)
        exact ⟨x, le_trans (le_of_lt hlt) hx1, hx1, hfx⟩
      · obtain ⟨x, hx1, hfx⟩ := base 1 (le_refl 1)
        exact ⟨x, heq ▸ hx1, hx1, hfx⟩
      · obtain ⟨x, hxY, hfx⟩ := base Y (le_of_lt hgt)
        exact ⟨x, hxY, le_trans (le_of_lt hgt) hxY, hfx⟩
    have hlen := zlist_length f hz N
    have h0N : pickZero f hz 0 ≤ pickZero f hz N := by
      cases N with
      | zero => exact le_refl _
      | succ m => exact le_of_lt (pickZero_mono f hz 0 (m + 1) (by omega))
    have hab : pickZero f hz 0 - 1 < pickZero f hz N + 1 :=
      lt_of_lt_of_le (sub_one_lt' _) (le_trans h0N (le_of_lt (lt_add_one' _)))
    have hbound := h (pickZero f hz 0 - 1) (pickZero f hz N + 1) hab
      (zlist f hz N) (zlist_nodup f hz N) (fun z hzm => by
        obtain ⟨h0, hn, hf⟩ := zlist_bounds f hz N z hzm
        exact ⟨lt_of_lt_of_le (sub_one_lt' _) h0, lt_of_le_of_lt hn (lt_add_one' _), hf⟩)
    rw [hlen] at hbound
    omega

/-! ## Discrimination

`UniformZeroBound` must be satisfiable by something that actually *has* a zero, or the bridge above
could be a theorem about an empty hypothesis — the failure this session already paid for once with
`hcharN`. `x − 1` has exactly one zero and bound `1`, and the bridge then fires on it. -/

private theorem eq_one_of_sub_one_eq_zero {z : Real} (h : z - 1 = 0) : z = 1 := by
  have e : z - 1 + 1 = z := by mach_ring
  rw [← e, h]
  mach_ring

theorem uniformZeroBound_specimen : UniformZeroBound (fun x => x - 1) 1 := by
  intro a b _ zeros hnd hmem
  cases zeros with
  | nil => exact Nat.zero_le 1
  | cons z rest =>
      cases rest with
      | nil => exact Nat.le_refl 1
      | cons w rest' =>
          exfalso
          have hz : z = 1 := eq_one_of_sub_one_eq_zero (hmem z (by simp)).2.2
          have hw : w = 1 := eq_one_of_sub_one_eq_zero (hmem w (by simp)).2.2
          have hne : z ∉ w :: rest' := (List.nodup_cons.mp hnd).1
          exact hne (by rw [hz, ← hw]; exact List.mem_cons_self)

/-- And the bridge fires on it: `x − 1` is eventually nonzero. -/
theorem specimen_eventually_nonzero :
    ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x → (fun x => x - 1) x ≠ 0 :=
  eventually_nonzero_of_uniformZeroBound uniformZeroBound_specimen

/-! ## What the zero-counting arc would have to deliver

Composing the bridge with `bipolyDichotomy_iff_noOscillation` and `oneQueryDichotomy_of_bipoly`
gives the exact shape of the remaining debt for `OneQueryDichotomy`.

**The hypothesis must be conditioned on `¬ EvZeroF`, and that is not cosmetic.** The naive form —
*every* such germ has a uniform bound — is **false**: take `N = []`, whose germ is identically zero
and therefore has no bound at all. Stated that way the theorem would be vacuous, which is the defect
this session spent most of its length repairing elsewhere. The germs that admit a bound are exactly
the ones not eventually zero, and the conditioning says so. -/

/-- **A conditional uniform bound gives no-oscillation.** The antecedent is precisely what the
Khovanskii arc would have to supply: `K` quantified **before** the interval, for germs that are not
eventually zero. -/
theorem bipolyNoOscillation_of_uniformBounds
    (h : ∀ (N : List (List Real)) (P Q : List Real),
        ¬ EvZeroF (fun x => bipev N x (Fbasis (pev P x / pev Q x))) →
        ∃ K : Nat, UniformZeroBound (fun x => bipev N x (Fbasis (pev P x / pev Q x))) K) :
    BipolyNoOscillation := by
  intro N P Q _ _ _ hne
  obtain ⟨K, hK⟩ := h N P Q hne
  exact eventually_nonzero_of_uniformZeroBound hK

/-- **And therefore `OneQueryDichotomy` on the whole of `FCtx`.** The full chain, in one statement:
uniform zero bounds ⟹ no oscillation ⟹ the bivariate dichotomy ⟹ the dichotomy for every context,
given the `div` side conditions along the curve. -/
theorem oneQueryDichotomy_of_uniformBounds
    (h : ∀ (N : List (List Real)) (P Q : List Real),
        ¬ EvZeroF (fun x => bipev N x (Fbasis (pev P x / pev Q x))) →
        ∃ K : Nat, UniformZeroBound (fun x => bipev N x (Fbasis (pev P x / pev Q x))) K) :
    ∀ (C : FCtx) (P Q : List Real) (X : Real), 1 ≤ X →
      (∀ x : Real, X ≤ x → pev Q x ≠ 0) →
      (∀ x : Real, X ≤ x → DivDenomsOK C x (Fbasis (pev P x / pev Q x))) →
      (∀ x : Real, X ≤ x → bipev (ctxFrac C).2 x (Fbasis (pev P x / pev Q x)) ≠ 0) →
        EvZeroF (fun x => FCtx.eval C x (Fbasis (pev P x / pev Q x)))
        ∨ ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
            FCtx.eval C x (Fbasis (pev P x / pev Q x)) ≠ 0 :=
  oneQueryDichotomy_of_bipoly
    (bipolyDichotomy_iff_noOscillation.mpr (bipolyNoOscillation_of_uniformBounds h))

end MachLib
