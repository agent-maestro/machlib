import MachLib.EMLZeroQueryNormalForm

/-!
# The first exclusion at query level zero: `sign` is not an `F`-free term

`not_zero_query_of_two_infinite_levels` has been ready since the normal form landed, and it was
stated against `floor`/`mod`. It could not be *instantiated* there: this corpus axiomatises `floor`
by bracketing only (`floor_le`, `lt_floor_add_one`, `floor_zero`), which does not pin it constant on
`[0,1)` — the axiom block's own docstring concedes the integer-valued facts are not derivable. The
exclusion was ready; the countertarget was under-specified.

`Real.sign` is not. It is a **definition**, not an axiom —

```
sign x = if 0 < x then 1 else if x < 0 then −1 else 0
```

— so its level sets are pinned by construction: `sign = 1` on the whole positive ray and `sign = −1`
on the whole negative ray. Two distinct levels, neither exhausted by any finite list. That is exactly
the shape the exclusion consumes, and it needs **no new axiom**.

## Why this is worth having beyond the mathematics

`sign` is a Forge-emit primitive — the Perlin-noise gradient builtin — and `Forge.lean` records that
it is "genuinely derived, not an opaque primitive", being a case split over a `Decidable` instance.
True, and compatible with what is proved here: derived from the field operations *plus a branch*.
The branch is the whole content. **`sign` cannot be compiled away into field operations**, no matter
how many, so a backend targeting an `F`-free datapath must implement the comparison; it cannot
arithmetise it.

The argument nowhere mentions continuity, which is the point — see the level-set discussion in
`EMLZeroQueryNormalForm`. It is entirely about how large a level set can be.
-/

namespace MachLib

open Real

private theorem neg_le_neg' {a b : Real} (h : a ≤ b) : 0 - b ≤ 0 - a := by
  have v := add_le_add_wit (le_refl (0 - a - b)) h
  have el : 0 - a - b + a = 0 - b := by mach_mpoly [a, b]
  have er : 0 - a - b + b = 0 - a := by mach_mpoly [a, b]
  rw [el, er] at v; exact v

private theorem le_add_of_nonneg_right' {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have v := add_le_add_wit (le_refl a) hb
  have e : a + 0 = a := by mach_ring
  rw [e] at v; exact v

/-- **No finite list exhausts the reals in either direction.** The finiteness witness in this corpus
is a `List`, so "infinitely many" is spelled "for every list there is a point outside it" — and this
is what makes that spelling usable. -/
theorem list_two_sided_bound : ∀ L : List Real, ∃ B : Real, 0 ≤ B ∧
    ∀ y : Real, y ∈ L → 0 - B ≤ y ∧ y ≤ B := by
  intro L
  induction L with
  | nil => exact ⟨0, le_refl 0, fun _ hy => by cases hy⟩
  | cons c cs ih =>
      obtain ⟨B, hB, hall⟩ := ih
      -- widen by |c|, written without `abs` so no case analysis on the definition is needed
      rcases lt_total c 0 with hc | hc | hc
      · refine ⟨B + (0 - c), ?_, fun y hy => ?_⟩
        · have h0 : (0 : Real) ≤ 0 - c := by
            have v := neg_le_neg' (le_of_lt hc)
            have e : (0 : Real) - 0 = 0 := by mach_ring
            rw [e] at v; exact v
          exact le_trans hB (le_add_of_nonneg_right' h0)
        · have hmono : B ≤ B + (0 - c) := by
            refine le_add_of_nonneg_right' ?_
            have v := neg_le_neg' (le_of_lt hc)
            have e : (0 : Real) - 0 = 0 := by mach_ring
            rw [e] at v; exact v
          cases hy with
          | head =>
              refine ⟨?_, le_trans (le_of_lt hc) (le_trans hB hmono)⟩
              have e : 0 - (B + (0 - c)) = (0 - B) + c := by mach_mpoly [B, c]
              rw [e]
              have v := add_le_add_wit (neg_le_neg' hB) (le_refl c)
              have e2 : (0 : Real) - 0 + c = c := by mach_ring
              rw [e2] at v; exact v
          | tail _ hy' =>
              obtain ⟨hlo, hhi⟩ := hall y hy'
              exact ⟨le_trans (neg_le_neg' hmono) hlo, le_trans hhi hmono⟩
      · refine ⟨B, hB, fun y hy => ?_⟩
        have hnb : 0 - B ≤ 0 := by
          have v := neg_le_neg' hB
          have e : (0 : Real) - 0 = 0 := by mach_ring
          rw [e] at v; exact v
        cases hy with
        | head => exact ⟨by rw [hc]; exact hnb, by rw [hc]; exact hB⟩
        | tail _ hy' => exact hall y hy'
      · refine ⟨B + c, le_trans hB (le_add_of_nonneg_right' (le_of_lt hc)), fun y hy => ?_⟩
        have hmono : B ≤ B + c := le_add_of_nonneg_right' (le_of_lt hc)
        cases hy with
        | head =>
            refine ⟨?_, le_trans (le_add_of_nonneg_right' hB) (le_of_eq (by mach_ring))⟩
            have hBc : (0 : Real) ≤ B + c := le_trans hB hmono
            exact le_trans (le_trans (neg_le_neg' hBc) (le_of_eq (by mach_ring))) (le_of_lt hc)
        | tail _ hy' =>
            obtain ⟨hlo, hhi⟩ := hall y hy'
            exact ⟨le_trans (neg_le_neg' hmono) hlo, le_trans hhi hmono⟩

/-! ## `sign`'s two rays -/

private theorem not_lt_of_lt_zero {x : Real} (h : x < 0) : ¬ (0 < x) :=
  fun h0 => lt_irrefl_ax (0 : Real) (lt_trans_ax h0 h)

theorem sign_pos {x : Real} (h : 0 < x) : Real.sign x = 1 := by
  show (if 0 < x then (1 : Real) else if x < 0 then -1 else 0) = 1
  rw [if_pos h]

theorem sign_neg {x : Real} (h : x < 0) : Real.sign x = -1 := by
  show (if 0 < x then (1 : Real) else if x < 0 then -1 else 0) = -1
  rw [if_neg (not_lt_of_lt_zero h), if_pos h]

private theorem one_ne_neg_one' : (1 : Real) ≠ -1 := by
  intro h
  -- `rw [h]` would rewrite BOTH ones; congrArg touches only the left summand
  have e1 := congrArg (fun z : Real => z + 1) h
  have e2 : (-1 : Real) + 1 = 0 := by mach_ring
  have e : (1 : Real) + 1 = 0 := by rw [e1]; exact e2
  have hp : (0 : Real) < 1 + 1 := two_pos
  rw [e] at hp
  exact lt_irrefl_ax 0 hp

/-- **`sign` is not zero-query.** No `F`-free term of the language equals it, at any size.

Both rays are infinite level sets — `list_two_sided_bound` produces, for any finite list, a point
beyond it on each side — and `not_zero_query_of_two_infinite_levels` does the rest. No new axiom, no
continuity, and no appeal to `sign` being "discrete": the argument is that a level set of a
zero-query function is finite or cofinite-off-`E`, and a ray is neither. -/
theorem sign_not_zero_query :
    ¬ ∃ T : FTerm, fOcc T = 0 ∧ ∀ x : Real, FTerm.eval T x = Real.sign x := by
  refine not_zero_query_of_two_infinite_levels Real.sign 1 (-1) one_ne_neg_one' ?_ ?_
  · intro L
    obtain ⟨B, hB, hbnd⟩ := list_two_sided_bound L
    refine ⟨B + 1, fun hmem => ?_, sign_pos ?_⟩
    · have hle := (hbnd (B + 1) hmem).2
      have hlt : B < B + 1 := by
        have v := add_lt_add_left zero_lt_one_ax B
        have e : B + 0 = B := by mach_ring
        rw [e] at v; exact v
      exact lt_irrefl_ax B (lt_of_lt_of_le hlt hle)
    · exact lt_of_lt_of_le zero_lt_one_ax (by
        have v := add_le_add_wit hB (le_refl (1 : Real))
        have e : (0 : Real) + 1 = 1 := by mach_ring
        rw [e] at v; exact v)
  · intro L
    obtain ⟨B, hB, hbnd⟩ := list_two_sided_bound L
    refine ⟨0 - (B + 1), fun hmem => ?_, sign_neg ?_⟩
    · have hge := (hbnd (0 - (B + 1)) hmem).1
      have hlt : 0 - (B + 1) < 0 - B := by
        have v := add_lt_add_left zero_lt_one_ax (0 - (B + 1))
        have e1 : 0 - (B + 1) + 0 = 0 - (B + 1) := by mach_ring
        have e2 : 0 - (B + 1) + 1 = 0 - B := by mach_mpoly [B]
        rw [e1, e2] at v; exact v
      exact lt_irrefl_ax (0 - (B + 1)) (lt_of_lt_of_le hlt hge)
    · have hpos : (0 : Real) < B + 1 :=
        lt_of_lt_of_le zero_lt_one_ax (by
          have v := add_le_add_wit hB (le_refl (1 : Real))
          have e : (0 : Real) + 1 = 1 := by mach_ring
          rw [e] at v; exact v)
      have v := add_lt_add_left hpos (0 - (B + 1))
      have el : 0 - (B + 1) + 0 = 0 - (B + 1) := by mach_ring
      have er : 0 - (B + 1) + (B + 1) = 0 := by mach_mpoly [B]
      rw [el, er] at v
      exact v

end MachLib
