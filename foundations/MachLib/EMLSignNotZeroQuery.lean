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

theorem neg_le_neg' {a b : Real} (h : a ≤ b) : 0 - b ≤ 0 - a := by
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

/-! ## The other direction: one totalised `log` already contains the branch

The exclusion above is a statement about the **field** fragment, and it is easy to over-read as
"the language cannot branch". It cannot — with `log` totalised, `sign` is a finite field expression
in two logarithms, and the whole trick is the totalisation this corpus already commits to.

`logGap x = log (2x) − log x` is the entire construction:

* `x > 0` — `log_mul` splits it and the `log x` cancels, leaving the **nonzero constant** `log 2`;
* `x ≤ 0` — then `2x ≤ 0` too, both logs are `0` by `log_nonpos`, and the gap is `0`.

Divide it by itself: `div_zero` sends the second case to `0`, `self_div` sends the first to `1`. That
is a positivity indicator built from field operations and a transcendental primitive, with no
comparison anywhere.

**So the zero-query barrier is a basis boundary, not an expressibility barrier.** Field operations
alone cannot implement a two-sided classifier (`sign_not_zero_query`); adding one totalised
transcendental makes it a finite expression. What is being measured is not "arithmetic versus
comparison" but **how much branch information is latent in the chosen basis** — and in a totalised
basis, the answer is: some.

The simplification worth recording: the natural construction takes `log x ² + log (2x) ²`, to dodge
`log 1 = 0`. The difference `log (2x) − log x` needs no squares — it is *constantly* `log 2` on the
positive ray, so it never vanishes there, and vanishes identically off it. -/

/-- `log (2x) − log x`: the constant `log 2` on `x > 0`, and `0` on `x ≤ 0`. -/
noncomputable def logGap (x : Real) : Real := log ((1 + 1) * x) - log x

private theorem two_ne_one : (1 + 1 : Real) ≠ 1 := by
  intro h
  have e1 := congrArg (fun z : Real => z - 1) h
  have el : (1 + 1 : Real) - 1 = 1 := by mach_ring
  have er : (1 : Real) - 1 = 0 := by mach_ring
  rw [el, er] at e1
  exact lt_irrefl_ax 0 (e1 ▸ zero_lt_one_ax)

theorem logGap_of_pos {x : Real} (h : 0 < x) : logGap x = log (1 + 1) := by
  show log ((1 + 1) * x) - log x = log (1 + 1)
  rw [log_mul two_pos h]
  mach_ring

theorem logGap_of_nonpos {x : Real} (h : x ≤ 0) : logGap x = 0 := by
  have h2 : (1 + 1) * x ≤ 0 := by
    have v := mul_le_mul_of_nonneg_left h (le_of_lt two_pos)
    have e : (1 + 1 : Real) * 0 = 0 := by mach_ring
    rw [e] at v; exact v
  show log ((1 + 1) * x) - log x = 0
  rw [log_nonpos h2, log_nonpos h]
  mach_ring

/-- **The positivity indicator, with no comparison in it.** -/
noncomputable def posIndicator (x : Real) : Real := logGap x / logGap x

theorem posIndicator_of_pos {x : Real} (h : 0 < x) : posIndicator x = 1 := by
  show logGap x / logGap x = 1
  refine self_div ?_
  rw [logGap_of_pos h]
  exact log_ne_zero_of_pos_of_ne_one two_pos two_ne_one

theorem posIndicator_of_nonpos {x : Real} (h : x ≤ 0) : posIndicator x = 0 := by
  show logGap x / logGap x = 0
  rw [logGap_of_nonpos h]
  exact div_zero 0

theorem sign_zero : Real.sign 0 = 0 := by
  show (if (0 : Real) < 0 then (1 : Real) else if (0 : Real) < 0 then -1 else 0) = 0
  rw [if_neg (lt_irrefl_ax (0 : Real))]
  rw [if_neg (lt_irrefl_ax (0 : Real))]

/-- **`sign` IS expressible — over field operations plus one totalised `log`.**

Together with `sign_not_zero_query` this locates the barrier exactly: `sign ∉ C₀`, yet `sign` is a
finite expression once a totalised transcendental is in the basis. The obstruction was never
"the language has no comparison". -/
theorem sign_eq_posIndicator (x : Real) :
    Real.sign x = posIndicator x - posIndicator (0 - x) := by
  have hnegzero : (0 : Real) - 0 = 0 := by mach_ring
  rcases lt_total 0 x with h | h | h
  · have hle : 0 - x ≤ 0 := by
      have v := neg_le_neg' (le_of_lt h)
      rw [hnegzero] at v; exact v
    rw [sign_pos h, posIndicator_of_pos h, posIndicator_of_nonpos hle]
    mach_ring
  · rw [← h, hnegzero, sign_zero, posIndicator_of_nonpos (le_refl 0)]
    mach_ring
  · have hpos : 0 < 0 - x := by
      have v := add_lt_add_left h (0 - x)
      have el : 0 - x + x = 0 := by mach_ring
      have er : 0 - x + 0 = 0 - x := by mach_ring
      rw [el, er] at v; exact v
    rw [sign_neg h, posIndicator_of_nonpos (le_of_lt h), posIndicator_of_pos hpos]
    mach_ring

end MachLib
