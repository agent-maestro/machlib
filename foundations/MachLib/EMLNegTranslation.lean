import MachLib.EMLDepthTameness
import MachLib.EMLDecayFloorIsGrowth
import MachLib.EMLAdditionClosureFailure

/-!
# The negative translation, growing-left branch

`EMLDepthTameness` leaves `NegativeTranslationGrowingLeft` open: a depth-3 node computing `x + c`
with `c < 0`, whose left child's exponential already dominates `exp x`. Its docstring calls it *"the
same species of difficulty as `ExpExpGapBelow` and `BoundedCellApproach`, which took an arc each"*,
and expects a cell enumeration.

**The enumeration is avoidable.** The route is written out in
`monogate-research/exploration/negative_translation_growing_left_2026_08_28/ROUTE.md`; the short form
is that `Hgrow` and a *growth* cap on the right child squeeze `A` into the band `[x, x+1]`, where the
depth-≤1 classification leaves only `var`; the equation then pins `B` to the single germ
`exp (exp x − x − c)`, which the same classification also refuses. `A` is collapsed to one form
*before* any enumeration, which is why twenty-five cells never appear.

This module builds that route bottom-up. It is a **separate module rather than an insertion** for a
mundane reason worth recording: `EMLDepthTameness` declares `depth_le_two_growth_envelope` at line
1921 and `self_le_exp` at line 2438, and a theorem is only usable *below* its declaration in the same
file — so an insertion would have to sit past both, far from the obligation it serves. A new module
imports the whole file and is free of the ordering entirely.

## §1 — the growth mirror of `depth_le_two_decay_on_ray`

`EMLDepthTameness` has the decay half (`−log (B x) ≤ C + log x`, wherever `B` is positive) and the
value envelope (`B x ≤ exp (exp x + K) + M`). It does not have the *log-growth* half, which is what
the growing-left branch needs, and which follows from the envelope in a few lines.
-/

namespace MachLib

open Real

/-- **The depth-≤2 log-growth cap.** `log (t x) ≤ exp x + K` on a ray — one level of nesting buys
exactly one exponential *inside* a logarithm, which is the statement the growing-left branch consumes.

Mirror of `depth_le_two_decay_on_ray`; together they bracket `log (t x)` for a depth-≤2 tree.

Three things the ray must absorb, and each is a real obligation rather than slack:
* `X₀` from the envelope itself;
* `exp (M − K)`, past which the envelope's additive `M` is dominated by its own exponential term, so
  the sum can be folded into a single `exp`;
* `exp (−K)`, past which `exp x + K` is non-negative — needed because `K` may be **negative**, and
  the totalised branch (`t x ≤ 0`, so `log (t x) = 0`) has to land under the bound too.

The `exp (·)` thresholds are the file's standing idiom: `self_le_exp` makes `exp a` an upper bound
for `a` whatever its sign, so a sum of exponentials dominates every constant in play without a case
split on signs. -/
theorem depth_le_two_log_growth_on_ray (t : EMLTree) (ht : t.depth ≤ 2) :
    ∃ K X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → log (t.eval x) ≤ exp x + K := by
  obtain ⟨K, M, X₀, hX₀, henv⟩ := depth_le_two_growth_envelope t ht
  refine ⟨1 + K, X₀ + exp (M - K) + exp (-K), ?_, ?_⟩
  · -- the ray dominates `X₀ ≥ 1`
    have h1 : X₀ + 0 + 0 ≤ X₀ + exp (M - K) + exp (-K) :=
      add_le_add_wit (add_le_add_wit (le_refl X₀) (le_of_lt (exp_pos (M - K))))
        (le_of_lt (exp_pos (-K)))
    have e : X₀ + (0 : Real) + 0 = X₀ := by mach_ring
    rw [e] at h1
    exact le_trans hX₀ h1
  intro x hx
  -- the three components of the ray, extracted
  have hxX₀ : X₀ ≤ x := by
    refine le_trans ?_ hx
    have h1 : X₀ + 0 + 0 ≤ X₀ + exp (M - K) + exp (-K) :=
      add_le_add_wit (add_le_add_wit (le_refl X₀) (le_of_lt (exp_pos (M - K))))
        (le_of_lt (exp_pos (-K)))
    have e : X₀ + (0 : Real) + 0 = X₀ := by mach_ring
    rw [e] at h1; exact h1
  have hxMK : M - K ≤ x := by
    refine le_trans (self_le_exp (M - K)) (le_trans ?_ hx)
    have h1 : (0 : Real) + exp (M - K) + 0 ≤ X₀ + exp (M - K) + exp (-K) :=
      add_le_add_wit (add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hX₀) (le_refl _))
        (le_of_lt (exp_pos (-K)))
    have e : (0 : Real) + exp (M - K) + 0 = exp (M - K) := by mach_ring
    rw [e] at h1; exact h1
  have hxnK : -K ≤ x := by
    refine le_trans (self_le_exp (-K)) (le_trans ?_ hx)
    have h1 : (0 : Real) + 0 + exp (-K) ≤ X₀ + exp (M - K) + exp (-K) :=
      add_le_add_wit (add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hX₀)
        (le_of_lt (exp_pos (M - K)))) (le_refl _)
    have e : (0 : Real) + (0 : Real) + exp (-K) = exp (-K) := by mach_ring
    rw [e] at h1; exact h1
  -- `exp x + K` is non-negative on this ray, which is what the totalised branch needs
  have hKnonneg : (0 : Real) ≤ exp x + K := by
    have h1 : -K ≤ exp x := le_trans hxnK (self_le_exp x)
    have v := add_le_add_wit h1 (le_refl K)
    have e : -K + K = (0 : Real) := by mach_ring
    rw [e] at v; exact v
  -- `M` is dominated by the envelope's own exponential term
  have hMdom : M ≤ exp (exp x + K) := by
    have h1 : M ≤ x + K := by
      have v := add_le_add_wit hxMK (le_refl K)
      have e : M - K + K = M := by mach_mpoly [M, K]
      rw [e] at v; exact v
    refine le_trans h1 (le_trans ?_ (self_le_exp (exp x + K)))
    exact add_le_add_wit (self_le_exp x) (le_refl K)
  -- fold `exp (exp x + K) + M` into a single exponential, using `1 + 1 ≤ exp 1`
  have hfold : exp (exp x + K) + M ≤ exp (1 + (exp x + K)) := by
    have hsum : exp (exp x + K) + M ≤ exp (exp x + K) + exp (exp x + K) :=
      add_le_add_wit (le_refl _) hMdom
    have htwo : (1 : Real) + 1 ≤ exp 1 := one_add_le_exp_of_one_le (le_refl 1)
    have hmul : ((1 : Real) + 1) * exp (exp x + K) ≤ exp 1 * exp (exp x + K) :=
      mul_le_mul_of_nonneg_right htwo (le_of_lt (exp_pos (exp x + K)))
    have edist : ((1 : Real) + 1) * exp (exp x + K) = exp (exp x + K) + exp (exp x + K) := by
      mach_mpoly [exp (exp x + K)]
    rw [edist] at hmul
    exact le_trans hsum (le_trans hmul (le_of_eq (exp_add 1 (exp x + K)).symm))
  rcases lt_total 0 (t.eval x) with hpos | hzero | hneg
  · -- positive: monotone `log` through the folded envelope, then `log_exp`
    have hchain : t.eval x ≤ exp (1 + (exp x + K)) := le_trans (henv x hxX₀) hfold
    have hl := log_le_log hpos hchain
    rw [log_exp] at hl
    have e : (1 : Real) + (exp x + K) = exp x + (1 + K) := by mach_ring
    rw [e] at hl; exact hl
  · -- totalised at zero
    rw [← hzero, log_nonpos (le_refl 0)]
    have v := add_le_add_wit hKnonneg (le_of_lt zero_lt_one_ax)
    have e : (0 : Real) + 0 = 0 := by mach_ring
    have e2 : exp x + K + 1 = exp x + (1 + K) := by mach_ring
    rw [e, e2] at v; exact v
  · -- totalised below zero
    rw [log_nonpos (le_of_lt hneg)]
    have v := add_le_add_wit hKnonneg (le_of_lt zero_lt_one_ax)
    have e : (0 : Real) + 0 = 0 := by mach_ring
    have e2 : exp x + K + 1 = exp x + (1 + K) := by mach_ring
    rw [e, e2] at v; exact v

/-! ## §2 — the squeeze: the left child is trapped just above the identity

`Heq` says `exp (A x) = x + c + log (B x)`. §1 caps `log (B x)` by `exp x + K`, so `exp (A x)` is at
most `exp x` plus something linear — and `exp (x+1) = e·exp x` has room to spare. The band's width is
deliberately `1` rather than the sharp `O(x e^{−x})`: the sharp form is true and costs more to prove,
and every later step only needs `x + 1`. -/
theorem growingLeft_A_le_succ (c : Real) (A B : EMLTree) (hB : B.depth ≤ 2)
    (heq : ∀ x : Real, 0 < x → exp (A.eval x) - log (B.eval x) = x + c) :
    ∃ X₁ : Real, 1 ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x → A.eval x ≤ x + 1 := by
  obtain ⟨K, XB, hXB, hlogB⟩ := depth_le_two_log_growth_on_ray B hB
  obtain ⟨X₂, hX₂, hlin⟩ := exp_beats_linear_eventually (1 + 1)
  refine ⟨XB + X₂ + exp (c + K), ?_, ?_⟩
  · have v : XB + 0 + 0 ≤ XB + X₂ + exp (c + K) :=
      add_le_add_wit (add_le_add_wit (le_refl XB)
        (le_trans (le_of_lt zero_lt_one_ax) hX₂)) (le_of_lt (exp_pos (c + K)))
    have e : XB + (0 : Real) + 0 = XB := by mach_ring
    rw [e] at v
    exact le_trans hXB v
  intro x hx
  have hxB : XB ≤ x := by
    refine le_trans ?_ hx
    have v : XB + 0 + 0 ≤ XB + X₂ + exp (c + K) :=
      add_le_add_wit (add_le_add_wit (le_refl XB)
        (le_trans (le_of_lt zero_lt_one_ax) hX₂)) (le_of_lt (exp_pos (c + K)))
    have e : XB + (0 : Real) + 0 = XB := by mach_ring
    rw [e] at v; exact v
  have hx2 : X₂ ≤ x := by
    refine le_trans ?_ hx
    have v : (0 : Real) + X₂ + 0 ≤ XB + X₂ + exp (c + K) :=
      add_le_add_wit (add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hXB) (le_refl X₂))
        (le_of_lt (exp_pos (c + K)))
    have e : (0 : Real) + X₂ + 0 = X₂ := by mach_ring
    rw [e] at v; exact v
  have hxcK : c + K ≤ x := by
    refine le_trans (self_le_exp (c + K)) (le_trans ?_ hx)
    have v : (0 : Real) + 0 + exp (c + K) ≤ XB + X₂ + exp (c + K) :=
      add_le_add_wit (add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hXB)
        (le_trans (le_of_lt zero_lt_one_ax) hX₂)) (le_refl _)
    have e : (0 : Real) + (0 : Real) + exp (c + K) = exp (c + K) := by mach_ring
    rw [e] at v; exact v
  have hx1 : (1 : Real) ≤ x := le_trans hX₂ hx2
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  -- `exp (A x) = x + c + log (B x) ≤ x + c + (exp x + K)`
  have hval := heq x hx0
  have hA : exp (A.eval x) ≤ x + c + (exp x + K) := by
    have e : exp (A.eval x) = x + c + log (B.eval x) := by
      have t : exp (A.eval x) - log (B.eval x) + log (B.eval x)
          = x + c + log (B.eval x) := by rw [hval]
      have l : exp (A.eval x) - log (B.eval x) + log (B.eval x) = exp (A.eval x) := by
        mach_mpoly [exp (A.eval x), log (B.eval x)]
      rw [l] at t; exact t
    rw [e]
    exact add_le_add_wit (le_refl (x + c)) (hlogB x hxB)
  -- and the right-hand side fits under `exp (x+1) = e · exp x`
  have hroom : x + c + (exp x + K) ≤ exp (x + 1) := by
    have hlinx : (1 + 1) * x ≤ exp x := hlin x hx2
    have hshift : x + (c + K) ≤ (1 + 1) * x := by
      have v := add_le_add_wit (le_refl x) hxcK
      have e : x + x = (1 + 1) * x := by mach_mpoly [x]
      rw [e] at v; exact v
    have hstep : x + c + (exp x + K) ≤ exp x + exp x := by
      have v := add_le_add_wit (le_trans hshift hlinx) (le_refl (exp x))
      have e : x + (c + K) + exp x = x + c + (exp x + K) := by
        mach_mpoly [x, c, K, exp x]
      rw [e] at v
      have e2 : exp x + exp x = exp x + exp x := by mach_ring
      rw [e2]; exact v
    have htwo : (1 : Real) + 1 ≤ exp 1 := one_add_le_exp_of_one_le (le_refl 1)
    have hmul : ((1 : Real) + 1) * exp x ≤ exp 1 * exp x :=
      mul_le_mul_of_nonneg_right htwo (le_of_lt (exp_pos x))
    have edist : ((1 : Real) + 1) * exp x = exp x + exp x := by mach_mpoly [exp x]
    rw [edist] at hmul
    have esum : exp (x + 1) = exp 1 * exp x := by
      rw [exp_add]
      have e : exp x * exp 1 = exp 1 * exp x := by mach_ring
      rw [e]
    rw [esum]
    exact le_trans hstep hmul
  -- `exp` is injective-monotone, so read the bound back through `log`
  have hle : exp (A.eval x) ≤ exp (x + 1) := le_trans hA hroom
  have hlog := log_le_log (exp_pos (A.eval x)) hle
  rw [log_exp, log_exp] at hlog
  exact hlog

/-! ## §3 — at depth ≤ 2 the band admits only `var`

Three local conveniences first. Every argument below is of the form *"pick one point far enough out
and derive a contradiction there"*, and the thresholds are always sums of exponentials — the file's
standing idiom, since `self_le_exp` makes `exp a` dominate `a` whatever its sign, so no case split on
signs is ever needed. `exists_big` does that arithmetic **once**; without it each branch repeats forty
lines of reassociating sums and the mathematics disappears into it.

(`set` does not exist in this corpus — hence an existential rather than a local definition.) -/

/-- Made **public** on 2026-08-28. The immediate cause evaporated — `EMLQueryGermUniform` wanted it,
could not reach it (no import path), and I inlined the two lines there instead. Kept public anyway,
because the general point stands and this file is where I had caused it: `private` on a
general-purpose arithmetic helper does not hide complexity, it guarantees the next module rewrites
it. `EMLRayIdentity` records the same complaint about `a < a + 1`, which has four private copies and
needed a fifth.

Recorded honestly rather than dressed up as a fix that was used: the change is a small unilateral
improvement, not a response to a live need. -/
theorem le_addr {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have v := add_le_add_wit (le_refl a) hb
  have e : a + (0 : Real) = a := by mach_ring
  rw [e] at v; exact v

/-- Public for the same reason as `le_addr`. -/
theorem le_addl {a b : Real} (ha : 0 ≤ a) : b ≤ a + b := by
  have v := add_le_add_wit ha (le_refl b)
  have e : (0 : Real) + b = b := by mach_ring
  rw [e] at v; exact v

/-- **One point past four thresholds**, with the fourth strict — the strictness is what turns a
`w ≤ d` conclusion into a contradiction rather than an equality, and it costs one `+ 1`. -/
private theorem exists_big (a b c d : Real) :
    ∃ w : Real, a ≤ w ∧ b ≤ w ∧ c ≤ w ∧ d < w ∧ 1 ≤ w := by
  have hn : ∀ z : Real, (0 : Real) ≤ exp z := fun z => le_of_lt (exp_pos z)
  refine ⟨exp a + exp b + exp c + exp d + 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (self_le_exp a)
      (le_trans (le_trans (le_trans (le_addr (hn b)) (le_addr (hn c))) (le_addr (hn d)))
        (le_addr (le_of_lt zero_lt_one_ax)))
  · exact le_trans (self_le_exp b)
      (le_trans (le_trans (le_trans (le_addl (hn a)) (le_addr (hn c))) (le_addr (hn d)))
        (le_addr (le_of_lt zero_lt_one_ax)))
  · exact le_trans (self_le_exp c)
      (le_trans (le_trans (le_addl (le_trans (hn a) (le_addr (hn b)))) (le_addr (hn d)))
        (le_addr (le_of_lt zero_lt_one_ax)))
  · refine lt_of_le_of_lt (le_trans (self_le_exp d)
      (le_addl (le_trans (hn a) (le_trans (le_addr (hn b)) (le_addr (hn c)))))) ?_
    have u := add_lt_add_left zero_lt_one_ax (exp a + exp b + exp c + exp d)
    have e : exp a + exp b + exp c + exp d + 0 = exp a + exp b + exp c + exp d := by mach_ring
    rw [e] at u; exact u
  · exact le_addl (le_trans (hn a) (le_trans (le_addr (hn b))
      (le_trans (le_addr (hn c)) (le_addr (hn d)))))

/-- **The growing branch cannot sit in the band.** If the left grandchild's exponential already
dominates `exp x`, the node is at least `exp x − log (B₂ x) ≥ exp x − (x + C)` — far beyond a band of
width `1` about the identity. `depth_le_one_log_le_linear` is the only fact used about `B₂`, and it is
why this branch needs no sign analysis: that bound holds whether or not `B₂` is positive, because the
totalised `log 0 = 0` is itself under `x + C`. -/
theorem band_growing_left_absurd (A₂ B₂ : EMLTree) (hB₂ : B₂.depth ≤ 1)
    (T₂ : Real) (hgrow2 : ∀ x : Real, T₂ ≤ x → exp x ≤ exp (A₂.eval x))
    (X₁ : Real) (hband : ∀ x : Real, X₁ ≤ x → exp (A₂.eval x) - log (B₂.eval x) ≤ x + 1) :
    False := by
  obtain ⟨C₁, hlogB₂⟩ := depth_le_one_log_le_linear B₂ hB₂
  obtain ⟨X₃, hX₃, hlin3⟩ := exp_beats_linear_eventually (1 + 1 + 1)
  obtain ⟨w, hwT, hw1, hw3, hwC, hw1'⟩ := exists_big T₂ X₁ X₃ (1 + C₁)
  have hbandw := hband w hw1
  have hgroww := hgrow2 w hwT
  have hlogw := hlogB₂ w hw1'
  -- `exp w ≤ exp (A₂ w)`, so the band bound applies to `exp w` too
  have h1 : exp w - log (B₂.eval w) ≤ w + 1 := by
    refine le_trans ?_ hbandw
    have v := add_le_add_wit hgroww (le_refl (-log (B₂.eval w)))
    have e1 : exp w + -log (B₂.eval w) = exp w - log (B₂.eval w) := by
      mach_mpoly [exp w, log (B₂.eval w)]
    have e2 : exp (A₂.eval w) + -log (B₂.eval w) = exp (A₂.eval w) - log (B₂.eval w) := by
      mach_mpoly [exp (A₂.eval w), log (B₂.eval w)]
    rw [e1, e2] at v; exact v
  have hchain : exp w ≤ w + 1 + (w + C₁) := by
    have v := add_le_add_wit h1 hlogw
    have e : exp w - log (B₂.eval w) + log (B₂.eval w) = exp w := by
      mach_mpoly [exp w, log (B₂.eval w)]
    rw [e] at v; exact v
  -- against `3w ≤ exp w`
  have hbad : w ≤ 1 + C₁ := by
    have h2 : (1 + 1 + 1) * w ≤ w + 1 + (w + C₁) := le_trans (hlin3 w hw3) hchain
    have v := add_le_add_wit h2 (le_refl (-(w + w)))
    have l : (1 + 1 + 1) * w + -(w + w) = w := by mach_mpoly [w]
    have r : w + 1 + (w + C₁) + -(w + w) = 1 + C₁ := by mach_mpoly [w, C₁]
    rw [l, r] at v; exact v
  exact lt_irrefl_ax _ (lt_of_lt_of_le hwC hbad)

/-- **The bounded branch cannot sit in the band either.** If the left grandchild's exponential is
capped by `Kb`, the node is at most `Kb + (C + log x)` — logarithmic, so it cannot stay *above* the
identity, which `Hgrow` demands.

This is the mechanism of `mirrorBand_not_depth_three_bounded_left` reused one level down, and the
totalisation splits the same way: where `B₂` is non-positive its log is `0` and the node is simply
`≤ Kb`, which is an easier contradiction, not a harder one. The reason the positive case still closes
is that `log w` is eventually under `w/2` — obtained by feeding `exp_beats_linear_eventually` the
point `log w` rather than `w`, which is the only slightly non-obvious step here. -/
theorem band_bounded_left_absurd (A₂ B₂ : EMLTree) (hB₂ : B₂.depth ≤ 1)
    (Kb : Real) (hKb : ∀ x : Real, 1 ≤ x → exp (A₂.eval x) ≤ Kb)
    (T : Real) (hxle : ∀ x : Real, T ≤ x → x ≤ exp (A₂.eval x) - log (B₂.eval x)) :
    False := by
  obtain ⟨C, X₀, hX₀, hdec⟩ := depth_le_two_decay_on_ray B₂ (by omega)
  obtain ⟨X₄, hX₄, hlin2⟩ := exp_beats_linear_eventually (1 + 1)
  obtain ⟨w, hwT, hwX₀, hwX₄, hwd, hw1⟩ :=
    exists_big T X₀ (exp X₄) (exp Kb + exp ((1 + 1) * Kb + (1 + 1) * C))
  have hn : ∀ z : Real, (0 : Real) ≤ exp z := fun z => le_of_lt (exp_pos z)
  have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
  have hKbw : Kb < w :=
    lt_of_le_of_lt (le_trans (self_le_exp Kb) (le_addr (hn ((1 + 1) * Kb + (1 + 1) * C)))) hwd
  have hCw : (1 + 1) * Kb + (1 + 1) * C < w :=
    lt_of_le_of_lt (le_trans (self_le_exp ((1 + 1) * Kb + (1 + 1) * C)) (le_addl (hn Kb))) hwd
  have hxlew := hxle w hwT
  have hKbww := hKb w hw1
  rcases lt_total 0 (B₂.eval w) with hpos | hzero | hneg
  · -- `B₂ w > 0`: the decay bound caps the node at `Kb + C + log w`, which is logarithmic
    have hcap : w ≤ Kb + (C + log w) := by
      refine le_trans hxlew ?_
      have v := add_le_add_wit hKbww (hdec w hwX₀ hpos)
      have e : exp (A₂.eval w) + -log (B₂.eval w) = exp (A₂.eval w) - log (B₂.eval w) := by
        mach_mpoly [exp (A₂.eval w), log (B₂.eval w)]
      rw [e] at v; exact v
    -- `2·log w ≤ w`, by applying the linear-vs-exp bound at the point `log w`
    have hlogw : X₄ ≤ log w := by
      have h := log_le_log (exp_pos X₄) hwX₄
      rw [log_exp] at h; exact h
    have h2log : (1 + 1) * log w ≤ w := by
      have h := hlin2 (log w) hlogw
      rw [exp_log hw0] at h; exact h
    -- so `w ≤ 2Kb + 2C`, contradicting the strict threshold
    have hbad : w ≤ (1 + 1) * Kb + (1 + 1) * C := by
      have hdouble : (1 + 1) * w ≤ (1 + 1) * Kb + (1 + 1) * C + (1 + 1) * log w := by
        have v := mul_le_mul_of_nonneg_left hcap (le_of_lt (add_pos zero_lt_one_ax zero_lt_one_ax))
        have e : ((1 : Real) + 1) * (Kb + (C + log w))
            = (1 + 1) * Kb + (1 + 1) * C + (1 + 1) * log w := by
          mach_mpoly [Kb, C, log w]
        rw [e] at v; exact v
      have hstep : (1 + 1) * w ≤ (1 + 1) * Kb + (1 + 1) * C + w :=
        le_trans hdouble (add_le_add_wit (le_refl _) h2log)
      have v := add_le_add_wit hstep (le_refl (-w))
      have l : ((1 : Real) + 1) * w + -w = w := by mach_mpoly [w]
      have r : ((1 : Real) + 1) * Kb + (1 + 1) * C + w + -w
          = (1 + 1) * Kb + (1 + 1) * C := by mach_mpoly [Kb, C, w]
      rw [l, r] at v; exact v
    exact lt_irrefl_ax _ (lt_of_lt_of_le hCw hbad)
  · -- `B₂ w = 0`: totalisation gives `log 0 = 0`, so the node is just `exp (A₂ w) ≤ Kb`
    refine lt_irrefl_ax _ (lt_of_lt_of_le hKbw ?_)
    refine le_trans hxlew ?_
    rw [← hzero, log_nonpos (le_refl 0)]
    have e : exp (A₂.eval w) - 0 = exp (A₂.eval w) := by mach_ring
    rw [e]; exact hKbww
  · -- `B₂ w < 0`: identically
    refine lt_irrefl_ax _ (lt_of_lt_of_le hKbw ?_)
    refine le_trans hxlew ?_
    rw [log_nonpos (le_of_lt hneg)]
    have e : exp (A₂.eval w) - 0 = exp (A₂.eval w) := by mach_ring
    rw [e]; exact hKbww

/-- **§3's conclusion: inside the band, a depth-≤2 tree IS the variable.**

Three constructor cases and no cell enumeration anywhere. A constant cannot stay above the identity;
the variable is the answer; and a node is killed by the dichotomy
`depth_le_one_exp_bounded_or_grows` on its left child — bounded loses to `Hgrow`, growing loses to
the band. That dichotomy is doing the work an enumeration of twenty-five depth-≤2 cells would
otherwise have to do, which is the whole reason this obligation is cheaper than its docstring feared.

Note what is *not* assumed: nothing about `B₂` beyond its depth. The right child is free, and both
branches still close. -/
theorem band_depth_le_two_is_var (A : EMLTree) (hA : A.depth ≤ 2)
    (T : Real) (hxle : ∀ x : Real, T ≤ x → x ≤ A.eval x)
    (X₁ : Real) (hband : ∀ x : Real, X₁ ≤ x → A.eval x ≤ x + 1) :
    ∀ x : Real, 0 < x → A.eval x = x := by
  cases A with
  | const p =>
      intro x _
      exfalso
      obtain ⟨w, hwT, _, _, hwp, _⟩ := exists_big T T T p
      have h := hxle w hwT
      have e : (EMLTree.const p).eval w = p := rfl
      rw [e] at h
      exact lt_irrefl_ax _ (lt_of_lt_of_le hwp h)
  | var => intro x _; rfl
  | eml A₂ B₂ =>
      exfalso
      have hd : 1 + Nat.max A₂.depth B₂.depth ≤ 2 := hA
      have hm1 : A₂.depth ≤ Nat.max A₂.depth B₂.depth := Nat.le_max_left _ _
      have hm2 : B₂.depth ≤ Nat.max A₂.depth B₂.depth := Nat.le_max_right _ _
      have hA₂ : A₂.depth ≤ 1 := by omega
      have hB₂ : B₂.depth ≤ 1 := by omega
      rcases depth_le_one_exp_bounded_or_grows A₂ hA₂ with ⟨Kb, hKb⟩ | ⟨T₂, hgrow2⟩
      · exact band_bounded_left_absurd A₂ B₂ hB₂ Kb hKb T hxle
      · exact band_growing_left_absurd A₂ B₂ hB₂ T₂ hgrow2 X₁ hband

/-! ## §4 — the reduction, and what is left

§1–§3 collapse the left child to `var`. The equation then pins the right child to a single germ, and
that is the whole of what remains. -/

/-- **The residual obligation.** After §1–§3, `NegativeTranslationGrowingLeft` is exactly this: a
depth-≤2 tree whose logarithm is the germ `exp x − x − c`.

Stated as its own `Prop` so that the shorthand *"the negative translation is nearly done"* cannot
form — the same discipline the parent obligation was given. It is strictly narrower than its parent:
no `A`, no growth hypothesis, one child, one equation.

**Why it should fall.** `log (B x) = exp x − x − c` forces `B x = exp (exp x − x − c)`, so a depth-2
`B = eml A₁ B₁` needs `A₁ x → exp x − x − c`. The depth-≤1 forms are `α`, `x`, `c′ − log x`,
`exp x − d` and `exp x − log x`, and **none of them carries a `−x` term**: producing one would need
`log (b x) = x + c` for `b` of depth 0, and neither `log (const)` nor `log x` is affine in `x`. That
sentence is the remaining proof; making it formal needs a two-sided bound on `exp (A₁ x)`, and the
lower half is the one that costs, because it needs the decay bound on `B₁` with its sign split. -/
def PinnedRightChild : Prop :=
  ∀ c : Real, c < 0 → ∀ B : EMLTree, B.depth ≤ 2 →
    (∀ x : Real, 0 < x → log (B.eval x) = exp x - x - c) → False

/-- **`Hgrow`, read through `log`.** `exp x ≤ exp (A x)` is the obligation's form; `x ≤ A x` is the
usable one. -/
private theorem le_of_exp_le {a b : Real} (h : exp a ≤ exp b) : a ≤ b := by
  have hl := log_le_log (exp_pos a) h
  rw [log_exp, log_exp] at hl; exact hl

/-- **§1–§3 assembled: the equation pins the right child.** Under the obligation's own hypotheses,
`A` is the variable and `log (B x)` is the germ `exp x − x − c` on all of `(0, ∞)`.

Note the hypotheses used: `c < 0` is **not** among them. The collapse of `A` is a fact about the
band, not about the sign of the translation — which is worth recording, because it says the negative
side's difficulty lives entirely in the residual and not in the geometry that gets there. -/
theorem growingLeft_pins_right (c : Real) (A B : EMLTree) (hA : A.depth ≤ 2) (hB : B.depth ≤ 2)
    (hgrow : ∃ T : Real, ∀ x : Real, T ≤ x → exp x ≤ exp (A.eval x))
    (heq : ∀ x : Real, 0 < x → exp (A.eval x) - log (B.eval x) = x + c) :
    ∀ x : Real, 0 < x → log (B.eval x) = exp x - x - c := by
  obtain ⟨T, hT⟩ := hgrow
  obtain ⟨X₁, _, hband⟩ := growingLeft_A_le_succ c A B hB heq
  have hxle : ∀ x : Real, T ≤ x → x ≤ A.eval x := fun x hx => le_of_exp_le (hT x hx)
  have hvar := band_depth_le_two_is_var A hA T hxle X₁ hband
  intro x hx
  have hval := heq x hx
  rw [hvar x hx] at hval
  -- `exp x - log (B x) = x + c`  ⟹  `log (B x) = exp x - x - c`
  have v := add_le_add_wit (le_of_eq hval) (le_refl (log (B.eval x) - x - c))
  have v' := add_le_add_wit (le_of_eq hval.symm) (le_refl (log (B.eval x) - x - c))
  have l : exp x - log (B.eval x) + (log (B.eval x) - x - c) = exp x - x - c := by
    mach_mpoly [exp x, log (B.eval x), x, c]
  have r : x + c + (log (B.eval x) - x - c) = log (B.eval x) := by
    mach_mpoly [log (B.eval x), x, c]
  rw [l, r] at v
  rw [l, r] at v'
  exact le_antisymm v' v

/-- **The obligation reduces to `PinnedRightChild`.** Everything except the residual is now proved.

This does **not** discharge `NegativeTranslationGrowingLeft` and the ledger must not read it as
doing so: a reduction to an open residue is one debt written in a new place, not one debt fewer. -/
theorem negativeTranslationGrowingLeft_of_pinned (h : PinnedRightChild) :
    NegativeTranslationGrowingLeft := by
  intro c hc A B hA hB hgrow heq
  exact h c hc B hB (growingLeft_pins_right c A B hA hB hgrow heq)

/-! ## §5 — the residue: no depth-≤2 tree has `exp x − x − c` as its logarithm

The germ `u x := exp x − x − c` is the whole content. `log (B x) = u x` forces `B x = exp (u x)`, and
a depth-2 `B = eml A₁ B₁` then needs `exp (A₁ x) − log (B₁ x) = exp (u x)` — a doubly-exponential
target hit by a depth-≤1 form perturbed by something at most linear. The perturbation is too small to
matter, so `A₁ x` is pinned to within `1` of `u x`, and none of the five depth-≤1 forms can sit there.

**Why `−x` is the obstruction.** `u x` carries a `−x` term. Of the five forms, the two that reach
`exp x` (`exp x − d`, `exp x − log x`) subtract only a constant or a logarithm, and the three that do
not reach `exp x` are hopeless anyway. Producing a `−x` would need `log (b x) = x + c` for `b` of
depth `0`, and neither `log (const)` nor `log x` is affine in `x`. -/

/-- `exp w − w − c` is positive once `w` is past the linear threshold — needed before the equation
can be inverted through `exp`, since the totalised `log` is `0` on non-positives. Uses `c < 0`, which
is the *first* place in this whole development the sign of the translation is consumed. -/
private theorem u_pos {c w : Real} (hc : c < 0) (h3 : (1 + 1 + 1) * w ≤ exp w) (hw1 : 1 ≤ w) :
    0 < exp w - w - c := by
  have htwo : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have h2w : c < (1 + 1) * w := by
    have hb : (1 : Real) + 1 ≤ (1 + 1) * w := by
      have v := mul_le_mul_of_nonneg_left hw1 (le_of_lt htwo)
      have e : ((1 : Real) + 1) * 1 = 1 + 1 := by mach_ring
      rw [e] at v; exact v
    exact lt_of_lt_of_le (lt_trans_ax hc htwo) hb
  have hstep : w + c < exp w := by
    refine lt_of_lt_of_le (add_lt_add_left h2w w) ?_
    have e : w + (1 + 1) * w = (1 + 1 + 1) * w := by mach_mpoly [w]
    rw [e]; exact h3
  have v := add_lt_add_left hstep (-(w + c))
  have l : -(w + c) + (w + c) = (0 : Real) := by mach_mpoly [w, c]
  have r : -(w + c) + exp w = exp w - w - c := by mach_mpoly [w, c, exp w]
  rw [l, r] at v; exact v

/-- **The depth-≤1 half of the residue.** `log (B x)` is at most linear there, and `exp x − x − c` is
not. Nothing subtle: the whole case is one linear-versus-exponential comparison. -/
private theorem pinned_depth_le_one (c : Real) (B : EMLTree) (hB : B.depth ≤ 1)
    (hpin : ∀ x : Real, 0 < x → log (B.eval x) = exp x - x - c) : False := by
  obtain ⟨C, hlin⟩ := depth_le_one_log_le_linear B hB
  obtain ⟨X₃, hX₃, hlin3⟩ := exp_beats_linear_eventually (1 + 1 + 1)
  obtain ⟨w, hw3, _, _, hwd, hw1⟩ := exists_big X₃ X₃ X₃ (c + C)
  have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
  -- `exp w - w - c = log (B w) ≤ w + C`
  have heq := hpin w hw0
  have hup : exp w - w - c ≤ w + C := by rw [← heq]; exact hlin w hw1
  -- against `3w ≤ exp w`
  have hbad : w ≤ c + C := by
    have h3 := hlin3 w hw3
    have hchain : (1 + 1 + 1) * w - w - c ≤ w + C := le_trans (by
      have v := add_le_add_wit (add_le_add_wit h3 (le_refl (-w))) (le_refl (-c))
      have e1 : exp w + -w + -c = exp w - w - c := by mach_mpoly [exp w, w, c]
      have e2 : (1 + 1 + 1) * w + -w + -c = (1 + 1 + 1) * w - w - c := by mach_mpoly [w, c]
      rw [e1, e2] at v; exact v) hup
    have v := add_le_add_wit hchain (le_refl (-w + c))
    have l : (1 + 1 + 1) * w - w - c + (-w + c) = w := by mach_mpoly [w, c]
    have r : w + C + (-w + c) = c + C := by mach_mpoly [w, C, c]
    rw [l, r] at v; exact v
  exact lt_irrefl_ax _ (lt_of_lt_of_le hwd hbad)

/-- `exists_big` re-read as a *threshold* rather than a point (named `far_enough` because
`big_threshold` is already taken by `EMLRationalGerm` with an unrelated signature): past `X`, all four bounds hold. The
band lemma needs "for every far enough `w`", not "for some `w`", because the five-form case split
happens afterwards and each form brings its own constant to dominate. -/
private theorem far_enough (a b c d : Real) :
    ∃ X : Real, 1 ≤ X ∧ ∀ w : Real, X ≤ w → a ≤ w ∧ b ≤ w ∧ c ≤ w ∧ d ≤ w := by
  obtain ⟨w₀, h1, h2, h3, h4, h5⟩ := exists_big a b c d
  exact ⟨w₀, h5, fun w hw =>
    ⟨le_trans h1 hw, le_trans h2 hw, le_trans h3 hw, le_trans (le_of_lt h4) hw⟩⟩

/-- **The perturbation is too small to move the exponent.** Writing `u = exp w − w − c`, the equation
gives `exp (A₁ w) = exp u + log (B₁ w)`, where `log (B₁ w)` is bracketed between `−(e^{C₂} + log w)`
and `w + C₁` — at most linear either way, against a target `exp u` that is exponential in `u`. One
step of `exp` swallows the whole perturbation, so `A₁ w` is pinned to `u ± 1`.

Both folds run on the same identity `exp (u ± 1) = e^{±1}·exp u` and both reduce, after `self_le_exp`
turns `exp u ≥ u`, to a linear-versus-exponential comparison. The only thing needing care is that the
*lower* bound consumes `B₁`'s sign split: the decay bound holds only where `B₁` is positive, and
where it is not the totalised `log 0 = 0` is already above the bound being claimed. -/
private theorem pinned_band (A₁ B₁ : EMLTree) (hB₁ : B₁.depth ≤ 1) (c : Real) (hc : c < 0)
    (hpin : ∀ x : Real, 0 < x →
      log (exp (A₁.eval x) - log (B₁.eval x)) = exp x - x - c) :
    ∃ X : Real, 1 ≤ X ∧ ∀ w : Real, X ≤ w →
      exp w - w - c - 1 ≤ A₁.eval w ∧ A₁.eval w ≤ exp w - w - c + 1 := by
  obtain ⟨C₁, hlin1⟩ := depth_le_one_log_le_linear B₁ hB₁
  obtain ⟨C₂, X₀, _, hdec⟩ := depth_le_two_decay_on_ray B₁ (by omega)
  obtain ⟨X₃, _, hlin3⟩ := exp_beats_linear_eventually (1 + 1 + 1)
  obtain ⟨X, hX1, hdom⟩ := far_enough X₃ X₀ (C₁ + c) (exp C₂ + 1 + c)
  refine ⟨X, hX1, ?_⟩
  intro w hw
  obtain ⟨hw3, hwX₀, hwC₁, hwC₂⟩ := hdom w hw
  have hw1 : (1 : Real) ≤ w := le_trans hX1 hw
  have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
  have h3 := hlin3 w hw3
  have hu : (0 : Real) < exp w - w - c := u_pos hc h3 hw1
  have hval := hpin w hw0
  have hlogw : log w ≤ w := by
    have h := self_le_exp (log w); rw [exp_log hw0] at h; exact h
  have hlogw0 : (0 : Real) ≤ log w := by
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hm := log_le_log zero_lt_one_ax hw1
    rw [hl1] at hm; exact hm
  have htwo : (1 : Real) + 1 ≤ exp 1 := one_add_le_exp_of_one_le (le_refl 1)
  -- the node's value is positive, else its totalised log would be `0`, and `u > 0`
  have hpos : (0 : Real) < exp (A₁.eval w) - log (B₁.eval w) := by
    rcases lt_total 0 (exp (A₁.eval w) - log (B₁.eval w)) with h | h | h
    · exact h
    · exact absurd (by rw [← hval, ← h, log_nonpos (le_refl 0)]) (ne_of_lt hu)
    · exact absurd (by rw [← hval, log_nonpos (le_of_lt h)]) (ne_of_lt hu)
  have hE : exp (A₁.eval w) = exp (exp w - w - c) + log (B₁.eval w) := by
    have h : exp (A₁.eval w) - log (B₁.eval w) = exp (exp w - w - c) := by
      rw [← hval, exp_log hpos]
    have v : exp (A₁.eval w) - log (B₁.eval w) + log (B₁.eval w)
        = exp (exp w - w - c) + log (B₁.eval w) := by rw [h]
    have l : exp (A₁.eval w) - log (B₁.eval w) + log (B₁.eval w) = exp (A₁.eval w) := by
      mach_mpoly [exp (A₁.eval w), log (B₁.eval w)]
    rw [l] at v; exact v
  -- `log (B₁ w)` bracketed: linear above, and below by the decay bound or by totalisation
  have hupB : log (B₁.eval w) ≤ w + C₁ := hlin1 w hw1
  have hlowB : -(exp C₂ + log w) ≤ log (B₁.eval w) := by
    have hnn : (0 : Real) ≤ exp C₂ + log w :=
      le_trans (le_of_lt (exp_pos C₂)) (le_addr hlogw0)
    rcases lt_total 0 (B₁.eval w) with h | h | h
    · have hstep : -log (B₁.eval w) ≤ exp C₂ + log w :=
        le_trans (hdec w hwX₀ h) (add_le_add_wit (self_le_exp C₂) (le_refl (log w)))
      have v := neg_le_neg_wit hstep
      have e : - -log (B₁.eval w) = log (B₁.eval w) := by mach_ring
      rw [e] at v; exact v
    · rw [← h, log_nonpos (le_refl 0)]
      have v := neg_le_neg_wit hnn
      have e : -(0 : Real) = 0 := by mach_ring
      rw [e] at v; exact v
    · rw [log_nonpos (le_of_lt h)]
      have v := neg_le_neg_wit hnn
      have e : -(0 : Real) = 0 := by mach_ring
      rw [e] at v; exact v
  -- linear quantities sit under `u` itself, hence under `exp u` and `exp (u−1)`
  have hlinU : w + C₁ ≤ exp w - w - c := by
    have hstep : (1 + 1 + 1) * w - w - c ≤ exp w - w - c := by
      have v := add_le_add_wit (add_le_add_wit h3 (le_refl (-w))) (le_refl (-c))
      have e1 : exp w + -w + -c = exp w - w - c := by mach_mpoly [exp w, w, c]
      have e2 : (1 + 1 + 1) * w + -w + -c = (1 + 1 + 1) * w - w - c := by mach_mpoly [w, c]
      rw [e1, e2] at v; exact v
    refine le_trans ?_ hstep
    have v := add_le_add_wit (le_refl w) hwC₁
    have e : w + (C₁ + c) = w + C₁ + c := by mach_mpoly [w, C₁, c]
    have e2 : w + w = (1 + 1) * w := by mach_mpoly [w]
    have hgoal : w + C₁ + c ≤ (1 + 1 + 1) * w - w - c + c := by
      have e3 : ((1 : Real) + 1 + 1) * w - w - c + c = (1 + 1) * w := by mach_mpoly [w, c]
      rw [e3, ← e2]; rw [← e]; exact v
    have v2 := add_le_add_wit hgoal (le_refl (-c))
    have l : w + C₁ + c + -c = w + C₁ := by mach_mpoly [w, C₁, c]
    have r : ((1 : Real) + 1 + 1) * w - w - c + c + -c = (1 + 1 + 1) * w - w - c := by
      mach_mpoly [w, c]
    rw [l, r] at v2; exact v2
  have hlinL : exp C₂ + log w ≤ exp w - w - c - 1 := by
    have hstep : (1 + 1 + 1) * w - w - c - 1 ≤ exp w - w - c - 1 := by
      have v := add_le_add_wit (add_le_add_wit (add_le_add_wit h3 (le_refl (-w)))
        (le_refl (-c))) (le_refl (-(1 : Real)))
      have e1 : exp w + -w + -c + -1 = exp w - w - c - 1 := by mach_mpoly [exp w, w, c]
      have e2 : (1 + 1 + 1) * w + -w + -c + -1 = (1 + 1 + 1) * w - w - c - 1 := by
        mach_mpoly [w, c]
      rw [e1, e2] at v; exact v
    refine le_trans ?_ hstep
    have hle : exp C₂ + log w ≤ exp C₂ + w := add_le_add_wit (le_refl (exp C₂)) hlogw
    refine le_trans hle ?_
    have v := add_le_add_wit (le_refl w) hwC₂
    have e : w + (exp C₂ + 1 + c) = exp C₂ + w + (1 + c) := by mach_mpoly [w, C₂, c, exp C₂]
    have e2 : ((1 : Real) + 1 + 1) * w - w - c - 1 + (1 + c) = (1 + 1) * w := by mach_mpoly [w, c]
    have e3 : w + w = ((1 : Real) + 1) * w := by mach_mpoly [w]
    rw [e] at v
    have v2 := add_le_add_wit v (le_refl (-(1 + c)))
    have l : exp C₂ + w + (1 + c) + -(1 + c) = exp C₂ + w := by mach_mpoly [C₂, w, c, exp C₂]
    have r : w + w + -(1 + c) = (1 + 1) * w - 1 - c := by mach_mpoly [w, c]
    rw [l, r] at v2
    refine le_trans v2 (le_of_eq ?_)
    mach_mpoly [w, c]
  -- upper fold
  have hupper : A₁.eval w ≤ exp w - w - c + 1 := by
    have hb : exp (A₁.eval w) ≤ exp (exp w - w - c) + exp (exp w - w - c) := by
      rw [hE]
      exact add_le_add_wit (le_refl _)
        (le_trans hupB (le_trans hlinU (self_le_exp (exp w - w - c))))
    have hmul : ((1 : Real) + 1) * exp (exp w - w - c) ≤ exp 1 * exp (exp w - w - c) :=
      mul_le_mul_of_nonneg_right htwo (le_of_lt (exp_pos _))
    have edist : ((1 : Real) + 1) * exp (exp w - w - c)
        = exp (exp w - w - c) + exp (exp w - w - c) := by mach_mpoly [exp (exp w - w - c)]
    rw [edist] at hmul
    have efold : exp 1 * exp (exp w - w - c) = exp (exp w - w - c + 1) := by
      rw [← exp_add]
      have e : (1 : Real) + (exp w - w - c) = exp w - w - c + 1 := by mach_mpoly [exp w, w, c]
      rw [e]
    rw [efold] at hmul
    have hfin := log_le_log (exp_pos (A₁.eval w)) (le_trans hb hmul)
    rw [log_exp, log_exp] at hfin; exact hfin
  -- lower fold
  have hlower : exp w - w - c - 1 ≤ A₁.eval w := by
    have hsplit : exp (exp w - w - c)
        = exp (exp w - w - c - 1) + exp (exp w - w - c - 1) * (exp 1 - 1) := by
      have e : exp w - w - c = (exp w - w - c - 1) + 1 := by mach_mpoly [exp w, w, c]
      rw [e, exp_add]
      have e2 : (exp w - w - c - 1 + 1) - 1 = exp w - w - c - 1 := by mach_mpoly [exp w, w, c]
      rw [e2]
      mach_mpoly [exp (exp w - w - c - 1), exp 1]
    have hone : (1 : Real) ≤ exp 1 - 1 := by
      have v := add_le_add_wit htwo (le_refl (-(1 : Real)))
      have l : (1 : Real) + 1 + -1 = 1 := by mach_ring
      have r : exp 1 + -(1 : Real) = exp 1 - 1 := by mach_mpoly [exp 1]
      rw [l, r] at v; exact v
    have hgap : exp (exp w - w - c - 1) ≤ exp (exp w - w - c - 1) * (exp 1 - 1) := by
      have v := mul_le_mul_of_nonneg_left hone (le_of_lt (exp_pos (exp w - w - c - 1)))
      have e : exp (exp w - w - c - 1) * (1 : Real) = exp (exp w - w - c - 1) := by mach_ring
      rw [e] at v; exact v
    have hpert : exp C₂ + log w ≤ exp (exp w - w - c - 1) :=
      le_trans hlinL (self_le_exp (exp w - w - c - 1))
    have hb : exp (exp w - w - c - 1) ≤ exp (A₁.eval w) := by
      rw [hE]
      -- `exp u` splits as `exp (u−1)` plus a gap that is itself at least `exp (u−1)`,
      -- and the perturbation fits inside that gap
      have step2 : exp (exp w - w - c - 1) + (exp C₂ + log w) ≤ exp (exp w - w - c) := by
        rw [hsplit]
        exact add_le_add_wit (le_refl _) (le_trans hpert hgap)
      have step3 := add_le_add_wit step2 (le_refl (-(exp C₂ + log w)))
      have l : exp (exp w - w - c - 1) + (exp C₂ + log w) + -(exp C₂ + log w)
          = exp (exp w - w - c - 1) := by
        mach_mpoly [exp (exp w - w - c - 1), exp C₂, log w]
      rw [l] at step3
      exact le_trans step3 (add_le_add_wit (le_refl (exp (exp w - w - c))) hlowB)
    have hfin := log_le_log (exp_pos (exp w - w - c - 1)) hb
    rw [log_exp, log_exp] at hfin; exact hfin
  exact ⟨hlower, hupper⟩

/-- **A form bounded above by a constant cannot meet the lower band.** `u − 1 ≤ M` says
`exp w ≤ M + w + c + 1`, and `3w ≤ exp w` then caps `2w`; since `w ≤ 2w`, any `w` past `M + c + 1`
is absurd. Forms `α` and `c′ − log x` both land here — the latter because `−log w ≤ 0`. -/
private theorem band_lower_const_absurd {c w M : Real}
    (h3 : (1 + 1 + 1) * w ≤ exp w) (hw1 : 1 ≤ w)
    (hband : exp w - w - c - 1 ≤ M) (hlt : M + c + 1 < w) : False := by
  have hexp : exp w ≤ M + w + c + 1 := by
    have v := add_le_add_wit hband (le_refl (w + c + 1))
    have l : exp w - w - c - 1 + (w + c + 1) = exp w := by mach_mpoly [exp w, w, c]
    have r : M + (w + c + 1) = M + w + c + 1 := by mach_mpoly [M, w, c]
    rw [l, r] at v; exact v
  have h2w : (1 + 1) * w ≤ M + c + 1 := by
    have hchain : (1 + 1 + 1) * w ≤ M + w + c + 1 := le_trans h3 hexp
    have v := add_le_add_wit hchain (le_refl (-w))
    have l : (1 + 1 + 1) * w + -w = (1 + 1) * w := by mach_mpoly [w]
    have r : M + w + c + 1 + -w = M + c + 1 := by mach_mpoly [M, w, c]
    rw [l, r] at v; exact v
  have hww : w ≤ (1 + 1) * w := by
    have hw0 : (0 : Real) ≤ w := le_trans (le_of_lt zero_lt_one_ax) hw1
    have v := add_le_add_wit (le_refl w) hw0
    have l : w + (0 : Real) = w := by mach_ring
    have r : w + w = (1 + 1) * w := by mach_mpoly [w]
    rw [l, r] at v; exact v
  exact lt_irrefl_ax _ (lt_of_lt_of_le hlt (le_trans hww h2w))

/-- **The residue is discharged.** `PinnedRightChild` holds: no depth-≤2 tree has `exp x − x − c` as
its logarithm.

Depth ≤1 is one linear-versus-exponential comparison. Depth 2 goes through `pinned_band`, which pins
`A₁ w` to `u ± 1`, and then the five depth-≤1 forms are exhausted:

| form | which half of the band kills it | why |
|---|---|---|
| `α` | lower | a constant cannot reach `u − 1 → ∞` |
| `x` | lower | would force `exp w ≤ 2w + c + 1` |
| `c′ − log x` | lower | `−log w ≤ 0`, so it is bounded by `c′` |
| `exp x − d` | upper | would force `w ≤ d − c + 1` |
| `exp x − log x` | upper | would force `w + c − 1 ≤ log w`, against `2 log w ≤ w` |

The two `exp x − …` forms are the only ones that reach the right *size*; they die on the `−x` term,
which is exactly the sentence the route predicted would be the whole proof. -/
theorem pinnedRightChild_holds : PinnedRightChild := by
  intro c hc B hB hpin
  cases Nat.lt_or_ge B.depth 2 with
  | inl hlt => exact pinned_depth_le_one c B (by omega) hpin
  | inr hge =>
      cases B with
      | const p =>
          have e : (EMLTree.const p).depth = 0 := rfl
          rw [e] at hge; omega
      | var =>
          have e : (EMLTree.var).depth = 0 := rfl
          rw [e] at hge; omega
      | eml A₁ B₁ =>
          have hd : 1 + Nat.max A₁.depth B₁.depth ≤ 2 := hB
          have hm1 : A₁.depth ≤ Nat.max A₁.depth B₁.depth := Nat.le_max_left _ _
          have hm2 : B₁.depth ≤ Nat.max A₁.depth B₁.depth := Nat.le_max_right _ _
          have hA₁ : A₁.depth ≤ 1 := by omega
          have hB₁ : B₁.depth ≤ 1 := by omega
          obtain ⟨X, _, hband⟩ := pinned_band A₁ B₁ hB₁ c hc hpin
          obtain ⟨X₃, _, hlin3⟩ := exp_beats_linear_eventually (1 + 1 + 1)
          obtain ⟨X₄, hX₄, hlin2⟩ := exp_beats_linear_eventually (1 + 1)
          rcases depth_le_one_classification A₁ hA₁ with
              ⟨α, hf⟩ | hf | ⟨c', _, hf⟩ | ⟨d, hf⟩ | hf
          · obtain ⟨w, hwX, hw3, _, hwd, hw1⟩ := exists_big X X₃ X₃ (α + c + 1)
            have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
            obtain ⟨hlow, _⟩ := hband w hwX
            rw [hf w hw0] at hlow
            exact band_lower_const_absurd (hlin3 w hw3) hw1 hlow hwd
          · obtain ⟨w, hwX, hw3, _, hwd, hw1⟩ := exists_big X X₃ X₃ (c + 1)
            have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
            obtain ⟨hlow, _⟩ := hband w hwX
            rw [hf w hw0] at hlow
            -- `u − 1 ≤ w` forces `exp w ≤ 2w + c + 1`, against `3w ≤ exp w`
            have hexp : exp w ≤ w + w + c + 1 := by
              have v := add_le_add_wit hlow (le_refl (w + c + 1))
              have l : exp w - w - c - 1 + (w + c + 1) = exp w := by mach_mpoly [exp w, w, c]
              have r : w + (w + c + 1) = w + w + c + 1 := by mach_mpoly [w, c]
              rw [l, r] at v; exact v
            have hbad : w ≤ c + 1 := by
              have hchain : (1 + 1 + 1) * w ≤ w + w + c + 1 := le_trans (hlin3 w hw3) hexp
              have v := add_le_add_wit hchain (le_refl (-(w + w)))
              have l : (1 + 1 + 1) * w + -(w + w) = w := by mach_mpoly [w]
              have r : w + w + c + 1 + -(w + w) = c + 1 := by mach_mpoly [w, c]
              rw [l, r] at v; exact v
            exact lt_irrefl_ax _ (lt_of_lt_of_le hwd hbad)
          · obtain ⟨w, hwX, hw3, _, hwd, hw1⟩ := exists_big X X₃ X₃ (c' + c + 1)
            have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
            obtain ⟨hlow, _⟩ := hband w hwX
            rw [hf w hw0] at hlow
            -- `c′ − log w ≤ c′` because `log w ≥ 0`
            have hlogw0 : (0 : Real) ≤ log w := by
              have hl1 : log (1 : Real) = 0 := by
                have hz : exp (0 : Real) = 1 := exp_zero
                rw [← hz, log_exp]
              have hm := log_le_log zero_lt_one_ax hw1
              rw [hl1] at hm; exact hm
            have hcap : c' - log w ≤ c' := by
              have v := add_le_add_wit (le_refl c') (neg_le_neg_wit hlogw0)
              have l : c' + -log w = c' - log w := by mach_mpoly [c', log w]
              have r : c' + -(0 : Real) = c' := by mach_ring
              rw [l, r] at v; exact v
            exact band_lower_const_absurd (hlin3 w hw3) hw1 (le_trans hlow hcap) hwd
          · obtain ⟨w, hwX, _, _, hwd, hw1⟩ := exists_big X X₃ X₃ (d - c + 1)
            have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
            obtain ⟨_, hup⟩ := hband w hwX
            rw [hf w hw0] at hup
            -- `exp w − d ≤ u + 1` forces `w ≤ d − c + 1`
            have hbad : w ≤ d - c + 1 := by
              have v := add_le_add_wit hup (le_refl (d - exp w))
              have l : exp w - d + (d - exp w) = (0 : Real) := by mach_mpoly [exp w, d]
              have r : exp w - w - c + 1 + (d - exp w) = d - c + 1 - w := by
                mach_mpoly [exp w, w, c, d]
              rw [l, r] at v
              have v2 := add_le_add_wit v (le_refl w)
              have l2 : (0 : Real) + w = w := by mach_ring
              have r2 : d - c + 1 - w + w = d - c + 1 := by mach_mpoly [d, c, w]
              rw [l2, r2] at v2; exact v2
            exact lt_irrefl_ax _ (lt_of_lt_of_le hwd hbad)
          · obtain ⟨w, hwX, _, hw4, hwd, hw1⟩ := exists_big X X₃ (exp X₄) (1 + 1 - (1 + 1) * c)
            have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
            obtain ⟨_, hup⟩ := hband w hwX
            rw [hf w hw0] at hup
            -- `exp w − log w ≤ u + 1` forces `w + c − 1 ≤ log w`; but `2 log w ≤ w`
            have hlogge : w + c - 1 ≤ log w := by
              have v := add_le_add_wit hup (le_refl (log w - exp w))
              have l : exp w - log w + (log w - exp w) = (0 : Real) := by
                mach_mpoly [exp w, log w]
              have r : exp w - w - c + 1 + (log w - exp w) = log w - w - c + 1 := by
                mach_mpoly [exp w, w, c, log w]
              rw [l, r] at v
              have v2 := add_le_add_wit v (le_refl (w + c - 1))
              have l2 : (0 : Real) + (w + c - 1) = w + c - 1 := by mach_mpoly [w, c]
              have r2 : log w - w - c + 1 + (w + c - 1) = log w := by mach_mpoly [log w, w, c]
              rw [l2, r2] at v2; exact v2
            have hlogw : X₄ ≤ log w := by
              have h := log_le_log (exp_pos X₄) hw4
              rw [log_exp] at h; exact h
            have h2log : (1 + 1) * log w ≤ w := by
              have h := hlin2 (log w) hlogw
              rw [exp_log hw0] at h; exact h
            have hbad : w ≤ 1 + 1 - (1 + 1) * c := by
              have hdouble : (1 + 1) * (w + c - 1) ≤ (1 + 1) * log w :=
                mul_le_mul_of_nonneg_left hlogge
                  (le_of_lt (add_pos zero_lt_one_ax zero_lt_one_ax))
              have hchain : (1 + 1) * (w + c - 1) ≤ w := le_trans hdouble h2log
              have v := add_le_add_wit hchain (le_refl (-w + (1 + 1) - (1 + 1) * c))
              have l : ((1 : Real) + 1) * (w + c - 1) + (-w + (1 + 1) - (1 + 1) * c) = w := by
                mach_mpoly [w, c]
              have r : w + (-w + ((1 : Real) + 1) - (1 + 1) * c) = 1 + 1 - (1 + 1) * c := by
                mach_mpoly [w, c]
              rw [l, r] at v; exact v
            exact lt_irrefl_ax _ (lt_of_lt_of_le hwd hbad)

/-- **And therefore the obligation itself.** `NegativeTranslationGrowingLeft` is a theorem. -/
theorem negativeTranslationGrowingLeft_holds : NegativeTranslationGrowingLeft :=
  negativeTranslationGrowingLeft_of_pinned pinnedRightChild_holds

/-- **Non-vacuity, shipped with the capstone.** An impossibility theorem is worth exactly as much as
its hypotheses are satisfiable *individually*: if no depth-≤2 tree could satisfy `Hgrow` at all, the
result above would be true and would say nothing about negative translations. That is the
`positive_branch_impossible` failure mode, and it is cheap to rule out here — `var` satisfies `Hgrow`
on the nose.

So the configuration space the theorem empties is not empty for a trivial reason: what it rules out
is the *conjunction* of a satisfiable growth condition with the equation. -/
theorem growingLeft_growth_hypothesis_satisfiable :
    ∃ A : EMLTree, A.depth ≤ 2 ∧ ∃ T : Real, ∀ x : Real, T ≤ x → exp x ≤ exp (A.eval x) :=
  ⟨EMLTree.var, Nat.zero_le 2, 0, fun _ _ => le_refl _⟩

/-! ## §6 — `d(x + c) = 4` for `c < 0`: §4's open cell, closed by assembly

`EMLDepthTameness` §4 leaves one cell open:

```
c > 0   d(x + c) = 4  exactly      c = 0   d(x) = 0      c < 0   d(x + c) ∈ {3, 4}
```

and calls it *"the first question this family raises that the existing machinery cannot answer."*

**The existing machinery could answer it; what was missing was §5.** The depth-3 exclusion for `c < 0`
splits on the left child's exponential — `depth_le_two_exp_bounded_or_grows` (`EMLDepthTameness`,
whose docstring already calls itself *"the brick a depth-3 band argument needs on its left child"*).
The bounded branch went to `mirrorBand_not_depth_three_bounded_left` and was closed; the growing
branch was the obligation discharged in §5. With both branches closed and the dichotomy exhaustive,
the cell closes by **assembly**: one small lemma (`x + c` is a mirror-band target) and a case split.

> **A correction worth keeping.** I opened this section by writing a depth-≤2 dichotomy from scratch,
> having concluded from a `grep … | head -6` that none existed. It existed, seven hits down the list
> the `head` had truncated. **Absence read off a truncated search is not absence** — and the failure
> is invisible, because a short result list looks the same as a short answer. Lean caught it with
> "has already been declared"; nothing else would have. The duplicate is deleted and the original
> used.
-/

/-- **`x + c` is a mirror-band target for `c < 0`.** The below-identity half is
`x_plus_neg_c_belowIdentity`; this supplies the super-logarithmic half.

`C + log w < w + c` needs `C − c < w − log w`, and the clean way to get it **strictly** without
dividing by two is to make `log w` do double duty: past `exp X₄` we have `2 log w ≤ w`, hence
`log w ≤ w − log w`; and past `exp (C − c)` we have `C − c < log w`. Chaining them gives the strict
inequality with no halving step. -/
theorem x_plus_neg_c_mirrorBand (c : Real) (hc : c < 0) : MirrorBand (fun x => x + c) := by
  refine ⟨x_plus_neg_c_belowIdentity c hc, ?_⟩
  intro C X
  obtain ⟨X₄, _, hlin2⟩ := exp_beats_linear_eventually (1 + 1)
  obtain ⟨w, hwX, hw4, _, hwd, hw1⟩ := exists_big X (exp X₄) X (exp (C - c))
  have hw0 : (0 : Real) < w := lt_of_lt_of_le zero_lt_one_ax hw1
  refine ⟨w, hwX, hw1, ?_⟩
  show C + log w < w + c
  have hlogw : X₄ ≤ log w := by
    have h := log_le_log (exp_pos X₄) hw4
    rw [log_exp] at h; exact h
  have h2log : (1 + 1) * log w ≤ w := by
    have h := hlin2 (log w) hlogw
    rw [exp_log hw0] at h; exact h
  have hhalf : log w ≤ w - log w := by
    have v := add_le_add_wit h2log (le_refl (-log w))
    have l : ((1 : Real) + 1) * log w + -log w = log w := by mach_mpoly [log w]
    have r : w + -log w = w - log w := by mach_mpoly [w, log w]
    rw [l, r] at v; exact v
  have hstrict : C - c < log w := by
    have h := log_lt_log (exp_pos (C - c)) hwd
    rw [log_exp] at h; exact h
  have hchain : C - c < w - log w := lt_of_lt_of_le hstrict hhalf
  have v := add_lt_add_left hchain (c + log w)
  have l : c + log w + (C - c) = C + log w := by mach_mpoly [c, C, log w]
  have r : c + log w + (w - log w) = w + c := by mach_mpoly [c, w, log w]
  rw [l, r] at v; exact v

/-- **No depth-3 tree computes `x + c` for `c < 0`.** The two branches of the dichotomy are now
exhaustive, and each is already closed: bounded by the mirror band, growing by §5. -/
theorem x_plus_neg_c_not_depth_le_three (c : Real) (hc : c < 0) (t : EMLTree) (ht : t.depth ≤ 3)
    (h : ∀ x : Real, 0 < x → t.eval x = x + c) : False := by
  cases Nat.lt_or_ge t.depth 3 with
  | inl hlt => exact x_plus_neg_c_not_depth_le_two c hc t (by omega) h
  | inr hge =>
      cases t with
      | const p =>
          have e : (EMLTree.const p).depth = 0 := rfl
          rw [e] at hge; omega
      | var =>
          have e : (EMLTree.var).depth = 0 := rfl
          rw [e] at hge; omega
      | eml A B =>
          have hd : 1 + Nat.max A.depth B.depth ≤ 3 := ht
          have hm1 : A.depth ≤ Nat.max A.depth B.depth := Nat.le_max_left _ _
          have hm2 : B.depth ≤ Nat.max A.depth B.depth := Nat.le_max_right _ _
          have hA : A.depth ≤ 2 := by omega
          have hB : B.depth ≤ 2 := by omega
          have heq : ∀ x : Real, 0 < x → exp (A.eval x) - log (B.eval x) = x + c := h
          rcases depth_le_two_exp_bounded_or_grows A hA with ⟨K, XK, _, hK⟩ | ⟨T, hT⟩
          · exact mirrorBand_not_depth_three_bounded_left (fun x => x + c)
              (x_plus_neg_c_mirrorBand c hc) A B hB K XK hK heq
          · exact negativeTranslationGrowingLeft_holds c hc A B hA hB ⟨T, hT⟩ heq

/-- **`d_(0,∞)(x + c) = 4` for every `c < 0` — the open cell of §4's table, closed.**

Upper bound: `eml_const_offset_closure` at `K = 1 − c` (positive since `c < 0`, with `K + c = 1`),
which `negOffset_depth` places at depth `2 + 2 + 0 = 4`. That construction was already general in
`c`; the open half was always the lower bound.

**So the value is the same on both sides of zero.** The `{3, 4}` uncertainty was an artefact of the
missing dichotomy, exactly as §4 suspected but could not decide. What is *not* symmetric, and stays
that way, is the argument: the positive side runs through `IntermediateBand` with `x < f x`, while
the negative side needs the mirror band, a depth-≤2 dichotomy that did not exist, and a separate
module for one of its two branches. Equal answers, unequal proofs. -/
theorem x_plus_neg_c_depth_exact_four (c : Real) (hc : c < 0) :
    (∀ t : EMLTree, t.depth ≤ 3 → (∀ x : Real, 0 < x → t.eval x = x + c) → False)
    ∧ (∃ t : EMLTree, t.depth = 4 ∧ ∀ x : Real, 0 < x → t.eval x = x + c) := by
  refine ⟨fun t ht hh => x_plus_neg_c_not_depth_le_three c hc t ht hh, ?_⟩
  have hK : (0 : Real) < 1 - c := by
    have v := add_lt_add_left hc (1 : Real)
    have r : (1 : Real) + 0 = 1 := by mach_ring
    rw [r] at v
    have w := add_lt_add_left v (-c)
    have l2 : -c + (1 + c) = 1 := by mach_mpoly [c]
    have r2 : -c + (1 : Real) = 1 - c := by mach_mpoly [c]
    rw [l2, r2] at w
    exact lt_trans_ax zero_lt_one_ax w
  have hKc : (0 : Real) < 1 - c + c := by
    have e : (1 : Real) - c + c = 1 := by mach_mpoly [c]
    rw [e]; exact zero_lt_one_ax
  refine ⟨negOffset (log (1 - c + c)) (negOffset (log (1 - c)) EMLTree.var), ?_, ?_⟩
  · rw [negOffset_depth, negOffset_depth]
    have e : (EMLTree.var).depth = 0 := rfl
    rw [e]
  · intro x _
    have h := eml_const_offset_closure EMLTree.var hK hKc x
    have e : (EMLTree.var).eval x = x := rfl
    rw [e] at h; exact h

end MachLib
