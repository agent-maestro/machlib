import MachLib.EMLDepthTameness
import MachLib.EMLDecayFloorIsGrowth

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

private theorem le_addr {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have v := add_le_add_wit (le_refl a) hb
  have e : a + (0 : Real) = a := by mach_ring
  rw [e] at v; exact v

private theorem le_addl {a b : Real} (ha : 0 ≤ a) : b ≤ a + b := by
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

end MachLib
