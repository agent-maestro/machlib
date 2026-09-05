import MachLib.EMLDepthTameness

/-!
# The depth-≤2 classification, packaged as a predicate

`depth_le_two_normal_form` (`EMLDepthTameness:5896`) already classifies every depth-≤2 tree:
constant, the identity, or `exp a − log b` with `a` and `b` both in `Depth1Form`. It states that
classification **inline**, about a tree. Depth 1 does not: it has a named predicate `Depth1Form`
together with a one-line wrapper `depth_le_one_form` carrying a tree into it, and that predicate is
what the depth-2 classification itself consumes in its third disjunct.

This file supplies the missing rung of that pattern — `Depth2Form` plus the wrapper — so the depth-3
classification can consume it the same way depth 2 consumes `Depth1Form`.

**Why a predicate rather than the inline statement.** The consumer is a *function*, not a tree: the
depth-3 branch lemmas destructure a node into `exp (a x) − log (b x)` and then need to say "and `a`
is itself a depth-2 shape". There is no tree left at that point to apply `depth_le_two_normal_form`
to. This is exactly why `Depth1Form` exists one level down, and the third disjunct below is where it
is used.

No new mathematics: the wrapper is definitional unfolding, and the proof term is the classification
itself. The content is the packaging, and the packaging is what the next rung is blocked on.
-/

namespace MachLib

open Real

/-- **Normal form at depth ≤ 2, as a predicate on the value function.** Constant, the identity, or
`exp a − log b` with both `a` and `b` in `Depth1Form`. Mirrors `Depth1Form` one level up. -/
def Depth2Form (f : Real → Real) : Prop :=
  (∃ c : Real, ∀ x : Real, 0 < x → f x = c)
  ∨ (∀ x : Real, 0 < x → f x = x)
  ∨ (∃ a b : Real → Real, Depth1Form a ∧ Depth1Form b ∧
      ∀ x : Real, 0 < x → f x = exp (a x) - log (b x))

/-- **Every depth-≤2 tree has `Depth2Form`.** The depth-2 analogue of `depth_le_one_form`; the
classification is `depth_le_two_normal_form`, and this is the wrapper that makes it usable where
only the value function survives. -/
theorem depth_le_two_form (t : EMLTree) (ht : t.depth ≤ 2) : Depth2Form t.eval := by
  -- `depth_le_one_form` needs no unfold because `depth_le_one_classification` already *concludes*
  -- `Depth1Form`. The depth-2 classification states its disjunction inline, so the wrapper has to
  -- open the definition — the one structural difference between the two rungs.
  unfold Depth2Form
  exact depth_le_two_normal_form t ht

/-- **A constant gap below a target for `exp ∘ t`, at depth ≤ 2.**

The depth-2 analogue of `depth_le_one_exp_gap_below` (`EMLDepthTameness:6377`), and the second of
the two inputs `depth_le_three_gap_below` needs (the first is `depth_le_two_form`, above).

**Route: transport, not re-enumeration.** The depth-1 version enumerates all five depth-1 shapes.
This one does not have to. For positive `ν`, `exp (t x) < ν` is exactly `t x < log ν`, so the
*value* gap `depth_le_two_gap_below` already carries the content, and `exp` transports it back:
`t x ≤ log ν − ε₀` gives `exp (t x) ≤ ν · exp (−ε₀)`.

**The gap changes shape under the transport, and that is not a defect.** What comes back is
`ν(1 − exp(−ε₀))` — *proportional* to `ν`, not the value gap `ε₀` itself. A fixed gap below `log ν`
is an exponentially larger gap below `ν` for large `ν`, and a smaller one for small `ν`. Stating it
as `ε₀` would be wrong; stating it proportionally is what the exponential actually gives.

Non-positive `ν` is vacuous: `exp` is positive, so the hypothesis never fires and any `ε` serves. -/
theorem depth_le_two_exp_gap_below (A : EMLTree) (hA : A.depth ≤ 2) (ν : Real) :
    ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → exp (A.eval x) < ν →
      ε ≤ ν - exp (A.eval x) := by
  rcases lt_total 0 ν with hν | hν | hν
  · -- `0 < ν` — the only branch with content.
    obtain ⟨ε₀, X₀, hε₀, hX₀, hg⟩ := depth_le_two_gap_below A hA (log ν)
    have hlt1 : exp (-ε₀) < 1 := by
      have h := exp_lt (neg_neg_of_pos hε₀)
      rw [exp_zero] at h; exact h
    refine ⟨ν - ν * exp (-ε₀), X₀, ?_, hX₀, ?_⟩
    · have h1 : (0 : Real) < 1 - exp (-ε₀) := by
        have u := add_lt_add_left hlt1 (-(exp (-ε₀)))
        have e1 : -(exp (-ε₀)) + exp (-ε₀) = 0 := by mach_ring
        have e2 : -(exp (-ε₀)) + 1 = 1 - exp (-ε₀) := by mach_ring
        rw [e1, e2] at u; exact u
      have h2 : (0 : Real) < ν * (1 - exp (-ε₀)) := mul_pos hν h1
      have e : ν * (1 - exp (-ε₀)) = ν - ν * exp (-ε₀) := by mach_ring
      rw [e] at h2; exact h2
    · intro x hx hlt
      -- `exp (A x) < ν` ⇒ `A x < log ν`, by `log` monotone and `log ∘ exp = id`
      have hAlt : A.eval x < log ν := by
        have h := log_lt_log (exp_pos (A.eval x)) hlt
        rw [log_exp] at h; exact h
      have hgap := hg x hx hAlt
      have hle : A.eval x ≤ log ν - ε₀ := by
        have u := sub_le_sub_left hgap (log ν)
        have e : log ν - (log ν - A.eval x) = A.eval x := by mach_ring
        rw [e] at u; exact u
      have h1 : exp (A.eval x) ≤ exp (log ν - ε₀) := exp_monotone hle
      have h2 : exp (log ν - ε₀) = ν * exp (-ε₀) := by
        have e : log ν - ε₀ = log ν + -ε₀ := by mach_ring
        rw [e, exp_add, exp_log hν]
      rw [h2] at h1
      exact sub_le_sub_left h1 ν
  · -- `ν = 0`: `exp > 0` refutes the hypothesis.
    refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x _ hlt
    rw [← hν] at hlt
    exact absurd (lt_trans_ax (exp_pos (A.eval x)) hlt) (lt_irrefl_ax 0)
  · -- `ν < 0`: likewise.
    refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x _ hlt
    have h0 : (0 : Real) < ν := lt_trans_ax (exp_pos (A.eval x)) hlt
    exact absurd (lt_trans_ax h0 hν) (lt_irrefl_ax 0)

/-- **Firing specimen: the gap statement above is not vacuous.**

`depth_le_two_exp_gap_below` concludes an *implication* — `exp (t x) < ν → ε ≤ ν − exp (t x)` — and
an implication whose hypothesis never fires is true for free. Two of the theorem's three branches
are vacuous by design (`ν ≤ 0` cannot exceed a positive `exp`), so the statement would still compile
if the third branch were vacuous too, and every gate would stay green.

This witnesses that it is not: with `t = const 0` and `ν = exp 1` the hypothesis holds at every `x`
(`exp 0 < exp 1`), so the content branch is reached and the `ε` it produces is a real bound. -/
private theorem depth_le_two_exp_gap_below_fires (x : Real) :
    exp ((EMLTree.const 0).eval x) < exp 1 := by
  show exp 0 < exp 1
  exact exp_lt zero_lt_one_ax

/-! ## The depth-2 logarithm bound is exponential, and that is not a naming accident -/

/-- `EMLDepthTameness`'s `one_le_ray` / `fst_le_ray` are `private`, so the two facts are re-proved
here rather than reached for. Same content, one threshold instead of two. -/
private theorem d2_one_le_shift (a : Real) : (1 : Real) ≤ 1 + exp a := by
  have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos a))
  have e : (1 : Real) + 0 = 1 := by mach_ring
  rw [e] at u; exact u

private theorem d2_le_shift (a : Real) : a ≤ 1 + exp a := by
  have h1 : a ≤ exp a := le_of_lt (exp_grows_strictly_thm a)
  have h2 : exp a ≤ 1 + exp a := by
    have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp a))
    have e : (0 : Real) + exp a = exp a := by mach_ring
    rw [e] at u; exact u
  exact le_trans h1 h2


/-- **There is no linear bound on `log` of a depth-≤2 tree.**

Depth 1 has `depth_le_one_log_le_linear` (`log (B x) ≤ x + C`). Depth 2 has only
`depth_le_two_log_le_exp` (`log (B x) ≤ exp x + K`), and `EMLDecayLadderStep`'s route note once
recorded these as "identical statement". They are not, and the gap between them is where the
depth-4 `const_left` branch loses its argument: `depth_le_two_gap_below`'s growing-left cell closes
because `exp x − (x + D)` outruns any `k`, which spends the **linear** bound. Replace it with the
exponential one and the same cell nets a constant instead of diverging.

So the absence of `depth_le_two_log_le_linear` is a **theorem, not a gap in the corpus**, and this
records it as one. The witness is `exp (exp x − log x) − log 1`: depth 2, and its logarithm is
`exp x − log x`, which outgrows every line.

Proved rather than asserted because the failure mode it guards against is silent — a phantom *name*
fails loudly at elaboration, whereas a bound assumed stronger than it is compiles fine and breaks
whatever consumes it. -/
theorem depth_le_two_log_not_le_linear :
    ¬ ∀ B : EMLTree, B.depth ≤ 2 →
        ∃ C : Real, ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ x + C := by
  intro h
  obtain ⟨C, hC⟩ := h (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) (EMLTree.const 1))
    (by simp [EMLTree.depth])
  obtain ⟨D, hD⟩ := depth_le_one_log_le_linear EMLTree.var (by simp [EMLTree.depth])
  obtain ⟨T, hT⟩ := two_mul_add_le_exp (C + D + 1)
  -- a point past both thresholds
  have hx1 : (1 : Real) ≤ 1 + exp T := d2_one_le_shift T
  have hxT : T ≤ 1 + exp T := d2_le_shift T
  have hCx := hC (1 + exp T) hx1
  have hDx := hD (1 + exp T) hx1
  have hTx := hT (1 + exp T) hxT
  -- `hD` is stated about `EMLTree.var.eval`, which is `x` only up to unfolding
  have hDx' : log (1 + exp T) ≤ (1 + exp T) + D := hDx
  -- the witness' logarithm is `exp x − log x`
  have hval : log ((EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
      (EMLTree.const 1)).eval (1 + exp T))
      = exp (1 + exp T) - log (1 + exp T) := by
    show log (exp (exp (1 + exp T) - log (1 + exp T)) - log (1 : Real)) = _
    rw [log_one]
    have e : exp (exp (1 + exp T) - log (1 + exp T)) - 0
        = exp (exp (1 + exp T) - log (1 + exp T)) := by mach_ring
    rw [e, log_exp]
  rw [hval] at hCx
  -- `exp x − log x ≥ x + (C + 1)`, against `hCx : exp x − log x ≤ x + C`
  have v := add_le_add_wit hTx (neg_le_neg_wit hDx')
  have e1 : (1 + exp T) + (1 + exp T) + (C + D + 1)
      + -((1 + exp T) + D) = (1 + exp T) + (C + 1) := by mach_ring
  have e2 : exp (1 + exp T) + -log (1 + exp T)
      = exp (1 + exp T) - log (1 + exp T) := by mach_ring
  rw [e1, e2] at v
  have hcontra := le_trans v hCx
  have w := add_le_add_wit hcontra (le_refl (-((1 + exp T) + C)))
  have e3 : (1 + exp T) + (C + 1) + -((1 + exp T) + C) = (1 : Real) := by mach_ring
  have e4 : (1 + exp T) + C + -((1 + exp T) + C) = (0 : Real) := by mach_ring
  rw [e3, e4] at w
  exact absurd (lt_of_lt_of_le zero_lt_one_ax w) (lt_irrefl_ax 0)

/-! ## Why the depth-3 gap cannot mirror the depth-2 one -/

/-- **The "growing left child outruns `k`" cell does NOT lift to depth 3 — and fails as badly as
possible.** For *every* real `d` there is a depth-3 node with a growing left child whose value is the
constant `−d`.

`depth_le_two_gap_below` (`EMLDepthTameness:6502`) closes its last cell by arguing that a growing
left child makes the node outrun `k` whatever the right child does. That argument spends
`depth_le_one_log_le_linear`: `exp x − (x + D) → ∞`. At depth 3 the right child has depth ≤ 2, where
the only bound is `log (B x) ≤ exp x + K` (`depth_le_two_log_le_exp`, and the linear bound is
*false* there — see `depth_le_two_log_not_le_linear` above). The left child, growing, supplies only
`exp x ≤ exp (A x)`. The two exponentials then cancel exactly.

The witness makes the cancellation exact rather than approximate: with `A = var` and
`B = eml (eml var (const (exp (−d)))) (const 1)`, the right child evaluates to `exp (exp x + d)`, so
`log (B x) = exp x + d` on the nose and the node is `exp x − (exp x + d) = −d` for every `x`.

**This does not refute `depth_le_three_gap_below`** — a constant node has a constant gap, so the
statement survives. It refutes the *route*: at depth 3 a growing left child no longer forces
divergence, so the cell must be split on whether the cancellation is exact, and that is a question
about the two children *together*. That is the same species of difficulty as `ExpExpGapBelow`, and
it is why the ~145-line mirror estimate in `EMLDecayLadderStep` cannot be met. -/
theorem depth_three_growing_left_can_be_constant (d : Real) :
    ∃ A B : EMLTree, A.depth ≤ 2 ∧ B.depth ≤ 2
      ∧ (∀ x : Real, exp x ≤ exp (A.eval x))
      ∧ (∀ x : Real, exp (A.eval x) - log (B.eval x) = -d) := by
  refine ⟨EMLTree.var,
          EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const (exp (-d)))) (EMLTree.const 1),
          by simp [EMLTree.depth], by simp [EMLTree.depth], fun x => le_refl _, ?_⟩
  intro x
  show exp x - log (exp (exp x - log (exp (-d))) - log (1 : Real)) = -d
  rw [log_exp, log_one]
  -- goal: `exp x - log (exp (exp x - -d) - 0) = -d`; normalise inside the `exp`, then strip the `- 0`
  have e1 : exp x - -d = exp x + d := by mach_ring
  rw [e1]
  have e2 : exp (exp x + d) - 0 = exp (exp x + d) := by mach_ring
  rw [e2, log_exp]
  mach_ring

/-- Two-threshold ray, the `private` `one_le_ray`/`fst_le_ray` re-proved for local use. -/
private theorem d2_ray_ge_one (a b : Real) : (1 : Real) ≤ 1 + exp a + exp b := by
  have u := add_le_add_wit (add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos a)))
    (le_of_lt (exp_pos b))
  have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
  rw [e] at u; exact u

private theorem d2_ray_ge_fst (a b : Real) : a ≤ 1 + exp a + exp b := by
  have h1 : a ≤ exp a := le_of_lt (exp_grows_strictly_thm a)
  have u := add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) h1) (le_of_lt (exp_pos b))
  have e : (0 : Real) + a + 0 = a := by mach_ring
  rw [e] at u; exact u

private theorem d2_ray_ge_snd (a b : Real) : b ≤ 1 + exp a + exp b := by
  have h1 : b ≤ exp b := le_of_lt (exp_grows_strictly_thm b)
  have u := add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos a))) h1
  have e : (0 : Real) + 0 + b = b := by mach_ring
  rw [e] at u; exact u

/-- **The growing-left cell DOES close, under the hypothesis the witness above shows is necessary.**

`depth_three_growing_left_can_be_constant` refutes the depth-2 route because `exp x ≤ exp (A x)` is
too weak: it permits `exp (A x) − exp x = 0`, and then the right child's `exp x + K` cancels the node
down to a constant. The repair is to ask for the *margin* to diverge rather than for the node to
grow — and once asked for, the cell is easy.

**Stating the margin as `exp x + M ≤ exp (A x)` rather than `x + δ ≤ A x` is what keeps this short.**
A `δ`-margin on `A` multiplies through the exponential (`exp (x+δ) − exp x = exp x (exp δ − 1)`) and
would need a product-divergence lemma this base does not have. Phrased additively *after* the
exponential, the two `exp x` terms cancel outright and the whole proof is three inequalities. -/
theorem depth_three_node_ge_of_exp_margin (A B : EMLTree) (hB : B.depth ≤ 2) (k : Real)
    (hA : ∀ M : Real, ∃ T : Real, 1 ≤ T ∧ ∀ x : Real, T ≤ x → exp x + M ≤ exp (A.eval x)) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → k ≤ exp (A.eval x) - log (B.eval x) := by
  obtain ⟨K, XB, hXB1, hK⟩ := depth_le_two_log_le_exp B hB
  obtain ⟨T, hT1, hT⟩ := hA (k + K)
  refine ⟨1 + exp T + exp XB, d2_ray_ge_one T XB, ?_⟩
  intro x hx
  have hxT : T ≤ x := le_trans (d2_ray_ge_fst T XB) hx
  have hxB : XB ≤ x := le_trans (d2_ray_ge_snd T XB) hx
  -- `exp x + (k + K) ≤ exp (A x)` and `log (B x) ≤ exp x + K`; the `exp x` terms cancel
  have v := add_le_add_wit (hT x hxT) (neg_le_neg_wit (hK x hxB))
  have e1 : exp x + (k + K) + -(exp x + K) = k := by mach_ring
  have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
  rw [e1, e2] at v
  exact v

/-- **The exponential margin grows at least as fast as the argument gap:
`exp x + (v − x) ≤ exp v` for `0 ≤ x ≤ v`.**

This is the tool that makes the margin hypothesis of `depth_three_node_ge_of_exp_margin` checkable.
That theorem asks for `exp x + M ≤ exp (A x)` — a statement *after* the exponential, which is awkward
to verify shape by shape. This lemma reduces it to `x + M ≤ A x`, a statement *before* it.

The proof is the tangent-line bound `1 + t ≤ exp t` (`Exp.lean:111`) applied to the gap, multiplied
back by `exp x ≥ 1`: `exp v = exp x · exp (v−x) ≥ exp x · (1 + (v−x)) = exp x + exp x · (v−x)`, and
`exp x ≥ 1` turns the last product into at least `v − x`. Nothing here is depth-specific — it is a
fact about `exp` that the depth-3 argument happens to need. -/
theorem exp_margin_ge {x v : Real} (hx : 0 ≤ x) (hv : x ≤ v) : exp x + (v - x) ≤ exp v := by
  have hd : (0 : Real) ≤ v - x := by
    have u := add_le_add_wit hv (le_refl (-x))
    have e1 : x + -x = (0 : Real) := by mach_ring
    have e2 : v + -x = v - x := by mach_ring
    rw [e1, e2] at u; exact u
  have he1 : (1 : Real) ≤ exp x := by
    have u : (1 : Real) ≤ 1 + x := by
      have w := add_le_add_wit (le_refl (1 : Real)) hx
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at w; exact w
    exact le_trans u (one_add_le_exp x)
  -- `exp x * exp (v−x) = exp v`. Note the direction: rewriting `v` into `x + (v−x)` would also
  -- rewrite the `v` inside `v − x`, so the equation is oriented to collapse the product instead.
  have hexpv : exp x * exp (v - x) = exp v := by
    rw [← exp_add]
    -- `mach_ring` normalises this to `x + (v + -x) = v` and stops; `mach_mpoly` closes it once the
    -- atoms are named. Same trap recorded for the numeral wall -- reach for the complete normaliser.
    have e : x + (v - x) = v := by mach_mpoly [x, v]
    rw [e]
  have hstep := mul_le_mul_of_nonneg_left (one_add_le_exp (v - x)) (le_of_lt (exp_pos x))
  have hgap : v - x ≤ exp x * (v - x) := by
    have u := mul_le_mul_of_nonneg_left he1 hd
    have e1 : (v - x) * 1 = v - x := by mach_ring
    have e2 : (v - x) * exp x = exp x * (v - x) := by mach_ring
    rw [e1, e2] at u; exact u
  have hsum : exp x + (v - x) ≤ exp x * (1 + (v - x)) := by
    have u := add_le_add_wit (le_refl (exp x)) hgap
    have e : exp x + exp x * (v - x) = exp x * (1 + (v - x)) := by mach_ring
    rw [e] at u; exact u
  rw [← hexpv]
  exact le_trans hsum hstep

/-- **The margin hypothesis, in terms of the argument rather than its exponential.**

Feeds `depth_three_node_ge_of_exp_margin` directly: if `A` outgrows the identity by every margin,
then `exp ∘ A` outgrows `exp` by every margin. Checking the former is a statement about
`Depth2Form`'s disjuncts; checking the latter was not.

The `M = 0` instance is taken separately to get `x ≤ A x`: a margin at some *negative* `M` says
nothing about `A` dominating the identity, so the ordering cannot be recovered from the `M` in hand. -/
theorem exp_margin_of_arg_margin {A : EMLTree}
    (h : ∀ M : Real, ∃ T : Real, 1 ≤ T ∧ ∀ x : Real, T ≤ x → x + M ≤ A.eval x) :
    ∀ M : Real, ∃ T : Real, 1 ≤ T ∧ ∀ x : Real, T ≤ x → exp x + M ≤ exp (A.eval x) := by
  intro M
  obtain ⟨T, hT1, hT⟩ := h M
  obtain ⟨T0, hT01, hT0⟩ := h 0
  refine ⟨1 + exp T + exp T0, d2_ray_ge_one T T0, ?_⟩
  intro x hx
  have hxT : T ≤ x := le_trans (d2_ray_ge_fst T T0) hx
  have hxT0 : T0 ≤ x := le_trans (d2_ray_ge_snd T T0) hx
  have hx0 : (0 : Real) ≤ x :=
    le_trans (le_of_lt zero_lt_one_ax) (le_trans (d2_ray_ge_one T T0) hx)
  have hxA : x ≤ A.eval x := by
    have u := hT0 x hxT0
    have e : x + (0 : Real) = x := by mach_ring
    rw [e] at u; exact u
  have hgap : M ≤ A.eval x - x := by
    have u := add_le_add_wit (hT x hxT) (le_refl (-x))
    have e1 : x + M + -x = M := by mach_ring
    have e2 : A.eval x + -x = A.eval x - x := by mach_ring
    rw [e1, e2] at u; exact u
  have u := add_le_add_wit (le_refl (exp x)) hgap
  exact le_trans u (exp_margin_ge hx0 hxA)

private theorem d2_ray_gt_fst (a b : Real) : a < 1 + exp a + exp b := by
  have h1 : a < exp a := exp_grows_strictly_thm a
  have h2 : exp a ≤ 1 + exp a + exp b := by
    have u := add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp a)))
      (le_of_lt (exp_pos b))
    have e : (0 : Real) + exp a + 0 = exp a := by mach_ring
    rw [e] at u; exact u
  exact lt_of_lt_of_le h1 h2

/-- **A growing depth-≤2 tree either IS the identity, or outgrows it by every margin.**

This is the trichotomy the growing cell needs, and it closes the conjecture left open by
`depth_three_growing_left_can_be_constant`: the witness there (`A = var`) is not one awkward case
among many, it is **the only** obstruction at depth ≤ 2.

Case on the tree rather than on `Depth2Form`. The predicate hands back *functions* `a b : Real → Real`
with `Depth1Form`, and the depth-1 toolkit (`depth_le_one_exp_bounded_or_grows`,
`depth_le_one_log_le_linear`, `depth_le_one_log_lower_at_infinity`) is stated about *trees* — so
destructuring `eml a b` gives children of depth ≤ 1 that those lemmas apply to directly, where
`Depth2Form` would have forced a five-way re-derivation of each. The predicate is the right tool for
consumers that have lost the tree; here the tree is still in hand.

* `const c` — cannot be growing: `x ≤ c` fails at `x = 1 + exp c`, since `c < exp c`.
* `var` — the identity, and the right disjunct. This is the residue.
* `eml a b` — split `a` on bounded-or-grows. Bounded is impossible: `exp (a x) ≤ K` and
  `Cl ≤ log (b x)` cap the node at `K − Cl`, which growth outruns. Growing gives
  `exp x ≤ exp (a x)` and `log (b x) ≤ x + D`, so the node is at least `exp x − (x + D)`, and
  `exp x ≥ x + x + (M + D)` turns that into `x + M`.

Combined with `exp_margin_of_arg_margin` and `depth_three_node_ge_of_exp_margin`, the depth-3 growing
cell is now closed **except** when the left child is the identity. -/
theorem depth_le_two_growing_identity_or_margin (A : EMLTree) (hA : A.depth ≤ 2)
    (hgrow : ∀ x : Real, 1 ≤ x → x ≤ A.eval x) :
    (∀ M : Real, ∃ T : Real, 1 ≤ T ∧ ∀ x : Real, T ≤ x → x + M ≤ A.eval x)
    ∨ (∀ x : Real, A.eval x = x) := by
  cases A with
  | const c =>
      exfalso
      have h := hgrow (1 + exp c) (d2_one_le_shift c)
      have hlt : c < 1 + exp c := by
        have h1 : c < exp c := exp_grows_strictly_thm c
        have h2 : exp c ≤ 1 + exp c := by
          have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp c))
          have e : (0 : Real) + exp c = exp c := by mach_ring
          rw [e] at u; exact u
        exact lt_of_lt_of_le h1 h2
      exact absurd (lt_of_lt_of_le hlt h) (lt_irrefl_ax c)
  | var => exact Or.inr (fun _ => rfl)
  | eml a b =>
      have ha : a.depth ≤ 1 := by
        simp only [EMLTree.depth] at hA
        have := Nat.le_max_left a.depth b.depth; omega
      have hb : b.depth ≤ 1 := by
        simp only [EMLTree.depth] at hA
        have := Nat.le_max_right a.depth b.depth; omega
      rcases depth_le_one_exp_bounded_or_grows a ha with ⟨K, hK⟩ | ⟨T, hT⟩
      · -- bounded left child: the node is capped, so it cannot dominate the identity
        exfalso
        obtain ⟨Cl, X₀, hX₀1, hCl⟩ := depth_le_one_log_lower_at_infinity b hb
        have hx1 : (1 : Real) ≤ 1 + exp (K - Cl) + exp X₀ := d2_ray_ge_one (K - Cl) X₀
        have hxX : X₀ ≤ 1 + exp (K - Cl) + exp X₀ := d2_ray_ge_snd (K - Cl) X₀
        have hnode := hgrow (1 + exp (K - Cl) + exp X₀) hx1
        have hcap : (EMLTree.eml a b).eval (1 + exp (K - Cl) + exp X₀) ≤ K - Cl := by
          show exp (a.eval (1 + exp (K - Cl) + exp X₀))
              - log (b.eval (1 + exp (K - Cl) + exp X₀)) ≤ K - Cl
          have u := add_le_add_wit (hK (1 + exp (K - Cl) + exp X₀) hx1)
            (neg_le_neg_wit (hCl (1 + exp (K - Cl) + exp X₀) hxX))
          have e1 : exp (a.eval (1 + exp (K - Cl) + exp X₀))
              + -log (b.eval (1 + exp (K - Cl) + exp X₀))
              = exp (a.eval (1 + exp (K - Cl) + exp X₀))
                - log (b.eval (1 + exp (K - Cl) + exp X₀)) := by mach_ring
          have e2 : K + -Cl = K - Cl := by mach_ring
          rw [e1, e2] at u; exact u
        exact absurd (lt_of_lt_of_le (d2_ray_gt_fst (K - Cl) X₀) (le_trans hnode hcap))
          (lt_irrefl_ax (K - Cl))
      · -- growing left child: the node beats every margin
        left
        intro M
        obtain ⟨D, hD⟩ := depth_le_one_log_le_linear b hb
        obtain ⟨T2, hT2⟩ := two_mul_add_le_exp (M + D)
        refine ⟨1 + exp T + exp T2, d2_ray_ge_one T T2, ?_⟩
        intro x hx
        have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_one T T2) hx
        have hxT : T ≤ x := le_trans (d2_ray_ge_fst T T2) hx
        have hxT2 : T2 ≤ x := le_trans (d2_ray_ge_snd T T2) hx
        show x + M ≤ exp (a.eval x) - log (b.eval x)
        have v1 := add_le_add_wit (hT x hxT) (neg_le_neg_wit (hD x hx1))
        have v2 := add_le_add_wit (hT2 x hxT2) (le_refl (-(x + D)))
        have e1 : x + x + (M + D) + -(x + D) = x + M := by mach_mpoly [x, M, D]
        have e2 : exp (a.eval x) + -log (b.eval x)
            = exp (a.eval x) - log (b.eval x) := by mach_ring
        rw [e1] at v2
        rw [e2] at v1
        exact le_trans v2 v1

/-- A point past two thresholds whose exponential also clears a third. -/
private theorem d3_big_point (X₀ L : Real) : ∃ x : Real, 1 ≤ x ∧ X₀ ≤ x ∧ L < exp x :=
  ⟨1 + exp X₀ + exp L, d2_ray_ge_one X₀ L, d2_ray_ge_fst X₀ L,
   lt_of_le_of_lt (d2_ray_ge_snd X₀ L) (exp_grows_strictly_thm _)⟩

/-- The witness tree's right child evaluates to `exp (exp x) + 1`. -/
private theorem d3_witness_right (y : Real) :
    (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.const (exp (-1)))).eval y = exp (exp y) + 1 := by
  show exp (exp y - log (1 : Real)) - log (exp (-1)) = exp (exp y) + 1
  rw [log_one, log_exp]
  have e : exp y - (0 : Real) = exp y := by mach_ring
  rw [e]
  mach_ring

/-- **`depth_le_three_gap_below` is FALSE — there is no depth-3 analogue of
`depth_le_two_gap_below`.** A depth-3 tree can approach a target from below with the gap shrinking
to zero, so no uniform `ε` exists.

Witness: `t = eml var (eml (eml var (const 1)) (const (exp (-1))))`, depth 3, with

  `t x = exp x − log (exp (exp x) + 1) = −log (1 + exp (−exp x))`

negative for every `x` and tending to `0`. At `k = 0` the hypothesis `t x < k` holds everywhere while
`k − t x → 0`. Numerically `−1.9e−9` at `x = 3`, `−1.9e−24` at `x = 4`.

**Not an artefact of `k = 0`.** Replacing `const 1` by `const (exp d)` gives `t x → d` from below, so
the construction refutes the statement at *every* target — including `d = exp (exp c)`, which is
exactly the instance `depth_three_decay_const_left` consumes (`EMLDepthTameness:6650`). The depth-4
`const_left` cell therefore cannot be routed through a depth-3 gap lemma: there is no such lemma to
prove, and the ~145-line estimate in `EMLDecayLadderStep` was pricing an impossibility.

**Why depth 2 escapes.** Cancellation needs `log (B x)` to reach `exp (A x)`. At depth 2 the right
child is at most singly exponential, so `log (B x)` is at most linear, while `exp (A x)` is constant,
`exp x`, or doubly exponential — they can never meet. At depth 3 the right child reaches doubly
exponential, so `log (B x)` reaches `exp x`, and `A = var` makes the two cancel exactly. That is the
same boundary `depth_le_two_log_not_le_linear` marks from the other side. -/
theorem depth_le_three_gap_below_refuted :
    ¬ ∀ t : EMLTree, t.depth ≤ 3 → ∀ k : Real,
        ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧
          ∀ x : Real, X₀ ≤ x → t.eval x < k → ε ≤ k - t.eval x := by
  intro h
  obtain ⟨ε, X₀, hε, hX₀, hgap⟩ :=
    h (EMLTree.eml EMLTree.var (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
        (EMLTree.const (exp (-1))))) (by simp [EMLTree.depth]) 0
  have hc : (0 : Real) < exp ε - 1 := by
    have h1 : (1 : Real) < exp ε := by
      have w := exp_lt hε
      rw [exp_zero] at w; exact w
    have u := add_lt_add_left h1 (-(1 : Real))
    have e1 : -(1 : Real) + 1 = 0 := by mach_ring
    have e2 : -(1 : Real) + exp ε = exp ε - 1 := by mach_ring
    rw [e1, e2] at u; exact u
  obtain ⟨x, hx1, hxX, hxL⟩ := d3_big_point X₀ (-log (exp ε - 1))
  -- `1 < exp (exp x) * (exp ε − 1)`, established through logs to avoid any division
  have hprodpos : (0 : Real) < exp (exp x) * (exp ε - 1) := mul_pos (exp_pos _) hc
  have hlogprod : log (exp (exp x) * (exp ε - 1)) = exp x + log (exp ε - 1) := by
    rw [log_mul (exp_pos _) hc, log_exp]
  have hprodgt : (1 : Real) < exp (exp x) * (exp ε - 1) := by
    have hpos : (0 : Real) < log (exp (exp x) * (exp ε - 1)) := by
      rw [hlogprod]
      have u := add_lt_add_left hxL (log (exp ε - 1))
      have e1 : log (exp ε - 1) + -log (exp ε - 1) = (0 : Real) := by mach_ring
      have e2 : log (exp ε - 1) + exp x = exp x + log (exp ε - 1) := by mach_ring
      rw [e1, e2] at u; exact u
    have w := exp_lt hpos
    rw [exp_zero, exp_log hprodpos] at w
    exact w
  -- hence `exp (exp x) + 1 < exp (exp x) * exp ε`
  have hstep : exp (exp x) + 1 < exp (exp x) * exp ε := by
    have u := add_lt_add_left hprodgt (exp (exp x))
    have e : exp (exp x) + exp (exp x) * (exp ε - 1) = exp (exp x) * exp ε := by
      mach_mpoly [exp (exp x), exp ε]
    rw [e] at u; exact u
  -- so `log (exp (exp x) + 1) < exp x + ε`
  have hone : (0 : Real) < exp (exp x) + 1 := by
    have u := add_lt_add_left zero_lt_one_ax (exp (exp x))
    have e : exp (exp x) + (0 : Real) = exp (exp x) := by mach_ring
    rw [e] at u
    exact lt_trans_ax (exp_pos _) u
  have hlog : log (exp (exp x) + 1) < exp x + ε := by
    have w := log_lt_log hone hstep
    rw [log_mul (exp_pos _) (exp_pos _), log_exp, log_exp] at w
    exact w
  -- the node is negative, so the gap hypothesis fires
  have hEltE1 : exp (exp x) < exp (exp x) + 1 := by
    have u := add_lt_add_left zero_lt_one_ax (exp (exp x))
    have e : exp (exp x) + (0 : Real) = exp (exp x) := by mach_ring
    rw [e] at u; exact u
  have hxlt : exp x < log (exp (exp x) + 1) := by
    have w := log_lt_log (exp_pos _) hEltE1
    rw [log_exp] at w; exact w
  have hneg : (EMLTree.eml EMLTree.var (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.const (exp (-1))))).eval x < 0 := by
    show exp x - log ((EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.const (exp (-1)))).eval x) < 0
    rw [d3_witness_right]
    have u := add_lt_add_left hxlt (-log (exp (exp x) + 1))
    have e1 : -log (exp (exp x) + 1) + exp x = exp x - log (exp (exp x) + 1) := by mach_ring
    have e2 : -log (exp (exp x) + 1) + log (exp (exp x) + 1) = (0 : Real) := by mach_ring
    rw [e1, e2] at u; exact u
  -- but the gap it forces contradicts `hlog`
  have hforced := hgap x hxX hneg
  rw [show (EMLTree.eml EMLTree.var (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.const (exp (-1))))).eval x = exp x - log (exp (exp x) + 1) from by
        show exp x - log ((EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
          (EMLTree.const (exp (-1)))).eval x) = _
        rw [d3_witness_right]] at hforced
  have hsmall : (0 : Real) - (exp x - log (exp (exp x) + 1)) < ε := by
    have u := add_lt_add_left hlog (-exp x)
    have e1 : -exp x + log (exp (exp x) + 1) = 0 - (exp x - log (exp (exp x) + 1)) := by
      mach_mpoly [exp x, log (exp (exp x) + 1)]
    have e2 : -exp x + (exp x + ε) = ε := by mach_mpoly [exp x, ε]
    rw [e1, e2] at u; exact u
  exact absurd (lt_of_le_of_lt hforced hsmall) (lt_irrefl_ax ε)

/-- **The decaying floor DOES hold on the very witness that refutes the constant gap.**

`depth_le_three_gap_below_refuted` kills the *shape* of the depth-3 statement, not the branch. What
`const_left` needs is `−log (exp c − log (Q x)) ≤ C + towerFn m x`, and an exponentially shrinking
gap still supplies that — `−log` of an exponentially small quantity is only *linearly* large in the
tower's argument. The replacement shape therefore mirrors `depth_le_two_approach_constant`
(`EMLDepthTameness:5751`), which already carries a decaying floor for approach from *above*:

    t x < k  →  exp (−C − exp x) ≤ k − t x

This is the firing specimen for that shape, on the witness where the constant version provably
fails, with `k = 0` and **`C = 1`**.

**`C = 1` makes it exact, which is why the constant is `1` and not a slack bound.** Writing
`z = exp (−1 − exp x)`, the tangent bound `exp z ≤ 1 + z·e` (`exp_le_one_add_scaled`) gives
`exp (exp x) · exp z ≤ exp (exp x) + exp (exp x)·z·e`, and `exp (exp x)·z·e = exp (exp x − 1 − exp x + 1) = exp 0 = 1`
exactly. So the inequality closes with no room to spare — `C = 1` is forced by the algebra, not chosen.
Numerically the true gap is `e/2 ≈ 1.36` times this floor.

Note the exponent: depth 2's floor is `exp (−C − x)`, depth 3's is `exp (−C − exp x)`. That is the
corpus's own "one level of nesting buys exactly one exponential", stated for the growth side in
`depth_le_two_growth_envelope`, appearing here on the decay side. -/
theorem depth_three_witness_decaying_floor (x : Real) :
    exp (-1 - exp x)
      ≤ 0 - (EMLTree.eml EMLTree.var (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
          (EMLTree.const (exp (-1))))).eval x := by
  have hz0 : (0 : Real) ≤ exp (-1 - exp x) := le_of_lt (exp_pos _)
  have hz1 : exp (-1 - exp x) ≤ 1 := by
    have hneg : -1 - exp x < 0 := by
      have u := add_lt_add_left (exp_pos x) (-1 - exp x)
      have e1 : -1 - exp x + 0 = -1 - exp x := by mach_ring
      have e2 : -1 - exp x + exp x = -1 := by mach_mpoly [exp x]
      rw [e1, e2] at u
      exact lt_trans_ax u (by
        have w := add_lt_add_left zero_lt_one_ax (-(1 : Real))
        have f1 : -(1 : Real) + 0 = -1 := by mach_ring
        have f2 : -(1 : Real) + 1 = 0 := by mach_ring
        rw [f1, f2] at w; exact w)
    have w := exp_monotone (le_of_lt hneg)
    rw [exp_zero] at w; exact w
  -- `exp (exp x) * exp z ≤ exp (exp x) + 1`, exactly
  have hkey : exp (exp x) * (exp (-1 - exp x) * exp 1) = 1 := by
    rw [← exp_add, ← exp_add]
    have e : exp x + (-1 - exp x + 1) = 0 := by mach_mpoly [exp x]
    rw [e, exp_zero]
  have hmul := mul_le_mul_of_nonneg_left (exp_le_one_add_scaled hz0 hz1)
    (le_of_lt (exp_pos (exp x)))
  have hbound : exp (exp x) * exp (exp (-1 - exp x)) ≤ exp (exp x) + 1 := by
    have e : exp (exp x) * (1 + exp (-1 - exp x) * exp 1)
        = exp (exp x) + exp (exp x) * (exp (-1 - exp x) * exp 1) := by
      mach_mpoly [exp (exp x), exp (-1 - exp x), exp 1]
    rw [e, hkey] at hmul
    exact hmul
  -- so `exp x + z ≤ log (exp (exp x) + 1)`
  have hsum : exp (exp x + exp (-1 - exp x)) ≤ exp (exp x) + 1 := by
    rw [exp_add]; exact hbound
  have hlog : exp x + exp (-1 - exp x) ≤ log (exp (exp x) + 1) := by
    have w := log_le_log (exp_pos _) hsum
    rw [log_exp] at w; exact w
  -- unfold the witness and rearrange
  show exp (-1 - exp x)
    ≤ 0 - (exp x - log ((EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
        (EMLTree.const (exp (-1)))).eval x))
  rw [d3_witness_right]
  have u := add_le_add_wit hlog (le_refl (-exp x))
  have e1 : exp x + exp (-1 - exp x) + -exp x = exp (-1 - exp x) := by
    mach_mpoly [exp x, exp (-1 - exp x)]
  have e2 : log (exp (exp x) + 1) + -exp x = 0 - (exp x - log (exp (exp x) + 1)) := by
    mach_mpoly [exp x, log (exp (exp x) + 1)]
  rw [e1, e2] at u
  exact u

private theorem d2_ray_ge_expsnd (a b : Real) : exp b ≤ 1 + exp a + exp b := by
  have u := add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos a)))
    (le_refl (exp b))
  have e : (0 : Real) + 0 + exp b = exp b := by mach_ring
  rw [e] at u; exact u

/-- The second witness evaluates to `exp (exp y) − log (exp (1 − log y) + 1)`. -/
private theorem d3_expexp_witness (y : Real) :
    (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.eml (EMLTree.eml (EMLTree.const 0) EMLTree.var)
        (EMLTree.const (exp (-1))))).eval y
      = exp (exp y) - log (exp (1 - log y) + 1) := by
  show exp (exp y - log (1 : Real))
      - log (exp (exp (0 : Real) - log y) - log (exp (-1))) = _
  rw [log_one, exp_zero, log_exp]
  have e1 : exp y - (0 : Real) = exp y := by mach_ring
  have e2 : exp ((1 : Real) - log y) - -1 = exp (1 - log y) + 1 := by
    mach_mpoly [exp ((1 : Real) - log y)]
  rw [e1, e2]

/-- **`ExpExpGapBelow` also fails at depth 3 — the collapse is systematic, not specific to
`const_left`.**

`depth_le_three_gap_below_refuted` kills the constant-gap shape for the `const_left` cell. This kills
it for `var_left` too: `ExpExpGapBelow` (`EMLDepthTameness:6909`) is a *theorem* for depth-≤2 `Q`,
and its depth-≤3 analogue is false.

Witness, depth 3:

    Q = eml (eml var (const 1)) (eml (eml (const 0) var) (const (exp (-1))))
    Q y = exp (exp y) − log (exp (1 − log y) + 1)

so `exp (exp y) − Q y = log (1 + e/y)`, which is strictly positive for every `y` — the hypothesis
`Q y < exp (exp y)` therefore fires everywhere — and tends to `0`, so no uniform `ε` exists.

**The decay rate is the useful part.** Here the gap vanishes only **polynomially** (`~1/y`: `9.9e−3`
at `y = 100`, `1.0e−16` at `y = 1e16`), against the **doubly exponential** vanishing of the
`const_left` witness. So the two cells need floors of very different strength — `exp (−C − log y)`
suffices here where `const_left` needs `exp (−C − exp y)`. A single decaying-floor shape covers both
only if it is taken at the weaker (`const_left`) rate.

**Why depth 2 is safe**, which is what makes `ExpExpGapBelow` provable there: the offset must tend to
`0` from *above*, and at depth ≤ 1 nothing does — the shapes are constant, `x`, `c − log x`,
`exp x − d`, `exp x − log x`, which go to a constant, `±∞`, or hit `0` exactly. The vanishing offset
here is `exp (1 − log y)`, and building it needs a `log` inside an `exp`, i.e. one more level. -/
private theorem d3_expexp_small {ε X : Real} (hc : 0 < exp ε - 1)
    (hX : 1 + 1 - log (exp ε - 1) ≤ log X) : log (exp (1 - log X) + 1) < ε := by
  have h1 : 1 - log X < log (exp ε - 1) := by
    have u := add_le_add_wit (le_refl (1 : Real)) (neg_le_neg_wit hX)
    have e1 : (1 : Real) + -(1 + 1 - log (exp ε - 1)) = log (exp ε - 1) - 1 := by
      mach_mpoly [log (exp ε - 1)]
    have e2 : (1 : Real) + -log X = 1 - log X := by mach_mpoly [log X]
    rw [e1, e2] at u
    have hlt : log (exp ε - 1) - 1 < log (exp ε - 1) := by
      have w := add_lt_add_left zero_lt_one_ax (log (exp ε - 1) - 1)
      have f1 : log (exp ε - 1) - 1 + 0 = log (exp ε - 1) - 1 := by mach_ring
      have f2 : log (exp ε - 1) - 1 + 1 = log (exp ε - 1) := by mach_mpoly [log (exp ε - 1)]
      rw [f1, f2] at w; exact w
    exact lt_of_le_of_lt u hlt
  have h2 : exp (1 - log X) < exp ε - 1 := by
    have w := exp_lt h1
    rw [exp_log hc] at w; exact w
  have h3 : exp (1 - log X) + 1 < exp ε := by
    have u := add_lt_add_left h2 (1 : Real)
    have e1 : (1 : Real) + exp (1 - log X) = exp (1 - log X) + 1 := by
      mach_mpoly [exp (1 - log X)]
    have e2 : (1 : Real) + (exp ε - 1) = exp ε := by mach_mpoly [exp ε]
    rw [e1, e2] at u; exact u
  have hpos : (0 : Real) < exp (1 - log X) + 1 := by
    have u := add_lt_add_left (exp_pos (1 - log X)) (0 : Real)
    have e1 : (0 : Real) + 0 = 0 := by mach_ring
    have e2 : (0 : Real) + exp (1 - log X) = exp (1 - log X) := by mach_ring
    rw [e1, e2] at u
    exact lt_trans_ax u (by
      have w := add_lt_add_left zero_lt_one_ax (exp (1 - log X))
      have f1 : exp (1 - log X) + 0 = exp (1 - log X) := by mach_ring
      rw [f1] at w; exact w)
  have w := log_lt_log hpos h3
  rw [log_exp] at w; exact w

theorem expExpGapBelow_depth_three_refuted :
    ¬ ∀ Q : EMLTree, Q.depth ≤ 3 → ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧
        ∀ x : Real, X₀ ≤ x → Q.eval x < exp (exp x) → ε ≤ exp (exp x) - Q.eval x := by
  intro h
  obtain ⟨ε, X₀, hε, hX₀, hgap⟩ :=
    h (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
        (EMLTree.eml (EMLTree.eml (EMLTree.const 0) EMLTree.var)
          (EMLTree.const (exp (-1))))) (by simp [EMLTree.depth])
  have hc : (0 : Real) < exp ε - 1 := by
    have h1 : (1 : Real) < exp ε := by
      have w := exp_lt hε
      rw [exp_zero] at w; exact w
    have u := add_lt_add_left h1 (-(1 : Real))
    have e1 : -(1 : Real) + 1 = 0 := by mach_ring
    have e2 : -(1 : Real) + exp ε = exp ε - 1 := by mach_ring
    rw [e1, e2] at u; exact u
  -- evaluate past `exp (1 + 1 - log (exp ε - 1))`, so that `1 - log x < log (exp ε - 1)`
  have hx1 : (1 : Real) ≤ 1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)) := d2_ray_ge_one _ _
  have hxX : X₀ ≤ 1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)) := d2_ray_ge_fst _ _
  have hxE : exp (1 + 1 - log (exp ε - 1)) ≤ 1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)) :=
    d2_ray_ge_expsnd _ _
  have hxpos : (0 : Real) < 1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)) :=
    lt_of_lt_of_le zero_lt_one_ax hx1
  -- the hypothesis fires: the offset is strictly positive
  have hoff : (0 : Real) < exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) := exp_pos _
  have hBgt : (1 : Real) < exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1 := by
    have u := add_lt_add_left hoff (1 : Real)
    have e1 : (1 : Real) + 0 = 1 := by mach_ring
    have e2 : (1 : Real) + exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1))))
        = exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1 := by
      mach_mpoly [exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1))))]
    rw [e1, e2] at u; exact u
  have hlogpos : (0 : Real)
      < log (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1) := by
    have w := log_lt_log zero_lt_one_ax hBgt
    rw [log_one] at w; exact w
  -- the evaluation point clears the threshold, so the remaining gap is below `ε`
  have hlogX : 1 + 1 - log (exp ε - 1)
      ≤ log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1))) := by
    have w := log_le_log (exp_pos _) hxE
    rw [log_exp] at w; exact w
  have hsmall := d3_expexp_small hc hlogX
  -- and the hypothesis of the gap statement fires
  have hlt : (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.eml (EMLTree.eml (EMLTree.const 0) EMLTree.var)
        (EMLTree.const (exp (-1))))).eval (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))
      < exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) := by
    rw [d3_expexp_witness]
    have u := add_lt_add_left hlogpos
      (exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) - log
        (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1))
    have e1 : exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) - log
        (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1) + 0
        = exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) - log
          (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1) := by mach_ring
    have e2 : exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) - log
        (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1)
        + log (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1)
        = exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) := by
      mach_mpoly [exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))),
        log (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1)]
    rw [e1, e2] at u; exact u
  have hforced := hgap _ hxX hlt
  rw [d3_expexp_witness] at hforced
  have e : exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1))))
      - (exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) - log
        (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1))
      = log (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1) := by
    mach_mpoly [exp (exp (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))),
      log (exp (1 - log (1 + exp X₀ + exp (1 + 1 - log (exp ε - 1)))) + 1)]
  rw [e] at hforced
  exact absurd (lt_of_le_of_lt hforced hsmall) (lt_irrefl_ax ε)

/-! ## The depth-3 statement in the shape that survives, and its residue -/

/-! ### The replacement was attacked before it was adopted

Two statements were refuted today by finding a tree whose gap vanishes, so the replacement was given
the same treatment before any effort went into proving it.

**The extremal approach-from-below at depth 3.** Take `t = eml var B` with
`B = eml (eml var (const (exp k))) (const α)` and `α ∈ (0,1)`. Then `B x = exp (exp x − k) + c` with
`c = −log α > 0`, and

    t x = k − log (1 + c·e^k·e^(−exp x))   →   k  from below,

so the gap is `≈ c·e^k·exp (−exp x)`. That is the *fastest* a depth-3 tree can approach from below,
and `exp (−C − exp x)` already sits under it (checked `x = 1..24`; at `x = 4` the gap is `1.9e−24`
against a `towerFn 1` floor of `7.1e−25`). `towerFn 2` has room to spare — at `x = 4` it is
`3e−223593715528665832814074`.

**Why it cannot be beaten, and it is the same fact as everywhere else today.** The gap is driven by
how far `B x` sits above its target, and that offset is `−log (b₂ x)` for a child `b₂` of depth ≤ 1.
For the offset to shrink to nothing, `b₂ x` would have to tend to `1` *from one side* — and no
depth-≤1 shape does: they are constant, `x`, `c − log x`, `exp x − d`, `exp x − log x`, which tend to
a constant, to `±∞`, or hit the value exactly (whereupon the hypothesis stops firing). So the offset
is bounded below by a positive constant, and the gap is bounded below by `C·exp (−exp x)`.

**That single fact cuts both ways**, which is what makes the pair of results coherent rather than
lucky. *No depth-≤1 shape tends to `0` from above* is why the **constant**-gap statement is FALSE —
the offset can shrink relative to a doubly exponential target — and simultaneously why the
**decaying**-floor statement is TRUE — the offset cannot shrink below a constant in absolute terms.
The same sentence refutes one shape and validates the other.
-/

/-- **Approach from below with a decaying floor, at depth ≤ 3.** The replacement for the refuted
`depth_le_three_gap_below`. The floor is `exp (−C − exp (exp x))`, i.e. `towerFn 2` — written out so
this module stays independent of `EMLCertifiedSynthesis`.

`towerFn 2` rather than `towerFn 1`: the tight witness
(`depth_three_witness_decaying_floor`) needs only `exp x`, but a general proof route through
`depth_le_two_approach_constant` (floor `exp (−C − x)`) and the depth-2 growth envelope
(`B x ≤ exp (exp x + K) + M`) costs an extra `x + exp x` in the exponent, and `x + exp x ≤ exp (exp x)`
past `x = 1`. The consumer tolerates it: `NodeDecayBound 3 m` admits any `m ≥ 3`. -/
def Depth3ApproachBelow : Prop :=
  ∀ t : EMLTree, t.depth ≤ 3 → ∀ k : Real, ∃ C X₀ : Real, 1 ≤ X₀ ∧
    ∀ x : Real, X₀ ≤ x → t.eval x < k → exp (-C - exp (exp x)) ≤ k - t.eval x

/-- **The residue: the `eml` constructor.** Both children have depth ≤ 2 and the target
`exp (A x) − k` *moves with `x`*, which is what makes this the hard case — the same moving-target
difficulty that made `ExpExpGapBelow` an arc at depth 3, and the reason
`depth_le_two_approach_constant` (a *constant* target) does not apply directly. -/
def Depth3ApproachBelowEml : Prop :=
  ∀ A B : EMLTree, A.depth ≤ 2 → B.depth ≤ 2 → ∀ k : Real, ∃ C X₀ : Real, 1 ≤ X₀ ∧
    ∀ x : Real, X₀ ≤ x → exp (A.eval x) - log (B.eval x) < k →
      exp (-C - exp (exp x)) ≤ k - (exp (A.eval x) - log (B.eval x))

/-- **The reduction: the two leaf constructors are free, so `eml` carries the whole statement.**
`const` is a fixed value — either it already sits below `k`, and a constant floor suffices because
`exp (−exp (exp x)) ≤ 1`, or it does not and the hypothesis never fires. `var` is emptier still: past
`x = k` the hypothesis `x < k` cannot hold, so the ray alone discharges it. -/
theorem depth3ApproachBelow_of_eml (h : Depth3ApproachBelowEml) : Depth3ApproachBelow := by
  intro t ht k
  cases t with
  | const c =>
      rcases lt_total c k with hck | hck | hck
      · -- `c < k`: the floor is below the constant gap because `exp (−exp (exp x)) ≤ 1`
        have hkc : (0 : Real) < k - c := by
          have u := add_lt_add_left hck (-c)
          have e1 : -c + c = (0 : Real) := by mach_ring
          have e2 : -c + k = k - c := by mach_mpoly [c, k]
          rw [e1, e2] at u; exact u
        refine ⟨-log (k - c), 1, le_refl 1, ?_⟩
        intro x _ _
        show exp (- -log (k - c) - exp (exp x)) ≤ k - c
        have hle : - -log (k - c) - exp (exp x) ≤ log (k - c) := by
          have u := add_le_add_wit (le_refl (log (k - c))) (neg_nonpos_of_nonneg
            (le_of_lt (exp_pos (exp x))))
          have e1 : log (k - c) + -exp (exp x) = - -log (k - c) - exp (exp x) := by
            mach_mpoly [log (k - c), exp (exp x)]
          have e2 : log (k - c) + 0 = log (k - c) := by mach_ring
          rw [e1, e2] at u; exact u
        have w := exp_monotone hle
        rw [exp_log hkc] at w
        exact w
      · -- `c = k`: the hypothesis is `k < k`
        refine ⟨0, 1, le_refl 1, ?_⟩
        intro x _ hlt
        exact absurd (by rw [hck] at hlt; exact hlt) (lt_irrefl_ax k)
      · -- `k < c`: the hypothesis contradicts it
        refine ⟨0, 1, le_refl 1, ?_⟩
        intro x _ hlt
        -- `hlt` is stated about `(const c).eval x`, which is `c` only up to unfolding
        have hlt' : c < k := hlt
        exact absurd (lt_trans_ax hlt' hck) (lt_irrefl_ax c)
  | var =>
      -- past `x = k` the hypothesis `x < k` cannot fire
      refine ⟨0, 1 + exp k, d2_one_le_shift k, ?_⟩
      intro x hx hlt
      exact absurd (lt_of_lt_of_le hlt (le_trans (d2_le_shift k) hx)) (lt_irrefl_ax x)
  | eml A B =>
      have hA : A.depth ≤ 2 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 2 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      exact h A B hA hB k

/-- **The diverging-margin part of the residue is already discharged.** When the left child outgrows
the identity by every margin, `depth_three_node_ge_of_exp_margin` puts the node above `k` on a ray,
so the hypothesis never fires and any floor serves. With
`depth_le_two_growing_identity_or_margin`, what is left of the growing branch is the single case
`A = var`. -/
theorem depth3ApproachBelowEml_margin_case (A B : EMLTree) (hB : B.depth ≤ 2) (k : Real)
    (hA : ∀ M : Real, ∃ T : Real, 1 ≤ T ∧ ∀ x : Real, T ≤ x → exp x + M ≤ exp (A.eval x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧
      ∀ x : Real, X₀ ≤ x → exp (A.eval x) - log (B.eval x) < k →
        exp (-C - exp (exp x)) ≤ k - (exp (A.eval x) - log (B.eval x)) := by
  obtain ⟨X₀, hX₀, hge⟩ := depth_three_node_ge_of_exp_margin A B hB k hA
  refine ⟨0, X₀, hX₀, ?_⟩
  intro x hx hlt
  exact absurd (lt_of_lt_of_le hlt (hge x hx)) (lt_irrefl_ax _)

/-- **The identity branch of the residue is vacuous whenever the right child has depth ≤ 1.**

With `A = var` the node is `exp x − log (B x)`, and a depth-≤1 right child admits the **linear** bound
`log (B x) ≤ x + D` (`depth_le_one_log_le_linear`) — the very bound that is *false* at depth 2
(`depth_le_two_log_not_le_linear`). So the node is at least `exp x − (x + D)`, which outruns every
`k`, the hypothesis never fires, and any floor serves.

This is the same argument the depth-2 gap lemma spends in its growing cell, reused at the one place
depth 3 still permits it. It cuts the live surface of `Depth3ApproachBelowEml` down to
`A = var` **and** `B` of depth exactly 2 — everything else in the growing branch is now discharged:
depth-≤1 right children here, and diverging-margin left children by
`depth3ApproachBelowEml_margin_case`. -/
theorem depth3ApproachBelowEml_identity_shallow_right (B : EMLTree) (hB : B.depth ≤ 1) (k : Real) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧
      ∀ x : Real, X₀ ≤ x → exp (EMLTree.var.eval x) - log (B.eval x) < k →
        exp (-C - exp (exp x)) ≤ k - (exp (EMLTree.var.eval x) - log (B.eval x)) := by
  obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B hB
  obtain ⟨T, hT⟩ := two_mul_add_le_exp (k + D)
  refine ⟨0, 1 + exp T + exp T, d2_ray_ge_one T T, ?_⟩
  intro x hx hlt
  have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_one T T) hx
  have hxT : T ≤ x := le_trans (d2_ray_ge_fst T T) hx
  -- `exp x ≥ x + x + (k + D)` and `log (B x) ≤ x + D`, so the node is at least `k`
  have hnode : k ≤ exp x - log (B.eval x) := by
    have v := add_le_add_wit (hT x hxT) (neg_le_neg_wit (hD x hx1))
    -- `2x + (k+D) − (x+D)` is `x + k`, not `k`; the spare `x` is then dropped by `x ≥ 1 > 0`
    have e1 : x + x + (k + D) + -(x + D) = x + k := by mach_mpoly [x, k, D]
    have e2 : exp x + -log (B.eval x) = exp x - log (B.eval x) := by mach_ring
    rw [e1, e2] at v
    have hxk : k ≤ x + k := by
      have u := add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hx1) (le_refl k)
      have e : (0 : Real) + k = k := by mach_ring
      rw [e] at u; exact u
    exact le_trans hxk v
  -- but the hypothesis says the node is below `k`
  have hlt' : exp x - log (B.eval x) < k := hlt
  exact absurd (lt_of_lt_of_le hlt' hnode) (lt_irrefl_ax _)

/-! ### Closing the residue: `A = var`, `B` of depth 2

With `A = var` the node is `exp x − log (B x)`, so the hypothesis `node < k` says exactly
`B x > exp (exp x − k)` — a **moving, doubly exponential** target. Enumerating `B` shows only one
shape can ever exceed it; the rest are vacuous, and the lemma below is the workhorse that retires
them. -/

/-- **An upper bound at or below the target makes the identity branch vacuous.**

If `B x ≤ exp (exp x − k)` on a ray then `log (B x) ≤ exp x − k`, so the node is at least `k` and the
hypothesis `node < k` never fires. The non-positive stretch is handled by the totalisation rather
than excluded: there `log (B x) = 0`, the node is `exp x`, and `exp x > x ≥ k` past `x = k`. -/
theorem d3_identity_vacuous_of_upper (B : EMLTree) (k X : Real) (_hX : 1 ≤ X)
    (hub : ∀ x : Real, X ≤ x → B.eval x ≤ exp (exp x - k)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log (B.eval x) < k →
        exp (-C - exp (exp x)) ≤ k - (exp (EMLTree.var.eval x) - log (B.eval x)) := by
  refine ⟨0, 1 + exp X + exp k, d2_ray_ge_one X k, ?_⟩
  intro x hx hlt
  have hxX : X ≤ x := le_trans (d2_ray_ge_fst X k) hx
  have hxk : k ≤ x := le_trans (d2_ray_ge_snd X k) hx
  have hlt' : exp x - log (B.eval x) < k := hlt
  -- `log (B x) ≤ exp x − k`, whether or not `B x` is positive
  have hlog : log (B.eval x) ≤ exp x - k := by
    rcases lt_total 0 (B.eval x) with hpos | hzero | hneg
    · have w := log_le_log hpos (hub x hxX)
      rw [log_exp] at w; exact w
    · -- `B x = 0`: totalised `log 0 = 0`, and `0 ≤ exp x − k` since `k ≤ x < exp x`
      rw [← hzero, log_nonpos (le_refl 0)]
      have hkx : k < exp x := lt_of_le_of_lt hxk (exp_grows_strictly_thm x)
      have u := add_lt_add_left hkx (-k)
      have e1 : -k + k = (0 : Real) := by mach_ring
      have e2 : -k + exp x = exp x - k := by mach_mpoly [k, exp x]
      rw [e1, e2] at u; exact le_of_lt u
    · rw [log_nonpos (le_of_lt hneg)]
      have hkx : k < exp x := lt_of_le_of_lt hxk (exp_grows_strictly_thm x)
      have u := add_lt_add_left hkx (-k)
      have e1 : -k + k = (0 : Real) := by mach_ring
      have e2 : -k + exp x = exp x - k := by mach_mpoly [k, exp x]
      rw [e1, e2] at u; exact le_of_lt u
  -- so the node is at least `k`, contradicting the hypothesis
  have hnode : k ≤ exp x - log (B.eval x) := by
    have u := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit hlog)
    have e1 : exp x + -(exp x - k) = k := by mach_mpoly [exp x, k]
    have e2 : exp x + -log (B.eval x) = exp x - log (B.eval x) := by mach_ring
    rw [e1, e2] at u; exact u
  exact absurd (lt_of_lt_of_le hlt' hnode) (lt_irrefl_ax _)

/-- Anything bounded by `exp x − k` is bounded by the target `exp (exp x − k)`, since `u < exp u`.
The target is doubly exponential; almost every shape of `B` is not, and this is the bridge that
says so once instead of five times. -/
theorem d3_below_target_of_below_sub {B : EMLTree} {k X : Real}
    (h : ∀ x : Real, X ≤ x → B.eval x ≤ exp x - k) :
    ∀ x : Real, X ≤ x → B.eval x ≤ exp (exp x - k) :=
  fun x hx => le_trans (h x hx) (le_of_lt (exp_grows_strictly_thm (exp x - k)))

/-- **`B = const c` is vacuous.** A fixed value cannot outrun a doubly exponential target. -/
theorem d3_identity_const_right (c k : Real) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.const c).eval x) < k →
        exp (-C - exp (exp x)) ≤ k - (exp (EMLTree.var.eval x) - log ((EMLTree.const c).eval x)) := by
  refine d3_identity_vacuous_of_upper (EMLTree.const c) k (1 + exp (c + k))
    (d2_one_le_shift (c + k)) (d3_below_target_of_below_sub ?_)
  intro x hx
  -- `x ≥ c + k` and `x < exp x` give `c ≤ exp x − k`
  have hxck : c + k ≤ x := le_trans (d2_le_shift (c + k)) hx
  have hlt : c + k < exp x := lt_of_le_of_lt hxck (exp_grows_strictly_thm x)
  show c ≤ exp x - k
  have u := add_lt_add_left hlt (-k)
  have e1 : -k + (c + k) = c := by mach_mpoly [c, k]
  have e2 : -k + exp x = exp x - k := by mach_mpoly [k, exp x]
  rw [e1, e2] at u
  exact le_of_lt u

/-- **`B = var` is vacuous.** `x` against `exp (exp x − k)`: the same gap, one shape up. -/
theorem d3_identity_var_right (k : Real) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log (EMLTree.var.eval x) < k →
        exp (-C - exp (exp x)) ≤ k - (exp (EMLTree.var.eval x) - log (EMLTree.var.eval x)) := by
  obtain ⟨T, hT⟩ := two_mul_add_le_exp k
  refine d3_identity_vacuous_of_upper EMLTree.var k (1 + exp T)
    (d2_one_le_shift T) (d3_below_target_of_below_sub ?_)
  intro x hx
  have hxT : T ≤ x := le_trans (d2_le_shift T) hx
  have hx1 : (1 : Real) ≤ x := le_trans (d2_one_le_shift T) hx
  show x ≤ exp x - k
  -- `x + x + k ≤ exp x`, so `exp x − k ≥ x + x ≥ x`
  have u := add_le_add_wit (hT x hxT) (le_refl (-k))
  have e1 : x + x + k + -k = x + x := by mach_mpoly [x, k]
  have e2 : exp x + -k = exp x - k := by mach_mpoly [x, k, exp x]
  rw [e1, e2] at u
  have hxx : x ≤ x + x := by
    have w := add_le_add_wit (le_refl x) (le_trans (le_of_lt zero_lt_one_ax) hx1)
    have e : x + 0 = x := by mach_ring
    rw [e] at w; exact w
  exact le_trans hxx u

/-- **A constant upper bound on `B` makes the identity branch vacuous.** Generalises
`d3_identity_const_right` from a literal constant to any eventually-bounded `B`. -/
theorem d3_identity_vacuous_of_const_bound (B : EMLTree) (k c X : Real) (_hX : 1 ≤ X)
    (hub : ∀ x : Real, X ≤ x → B.eval x ≤ c) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log (B.eval x) < k →
        exp (-C - exp (exp x)) ≤ k - (exp (EMLTree.var.eval x) - log (B.eval x)) := by
  refine d3_identity_vacuous_of_upper B k (1 + exp X + exp (c + k))
    (d2_ray_ge_one X (c + k)) (d3_below_target_of_below_sub ?_)
  intro x hx
  have hxX : X ≤ x := le_trans (d2_ray_ge_fst X (c + k)) hx
  have hxck : c + k ≤ x := le_trans (d2_ray_ge_snd X (c + k)) hx
  have hlt : c + k < exp x := lt_of_le_of_lt hxck (exp_grows_strictly_thm x)
  have hcx : c ≤ exp x - k := by
    have u := add_lt_add_left hlt (-k)
    have e1 : -k + (c + k) = c := by mach_mpoly [c, k]
    have e2 : -k + exp x = exp x - k := by mach_mpoly [k, exp x]
    rw [e1, e2] at u; exact le_of_lt u
  exact le_trans (hub x hxX) hcx

/-- **`B = eml b₁ b₂` with a BOUNDED left child is vacuous.** `exp (b₁ x) ≤ K` caps the node's
right child at `K − Cl`, where `Cl` is the depth-1 logarithm's floor
(`depth_le_one_log_lower_at_infinity`) — a constant, and constants lose to the target.

Both inputs are depth-1 facts, which is the point: the residue is only hard where `b₁` reaches the
doubly exponential scale, and a bounded `b₁` never does. -/
theorem d3_identity_eml_bounded_left (b1 b2 : EMLTree) (_h1 : b1.depth ≤ 1) (h2 : b2.depth ≤ 1)
    (k K : Real) (hK : ∀ x : Real, 1 ≤ x → exp (b1.eval x) ≤ K) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
  obtain ⟨Cl, X₀, hX₀, hCl⟩ := depth_le_one_log_lower_at_infinity b2 h2
  refine d3_identity_vacuous_of_const_bound (EMLTree.eml b1 b2) k (K - Cl)
    (1 + exp X₀ + exp 1) (d2_ray_ge_one X₀ 1) ?_
  intro x hx
  have hxX : X₀ ≤ x := le_trans (d2_ray_ge_fst X₀ 1) hx
  have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_snd X₀ 1) hx
  show exp (b1.eval x) - log (b2.eval x) ≤ K - Cl
  have u := add_le_add_wit (hK x hx1) (neg_le_neg_wit (hCl x hxX))
  have e1 : exp (b1.eval x) + -log (b2.eval x) = exp (b1.eval x) - log (b2.eval x) := by mach_ring
  have e2 : K + -Cl = K - Cl := by mach_mpoly [K, Cl]
  rw [e1, e2] at u
  exact u

/-- **The workhorse in log form.** Bounding `log (B x)` directly needs no positivity split at all —
the node is `exp x − log (B x) ≥ k` immediately. `d3_identity_vacuous_of_upper` is the value-form
door for shapes where a bound on `B x` is what is in hand. -/
theorem d3_identity_vacuous_of_log_upper (B : EMLTree) (k X : Real) (hX : 1 ≤ X)
    (hub : ∀ x : Real, X ≤ x → log (B.eval x) ≤ exp x - k) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log (B.eval x) < k →
        exp (-C - exp (exp x)) ≤ k - (exp (EMLTree.var.eval x) - log (B.eval x)) := by
  refine ⟨0, X, hX, ?_⟩
  intro x hx hlt
  have hlt' : exp x - log (B.eval x) < k := hlt
  have hnode : k ≤ exp x - log (B.eval x) := by
    have u := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit (hub x hx))
    have e1 : exp x + -(exp x - k) = k := by mach_mpoly [exp x, k]
    have e2 : exp x + -log (B.eval x) = exp x - log (B.eval x) := by mach_ring
    rw [e1, e2] at u; exact u
  exact absurd (lt_of_lt_of_le hlt' hnode) (lt_irrefl_ax _)

/-- `log (1 + y) ≤ y` for `y ≥ 0`, from the tangent-line bound `1 + t ≤ exp t` at `t = log (1+y)`. -/
theorem d3_log_one_add_le (y : Real) (hy : 0 ≤ y) : log (1 + y) ≤ y := by
  have hpos : (0 : Real) < 1 + y := by
    have u := add_le_add_wit (le_refl (1 : Real)) hy
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at u
    exact lt_of_lt_of_le zero_lt_one_ax u
  have h := one_add_le_exp (log (1 + y))
  rw [exp_log hpos] at h
  -- `1 + log (1+y) ≤ 1 + y`
  have u := add_le_add_wit h (le_refl (-(1 : Real)))
  have e1 : (1 : Real) + log (1 + y) + -1 = log (1 + y) := by mach_mpoly [log (1 + y)]
  have e2 : (1 : Real) + y + -1 = y := by mach_mpoly [y]
  rw [e1, e2] at u; exact u

/-- **A singly exponential `B` loses to the doubly exponential target.** `B x ≤ exp x + M` puts `B`
below `exp (exp x − k)` on a ray, because `exp (exp x − k) ≥ 2·exp x + M` once `exp x − k` clears the
`two_mul_add_le_exp` threshold. This is the door for `b₁ x = x`, where `B x ≈ exp x`. -/
theorem d3_below_target_of_below_exp_shift {B : EMLTree} (k M X : Real)
    (h : ∀ x : Real, X ≤ x → B.eval x ≤ exp x + M) :
    ∃ X' : Real, 1 ≤ X' ∧ ∀ x : Real, X' ≤ x → B.eval x ≤ exp (exp x - k) := by
  obtain ⟨T, hT⟩ := two_mul_add_le_exp (M + k + k)
  refine ⟨1 + exp X + exp (T + k), d2_ray_ge_one X (T + k), ?_⟩
  intro x hx
  have hxX : X ≤ x := le_trans (d2_ray_ge_fst X (T + k)) hx
  have hxTk : T + k ≤ x := le_trans (d2_ray_ge_snd X (T + k)) hx
  -- `exp x − k ≥ T`
  have hT' : T ≤ exp x - k := by
    have hlt : T + k < exp x := lt_of_le_of_lt hxTk (exp_grows_strictly_thm x)
    have u := add_lt_add_left hlt (-k)
    have e1 : -k + (T + k) = T := by mach_mpoly [T, k]
    have e2 : -k + exp x = exp x - k := by mach_mpoly [k, exp x]
    rw [e1, e2] at u; exact le_of_lt u
  have hbig := hT (exp x - k) hT'
  -- `(exp x − k) + (exp x − k) + (M + k + k) = exp x + (exp x + M)`
  have e : exp x - k + (exp x - k) + (M + k + k) = exp x + (exp x + M) := by
    mach_mpoly [exp x, k, M]
  rw [e] at hbig
  -- and `exp x + M ≤ exp x + (exp x + M)` since `exp x > 0`
  have hstep : exp x + M ≤ exp x + (exp x + M) := by
    have u := add_le_add_wit (le_of_lt (exp_pos x)) (le_refl (exp x + M))
    have e2 : (0 : Real) + (exp x + M) = exp x + M := by mach_ring
    rw [e2] at u; exact u
  exact le_trans (h x hxX) (le_trans hstep hbig)

/-- **`b₁` the identity is vacuous.** Then `B x = exp x − log (b₂ x) ≤ exp x + (−Cl)`, singly
exponential, and the target is doubly exponential. -/
theorem d3_identity_eml_identity_left (b1 b2 : EMLTree) (h2 : b2.depth ≤ 1) (k : Real)
    (hb1 : ∀ x : Real, 0 < x → b1.eval x = x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
  obtain ⟨Cl, XL, hXL, hCl⟩ := depth_le_one_log_lower_at_infinity b2 h2
  have hbound : ∀ x : Real, 1 + exp XL + exp 1 ≤ x →
      (EMLTree.eml b1 b2).eval x ≤ exp x + -Cl := by
    intro x hx
    have hxL : XL ≤ x := le_trans (d2_ray_ge_fst XL 1) hx
    have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_snd XL 1) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    show exp (b1.eval x) - log (b2.eval x) ≤ exp x + -Cl
    rw [hb1 x hxpos]
    have u := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit (hCl x hxL))
    have e : exp x + -log (b2.eval x) = exp x - log (b2.eval x) := by mach_ring
    rw [e] at u
    exact u
  obtain ⟨X', hX', hbelow⟩ :=
    d3_below_target_of_below_exp_shift k (-Cl) (1 + exp XL + exp 1) hbound
  exact d3_identity_vacuous_of_upper (EMLTree.eml b1 b2) k X' hX' hbelow

/-- **`b₁` constant is vacuous**: `exp (b₁ x) = exp α`, a constant, and constants lose. -/
theorem d3_identity_eml_const_left (b1 b2 : EMLTree) (h1 : b1.depth ≤ 1) (h2 : b2.depth ≤ 1)
    (k α : Real) (hb1 : ∀ x : Real, 0 < x → b1.eval x = α) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
  refine d3_identity_eml_bounded_left b1 b2 h1 h2 k (exp α) ?_
  intro x hx1
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  rw [hb1 x hxpos]
  exact le_refl _

/-- **`b₁ x = c − log x` is vacuous**: `log x ≥ 0` past `x = 1`, so `exp (b₁ x) ≤ exp c`. -/
theorem d3_identity_eml_declog_left (b1 b2 : EMLTree) (h1 : b1.depth ≤ 1) (h2 : b2.depth ≤ 1)
    (k c : Real) (hb1 : ∀ x : Real, 0 < x → b1.eval x = c - log x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
  refine d3_identity_eml_bounded_left b1 b2 h1 h2 k (exp c) ?_
  intro x hx1
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  rw [hb1 x hxpos]
  -- `log x ≥ log 1 = 0`, so `c − log x ≤ c`
  have hlog0 : (0 : Real) ≤ log x := by
    have w := log_le_log zero_lt_one_ax hx1
    rw [log_one] at w; exact w
  have hle : c - log x ≤ c := by
    have u := add_le_add_wit (le_refl c) (neg_nonpos_of_nonneg hlog0)
    have e1 : c + -log x = c - log x := by mach_ring
    have e2 : c + 0 = c := by mach_ring
    rw [e1, e2] at u; exact u
  exact exp_monotone hle

/-- **`log (exp v + m) ≤ v + m·exp (−v)` for `m ≥ 0`.** The additive perturbation of an exponential
costs only a term that decays like `exp (−v)`.

Proof without `log_mul`: `exp v · (1 + m·exp (−v)) = exp v + m` exactly, because
`exp v · exp (−v) = exp 0 = 1`; the tangent bound `1 + t ≤ exp t` then lifts the left side to
`exp v · exp (m·exp (−v)) = exp (v + m·exp (−v))`, and `log` is monotone. -/
theorem d3_log_exp_add_le (v m : Real) (hm : 0 ≤ m) : log (exp v + m) ≤ v + m * exp (-v) := by
  have hinv : exp v * exp (-v) = 1 := by
    rw [← exp_add]
    have e : v + -v = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  have key : exp v * (1 + m * exp (-v)) = exp v + m := by
    have e : exp v * (1 + m * exp (-v)) = exp v + m * (exp v * exp (-v)) := by
      mach_mpoly [exp v, m, exp (-v)]
    rw [e, hinv]
    mach_mpoly [exp v, m]
  have step := mul_le_mul_of_nonneg_left (one_add_le_exp (m * exp (-v))) (le_of_lt (exp_pos v))
  rw [key] at step
  -- `exp v * exp (m·exp (−v)) = exp (v + m·exp (−v))`
  have hcomb : exp v * exp (m * exp (-v)) = exp (v + m * exp (-v)) := by rw [← exp_add]
  rw [hcomb] at step
  have hpos : (0 : Real) < exp v + m := by
    have u := add_le_add_wit (le_refl (exp v)) hm
    have e : exp v + 0 = exp v := by mach_ring
    rw [e] at u
    exact lt_of_lt_of_le (exp_pos v) u
  have w := log_le_log hpos step
  rw [log_exp] at w
  exact w

/-- **`b₁ x = exp x − log x` is vacuous.** This is the shape that comes *closest* to the target
without reaching it: `exp (b₁ x) = exp (exp x − log x)` is doubly exponential, like the target
`exp (exp x − k)`, but short by `log x − k`, which diverges. The `log x` in the exponent is exactly
the margin the live shape `exp x − d` does not have.

Two details. The right child's floor `Cl` may be negative, so it is replaced by `exp (−Cl) > 0`
(`exp M > M` always) to feed `d3_log_exp_add_le`, which needs a non-negative perturbation — the same
substitution `lowerEnvBound_three` uses. And where `B x ≤ 0` the totalised `log` gives `0`, which is
below `exp x − k` past `x = k`. -/
theorem d3_identity_eml_explog_left (b1 b2 : EMLTree) (h2 : b2.depth ≤ 1) (k : Real)
    (hb1 : ∀ x : Real, 0 < x → b1.eval x = exp x - log x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
  obtain ⟨Cl, XL, hXL, hCl⟩ := depth_le_one_log_lower_at_infinity b2 h2
  have hm : (0 : Real) ≤ exp (-Cl) := le_of_lt (exp_pos _)
  refine d3_identity_vacuous_of_log_upper (EMLTree.eml b1 b2) k
    (1 + exp (1 + exp XL + exp (exp (k + exp (-Cl)))) + exp k)
    (d2_ray_ge_one _ _) ?_
  intro x hx
  have hxR : 1 + exp XL + exp (exp (k + exp (-Cl))) ≤ x := le_trans (d2_ray_ge_fst _ _) hx
  have hxk : k ≤ x := le_trans (d2_ray_ge_snd _ _) hx
  have hxL : XL ≤ x := le_trans (d2_ray_ge_fst XL _) hxR
  have hxP : exp (k + exp (-Cl)) ≤ x := le_trans (d2_ray_ge_snd XL _) hxR
  have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_one XL _) hxR
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  -- `exp x − k ≥ 0`, used by both branches
  have hnn : (0 : Real) ≤ exp x - k := by
    have hlt : k < exp x := lt_of_le_of_lt hxk (exp_grows_strictly_thm x)
    have u := add_lt_add_left hlt (-k)
    have e1 : -k + k = (0 : Real) := by mach_ring
    have e2 : -k + exp x = exp x - k := by mach_mpoly [k, exp x]
    rw [e1, e2] at u; exact le_of_lt u
  rcases lt_total 0 ((EMLTree.eml b1 b2).eval x) with hpos | hz | hneg
  · -- positive: bound `log (B x)` through `d3_log_exp_add_le`
    have hBub : (EMLTree.eml b1 b2).eval x ≤ exp (exp x - log x) + exp (-Cl) := by
      show exp (b1.eval x) - log (b2.eval x) ≤ _
      rw [hb1 x hxpos]
      have hstep : -log (b2.eval x) ≤ exp (-Cl) := by
        have u := neg_le_neg_wit (hCl x hxL)
        exact le_trans u (le_of_lt (exp_grows_strictly_thm (-Cl)))
      have u := add_le_add_wit (le_refl (exp (exp x - log x))) hstep
      have e : exp (exp x - log x) + -log (b2.eval x)
          = exp (exp x - log x) - log (b2.eval x) := by mach_ring
      rw [e] at u; exact u
    have hchain := le_trans (log_le_log hpos hBub)
      (d3_log_exp_add_le (exp x - log x) (exp (-Cl)) hm)
    -- `v + m·exp (−v) ≤ exp x − k` because `exp (−v) ≤ 1` and `log x ≥ k + m`
    have hv0 : (0 : Real) ≤ exp x - log x := by
      have hlx : log x < x := by
        have w := exp_grows_strictly_thm (log x)
        rw [exp_log hxpos] at w; exact w
      have hxe : x < exp x := exp_grows_strictly_thm x
      have u := add_lt_add_left (lt_trans_ax hlx hxe) (-log x)
      have e1 : -log x + log x = (0 : Real) := by mach_ring
      have e2 : -log x + exp x = exp x - log x := by mach_mpoly [log x, exp x]
      rw [e1, e2] at u; exact le_of_lt u
    have hdecay : exp (-(exp x - log x)) ≤ 1 := by
      have w := exp_monotone (neg_nonpos_of_nonneg hv0)
      rw [exp_zero] at w; exact w
    have hmd : exp (-Cl) * exp (-(exp x - log x)) ≤ exp (-Cl) := by
      have u := mul_le_mul_of_nonneg_left hdecay hm
      have e : exp (-Cl) * 1 = exp (-Cl) := by mach_ring
      rw [e] at u; exact u
    have hlogx : k + exp (-Cl) ≤ log x := by
      have w := log_le_log (exp_pos _) hxP
      rw [log_exp] at w; exact w
    have hfin : exp x - log x + exp (-Cl) * exp (-(exp x - log x)) ≤ exp x - k := by
      have u := add_le_add_wit (le_refl (exp x - log x)) hmd
      have hshift : exp x - log x + exp (-Cl) ≤ exp x - k := by
        have v := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit hlogx)
        have e1 : exp x + -log x = exp x - log x := by mach_ring
        have e2 : exp x + -(k + exp (-Cl)) = exp x - k - exp (-Cl) := by
          mach_mpoly [exp x, k, exp (-Cl)]
        rw [e1] at v
        have e3 : exp x - log x + exp (-Cl) ≤ exp x + -(k + exp (-Cl)) + exp (-Cl) := by
          have w2 := add_le_add_wit v (le_refl (exp (-Cl)))
          exact w2
        have e4 : exp x + -(k + exp (-Cl)) + exp (-Cl) = exp x - k := by
          mach_mpoly [exp x, k, exp (-Cl)]
        rw [e4] at e3; exact e3
      exact le_trans u hshift
    exact le_trans hchain hfin
  · rw [← hz, log_nonpos (le_refl 0)]; exact hnn
  · rw [log_nonpos (le_of_lt hneg)]; exact hnn

/-! ### The live shape `b₁ x = exp x − d`, split on `d` against `k` -/

/-- **`d > k` is still vacuous.** `exp (b₁ x) = exp (exp x − d)` reaches the target's scale but sits
a constant factor `exp (k − d) < 1` below it, and the right child's perturbation decays.

The bound is kept division-free by writing the perturbation as a single exponential:
`exp (−Cl) · exp (−v) = exp (−Cl − v)`, so the requirement `exp (−Cl − v) ≤ d − k` becomes the
linear threshold `v ≥ −Cl − log (d − k)`. -/
theorem d3_identity_eml_expd_left_gt (b1 b2 : EMLTree) (h2 : b2.depth ≤ 1) (k d : Real)
    (hdk : k < d) (hb1 : ∀ x : Real, 0 < x → b1.eval x = exp x - d) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
  obtain ⟨Cl, XL, hXL, hCl⟩ := depth_le_one_log_lower_at_infinity b2 h2
  have hm : (0 : Real) ≤ exp (-Cl) := le_of_lt (exp_pos _)
  have hdkpos : (0 : Real) < d - k := by
    have u := add_lt_add_left hdk (-k)
    have e1 : -k + k = (0 : Real) := by mach_ring
    have e2 : -k + d = d - k := by mach_mpoly [k, d]
    rw [e1, e2] at u; exact u
  refine d3_identity_vacuous_of_log_upper (EMLTree.eml b1 b2) k
    (1 + exp (1 + exp XL + exp (d + -Cl - log (d - k))) + exp k) (d2_ray_ge_one _ _) ?_
  intro x hx
  have hxR : 1 + exp XL + exp (d + -Cl - log (d - k)) ≤ x := le_trans (d2_ray_ge_fst _ _) hx
  have hxk : k ≤ x := le_trans (d2_ray_ge_snd _ _) hx
  have hxL : XL ≤ x := le_trans (d2_ray_ge_fst XL _) hxR
  have hxT : d + -Cl - log (d - k) ≤ x := le_trans (d2_ray_ge_snd XL _) hxR
  have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_one XL _) hxR
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hnn : (0 : Real) ≤ exp x - k := by
    have hlt : k < exp x := lt_of_le_of_lt hxk (exp_grows_strictly_thm x)
    have u := add_lt_add_left hlt (-k)
    have e1 : -k + k = (0 : Real) := by mach_ring
    have e2 : -k + exp x = exp x - k := by mach_mpoly [k, exp x]
    rw [e1, e2] at u; exact le_of_lt u
  -- `v = exp x − d` clears the threshold `−Cl − log (d − k)`
  have hvT : -Cl - log (d - k) ≤ exp x - d := by
    have hlt : d + -Cl - log (d - k) < exp x := lt_of_le_of_lt hxT (exp_grows_strictly_thm x)
    have u := add_lt_add_left hlt (-d)
    have e1 : -d + (d + -Cl - log (d - k)) = -Cl - log (d - k) := by
      mach_mpoly [d, Cl, log (d - k)]
    have e2 : -d + exp x = exp x - d := by mach_mpoly [d, exp x]
    rw [e1, e2] at u; exact le_of_lt u
  -- hence the perturbation is below `d − k`
  have hpert : exp (-Cl) * exp (-(exp x - d)) ≤ d - k := by
    have hcomb : exp (-Cl) * exp (-(exp x - d)) = exp (-Cl - (exp x - d)) := by
      rw [← exp_add]
      have e : -Cl + -(exp x - d) = -Cl - (exp x - d) := by mach_mpoly [Cl, exp x, d]
      rw [e]
    rw [hcomb]
    have harg : -Cl - (exp x - d) ≤ log (d - k) := by
      have u := add_le_add_wit (le_refl (-Cl)) (neg_le_neg_wit hvT)
      have e1 : -Cl + -(exp x - d) = -Cl - (exp x - d) := by mach_mpoly [Cl, exp x, d]
      have e2 : -Cl + -(-Cl - log (d - k)) = log (d - k) := by mach_mpoly [Cl, log (d - k)]
      rw [e1, e2] at u; exact u
    have w := exp_monotone harg
    rw [exp_log hdkpos] at w
    exact w
  rcases lt_total 0 ((EMLTree.eml b1 b2).eval x) with hpos | hz | hneg
  · have hBub : (EMLTree.eml b1 b2).eval x ≤ exp (exp x - d) + exp (-Cl) := by
      show exp (b1.eval x) - log (b2.eval x) ≤ _
      rw [hb1 x hxpos]
      have hstep : -log (b2.eval x) ≤ exp (-Cl) :=
        le_trans (neg_le_neg_wit (hCl x hxL)) (le_of_lt (exp_grows_strictly_thm (-Cl)))
      have u := add_le_add_wit (le_refl (exp (exp x - d))) hstep
      have e : exp (exp x - d) + -log (b2.eval x) = exp (exp x - d) - log (b2.eval x) := by mach_ring
      rw [e] at u; exact u
    have hchain := le_trans (log_le_log hpos hBub)
      (d3_log_exp_add_le (exp x - d) (exp (-Cl)) hm)
    have hfin : exp x - d + exp (-Cl) * exp (-(exp x - d)) ≤ exp x - k := by
      have u := add_le_add_wit (le_refl (exp x - d)) hpert
      have e : exp x - d + (d - k) = exp x - k := by mach_mpoly [exp x, d, k]
      rw [e] at u; exact u
    exact le_trans hchain hfin
  · rw [← hz, log_nonpos (le_refl 0)]; exact hnn
  · rw [log_nonpos (le_of_lt hneg)]; exact hnn

/-- **`d < k`: the gap tends to the constant `k − d`, so the decaying floor is dwarfed.**

The node's right child is `exp (exp x − d)` against a target `exp (exp x − k)` that is a constant
factor `exp (d − k) < 1` *smaller*, so the gap does not vanish at all — it tends to `k − d`.

Two devices keep this division-free in a base where division is totalised. The offset is
`ε = (k − d)·exp (−1)`, which is below `(k − d)/2` because `e⁻¹ < ½`, so `ε < k − d` with no halving.
And the product threshold `exp (v − ε)·ρ ≥ x + D` (with `ρ = exp ε − 1 > 0`) is discharged through
logs: it is `(v − ε) + log ρ ≥ log (x + D)`, and `log u < u` reduces that to a linear inequality that
`two_mul_add_le_exp` supplies. -/
theorem d3_identity_eml_expd_left_lt (b1 b2 : EMLTree) (h2 : b2.depth ≤ 1) (k d : Real)
    (hdk : d < k) (hb1 : ∀ x : Real, 0 < x → b1.eval x = exp x - d) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
  obtain ⟨D, hD⟩ := depth_le_one_log_le_linear b2 h2
  have hg : (0 : Real) < k - d := by
    have u := add_lt_add_left hdk (-d)
    have e1 : -d + d = (0 : Real) := by mach_ring
    have e2 : -d + k = k - d := by mach_mpoly [d, k]
    rw [e1, e2] at u; exact u
  have hexp1 : exp (-1 : Real) < 1 := by
    have hneg : (-1 : Real) < 0 := by
      have w := add_lt_add_left zero_lt_one_ax (-(1 : Real))
      have f1 : -(1 : Real) + 0 = -1 := by mach_ring
      have f2 : -(1 : Real) + 1 = 0 := by mach_ring
      rw [f1, f2] at w; exact w
    have h := exp_lt hneg
    rw [exp_zero] at h; exact h
  have h1me : (0 : Real) < 1 - exp (-1 : Real) := by
    have u := add_lt_add_left hexp1 (-exp (-1 : Real))
    have e1 : -exp (-1 : Real) + exp (-1 : Real) = (0 : Real) := by mach_ring
    have e2 : -exp (-1 : Real) + 1 = 1 - exp (-1 : Real) := by mach_mpoly [exp (-1 : Real)]
    rw [e1, e2] at u; exact u
  have heps : (0 : Real) < (k - d) * exp (-1 : Real) := mul_pos hg (exp_pos _)
  -- `ε < k − d`, from `0 < (k−d)·(1 − e⁻¹)`; no halving, because `e⁻¹ < ½`
  have hgap0 : (0 : Real) < k - d - (k - d) * exp (-1 : Real) := by
    have hp := mul_pos hg h1me
    have e : (k - d) * (1 - exp (-1 : Real)) = k - d - (k - d) * exp (-1 : Real) := by
      mach_mpoly [k, d, exp (-1 : Real)]
    rw [e] at hp; exact hp
  have hrho : (0 : Real) < exp ((k - d) * exp (-1 : Real)) - 1 := by
    have h := exp_lt heps
    rw [exp_zero] at h
    have u := add_lt_add_left h (-(1 : Real))
    have e1 : -(1 : Real) + 1 = (0 : Real) := by mach_ring
    have e2 : -(1 : Real) + exp ((k - d) * exp (-1 : Real))
        = exp ((k - d) * exp (-1 : Real)) - 1 := by
      mach_mpoly [exp ((k - d) * exp (-1 : Real))]
    rw [e1, e2] at u; exact u
  obtain ⟨T, hT⟩ := two_mul_add_le_exp
    (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1))
  refine ⟨-log (k - d - (k - d) * exp (-1 : Real)),
          1 + exp T + exp (-D + 1), d2_ray_ge_one T (-D + 1), ?_⟩
  intro x hx hlt
  have hxT : T ≤ x := le_trans (d2_ray_ge_fst T (-D + 1)) hx
  have hxD1 : -D + 1 ≤ x := le_trans (d2_ray_ge_snd T (-D + 1)) hx
  have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_one T (-D + 1)) hx
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hxD : (0 : Real) < x + D := by
    have u := add_le_add_wit hxD1 (le_refl D)
    have e1 : -D + 1 + D = (1 : Real) := by mach_mpoly [D]
    rw [e1] at u
    exact lt_of_lt_of_le zero_lt_one_ax u
  -- the product threshold, discharged through logs: `(v − ε) + log ρ ≥ log (x + D)`
  have hlin : x + D ≤ exp x - d - (k - d) * exp (-1 : Real) + log (exp ((k - d) * exp (-1 : Real)) - 1) := by
    have hbig := hT x hxT
    have hxx : x ≤ x + x := by
      have w := add_le_add_wit (le_refl x) (le_of_lt hxpos)
      have e : x + 0 = x := by mach_ring
      rw [e] at w; exact w
    have u := add_le_add_wit hxx (le_refl (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)))
    have e2 : x + x + (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1))
        = x + x + (D + d + (k - d) * exp (-1 : Real)) - log (exp ((k - d) * exp (-1 : Real)) - 1) := by
      mach_mpoly [x, D, d, (k - d) * exp (-1 : Real), log (exp ((k - d) * exp (-1 : Real)) - 1)]
    rw [e2] at hbig
    have hchain : x + (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1))
        ≤ exp x - (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) + (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) := by
      have w := le_trans u (le_trans (le_of_eq (by
        mach_mpoly [x, D, d, (k - d) * exp (-1 : Real), log (exp ((k - d) * exp (-1 : Real)) - 1)])) hbig)
      have e3 : exp x - (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) + (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) = exp x := by
        mach_mpoly [exp x, D, d, (k - d) * exp (-1 : Real), log (exp ((k - d) * exp (-1 : Real)) - 1)]
      rw [e3]; exact w
    have e4 : exp x - (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) + (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) = exp x := by
      mach_mpoly [exp x, D, d, (k - d) * exp (-1 : Real), log (exp ((k - d) * exp (-1 : Real)) - 1)]
    rw [e4] at hchain
    have e5 : x + (D + d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) = x + D + (d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) := by
      mach_mpoly [x, D, d, (k - d) * exp (-1 : Real), log (exp ((k - d) * exp (-1 : Real)) - 1)]
    rw [e5] at hchain
    have v := add_le_add_wit hchain (le_refl (-(d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1))))
    have e6 : x + D + (d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) + -(d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1)) = x + D := by
      mach_mpoly [x, D, d, (k - d) * exp (-1 : Real), log (exp ((k - d) * exp (-1 : Real)) - 1)]
    have e7 : exp x + -(d + (k - d) * exp (-1 : Real) - log (exp ((k - d) * exp (-1 : Real)) - 1))
        = exp x - d - (k - d) * exp (-1 : Real) + log (exp ((k - d) * exp (-1 : Real)) - 1) := by
      mach_mpoly [exp x, d, (k - d) * exp (-1 : Real), log (exp ((k - d) * exp (-1 : Real)) - 1)]
    rw [e6, e7] at v; exact v
  -- exponentiate: `x + D ≤ exp (v − ε)·ρ`
  have hprod : x + D ≤ exp (exp x - d - (k - d) * exp (-1 : Real)) * (exp ((k - d) * exp (-1 : Real)) - 1) := by
    have hlogx : log (x + D) < x + D := by
      have w := exp_grows_strictly_thm (log (x + D))
      rw [exp_log hxD] at w; exact w
    have hstep : log (x + D) ≤ exp x - d - (k - d) * exp (-1 : Real) + log (exp ((k - d) * exp (-1 : Real)) - 1) :=
      le_trans (le_of_lt hlogx) hlin
    have w := exp_monotone hstep
    rw [exp_log hxD] at w
    have hsplit : exp (exp x - d - (k - d) * exp (-1 : Real) + log (exp ((k - d) * exp (-1 : Real)) - 1))
        = exp (exp x - d - (k - d) * exp (-1 : Real)) * (exp ((k - d) * exp (-1 : Real)) - 1) := by
      rw [exp_add, exp_log hrho]
    rw [hsplit] at w; exact w
  -- `exp v − exp (v − ε) = exp (v − ε)·ρ`, so the right child cannot eat the margin
  have hsub : exp (exp x - d) - exp (exp x - d - (k - d) * exp (-1 : Real))
      = exp (exp x - d - (k - d) * exp (-1 : Real)) * (exp ((k - d) * exp (-1 : Real)) - 1) := by
    have hcomb : exp (exp x - d) = exp (exp x - d - (k - d) * exp (-1 : Real)) * exp ((k - d) * exp (-1 : Real)) := by
      rw [← exp_add]
      have e : exp x - d - (k - d) * exp (-1 : Real) + (k - d) * exp (-1 : Real) = exp x - d := by
        mach_mpoly [exp x, d, (k - d) * exp (-1 : Real)]
      rw [e]
    rw [hcomb]
    mach_mpoly [exp (exp x - d - (k - d) * exp (-1 : Real)), exp ((k - d) * exp (-1 : Real))]
  have hBlow : exp (exp x - d - (k - d) * exp (-1 : Real)) ≤ (EMLTree.eml b1 b2).eval x := by
    show _ ≤ exp (b1.eval x) - log (b2.eval x)
    rw [hb1 x hxpos]
    have hw : log (b2.eval x) ≤ x + D := hD x hx1
    have u := add_le_add_wit (le_refl (exp (exp x - d))) (neg_le_neg_wit
      (le_trans hw (le_trans hprod (le_of_eq hsub.symm))))
    have e1 : exp (exp x - d) + -(exp (exp x - d) - exp (exp x - d - (k - d) * exp (-1 : Real)))
        = exp (exp x - d - (k - d) * exp (-1 : Real)) := by
      mach_mpoly [exp (exp x - d), exp (exp x - d - (k - d) * exp (-1 : Real))]
    have e2 : exp (exp x - d) + -log (b2.eval x) = exp (exp x - d) - log (b2.eval x) := by
      mach_ring
    rw [e1, e2] at u; exact u
  -- so `log (B x) ≥ v − ε`, and the gap is at least the constant `k − d − ε`
  have hlogB : exp x - d - (k - d) * exp (-1 : Real) ≤ log ((EMLTree.eml b1 b2).eval x) := by
    have w := log_le_log (exp_pos _) hBlow
    rw [log_exp] at w; exact w
  have hgapc : k - d - (k - d) * exp (-1 : Real)
      ≤ k - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
    show _ ≤ k - (exp x - log ((EMLTree.eml b1 b2).eval x))
    have u := add_le_add_wit (le_refl (k - exp x)) hlogB
    have e1 : k - exp x + (exp x - d - (k - d) * exp (-1 : Real)) = k - d - (k - d) * exp (-1 : Real) := by
      mach_mpoly [k, exp x, d, (k - d) * exp (-1 : Real)]
    have e2 : k - exp x + log ((EMLTree.eml b1 b2).eval x)
        = k - (exp x - log ((EMLTree.eml b1 b2).eval x)) := by
      mach_mpoly [k, exp x, log ((EMLTree.eml b1 b2).eval x)]
    rw [e1, e2] at u; exact u
  -- the floor is below that constant, since `exp (exp x) > 0`
  have hfloor : exp (- -log (k - d - (k - d) * exp (-1 : Real)) - exp (exp x)) ≤ k - d - (k - d) * exp (-1 : Real) := by
    have harg : - -log (k - d - (k - d) * exp (-1 : Real)) - exp (exp x) ≤ log (k - d - (k - d) * exp (-1 : Real)) := by
      have u := add_le_add_wit (le_refl (log (k - d - (k - d) * exp (-1 : Real))))
        (neg_nonpos_of_nonneg (le_of_lt (exp_pos (exp x))))
      have e1 : log (k - d - (k - d) * exp (-1 : Real)) + -exp (exp x)
          = - -log (k - d - (k - d) * exp (-1 : Real)) - exp (exp x) := by
        mach_mpoly [log (k - d - (k - d) * exp (-1 : Real)), exp (exp x)]
      have e2 : log (k - d - (k - d) * exp (-1 : Real)) + 0 = log (k - d - (k - d) * exp (-1 : Real)) := by mach_ring
      rw [e1, e2] at u; exact u
    have w := exp_monotone harg
    rw [exp_log hgap0] at w; exact w
  exact le_trans hfloor hgapc

/-- **A depth-≤1 logarithm is eventually non-negative, or eventually bounded away below zero.**

There is no third possibility: it cannot creep up to `0` from below. This is the "nothing tends to
`0` from above" fact that underlies every result in this file, stated for `log` and proved by
enumeration — and the *only* shape landing in the negative branch is a constant, which is why the
bound there is uniform.

| shape | branch |
|---|---|
| `α` | either, by the sign of `log α`; if negative, `δ = −log α` is a genuine constant |
| `x` | non-negative past `x = 1` |
| `c − log x` | goes non-positive, so the totalised `log` is exactly `0` |
| `exp x − d` | exceeds `1` past `x = d + 1` |
| `exp x − log x` | exceeds `1` always, since `1 + x ≤ exp x` and `log x < x` |

The `d = k` cell of the depth-3 residue needs exactly this: its gap is `log (1 + m·e^{k−exp x})`
with `m = −log (b₂ x)`, and a floor must be chosen *before* `x`, so `m` has to be uniformly
positive. -/
theorem depth_le_one_log_sign_dichotomy (b : EMLTree) (hb : b.depth ≤ 1) :
    (∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 ≤ log (b.eval x))
    ∨ (∃ δ X : Real, 0 < δ ∧ 1 ≤ X ∧ ∀ x : Real, X ≤ x → log (b.eval x) ≤ -δ) := by
  have hlog_ge_zero_of_one_le : ∀ y : Real, 1 ≤ y → 0 ≤ log y := by
    intro y hy
    have w := log_le_log zero_lt_one_ax hy
    rw [log_one] at w; exact w
  rcases depth_le_one_form b hb with ⟨α, hb'⟩ | hb' | ⟨c, hc, hb'⟩ | ⟨dd, hb'⟩ | hb'
  · -- constant: split on the sign of `log α`
    rcases lt_total (log α) 0 with hneg | hz | hpos
    · refine Or.inr ⟨-log α, 1, ?_, le_refl 1, ?_⟩
      · have u := add_lt_add_left hneg (-log α)
        have e1 : -log α + log α = (0 : Real) := by mach_ring
        have e2 : -log α + 0 = -log α := by mach_ring
        rw [e1, e2] at u; exact u
      · intro x hx
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
        rw [hb' x hxpos]
        have e : - -log α = log α := by mach_ring
        rw [e]
        exact le_refl _
    · exact Or.inl ⟨1, le_refl 1, fun x hx => by
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
        rw [hb' x hxpos, ← hz]
        exact le_refl _⟩
    · exact Or.inl ⟨1, le_refl 1, fun x hx => by
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
        rw [hb' x hxpos]; exact le_of_lt hpos⟩
  · -- the identity: `log x ≥ 0` past `x = 1`
    exact Or.inl ⟨1, le_refl 1, fun x hx => by
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb' x hxpos]; exact hlog_ge_zero_of_one_le x hx⟩
  · -- `c − log x` goes non-positive, and the totalisation makes the log exactly `0`
    -- the threshold is built from `exp c`, not `c`: what is needed is `log x ≥ c`, i.e. `x ≥ exp c`
    refine Or.inl ⟨1 + exp (exp c), d2_one_le_shift (exp c), fun x hx => ?_⟩
    have hxc : exp c ≤ x := le_trans (d2_le_shift (exp c)) hx
    have hx1 : (1 : Real) ≤ x := le_trans (d2_one_le_shift (exp c)) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb' x hxpos]
    have hle : c - log x ≤ 0 := by
      have hlogx : c ≤ log x := by
        have w := log_le_log (exp_pos c) hxc
        rw [log_exp] at w
        exact w
      have u := add_le_add_wit hlogx (le_refl (-log x))
      have e1 : c + -log x = c - log x := by mach_ring
      have e2 : log x + -log x = (0 : Real) := by mach_ring
      rw [e1, e2] at u; exact u
    rw [log_nonpos hle]
    exact le_refl _
  · -- `exp x − d` exceeds `1` past `x = d + 1`
    refine Or.inl ⟨1 + exp (dd + 1), d2_one_le_shift (dd + 1), fun x hx => ?_⟩
    have hxd : dd + 1 ≤ x := le_trans (d2_le_shift (dd + 1)) hx
    have hx1 : (1 : Real) ≤ x := le_trans (d2_one_le_shift (dd + 1)) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb' x hxpos]
    refine hlog_ge_zero_of_one_le _ ?_
    have hlt : dd + 1 < exp x := lt_of_le_of_lt hxd (exp_grows_strictly_thm x)
    have u := add_lt_add_left hlt (-dd)
    have e1 : -dd + (dd + 1) = (1 : Real) := by mach_mpoly [dd]
    have e2 : -dd + exp x = exp x - dd := by mach_mpoly [dd, exp x]
    rw [e1, e2] at u; exact le_of_lt u
  · -- `exp x − log x ≥ 1`, from `1 + x ≤ exp x` and `log x < x`
    refine Or.inl ⟨1, le_refl 1, fun x hx => ?_⟩
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
    rw [hb' x hxpos]
    refine hlog_ge_zero_of_one_le _ ?_
    have hlx : log x < x := by
      have w := exp_grows_strictly_thm (log x)
      rw [exp_log hxpos] at w; exact w
    have hex : 1 + x ≤ exp x := one_add_le_exp x
    have u := add_le_add_wit hex (neg_le_neg_wit (le_of_lt hlx))
    have e1 : 1 + x + -x = (1 : Real) := by mach_mpoly [x]
    have e2 : exp x + -log x = exp x - log x := by mach_ring
    rw [e1, e2] at u; exact u

/-- **`d = k`: the tight cell, and the last one.**

Here `exp (b₁ x) = exp (exp x − k)` is the target *exactly*, so the hypothesis `node < k` reduces to
`log (b₂ x) < 0` — the node clears the target only by whatever the right child's logarithm gives
back. The gap is then `log (1 + m·e^{k−exp x})` with `m = −log (b₂ x) > 0`, which decays only
**singly** exponentially, while the floor decays **doubly**. So the estimate is not the difficulty.

The difficulty is that the floor's constant must be chosen *before* `x`, so `m` has to be uniformly
positive — and that is exactly `depth_le_one_log_sign_dichotomy`. Its non-negative branch makes the
hypothesis unfireable (vacuous); its negative branch supplies the uniform `δ`.

This is the cell whose witness refuted the constant-gap statement outright
(`depth_le_three_gap_below_refuted`). The decaying floor survives it with room to spare. -/
theorem d3_identity_eml_expd_left_eq (b1 b2 : EMLTree) (h2 : b2.depth ≤ 1) (k : Real)
    (hb1 : ∀ x : Real, 0 < x → b1.eval x = exp x - k) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp (EMLTree.var.eval x) - log ((EMLTree.eml b1 b2).eval x)) := by
  rcases depth_le_one_log_sign_dichotomy b2 h2 with ⟨XN, hXN, hnn⟩ | ⟨δ, XD, hδ, hXD, hneg⟩
  · -- non-negative branch: `B x ≤ exp (exp x − k)`, so the hypothesis never fires
    refine d3_identity_vacuous_of_upper (EMLTree.eml b1 b2) k XN hXN ?_
    intro x hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hXN hx)
    show exp (b1.eval x) - log (b2.eval x) ≤ exp (exp x - k)
    rw [hb1 x hxpos]
    have u := add_le_add_wit (le_refl (exp (exp x - k))) (neg_nonpos_of_nonneg (hnn x hx))
    have e1 : exp (exp x - k) + -log (b2.eval x) = exp (exp x - k) - log (b2.eval x) := by mach_ring
    have e2 : exp (exp x - k) + 0 = exp (exp x - k) := by mach_ring
    rw [e1, e2] at u; exact u
  · -- negative branch: `m ≥ δ > 0` uniformly, and the floor is doubly exponentially smaller
    refine ⟨1 - k - log δ, 1 + exp XD + exp (-(1 - k - log δ)), d2_ray_ge_one XD _, ?_⟩
    intro x hx _
    have hxD : XD ≤ x := le_trans (d2_ray_ge_fst XD _) hx
    have hxC : -(1 - k - log δ) ≤ x := le_trans (d2_ray_ge_snd XD _) hx
    have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_one XD _) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    have hm : δ ≤ -log (b2.eval x) := by
      have u := neg_le_neg_wit (hneg x hxD)
      have e : - -δ = δ := by mach_ring
      rw [e] at u; exact u
    have hBlow : exp (exp x - k) + δ ≤ (EMLTree.eml b1 b2).eval x := by
      show _ ≤ exp (b1.eval x) - log (b2.eval x)
      rw [hb1 x hxpos]
      have u := add_le_add_wit (le_refl (exp (exp x - k))) hm
      have e : exp (exp x - k) + -log (b2.eval x) = exp (exp x - k) - log (b2.eval x) := by mach_ring
      rw [e] at u; exact u
    -- the floor `t` is in `[0,1]`
    have ht0 : (0 : Real) ≤ exp (-(1 - k - log δ) - exp (exp x)) := le_of_lt (exp_pos _)
    have ht1 : exp (-(1 - k - log δ) - exp (exp x)) ≤ 1 := by
      have harg : -(1 - k - log δ) - exp (exp x) ≤ 0 := by
        have hxx : -(1 - k - log δ) < exp (exp x) :=
          lt_of_le_of_lt hxC (lt_trans_ax (exp_grows_strictly_thm x)
            (exp_grows_strictly_thm (exp x)))
        have u := add_lt_add_left hxx (-exp (exp x))
        have e1 : -exp (exp x) + -(1 - k - log δ) = -(1 - k - log δ) - exp (exp x) := by
          mach_mpoly [exp (exp x), k, log δ]
        have e2 : -exp (exp x) + exp (exp x) = (0 : Real) := by mach_ring
        rw [e1, e2] at u; exact le_of_lt u
      have w := exp_monotone harg
      rw [exp_zero] at w; exact w
    -- `exp v · t · e ≤ δ`, because `exp x ≤ exp (exp x)` swallows the constant
    have hprod : exp (exp x - k) * (exp (-(1 - k - log δ) - exp (exp x)) * exp 1) ≤ δ := by
      have hcomb : exp (exp x - k) * (exp (-(1 - k - log δ) - exp (exp x)) * exp 1)
          = exp (exp x - k + (-(1 - k - log δ) - exp (exp x) + 1)) := by
        rw [← exp_add, ← exp_add]
      rw [hcomb]
      have harg : exp x - k + (-(1 - k - log δ) - exp (exp x) + 1) ≤ log δ := by
        have hxx : exp x ≤ exp (exp x) := le_of_lt (exp_grows_strictly_thm (exp x))
        have u := add_le_add_wit hxx (le_refl (log δ - exp (exp x)))
        have e1 : exp x - k + (-(1 - k - log δ) - exp (exp x) + 1)
            = exp x + (log δ - exp (exp x)) := by
          mach_mpoly [exp x, k, log δ, exp (exp x)]
        have e2 : exp (exp x) + (log δ - exp (exp x)) = log δ := by
          mach_mpoly [log δ, exp (exp x)]
        rw [e1]
        rw [e2] at u
        exact u
      have w := exp_monotone harg
      rw [exp_log hδ] at w; exact w
    -- so `exp (v + t) ≤ exp v + δ ≤ B x`
    have hlift : exp (exp x - k + exp (-(1 - k - log δ) - exp (exp x)))
        ≤ (EMLTree.eml b1 b2).eval x := by
      have hstep := mul_le_mul_of_nonneg_left
        (exp_le_one_add_scaled ht0 ht1) (le_of_lt (exp_pos (exp x - k)))
      have e : exp (exp x - k) * (1 + exp (-(1 - k - log δ) - exp (exp x)) * exp 1)
          = exp (exp x - k)
            + exp (exp x - k) * (exp (-(1 - k - log δ) - exp (exp x)) * exp 1) := by
        mach_mpoly [exp (exp x - k), exp (-(1 - k - log δ) - exp (exp x)), exp 1]
      rw [e] at hstep
      have hsum : exp (exp x - k)
          + exp (exp x - k) * (exp (-(1 - k - log δ) - exp (exp x)) * exp 1)
          ≤ exp (exp x - k) + δ :=
        add_le_add_wit (le_refl _) hprod
      have hcomb : exp (exp x - k) * exp (exp (-(1 - k - log δ) - exp (exp x)))
          = exp (exp x - k + exp (-(1 - k - log δ) - exp (exp x))) := by rw [← exp_add]
      rw [hcomb] at hstep
      exact le_trans (le_trans hstep hsum) hBlow
    -- take logs and rearrange
    have hlog := log_le_log (exp_pos _) hlift
    rw [log_exp] at hlog
    show exp (-(1 - k - log δ) - exp (exp x))
      ≤ k - (exp x - log ((EMLTree.eml b1 b2).eval x))
    have u := add_le_add_wit hlog (le_refl (-(exp x - k)))
    have e1 : exp x - k + exp (-(1 - k - log δ) - exp (exp x)) + -(exp x - k)
        = exp (-(1 - k - log δ) - exp (exp x)) := by
      mach_mpoly [exp x, k, exp (-(1 - k - log δ) - exp (exp x))]
    have e2 : log ((EMLTree.eml b1 b2).eval x) + -(exp x - k)
        = k - (exp x - log ((EMLTree.eml b1 b2).eval x)) := by
      mach_mpoly [k, exp x, log ((EMLTree.eml b1 b2).eval x)]
    rw [e1, e2] at u
    exact u

/-! ### Route map for the one remaining branch: `A = eml a₁ a₂`, bounded

**Four of the five branches of `Depth3ApproachBelowEml` are closed.** What remains is `A` bounded and
compound. Sized here rather than guessed, because this file has twice paid for the opposite.

*Narrower than it looks.* For `exp (A x)` to be bounded, `exp (a₁ x)` must be bounded above, which
kills three of the five `Depth1Form` shapes outright — only `a₁ x = α` and `a₁ x = c − log x` survive,
and in both `exp (a₁ x) ≤ P` for a constant `P`.

*But the obvious reduction fails.* If `exp (A x) ≤ a` then the gap `k − exp (A x) + log (B x)`
dominates the constant-case gap, yet our hypothesis `log (B x) > exp (A x) − k` is **weaker** than the
constant case's `log (B x) > a − k`. They do not line up in either direction, so
`d3_const_left_eml` cannot be reused as a bound.

*Where the difficulty actually sits.* Splitting on `a₂` gives one easy family and one hard one:

* `log (a₂ x) → ∞` (`a₂ ∈ {x, exp x − d, exp x − log x}`): then `exp (A x) → 0`, and the node is
  `−log (B x)` plus a vanishing term. Fine unless `k + log (B x) → 0` too, and then **both** terms
  vanish and the gap is their difference.
* `log (a₂ x)` bounded: `exp (A x)` tends to a constant, and the node is that constant minus
  `log (B x)` — the constant case *in the limit*, but only in the limit.

Both hard sub-cases are the same shape: two quantities, each tending to a limit at its own rate, whose
**difference** is the gap. That is a *separation* question — how close two EML-expressible values can
come without coinciding — and this corpus has no lemma of that kind. `depth_le_two_approach_constant`
bounds approach to a **fixed** constant; nothing bounds the approach of one moving value to another.

*Estimate.* A nested enumeration (`a₁` × `a₂` × `B`) plus at least one new rate-separation lemma.
Plausibly larger than the identity branch, which took ~700 lines. **Not** a transcription, and not
something to start without deciding it is the best-posed target available — the same check that sent
this arc here in the first place.

*Evidence it is TRUE, so the target is worth the work.* The competing scales are `exp (−x)`-ish
(single exponential) against a floor of `exp (−C − exp (exp x))` (triple). Even exact cancellation of
leading terms leaves next-order terms at `exp (−2x)` or `x·exp (−x)`, still astronomically above the
floor. Nothing here suggests a counterexample; the difficulty is machinery, not truth. -/

/-! ### The bounded-left branch: `A = const c` -/

/-- **`A = const c` closes via the depth-2 approach lemma.**

With a constant left child the target stops moving: the hypothesis `exp c − log (B x) < k` is
`B x > exp (exp c − k)`, a **fixed** value. `depth_le_two_approach_constant` then supplies
`exp (−C − x) ≤ B x − T` — a floor decaying only *singly* exponentially, against a *doubly*
exponentially small requirement, so the margin is enormous.

The non-positive branch is not an edge case to wave at: there the totalised `log (B x) = 0`, the node
is `exp c`, and the hypothesis says `exp c < k`, leaving the constant gap `k − exp c`. -/
theorem d3_const_left_eml (c : Real) (B : EMLTree) (hB : B.depth ≤ 2) (k : Real) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp ((EMLTree.const c).eval x) - log (B.eval x) < k →
        exp (-C - exp (exp x)) ≤ k
          - (exp ((EMLTree.const c).eval x) - log (B.eval x)) := by
  obtain ⟨Capp, X₀, hX₀, happ⟩ := depth_le_two_approach_constant B hB (exp (exp c - k))
  -- `C` must serve BOTH branches, and `exp t > t` gives a bound above two constants at once
  refine ⟨exp (exp c - k + 1 + Capp) + exp (-log (k - exp c)),
          1 + exp X₀ + exp 1, d2_ray_ge_one X₀ 1, ?_⟩
  intro x hx hlt
  have hxX : X₀ ≤ x := le_trans (d2_ray_ge_fst X₀ 1) hx
  have hx1 : (1 : Real) ≤ x := le_trans (d2_ray_ge_one X₀ 1) hx
  have hlt' : exp c - log (B.eval x) < k := hlt
  have hloggt : exp c - k < log (B.eval x) := by
    have u := add_lt_add_left hlt' (-exp c + log (B.eval x))
    have e1 : -exp c + log (B.eval x) + (exp c - log (B.eval x)) = (0 : Real) := by
      mach_mpoly [exp c, log (B.eval x)]
    have e2 : -exp c + log (B.eval x) + k = k - exp c + log (B.eval x) := by
      mach_mpoly [exp c, log (B.eval x), k]
    rw [e1, e2] at u
    have v := add_lt_add_left u (exp c - k)
    have e3 : exp c - k + 0 = exp c - k := by mach_ring
    have e4 : exp c - k + (k - exp c + log (B.eval x)) = log (B.eval x) := by
      mach_mpoly [exp c, k, log (B.eval x)]
    rw [e3, e4] at v; exact v
  -- the two constants the floor must clear
  have hC1 : exp c - k + 1 + Capp
      ≤ exp (exp c - k + 1 + Capp) + exp (-log (k - exp c)) := by
    have u := add_le_add_wit (le_of_lt (exp_grows_strictly_thm (exp c - k + 1 + Capp)))
      (le_of_lt (exp_pos (-log (k - exp c))))
    have e : exp c - k + 1 + Capp + 0 = exp c - k + 1 + Capp := by mach_ring
    rw [e] at u; exact u
  have hC2 : -log (k - exp c)
      ≤ exp (exp c - k + 1 + Capp) + exp (-log (k - exp c)) := by
    have u := add_le_add_wit (le_of_lt (exp_pos (exp c - k + 1 + Capp)))
      (le_of_lt (exp_grows_strictly_thm (-log (k - exp c))))
    have e : (0 : Real) + -log (k - exp c) = -log (k - exp c) := by mach_ring
    rw [e] at u; exact u
  show exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x))
    ≤ k - (exp c - log (B.eval x))
  -- both non-positive branches: totalised `log = 0`, node is `exp c`, gap is the constant `k − exp c`
  have hzero_branch : log (B.eval x) = 0 →
      exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x))
        ≤ k - (exp c - log (B.eval x)) := by
    intro hlz
    rw [hlz] at hloggt ⊢
    have hkc : (0 : Real) < k - exp c := by
      have u := add_lt_add_left hloggt (k - exp c)
      have e1 : k - exp c + (exp c - k) = (0 : Real) := by mach_mpoly [k, exp c]
      have e2 : k - exp c + 0 = k - exp c := by mach_ring
      rw [e1, e2] at u; exact u
    have harg : -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x)
        ≤ log (k - exp c) := by
      have u := add_le_add_wit (neg_le_neg_wit hC2)
        (neg_nonpos_of_nonneg (le_of_lt (exp_pos (exp x))))
      have e1 : - -log (k - exp c) + 0 = log (k - exp c) := by mach_ring
      have e2 : -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) + -exp (exp x)
          = -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x) := by
        mach_mpoly [exp (exp c - k + 1 + Capp), exp (-log (k - exp c)), exp (exp x)]
      rw [e2, e1] at u; exact u
    have w := exp_monotone harg
    rw [exp_log hkc] at w
    have e3 : k - (exp c - 0) = k - exp c := by mach_mpoly [k, exp c]
    rw [e3]; exact w
  rcases lt_total 0 (B.eval x) with hpos | hz | hneg
  · -- `B x > 0`: the target is genuinely exceeded, so the approach lemma applies
    have hTlt : exp (exp c - k) < B.eval x := by
      have w := exp_lt hloggt
      rw [exp_log hpos] at w; exact w
    have hfloor := happ x hxX hTlt
    have ht0 : (0 : Real) ≤ exp (-(exp (exp c - k + 1 + Capp)
      + exp (-log (k - exp c))) - exp (exp x)) := le_of_lt (exp_pos _)
    have hBIGpos : (0 : Real) < exp (exp c - k + 1 + Capp) + exp (-log (k - exp c)) := by
      have u := add_lt_add_left (exp_pos (-log (k - exp c))) (exp (exp c - k + 1 + Capp))
      have e : exp (exp c - k + 1 + Capp) + 0 = exp (exp c - k + 1 + Capp) := by mach_ring
      rw [e] at u
      exact lt_trans_ax (exp_pos _) u
    have ht1 : exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x)) ≤ 1 := by
      refine le_trans (exp_monotone ?_) (le_of_eq exp_zero)
      have u := add_le_add_wit (neg_nonpos_of_nonneg (le_of_lt hBIGpos))
        (neg_nonpos_of_nonneg (le_of_lt (exp_pos (exp x))))
      have e1 : -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) + -exp (exp x) = -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x) := by
        mach_mpoly [exp (exp c - k + 1 + Capp), exp (-log (k - exp c)), exp (exp x)]
      have e2 : (0 : Real) + 0 = 0 := by mach_ring
      rw [e1, e2] at u; exact u
    -- `T·t·e ≤ exp (−Capp − x)`, the approach lemma's own floor
    have hstep : exp (exp c - k)
        * (exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x)) * exp 1)
        ≤ exp (-Capp - x) := by
      rw [← exp_add, ← exp_add]
      refine exp_monotone ?_
      have hxx : x ≤ exp (exp x) :=
        le_of_lt (lt_trans_ax (exp_grows_strictly_thm x) (exp_grows_strictly_thm (exp x)))
      have u := add_le_add_wit (neg_le_neg_wit hC1) (neg_le_neg_wit hxx)
      have e1 : -(exp c - k + 1 + Capp) + -x
          = -(exp c - k + 1 + Capp) - x := by mach_mpoly [exp c, k, Capp, x]
      rw [e1] at u
      have e2 : exp c - k + (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c)))
          - exp (exp x) + 1)
          = -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) + (exp c - k + 1)
            - exp (exp x) := by
        mach_mpoly [exp c, k, exp (exp c - k + 1 + Capp), exp (-log (k - exp c)), exp (exp x)]
      rw [e2]
      have hchain : -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) + (exp c - k + 1)
          - exp (exp x) ≤ -Capp - x := by
        have v := add_le_add_wit (neg_le_neg_wit hC1) (neg_le_neg_wit hxx)
        have f1 : -(exp c - k + 1 + Capp) + -x = -(exp c - k + 1 + Capp) - x := by
          mach_mpoly [exp c, k, Capp, x]
        have f2 : -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) + -exp (exp x)
            = -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x) := by
          mach_mpoly [exp (exp c - k + 1 + Capp), exp (-log (k - exp c)), exp (exp x)]
        rw [f1, f2] at v
        have w2 := add_le_add_wit v (le_refl (exp c - k + 1))
        have f3 : -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x)
            + (exp c - k + 1)
            = -(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) + (exp c - k + 1)
              - exp (exp x) := by
          mach_mpoly [exp (exp c - k + 1 + Capp), exp (-log (k - exp c)), exp (exp x), exp c, k]
        have f4 : -(exp c - k + 1 + Capp) - x + (exp c - k + 1) = -Capp - x := by
          mach_mpoly [exp c, k, Capp, x]
        rw [f3, f4] at w2; exact w2
      exact hchain
    -- assemble: `B x ≥ T·exp t`, so `log (B x) ≥ (exp c − k) + t`
    have hlift : exp (exp c - k
        + exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x)))
        ≤ B.eval x := by
      have hsc := mul_le_mul_of_nonneg_left (exp_le_one_add_scaled ht0 ht1)
        (le_of_lt (exp_pos (exp c - k)))
      have e : exp (exp c - k) * (1
          + exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x)) * exp 1)
          = exp (exp c - k) + exp (exp c - k)
            * (exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x))
              * exp 1) := by
        mach_mpoly [exp (exp c - k),
          exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x)), exp 1]
      rw [e] at hsc
      have hb : exp (exp c - k) + exp (-Capp - x) ≤ B.eval x := by
        have u := add_le_add_wit (le_refl (exp (exp c - k))) hfloor
        have e2 : exp (exp c - k) + (B.eval x - exp (exp c - k)) = B.eval x := by
          mach_mpoly [exp (exp c - k), B.eval x]
        rw [e2] at u; exact u
      have hmid := add_le_add_wit (le_refl (exp (exp c - k))) hstep
      rw [← exp_add] at hsc
      exact le_trans hsc (le_trans hmid hb)
    have hlog := log_le_log (exp_pos _) hlift
    rw [log_exp] at hlog
    have u := add_le_add_wit hlog (le_refl (k - exp c))
    have e1 : exp c - k
        + exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x))
        + (k - exp c)
        = exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x)) := by
      mach_mpoly [exp c, k,
        exp (-(exp (exp c - k + 1 + Capp) + exp (-log (k - exp c))) - exp (exp x))]
    have e2 : log (B.eval x) + (k - exp c) = k - (exp c - log (B.eval x)) := by
      mach_mpoly [log (B.eval x), k, exp c]
    rw [e1, e2] at u; exact u
  · exact hzero_branch (by rw [← hz, log_nonpos (le_refl 0)])
  · exact hzero_branch (log_nonpos (le_of_lt hneg))

/-- **The bounded-left branch splits, and the large-`B` half is immediate.**

If `exp (A x) ≤ K` and `log (B x)` eventually clears `K − k + 1`, the gap is at least `1` — no
cancellation analysis required, because the two bounds simply do not overlap. The floor
`exp (−0 − exp (exp x))` is below `1` for every `x`, since `exp (exp x) > 0`.

This is worth stating separately because it isolates the *actual* residue: the bounded-left branch is
hard only when `log (B x)` is **also** bounded, so that `exp (A x)` and `log (B x)` are two bounded
quantities whose difference must be separated from `k`. Everything outside that window is arithmetic.
-/
theorem d3_bounded_left_large_right (A B : EMLTree) (k K X : Real) (hX : 1 ≤ X)
    (hK : ∀ x : Real, X ≤ x → exp (A.eval x) ≤ K)
    (hBig : ∀ x : Real, X ≤ x → K - k + 1 ≤ log (B.eval x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (A.eval x) - log (B.eval x) < k →
        exp (-C - exp (exp x)) ≤ k - (exp (A.eval x) - log (B.eval x)) := by
  -- `C = 1` rather than `0`: a literal `-0` in the floor makes the normaliser grind for nothing
  refine ⟨1, X, hX, ?_⟩
  intro x hx _
  have hfl : exp (-1 - exp (exp x)) ≤ 1 := by
    refine le_trans (exp_monotone ?_) (le_of_eq exp_zero)
    have hneg : (-1 : Real) < 0 := by
      have w := add_lt_add_left zero_lt_one_ax (-(1 : Real))
      have f1 : -(1 : Real) + 0 = -1 := by mach_ring
      have f2 : -(1 : Real) + 1 = 0 := by mach_ring
      rw [f1, f2] at w; exact w
    have u := add_le_add_wit (le_of_lt hneg)
      (neg_nonpos_of_nonneg (le_of_lt (exp_pos (exp x))))
    have e1 : -1 + -exp (exp x) = -1 - exp (exp x) := by mach_ring
    have e2 : (0 : Real) + 0 = 0 := by mach_ring
    rw [e1, e2] at u; exact u
  -- and the gap is at least `1`, because the two bounds do not overlap
  have hgap : (1 : Real) ≤ k - (exp (A.eval x) - log (B.eval x)) := by
    have u := add_le_add_wit (neg_le_neg_wit (hK x hx)) (hBig x hx)
    have e1 : -K + (K - k + 1) = 1 - k := by mach_mpoly [K, k]
    have e2 : -exp (A.eval x) + log (B.eval x)
        = -(exp (A.eval x) - log (B.eval x)) := by mach_ring
    rw [e1, e2] at u
    have v := add_le_add_wit u (le_refl k)
    have e3 : 1 - k + k = (1 : Real) := by mach_mpoly [k]
    have e4 : -(exp (A.eval x) - log (B.eval x)) + k
        = k - (exp (A.eval x) - log (B.eval x)) := by
      mach_mpoly [k, exp (A.eval x), log (B.eval x)]
    rw [e3, e4] at v; exact v
  exact le_trans hfl hgap


end MachLib
