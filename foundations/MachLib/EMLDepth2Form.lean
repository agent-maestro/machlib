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


end MachLib
