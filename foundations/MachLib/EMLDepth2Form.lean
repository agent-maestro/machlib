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


end MachLib
