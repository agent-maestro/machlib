import MachLib.EMLDepth2InvX

/-!
# The growth envelope `E_k` — a depth-indexed ceiling, and the lower-bound tool it gives

`depth_le_one_upper_bound` (`M − log x`) and `depth_le_two_growth_ceiling` (`C/x`) were proved ad
hoc, one shape at a time. They are the first two rungs of a tower: `exp(M − log x) = exp(M)/x`, so

```
envelope 0       M x = M − log x
envelope (k+1)   M x = exp (envelope k M x)
```

and the general statement is one induction, with **no shape analysis and no cutoff**.

## The side condition is real

The step is `t = eml a b`, `t x = exp(a x) − log(b x)`. The `exp(a x)` half follows from the IH.
The `−log(b x)` half does not: for `0 < b x < 1` it is positive and **unbounded**, so no ceiling on
`b` controls it. That is the arm's **dual ceiling**, and removing it in general needs to know a
shallow tree cannot be arbitrarily small while staying positive — i.e. finiteness of sign changes
for exp-log expressions, a **Khovanskii/Pfaffian** input.

So the envelope carries `LogSafe`: every `eml` right child stays `≥ 1`. Then `log (b x) ≥ 0`, the
bad half vanishes, and the induction closes.

## `1/x` is NOT excluded by this

`1/x ≤ exp(M)/x = envelope 1 M x` for `M ≥ 0`, so the reciprocal sits *inside* the first rung. **The
envelope cannot settle `d(1/x)`** — which is muse 1's correction made concrete: EML depth is *gate*
complexity, not *growth* complexity. It also explains why growth arguments never closed `d(1/x)`:
wrong instrument for that target. The envelope bites on targets that grow *faster* than the tower —
`inv_x_sq_not_log_safe_depth_one` below is the worked example.
-/

namespace MachLib

open Real

/-- The `k`-fold exponential tower seeded by `M − log x`. -/
noncomputable def envelope : Nat → Real → Real → Real
  | 0, M, x => M - log x
  | (k + 1), M, x => exp (envelope k M x)

/-- Every `eml` right child stays `≥ 1` on `(0, d]`, so no totalised `log` in the tree is negative. -/
def LogSafe (d : Real) : EMLTree → Prop
  | .const _ => True
  | .var => True
  | .eml a b => LogSafe d a ∧ LogSafe d b ∧ (∀ x : Real, 0 < x → x ≤ d → 1 ≤ b.eval x)

/-- **The tower is increasing in `k`**, from `y < exp y`. -/
theorem envelope_le_succ (k : Nat) (M x : Real) : envelope k M x ≤ envelope (k + 1) M x := by
  show envelope k M x ≤ exp (envelope k M x)
  exact le_of_lt (exp_grows_strictly_thm _)

theorem envelope_mono_k {j k : Nat} (h : j ≤ k) (M x : Real) :
    envelope j M x ≤ envelope k M x := by
  induction k with
  | zero =>
      have hj : j = 0 := Nat.le_zero.mp h
      subst hj; exact le_refl _
  | succ n ih =>
      rcases Nat.lt_or_ge j (n + 1) with hlt | hge
      · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (envelope_le_succ n M x)
      · have hj : j = n + 1 := Nat.le_antisymm h hge
        subst hj; exact le_refl _

/-- **The envelope, at the tree's own depth.** One induction on the tree; no shape cases, no cutoff.

Only the *left* child's induction hypothesis is used — the right child contributes solely through
`LogSafe`, which makes its `log` non-negative. -/
theorem growth_envelope_exact (t : EMLTree) (hs : LogSafe 1 t) :
    ∃ M : Real, ∀ x : Real, 0 < x → x ≤ 1 → t.eval x ≤ envelope t.depth M x := by
  have hnl : ∀ x : Real, 0 < x → x ≤ 1 → (0 : Real) ≤ -log x := by
    intro x hx h1
    have hh := neg_le_neg_wit (log_nonpos_of_le_one hx h1)
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at hh; exact hh
  induction t with
  | const c =>
      refine ⟨c, fun x hx h1 => ?_⟩
      show c ≤ c - log x
      have s := add_le_add_wit (le_refl c) (hnl x hx h1)
      have l : c + (0 : Real) = c := by mach_ring
      have r : c + -log x = c - log x := by mach_mpoly [c, log x]
      rw [l, r] at s; exact s
  | var =>
      refine ⟨1, fun x hx h1 => ?_⟩
      show x ≤ 1 - log x
      have s := add_le_add_wit h1 (hnl x hx h1)
      have l : x + (0 : Real) = x := by mach_ring
      have r : (1 : Real) + -log x = 1 - log x := by mach_mpoly [log x]
      rw [l, r] at s; exact s
  | eml a b iha ihb =>
      obtain ⟨hsa, _, hb1⟩ := hs
      obtain ⟨M, hM⟩ := iha hsa
      refine ⟨M, fun x hx h1 => ?_⟩
      show exp (a.eval x) - log (b.eval x) ≤ _
      -- log-safety kills the subtracted term
      have hlog : (0 : Real) ≤ log (b.eval x) := by
        have s := log_le_log one_pos (hb1 x hx h1)
        rwa [log_one] at s
      have hstep : exp (a.eval x) - log (b.eval x) ≤ exp (a.eval x) := by
        have s := add_le_add_wit (le_refl (exp (a.eval x))) (neg_le_neg_wit hlog)
        have l : exp (a.eval x) + -log (b.eval x) = exp (a.eval x) - log (b.eval x) := by
          mach_mpoly [exp (a.eval x), log (b.eval x)]
        have r : exp (a.eval x) + -(0 : Real) = exp (a.eval x) := by mach_ring
        rw [l, r] at s; exact s
      -- the left child's IH, exponentiated, is rung `a.depth + 1`
      have hexp : exp (a.eval x) ≤ envelope (a.depth + 1) M x := exp_monotone (hM x hx h1)
      have hle : a.depth + 1 ≤ (EMLTree.eml a b).depth := by
        simp only [EMLTree.depth]
        have : a.depth ≤ max a.depth b.depth := Nat.le_max_left _ _
        omega
      exact le_trans hstep (le_trans hexp (envelope_mono_k hle M x))

/-- The envelope at any `k ≥ depth`. -/
theorem growth_envelope (t : EMLTree) (k : Nat) (hk : t.depth ≤ k) (hs : LogSafe 1 t) :
    ∃ M : Real, ∀ x : Real, 0 < x → x ≤ 1 → t.eval x ≤ envelope k M x := by
  obtain ⟨M, hM⟩ := growth_envelope_exact t hs
  exact ⟨M, fun x hx h1 => le_trans (hM x hx h1) (envelope_mono_k hk M x)⟩

/-- # **The lower-bound tool.**

A target that outgrows rung `k` **for every constant `M`** cannot be computed by any log-safe tree
of depth `≤ k`. This is the schema `complexity(T) ≤ k ⟹ germ(T) ∈ E_k`, contraposed. -/
theorem depth_gt_of_outgrows (f : Real → Real) (k : Nat)
    (hf : ∀ M : Real, ∃ x : Real, 0 < x ∧ x ≤ 1 ∧ envelope k M x < f x) :
    ∀ t : EMLTree, t.depth ≤ k → LogSafe 1 t →
      ¬ (∀ x : Real, 0 < x → x ≤ 1 → t.eval x = f x) := by
  intro t hk hs heq
  obtain ⟨M, hM⟩ := growth_envelope t k hk hs
  obtain ⟨x, hx, hx1, hlt⟩ := hf M
  have h1 : f x ≤ envelope k M x := by rw [← heq x hx hx1]; exact hM x hx hx1
  exact (ne_of_lt (lt_of_lt_of_le hlt h1)) rfl

/-! ## ▸ The envelope in the metric that is priced

T38-NNP prices **size**, not depth. `two_mul_depth_succ_le_size` transfers the envelope: a size
bound implies a depth bound, so the whole ladder reads in node count. Stated with `2k+1` so **no
Nat division appears**. -/

/-- **Size-indexed envelope.** A log-safe tree of at most `2k+1` nodes is under rung `k`. -/
theorem size_envelope (t : EMLTree) (k : Nat) (hn : t.size ≤ 2 * k + 1) (hs : LogSafe 1 t) :
    ∃ M : Real, ∀ x : Real, 0 < x → x ≤ 1 → t.eval x ≤ envelope k M x := by
  have hb := two_mul_depth_succ_le_size t
  exact growth_envelope t k (by omega) hs

/-- **A size LOWER bound from a growth argument** — the first in this arm. A target outgrowing
rung `k` cannot be computed by any log-safe tree of `2k+1` nodes or fewer. -/
theorem size_gt_of_outgrows (f : Real → Real) (k : Nat)
    (hf : ∀ M : Real, ∃ x : Real, 0 < x ∧ x ≤ 1 ∧ envelope k M x < f x)
    (t : EMLTree) (hs : LogSafe 1 t) (heq : ∀ x : Real, 0 < x → x ≤ 1 → t.eval x = f x) :
    2 * k + 1 < t.size := by
  rcases Nat.lt_or_ge (2 * k + 1) t.size with hgt | hle
  · exact hgt
  · exfalso
    obtain ⟨M, hM⟩ := size_envelope t k hle hs
    obtain ⟨x, hx, hx1, hlt⟩ := hf M
    have h1 : f x ≤ envelope k M x := by rw [← heq x hx hx1]; exact hM x hx hx1
    exact (ne_of_lt (lt_of_lt_of_le hlt h1)) rfl

/-- Sharpened by oddness: `> 2k+1` is `≥ 2k+3`, since sizes are never even. -/
theorem size_ge_of_outgrows (f : Real → Real) (k : Nat)
    (hf : ∀ M : Real, ∃ x : Real, 0 < x ∧ x ≤ 1 ∧ envelope k M x < f x)
    (t : EMLTree) (hs : LogSafe 1 t) (heq : ∀ x : Real, 0 < x → x ≤ 1 → t.eval x = f x) :
    2 * k + 3 ≤ t.size := by
  have h := size_gt_of_outgrows f k hf t hs heq
  obtain ⟨j, hj⟩ := size_odd t
  omega

/-- **The transfer is one-directional, with a specimen.** A *size* bound gives a *depth* bound
(above); a *depth* bound gives **no** size bound. Both trees below have depth `3`; one has `7` nodes
and the other `15`. So there is no size envelope indexed by depth. -/
theorem depth_does_not_bound_size :
    (EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0))
        (EMLTree.const 0)) (EMLTree.const 0)).depth = 3
    ∧ (EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0))
        (EMLTree.const 0)) (EMLTree.const 0)).size = 7
    ∧ (EMLTree.eml
        (EMLTree.eml (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0))
          (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0)))
        (EMLTree.eml (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0))
          (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0)))).depth = 3
    ∧ (EMLTree.eml
        (EMLTree.eml (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0))
          (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0)))
        (EMLTree.eml (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0))
          (EMLTree.eml (EMLTree.const 0) (EMLTree.const 0)))).size = 15 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## ▸ Worked example: `1/x²` needs more than one rung

`envelope 1 M x = exp(M − log x)`, and `x · exp(M − log x) = exp M`. So `x²·envelope 1 M x = x·exp M`,
which drops below `1` as soon as `x < exp(−M)` — and `two_bound_witness` supplies such an `x` that is
also `≤ 1`, with no `min`. -/

theorem inv_x_sq_not_log_safe_depth_one (t : EMLTree) (hd : t.depth ≤ 1) (hs : LogSafe 1 t) :
    ¬ (∀ x : Real, 0 < x → x ≤ 1 → x * (x * t.eval x) = 1) := by
  intro heq
  obtain ⟨M, hM⟩ := growth_envelope t 1 hd hs
  obtain ⟨w, hwpos, hw1, hwE⟩ := two_bound_witness' one_pos (exp_pos (-M))
  have hwle : w ≤ 1 := le_of_lt hw1
  -- t w ≤ envelope 1 M w = exp (M − log w)
  have hub : t.eval w ≤ exp (M - log w) := hM w hwpos hwle
  -- so w·(w·t w) ≤ w·exp M
  have hstep : w * (w * t.eval w) ≤ w * exp M := by
    have inner : w * t.eval w ≤ exp M := by
      have s := mul_le_mul_of_nonneg_left hub (le_of_lt hwpos)
      rwa [mul_exp_sub_log hwpos] at s
    exact mul_le_mul_of_nonneg_left inner (le_of_lt hwpos)
  -- and w·exp M < exp(−M)·exp M = 1
  have hprod : exp (-M) * exp M = 1 := by
    rw [← exp_add]
    have e : -M + M = 0 := by mach_ring
    rw [e, exp_zero]
  have hlt : w * exp M < 1 := by
    have s := mul_lt_mul_of_pos_right hwE (exp_pos M)
    rwa [hprod] at s
  rw [heq w hwpos hwle] at hstep
  exact (ne_of_lt (lt_of_le_of_lt hstep hlt)) rfl

/-- **`1/x²` needs at least 5 nodes** (if log-safe) — the size reading of the example above.
Weak, because rung 1 is low; the point is that the *mechanism* now lands in node count. -/
theorem inv_x_sq_size_ge_five (t : EMLTree) (hs : LogSafe 1 t)
    (heq : ∀ x : Real, 0 < x → x ≤ 1 → x * (x * t.eval x) = 1) : 5 ≤ t.size := by
  have hb := two_mul_depth_succ_le_size t
  rcases Nat.lt_or_ge t.depth 2 with hlt | hge
  · exact absurd heq (inv_x_sq_not_log_safe_depth_one t (by omega) hs)
  · omega

/-! ## ▸ And the honest limit: `1/x` is INSIDE the first rung

`1/x ≤ exp(M)/x` for `M ≥ 0`, so no growth argument at any rung excludes the reciprocal. -/

theorem inv_x_within_envelope_one (x : Real) (hx : 0 < x) :
    1 / x ≤ envelope 1 0 x := by
  show 1 / x ≤ exp ((0 : Real) - log x)
  have hexp : x * exp ((0 : Real) - log x) = 1 := by
    have t := mul_exp_sub_log (A := 0) hx
    rwa [exp_zero] at t
  have hinv : x * (1 / x) = 1 := mul_inv x (ne_of_gt hx)
  have heq : x * (1 / x) = x * exp ((0 : Real) - log x) := by rw [hinv, hexp]
  exact le_of_mul_le_mul_pos_left hx (le_of_eq heq)

end MachLib
