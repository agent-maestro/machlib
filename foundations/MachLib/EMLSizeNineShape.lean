import MachLib.EMLDepth2InvX
import MachLib.EMLNetlistDepth

/-!
# The 9-node question is a question about PATHS

`s(1/x) ∈ {9, 11}` is the last open integer in the reciprocal arm, and after
`EMLNetlistDepth` it is known to be a question about the *tree encoding* — no datapath bound
depends on it. That makes it more attractive as a self-contained problem, not less: it needs no
hardware story, and the search space is finite. This module makes "finite" concrete.

**The reduction.** `two_mul_depth_succ_le_size` gives `2·depth + 1 ≤ size` for every tree, and a
tree meeting that bound with equality is forced to be a **path**: every `eml` node has a *leaf*
child, so the tree is a single chain of `eml`s with one leaf hanging off each. That is
`minimal_size_isPath`, and it holds for any depth.

Applied to the reciprocal: `d(1/x) = 4` and `s(1/x) ≥ 9` give `9 = 2·4 + 1`, so **a 9-node tree
computing `1/x` must be a depth-4 path** (`inv_x_size_nine_isPath`). An unbounded search over trees
becomes a search over 4-level chains with a leaf at each level.

**What the search space actually is.** A depth-4 path has, at each of its 4 levels, a choice of
which side carries the chain (2) and what kind of leaf hangs off the other (`const c` or `var`, 2),
plus a terminal leaf (2): `2⁴ · 2⁴ · 2 = 512` shapes, carrying at most 5 real parameters. Against
`invX4` at 11 nodes (`invX4_size`), settling `s(1/x)` means eliminating those 512 families or
exhibiting one.

**Not settled here.** This module proves the reduction, not the answer. A refutation must be
*semantic* — 9 nodes do permit depth 4, so no counting argument can close it — and the arm's own
history says numerical non-existence is navigation, not evidence: an earlier grid search missed a
witness that lived on a transcendental locus.
-/

namespace MachLib

/-- A tree with no `eml` node. -/
def EMLTree.isLeaf : EMLTree → Prop
  | EMLTree.const _ => True
  | EMLTree.var => True
  | EMLTree.eml _ _ => False

/-- Every `eml` node has a leaf child, and the non-leaf side is itself a path. So the tree is one
chain of `eml`s with a leaf hanging off each level. -/
def EMLTree.isPath : EMLTree → Prop
  | EMLTree.const _ => True
  | EMLTree.var => True
  | EMLTree.eml a b => (a.isLeaf ∧ b.isPath) ∨ (b.isLeaf ∧ a.isPath)

theorem size_one_isLeaf : ∀ t : EMLTree, t.size = 1 → t.isLeaf := by
  intro t h
  cases t with
  | const c => exact True.intro
  | var => exact True.intro
  | eml a b =>
    exfalso
    have ha := two_mul_depth_succ_le_size a
    have hb := two_mul_depth_succ_le_size b
    have : (EMLTree.eml a b).size = 1 + a.size + b.size := rfl
    omega

/-- **A tree of minimal size for its depth is a path.** The bound `2·depth + 1 ≤ size` is met with
equality exactly when nothing is spent off the critical chain: at each `eml`, the deeper child is
itself minimal and the other child is a single leaf. -/
theorem minimal_size_isPath : ∀ t : EMLTree, t.size = 2 * t.depth + 1 → t.isPath := by
  intro t
  induction t with
  | const c => intro _; exact True.intro
  | var => intro _; exact True.intro
  | eml a b iha ihb =>
    intro h
    have hsz : (EMLTree.eml a b).size = 1 + a.size + b.size := rfl
    have hdp : (EMLTree.eml a b).depth = 1 + max a.depth b.depth := rfl
    have ha := two_mul_depth_succ_le_size a
    have hb := two_mul_depth_succ_le_size b
    rw [hsz, hdp] at h
    rcases Nat.le_total b.depth a.depth with hle | hle
    · -- `a` is the deeper side: it must be minimal, and `b` must be a bare leaf.
      rw [Nat.max_eq_left hle] at h
      have hbsize : b.size = 1 := by omega
      have hamin : a.size = 2 * a.depth + 1 := by omega
      exact Or.inr ⟨size_one_isLeaf b hbsize, iha hamin⟩
    · rw [Nat.max_eq_right hle] at h
      have hasize : a.size = 1 := by omega
      have hbmin : b.size = 2 * b.depth + 1 := by omega
      exact Or.inl ⟨size_one_isLeaf a hasize, ihb hbmin⟩

/-- **A 9-node tree computing `1/x` is a depth-4 path.** `d(1/x) = 4` forces `depth ≥ 4`, and
`2·depth + 1 ≤ 9` forces `depth ≤ 4`; equality then forces the shape. -/
theorem inv_x_size_nine_isPath (t : EMLTree) (hs : t.size = 9)
    (h : ∀ x : Real, 0 < x → t.eval x = 1 / x) :
    t.depth = 4 ∧ t.isPath := by
  have hbound := two_mul_depth_succ_le_size t
  have hno : ¬ (t.depth ≤ 3) := fun h3 => inv_x_not_in_eml_depth_le_3 t h3 h
  have hd : t.depth = 4 := by omega
  refine ⟨hd, minimal_size_isPath t ?_⟩
  omega

/-- The upper bound, for contrast: `invX4` computes `1/x` at 11 nodes, so `s(1/x) ∈ {9, 11}` and the
question is exactly whether the path family above contains a solution. -/
theorem inv_x_nine_or_eleven_shape :
    invX4.size = 11 ∧ (∀ x : Real, 0 < x → invX4.eval x = 1 / x)
    ∧ ∀ t : EMLTree, t.size = 9 → (∀ x : Real, 0 < x → t.eval x = 1 / x) → t.isPath :=
  ⟨invX4_size, invX4_eval, fun t hs h => (inv_x_size_nine_isPath t hs h).2⟩

/-- The witness is **not** a path — it spends 11 nodes precisely by branching. Concrete evidence
that the 9-node family is a genuinely different shape from the one known to work, rather than a
tightening of it. -/
theorem invX4_not_isPath : ¬ invX4.isPath := by
  intro h
  rcases h with ⟨hl, _⟩ | ⟨hl, _⟩
  · exact hl
  · exact hl

/-- **Only two splits are possible at 9 nodes.** `depth = 4` forces one child to have depth 3, hence
size `≥ 7`; the 8 nodes below the root then leave the sibling exactly 1. So a 9-node solution is
either `eml (leaf) R` with `R` a depth-3 path of size 7, or `eml L (leaf)` with `L` one. The
intermediate splits `(3,5)` and `(5,3)` are impossible — neither child could then reach depth 3. -/
theorem inv_x_size_nine_split (t : EMLTree) (hs : t.size = 9)
    (h : ∀ x : Real, 0 < x → t.eval x = 1 / x) :
    ∃ L R : EMLTree, t = EMLTree.eml L R ∧
      ((L.size = 1 ∧ R.size = 7 ∧ R.depth = 3) ∨ (L.size = 7 ∧ L.depth = 3 ∧ R.size = 1)) := by
  have hd := (inv_x_size_nine_isPath t hs h).1
  cases t with
  | const c => exact absurd hd (by simp only [EMLTree.depth]; omega)
  | var => exact absurd hd (by simp only [EMLTree.depth]; omega)
  | eml L R =>
    refine ⟨L, R, rfl, ?_⟩
    have hsz : (EMLTree.eml L R).size = 1 + L.size + R.size := rfl
    have hdp : (EMLTree.eml L R).depth = 1 + max L.depth R.depth := rfl
    have hL := two_mul_depth_succ_le_size L
    have hR := two_mul_depth_succ_le_size R
    rw [hsz] at hs
    rw [hdp] at hd
    rcases Nat.le_total R.depth L.depth with hle | hle
    · rw [Nat.max_eq_left hle] at hd
      exact Or.inr ⟨by omega, by omega, by omega⟩
    · rw [Nat.max_eq_right hle] at hd
      exact Or.inl ⟨by omega, by omega, by omega⟩

/-! ## ▸ How fast can a shallow tree fall at `0⁺`?

The lemmas below are the growth companion to `rung2_positive_floor`. Rung 2 bounds a *positive*
depth-≤2 tree **below** by `C·x²`; these bound an **arbitrary** depth-≤2 tree below by `F + log x` —
no positivity needed, and about the value rather than its log.

The payoff is `shifted_inv_not_in_eml_depth_le_2`: **`K − 1/x` is out of reach at depth 2, for every
`K`** — which kills a named sub-case of the 9-node question (see the closing note).
-/

open Real

/-- A leaf is bounded above on `(0,1]`. -/
theorem leaf_eval_bounded (a : EMLTree) (ha : a.depth = 0) :
    ∃ P : Real, ∀ x : Real, 0 < x → x ≤ 1 → a.eval x ≤ P := by
  cases a with
  | const p => exact ⟨p, fun _ _ _ => le_refl p⟩
  | var => exact ⟨1, fun _ _ h1 => h1⟩
  | eml _ _ => exact absurd ha (by simp only [EMLTree.depth]; omega)

/-- Adding a non-negative amount to the right of a `≤`. -/
private theorem le_add_nonneg {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have u := add_le_add_wit (le_refl a) hb
  have l : a + 0 = a := by mach_mpoly [a]
  rw [l] at u; exact u

/-- `−log` of a leaf grows at most like `−log x` on `(0,1]`, with a **non-negative** constant. That
non-negativity is used downstream, so it is part of the statement. -/
theorem leaf_neg_log_bounded (b : EMLTree) (hb : b.depth = 0) :
    ∃ Q : Real, 0 ≤ Q ∧ ∀ x : Real, 0 < x → x ≤ 1 → -log (b.eval x) ≤ Q - log x := by
  cases b with
  | const q =>
    refine ⟨exp (-log q), le_of_lt (exp_pos _), fun x hx h1 => ?_⟩
    have hb : (EMLTree.const q).eval x = q := rfl
    rw [hb]
    have hself : -log q ≤ exp (-log q) := le_of_lt (exp_grows_strictly_thm _)
    have hlx : (0 : Real) ≤ -log x := by
      have := log_nonpos_of_le_one hx h1
      have u := neg_le_neg_wit this
      have l : -(0 : Real) = 0 := by mach_ring
      rw [l] at u; exact u
    have hstep : exp (-log q) ≤ exp (-log q) - log x := by
      have u := le_add_nonneg (a := exp (-log q)) hlx
      have r : exp (-log q) + -log x = exp (-log q) - log x := by
        mach_mpoly [exp (-log q), log x]
      rw [r] at u; exact u
    exact le_trans hself hstep
  | var =>
    refine ⟨0, le_refl 0, fun x _ _ => ?_⟩
    have hb : (EMLTree.var).eval x = x := rfl
    rw [hb]
    have e : (0 : Real) - log x = -log x := by mach_mpoly [log x]
    rw [e]; exact le_refl _
  | eml _ _ => exact absurd hb (by simp only [EMLTree.depth]; omega)

/-- **A depth-≤1 tree grows at most logarithmically at `0⁺`.** The upper companion to
`depth_le_one_right_tetrachotomy`, which supplies lower bounds. `1 ≤ E` is part of the statement so
that `E - log x ≥ 1` on `(0,1]` and `log_le_sub_one_of_one_le` applies one level up. -/
theorem depth_le_one_upper_log_bound (B : EMLTree) (hB : B.depth ≤ 1) :
    ∃ E : Real, 1 ≤ E ∧ ∀ x : Real, 0 < x → x ≤ 1 → B.eval x ≤ E - log x := by
  have key : ∀ (C : Real), 1 ≤ C → ∀ x : Real, 0 < x → x ≤ 1 → C ≤ C - log x := by
    intro C _ x hx h1
    have hlx : (0 : Real) ≤ -log x := by
      have := log_nonpos_of_le_one hx h1
      have u := neg_le_neg_wit this
      have l : -(0 : Real) = 0 := by mach_ring
      rw [l] at u; exact u
    have u := le_add_nonneg (a := C) hlx
    have r : C + -log x = C - log x := by mach_mpoly [C, log x]
    rw [r] at u; exact u
  cases B with
  | const q =>
    refine ⟨1 + exp q, le_add_nonneg (le_of_lt (exp_pos q)), fun x hx h1 => ?_⟩
    have hb : (EMLTree.const q).eval x = q := rfl
    rw [hb]
    have hself : q ≤ exp q := le_of_lt (exp_grows_strictly_thm q)
    have hpad : exp q ≤ 1 + exp q := by
      have v := le_add_nonneg (a := exp q) (le_of_lt one_pos)
      have w : exp q + 1 = 1 + exp q := by mach_mpoly [exp q]
      rw [w] at v; exact v
    exact le_trans (le_trans hself hpad)
      (key (1 + exp q) (le_add_nonneg (le_of_lt (exp_pos q))) x hx h1)
  | var => exact ⟨1, le_refl 1, fun x hx h1 => le_trans h1 (key 1 (le_refl 1) x hx h1)⟩
  | eml a b =>
    have ha0 : a.depth = 0 := by
      have := Nat.le_max_left a.depth b.depth
      simp only [EMLTree.depth] at hB; omega
    have hb0 : b.depth = 0 := by
      have := Nat.le_max_right a.depth b.depth
      simp only [EMLTree.depth] at hB; omega
    obtain ⟨P, hP⟩ := leaf_eval_bounded a ha0
    obtain ⟨Q, hQ0, hQ⟩ := leaf_neg_log_bounded b hb0
    refine ⟨1 + exp P + Q, ?_, fun x hx h1 => ?_⟩
    · have s1 : (1 : Real) ≤ 1 + exp P := le_add_nonneg (le_of_lt (exp_pos P))
      exact le_trans s1 (le_add_nonneg hQ0)
    · have hev : (EMLTree.eml a b).eval x = exp (a.eval x) - log (b.eval x) := rfl
      rw [hev]
      have h1' : exp (a.eval x) ≤ exp P := exp_monotone (hP x hx h1)
      have h2' : -log (b.eval x) ≤ Q - log x := hQ x hx h1
      have u := add_le_add_wit h1' h2'
      have l : exp (a.eval x) + -log (b.eval x) = exp (a.eval x) - log (b.eval x) := by
        mach_mpoly [exp (a.eval x), log (b.eval x)]
      have r : exp P + (Q - log x) = exp P + Q - log x := by mach_mpoly [exp P, Q, log x]
      rw [l, r] at u
      have hpad : exp P + Q - log x ≤ 1 + exp P + Q - log x := by
        have v := le_add_nonneg (a := exp P + Q - log x) (le_of_lt one_pos)
        have w : exp P + Q - log x + 1 = 1 + exp P + Q - log x := by
          mach_mpoly [exp P, Q, log x]
        rw [w] at v; exact v
      exact le_trans u hpad

/-- `1/(1/y) = y` for `y > 0`. -/
private theorem one_div_one_div_pos {y : Real} (hy : 0 < y) : 1 / (1 / y) = y := by
  have hu : (0 : Real) < 1 / y := one_div_pos_of_pos hy
  have h1 : (1 / y) * (1 / (1 / y)) = 1 := mul_inv (1 / y) (ne_of_gt hu)
  have h2 : (1 / y) * y = 1 := by
    have hv := mul_inv y (ne_of_gt hy)
    rw [mul_comm] at hv; exact hv
  exact mul_left_cancel (ne_of_gt hu) (h1.trans h2.symm)

/-- **A depth-≤2 tree falls at most logarithmically at `0⁺`.** No positivity hypothesis: `exp ≥ 0`
caps the first term from below and `depth_le_one_upper_log_bound` caps the second, so nothing at
depth 2 can carry a pole. Companion to `rung2_positive_floor`, which needs positivity and bounds
the value below by `C·x²`. -/
theorem depth_le_two_log_decay_floor (t : EMLTree) (ht : t.depth ≤ 2) :
    ∃ F : Real, ∀ x : Real, 0 < x → x ≤ 1 → F + log x ≤ t.eval x := by
  cases t with
  | const q =>
    refine ⟨q, fun x hx h1 => ?_⟩
    have hb : (EMLTree.const q).eval x = q := rfl
    rw [hb]
    have hlx : log x ≤ 0 := log_nonpos_of_le_one hx h1
    have u := add_le_add_wit (le_refl q) hlx
    have l : q + 0 = q := by mach_mpoly [q]
    rw [l] at u; exact u
  | var =>
    refine ⟨0, fun x hx h1 => ?_⟩
    have hb : (EMLTree.var).eval x = x := rfl
    rw [hb]
    have hlx : log x ≤ 0 := log_nonpos_of_le_one hx h1
    have e : (0 : Real) + log x = log x := by mach_mpoly [log x]
    rw [e]
    exact le_trans hlx (le_of_lt hx)
  | eml A B =>
    have hB1 : B.depth ≤ 1 := by
      have := Nat.le_max_right A.depth B.depth
      simp only [EMLTree.depth] at ht; omega
    obtain ⟨E, hE1, hE⟩ := depth_le_one_upper_log_bound B hB1
    refine ⟨1 - E, fun x hx h1 => ?_⟩
    have hev : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
    have hlx : (0 : Real) ≤ -log x := by
      have hle := log_nonpos_of_le_one hx h1
      have u := neg_le_neg_wit hle
      have l : -(0 : Real) = 0 := by mach_ring
      rw [l] at u; exact u
    -- `E - log x ≥ 1`, so `log` of the cap is bounded by the cap minus one.
    have hcap1 : (1 : Real) ≤ E - log x := by
      have u := le_add_nonneg (a := E) hlx
      have r : E + -log x = E - log x := by mach_mpoly [E, log x]
      rw [r] at u; exact le_trans hE1 u
    have hkey : -log (B.eval x) ≥ 1 - E + log x := by
      rcases lt_total (B.eval x) 0 with hneg | heq | hpos
      · rw [log_nonpos (le_of_lt hneg)]
        have e : -(0 : Real) = 0 := by mach_ring
        rw [e]
        have hlx' : log x ≤ 0 := log_nonpos_of_le_one hx h1
        have hEle : (1 : Real) - E ≤ 0 := by
          have u := add_le_add_wit (le_refl (1 : Real)) (neg_le_neg_wit hE1)
          have l : (1 : Real) + -E = 1 - E := by mach_mpoly [E]
          have r : (1 : Real) + -(1 : Real) = 0 := by mach_ring
          rw [l, r] at u; exact u
        have u := add_le_add_wit hEle hlx'
        have l : (0 : Real) + 0 = 0 := by mach_ring
        rw [l] at u; exact u
      · rw [heq, log_zero_totalised]
        have e : -(0 : Real) = 0 := by mach_ring
        rw [e]
        have hlx' : log x ≤ 0 := log_nonpos_of_le_one hx h1
        have hEle : (1 : Real) - E ≤ 0 := by
          have u := add_le_add_wit (le_refl (1 : Real)) (neg_le_neg_wit hE1)
          have l : (1 : Real) + -E = 1 - E := by mach_mpoly [E]
          have r : (1 : Real) + -(1 : Real) = 0 := by mach_ring
          rw [l, r] at u; exact u
        have u := add_le_add_wit hEle hlx'
        have l : (0 : Real) + 0 = 0 := by mach_ring
        rw [l] at u; exact u
      · have hmono : log (B.eval x) ≤ log (E - log x) := log_le_log hpos (hE x hx h1)
        have hsub : log (E - log x) ≤ E - log x - 1 := log_le_sub_one_of_one_le hcap1
        have hchain : log (B.eval x) ≤ E - log x - 1 := le_trans hmono hsub
        have u := neg_le_neg_wit hchain
        have r : -(E - log x - 1) = 1 - E + log x := by mach_mpoly [E, log x]
        rw [r] at u; exact u
    rw [hev]
    have hexp : (0 : Real) ≤ exp (A.eval x) := le_of_lt (exp_pos _)
    have u := add_le_add_wit hexp hkey
    have l : (0 : Real) + (1 - E + log x) = 1 - E + log x := by mach_mpoly [E, log x]
    have r : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
      mach_mpoly [exp (A.eval x), log (B.eval x)]
    rw [l, r] at u; exact u

/-- **`K − 1/x` is out of reach at depth 2, for every `K`.** The pole is the obstruction: a depth-≤2
tree falls at most logarithmically at `0⁺`, and `−1/x` falls faster than any logarithm. -/
theorem shifted_inv_not_in_eml_depth_le_2 (K : Real) (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = K - 1 / x) : False := by
  obtain ⟨F, hF⟩ := depth_le_two_log_decay_floor t ht
  obtain ⟨s, hs1, hs⟩ := exp_beats_linear (α := 1) (β := K - F) (le_of_lt one_pos)
  have hes : (0 : Real) < exp s := exp_pos s
  have hx : (0 : Real) < 1 / exp s := one_div_pos_of_pos hes
  have hx1 : 1 / exp s ≤ 1 := by
    have hneg : -s ≤ 0 := by
      have u := neg_le_neg_wit (le_trans (le_of_lt zero_lt_one_ax) hs1)
      have l : -(0 : Real) = 0 := by mach_ring
      rw [l] at u; exact u
    have hm := exp_monotone hneg
    rw [exp_zero, exp_neg_inv] at hm
    exact hm
  have hinv : 1 / (1 / exp s) = exp s := one_div_one_div_pos hes
  have hlog : log (1 / exp s) = -s := by
    rw [← exp_neg_inv, log_exp]
  have hfl := hF (1 / exp s) hx hx1
  rw [h (1 / exp s) hx, hinv, hlog] at hfl
  -- `F + -s ≤ K - exp s` against `s + (K - F) < exp s`
  have l1 : (1 : Real) * s + (K - F) = s + (K - F) := by mach_mpoly [s, K, F]
  rw [l1] at hs
  have hcontra : exp s ≤ K - F + s := by
    have u := add_le_add_wit hfl (le_refl (exp s - F + s))
    have lhs : F + -s + (exp s - F + s) = exp s := by mach_mpoly [F, s, exp s]
    have rhs : K - exp s + (exp s - F + s) = K - F + s := by mach_mpoly [K, F, s, exp s]
    rw [lhs, rhs] at u; exact u
  have hbad : s + (K - F) = K - F + s := by mach_mpoly [s, K, F]
  rw [hbad] at hs
  exact lt_irrefl_ax _ (lt_of_lt_of_le hs hcontra)

/-! ## ▸ What this closes in the 9-node question, and what it does not

`inv_x_size_nine_split` leaves exactly two top-level shapes. Write `t = eml L R` with `t.eval = 1/x`
on `(0,∞)`.

**Split A — `t = eml (leaf) R`, `R` a depth-3 path of size 7.** Then
`exp(ℓ x) − log(R x) = 1/x`, and `R x > 0` throughout (otherwise the totalised `log` forces
`exp(ℓ x) = 1/x` identically, impossible for `ℓ` a leaf). So `R x = exp(exp(ℓ x) − 1/x)`.

Take `ℓ = const c`, so `R x = exp(K − 1/x)` with `K = exp c > 0`, and take the depth-3 path to
branch left: `R = eml R₂ (leaf₂)` with `R₂` of depth 2. Then
`exp(R₂ x) − log(leaf₂) = exp(K − 1/x)`.

*If `log(leaf₂) = 0`* — that is, `leaf₂ = const q` with `q ≤ 0`, or `q = 1` — this says
`R₂ x = K − 1/x` with `R₂` of depth 2. **`shifted_inv_not_in_eml_depth_le_2` closes it.**

**What is NOT closed.** Everything else: `log(leaf₂) ≠ 0`, `leaf₂ = var`, the right-branching
depth-3 paths, `ℓ = var`, and the whole of split B (`t = eml L (leaf)`, where `exp(L x) = 1/x + κ`
puts the pole inside an `exp` rather than a `log`). Those need their own arguments, and the
`leaf₂ = var` one looks easy — `exp(R₂ x) = exp(K − 1/x) + log x` has a negative right-hand side
near `0` and a positive left-hand side — but *looks easy* is not a proof and it is not claimed here.

The shape of the remaining work is now explicit rather than open-ended, which is the point of the
reduction. What is **not** available is a counting argument: 9 nodes genuinely permit depth 4, so any
refutation must be semantic, one branch at a time.
-/

end MachLib