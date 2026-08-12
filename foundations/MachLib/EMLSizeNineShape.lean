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

/-- **No depth-≤2 tree can be capped by `C − 1/x` near `0`.** The general pole obstruction: depth 2
falls at most logarithmically at `0⁺`, and `−1/x` falls faster than any logarithm. Stated as an
*upper bound* rather than an equation so it applies wherever a pole appears, however it is dressed. -/
theorem no_pole_at_depth_le_2 (C : Real) (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → x ≤ 1 → t.eval x ≤ C - 1 / x) : False := by
  obtain ⟨F, hF⟩ := depth_le_two_log_decay_floor t ht
  obtain ⟨s, hs1, hs⟩ := exp_beats_linear (α := 1) (β := C - F) (le_of_lt one_pos)
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
  have hlog : log (1 / exp s) = -s := by rw [← exp_neg_inv, log_exp]
  have hfl := hF (1 / exp s) hx hx1
  have hup := h (1 / exp s) hx hx1
  rw [hinv] at hup
  rw [hlog] at hfl
  have hchain : F + -s ≤ C - exp s := le_trans hfl hup
  have l1 : (1 : Real) * s + (C - F) = s + (C - F) := by mach_mpoly [s, C, F]
  rw [l1] at hs
  have hcontra : exp s ≤ C - F + s := by
    have u := add_le_add_wit hchain (le_refl (exp s - F + s))
    have lhs : F + -s + (exp s - F + s) = exp s := by mach_mpoly [F, s, exp s]
    have rhs : C - exp s + (exp s - F + s) = C - F + s := by mach_mpoly [C, F, s, exp s]
    rw [lhs, rhs] at u; exact u
  have hbad : s + (C - F) = C - F + s := by mach_mpoly [s, C, F]
  rw [hbad] at hs
  exact lt_irrefl_ax _ (lt_of_lt_of_le hs hcontra)

/-- **`K − 1/x` is out of reach at depth 2, for every `K`** — the equational instance. -/
theorem shifted_inv_not_in_eml_depth_le_2 (K : Real) (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = K - 1 / x) : False :=
  no_pole_at_depth_le_2 K t ht (fun x hx _ => le_of_eq (h x hx))

/-! ## ▸ What this closes in the 9-node question, and what it does not

`inv_x_size_nine_split` leaves exactly two top-level shapes. Write `t = eml L R` with
`t.eval = 1/x` on `(0,∞)`.

**Split A — `t = eml (leaf) R`, `R` a depth-3 path of size 7.** Then
`exp(ℓ x) − log(R x) = 1/x`, and `R x > 0` throughout (otherwise the totalised `log` forces
`exp(ℓ x) = 1/x` identically, impossible for a leaf `ℓ`). So `R x = exp(exp(ℓ x) − 1/x)`.

Take `ℓ = const c`, so `R x = exp(K − 1/x)` with `K = exp c > 0`, and let the depth-3 path branch
left: `R = eml R₂ (leaf₂)`, `R₂` of depth 2. Then `exp(R₂ x) − log(leaf₂) = exp(K − 1/x)`, and the
four possibilities for `log(leaf₂)` now stand as:

| `leaf₂` | `log(leaf₂)` | status |
|---|---|---|
| `var` | `log x` | **dead** — `split_a_leaf_var_absurd`, *any* depth |
| `const q`, `0 < q < 1` | `< 0` | **dead** — `split_a_leaf_const_neg_absurd`, *any* depth |
| `const q`, `q = 1` or `q ≤ 0` | `= 0` | **dead** — `shifted_inv_not_in_eml_depth_le_2`, needs depth 2 |
| `const q`, `q > 1` | `> 0` | **open** |

The pattern is worth recording. Three of the four die, and only the third needed real machinery:
the other two collapse on **sign**, because their right-hand sides go negative near `0` while a
left-hand `exp` cannot. The `log(leaf₂) = 0` case is exactly the one whose right-hand side stays
*positive*, so no sign clash exists and the pole must instead be chased through the growth bound —
which is why `depth_le_two_log_decay_floor` had to be built. **A case needs machinery precisely when
it is sign-consistent.**

**The same table holds for `ℓ = var`.** There the top-level equation gives
`R x = exp(exp x − 1/x)`, and branching the depth-3 path left reproduces the pattern exactly:
`leaf₂ = var` dies by sign (`var_family_leaf_var_absurd`), `log(leaf₂) = 0` dies by the pole bound
(`var_family_leaf_const_zero_absurd`), `log(leaf₂) < 0` dies by sign via `exp_add_absurd`, and
`log(leaf₂) > 0` is open. That the triage rule *predicted* which cell would cost anything, in a
family it was not derived from, is the reason to trust it for the rest.

**Split B — `t = eml L (leaf)`** — is a different problem: `exp(L x) = 1/x + κ` puts the pole under
an `exp` rather than a `log`, and none of the split-A arguments transfer. The triage rule still finds
its free cell: `κ < 0` dies by sign (`split_b_leaf_const_neg_absurd`), because `exp` is positive and
`1/x + κ` is not, once `1/x` drops below `−κ`.

**What is NOT closed.** The `> 0` cell in both split-A families; the right-branching depth-3 paths
(`R = eml (leaf₂) R₂`); and split B's `κ = 0` and `κ > 0` cells plus its `leaf = var` case. Split B's
`κ = 0` cell is the sharpest of these: it asks whether a depth-3 tree can compute `−log x` exactly.

**No counting argument can finish this.** 9 nodes genuinely permit depth 4 — that is what
`inv_x_size_nine_isPath` says — so every remaining refutation must be semantic, one branch at a time.
-/
/-! ## ▸ Two more branches, closed by sign alone

Neither needs a hypothesis on the subtree's depth. Worth noticing: the `log(leaf₂) = 0` branch
needed the full depth-2 machinery precisely because *its* right-hand side stays positive, so no sign
clash is available and the pole has to be chased through the growth bound instead.
-/

/-- `y < 1 + exp y`, the step used to manufacture a point past any prescribed threshold. -/
private theorem lt_one_add_exp (y : Real) : y < 1 + exp y := by
  have h1 : y < exp y := exp_grows_strictly_thm y
  have h2 : exp y < 1 + exp y := by
    have u := add_lt_add_left zero_lt_one_ax (exp y)
    have l : exp y + 0 = exp y := by mach_mpoly [exp y]
    have r : exp y + 1 = 1 + exp y := by mach_mpoly [exp y]
    rw [l, r] at u; exact u
  exact lt_trans_ax h1 h2

/-- A pole point: `1/x` exceeds any prescribed `C` somewhere on `(0,∞)`. -/
private theorem pole_point (C : Real) : ∃ x : Real, 0 < x ∧ C < 1 / x := by
  refine ⟨1 / exp (1 + exp C), one_div_pos_of_pos (exp_pos _), ?_⟩
  rw [one_div_one_div_pos (exp_pos _)]
  exact lt_trans_ax (lt_one_add_exp C) (exp_grows_strictly_thm _)

/-- **Split A, `leaf₂ = var`: dead.** `exp(R₂ x) = exp(K − 1/x) + log x` equates a strictly positive
quantity with one that goes negative — near `0` the first summand drops below `1` while `log x` is
below `−1`. Holds for **any** `R₂`, at any depth. -/
theorem split_a_leaf_var_absurd (K : Real) (R₂ : EMLTree)
    (h : ∀ x : Real, 0 < x → exp (R₂.eval x) - log x = exp (K - 1 / x)) : False := by
  have hKe : K < exp (1 + exp K) :=
    lt_trans_ax (lt_one_add_exp K) (exp_grows_strictly_thm _)
  have hxpos : (0 : Real) < 1 / exp (1 + exp K) := one_div_pos_of_pos (exp_pos _)
  have hinv : 1 / (1 / exp (1 + exp K)) = exp (1 + exp K) := one_div_one_div_pos (exp_pos _)
  have hlog : log (1 / exp (1 + exp K)) = -(1 + exp K) := by rw [← exp_neg_inv, log_exp]
  have key := h (1 / exp (1 + exp K)) hxpos
  rw [hinv, hlog] at key
  have hneg : K - exp (1 + exp K) < 0 := by
    have u := add_lt_add_left hKe (-exp (1 + exp K))
    have l : -exp (1 + exp K) + K = K - exp (1 + exp K) := by
      mach_mpoly [K, exp (1 + exp K)]
    have r : -exp (1 + exp K) + exp (1 + exp K) = 0 := by mach_mpoly [exp (1 + exp K)]
    rw [l, r] at u; exact u
  have hlt1 : exp (K - exp (1 + exp K)) < 1 := by
    have hm := exp_lt hneg; rw [exp_zero] at hm; exact hm
  have hone : (1 : Real) < 1 + exp K := by
    have u := add_lt_add_left (exp_pos K) 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have hgrow : (1 : Real) + exp K
      < exp (R₂.eval (1 / exp (1 + exp K))) - -(1 + exp K) := by
    have u := add_lt_add_left (exp_pos (R₂.eval (1 / exp (1 + exp K)))) (1 + exp K)
    have l : (1 : Real) + exp K + 0 = 1 + exp K := by mach_mpoly [exp K]
    have r : (1 : Real) + exp K + exp (R₂.eval (1 / exp (1 + exp K)))
           = exp (R₂.eval (1 / exp (1 + exp K))) - -(1 + exp K) := by
      mach_mpoly [exp K, exp (R₂.eval (1 / exp (1 + exp K)))]
    rw [l, r] at u; exact u
  rw [key] at hgrow
  exact lt_irrefl_ax _ (lt_trans_ax (lt_trans_ax hone hgrow) hlt1)

/-- **Split A, `leaf₂ = const q` with `log q < 0` (that is `0 < q < 1`): dead.** `exp(K − 1/x)` would
have to stay above the fixed positive `μ = −log q`, and it does not: push `1/x` past `K − log μ`.
Again no depth hypothesis. -/
theorem split_a_leaf_const_neg_absurd (K μ : Real) (hμ : 0 < μ) (R₂ : EMLTree)
    (h : ∀ x : Real, 0 < x → exp (R₂.eval x) + μ = exp (K - 1 / x)) : False := by
  obtain ⟨x, hx, hbig⟩ := pole_point (K - log μ)
  have key := h x hx
  have harg : K - 1 / x < log μ := by
    have u := add_lt_add_left hbig (log μ - 1 / x)
    have l : log μ - 1 / x + (K - log μ) = K - 1 / x := by
      mach_mpoly [K, log μ, (1 / x : Real)]
    have r : log μ - 1 / x + 1 / x = log μ := by mach_mpoly [log μ, (1 / x : Real)]
    rw [l, r] at u; exact u
  have hsmall : exp (K - 1 / x) < μ := by
    have hm := exp_lt harg; rw [exp_log hμ] at hm; exact hm
  have hbigger : μ < exp (R₂.eval x) + μ := by
    have u := add_lt_add_left (exp_pos (R₂.eval x)) μ
    have l : μ + 0 = μ := by mach_mpoly [μ]
    have r : μ + exp (R₂.eval x) = exp (R₂.eval x) + μ := by
      mach_mpoly [μ, exp (R₂.eval x)]
    rw [l, r] at u; exact u
  rw [key] at hbigger
  exact lt_irrefl_ax _ (lt_trans_ax hbigger hsmall)

/-! ## ▸ The `ℓ = var` family, same 3-of-4 pattern

With `ℓ = var` the top-level equation is `exp x − log(R x) = 1/x`, so `R x = exp(exp x − 1/x)`.
Branching the depth-3 path left as `R = eml R₂ (leaf₂)` gives the same four cells as before, and the
triage rule earned in the `ℓ = const` family — *check the sign first, buy a growth argument only
where the signs agree* — predicts which one costs anything. It does.

The two reusable primitives below separate the trivial contradiction from the per-branch work of
exhibiting a point. That split is what makes each branch a few lines.
-/

/-- If `exp(R₂ x) − log x` is pinned to `g`, one point where `g x + log x ≤ 0` finishes it. -/
theorem exp_sub_log_absurd (R₂ : EMLTree) (g : Real → Real)
    (hpt : ∃ x : Real, 0 < x ∧ g x + log x ≤ 0)
    (h : ∀ x : Real, 0 < x → exp (R₂.eval x) - log x = g x) : False := by
  obtain ⟨x, hx, hle⟩ := hpt
  have key := h x hx
  have hval : exp (R₂.eval x) = g x + log x := by
    rw [← key]; mach_mpoly [exp (R₂.eval x), log x]
  have hp := exp_pos (R₂.eval x)
  rw [hval] at hp
  exact lt_irrefl_ax _ (lt_of_lt_of_le hp hle)

/-- If `exp(R₂ x) + μ` is pinned to `g`, one point where `g x < μ` finishes it. The `0 < μ` one
expects to need is **not** required — `exp > 0` alone does it. -/
theorem exp_add_absurd (μ : Real) (R₂ : EMLTree) (g : Real → Real)
    (hpt : ∃ x : Real, 0 < x ∧ g x < μ)
    (h : ∀ x : Real, 0 < x → exp (R₂.eval x) + μ = g x) : False := by
  obtain ⟨x, hx, hlt⟩ := hpt
  have key := h x hx
  have hbigger : μ < exp (R₂.eval x) + μ := by
    have u := add_lt_add_left (exp_pos (R₂.eval x)) μ
    have l : μ + 0 = μ := by mach_mpoly [μ]
    have r : μ + exp (R₂.eval x) = exp (R₂.eval x) + μ := by
      mach_mpoly [μ, exp (R₂.eval x)]
    rw [l, r] at u; exact u
  rw [key] at hbigger
  exact lt_irrefl_ax _ (lt_trans_ax hbigger hlt)

/-- The point that serves both `ℓ = var` sign branches: at `x = 1/e`, `exp x − 1/x < 0`. -/
private theorem var_family_point : exp (1 / exp 1) - 1 / (1 / exp 1) < 0 := by
  have he : (0 : Real) < exp 1 := exp_pos 1
  have hx : (0 : Real) < 1 / exp 1 := one_div_pos_of_pos he
  have hinv : 1 / (1 / exp 1) = exp 1 := one_div_one_div_pos he
  rw [hinv]
  have hlt : 1 / exp 1 < 1 := by
    have h1e : (1 : Real) < exp 1 := by
      have u := exp_lt zero_lt_one_ax
      rw [exp_zero] at u; exact u
    have hm := div_lt_one_of_pos_lt he h1e
    exact hm
  have hmono : exp (1 / exp 1) < exp 1 := exp_lt hlt
  have u := add_lt_add_left hmono (-exp 1)
  have l : -exp 1 + exp (1 / exp 1) = exp (1 / exp 1) - exp 1 := by
    mach_mpoly [exp 1, exp (1 / exp 1)]
  have r : -exp 1 + exp 1 = 0 := by mach_mpoly [exp 1]
  rw [l, r] at u; exact u

/-- **`ℓ = var`, `leaf₂ = var`: dead by sign, any depth.** -/
theorem var_family_leaf_var_absurd (R₂ : EMLTree)
    (h : ∀ x : Real, 0 < x → exp (R₂.eval x) - log x = exp (exp x - 1 / x)) : False := by
  refine exp_sub_log_absurd R₂ (fun x => exp (exp x - 1 / x)) ⟨1 / exp 1, ?_, ?_⟩ h
  · exact one_div_pos_of_pos (exp_pos 1)
  · have hlog : log (1 / exp 1) = -1 := by rw [← exp_neg_inv, log_exp]
    have hle1 : exp (exp (1 / exp 1) - 1 / (1 / exp 1)) ≤ 1 := by
      have hm := exp_lt var_family_point
      rw [exp_zero] at hm
      exact le_of_lt hm
    rw [hlog]
    have u := add_le_add_wit hle1 (le_refl (-1 : Real))
    have r : (1 : Real) + -1 = 0 := by mach_ring
    rw [r] at u; exact u

/-- **`ℓ = var`, `leaf₂ = const q` with `log q = 0`: dead by the pole bound.** The remaining
equation is `R₂ x = exp x − 1/x`, capped by `exp 1 − 1/x` on `(0,1]`. -/
theorem var_family_leaf_const_zero_absurd (R₂ : EMLTree) (hd : R₂.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → R₂.eval x = exp x - 1 / x) : False := by
  refine no_pole_at_depth_le_2 (exp 1) R₂ hd (fun x hx h1 => ?_)
  rw [h x hx]
  have hm : exp x ≤ exp 1 := exp_monotone h1
  have u := add_le_add_wit hm (le_refl (-(1 / x) : Real))
  have l : exp x + -(1 / x) = exp x - 1 / x := by mach_mpoly [exp x, (1 / x : Real)]
  have r : exp 1 + -(1 / x) = exp 1 - 1 / x := by mach_mpoly [exp 1, (1 / x : Real)]
  rw [l, r] at u; exact u

/-- **`ℓ = var`, `leaf₂ = const q` with `log q < 0`: dead by sign.** `exp(exp x − 1/x)` would have to
stay above the fixed positive `μ = −log q`; push `1/x` past `exp 1 − log μ` and it does not. -/
theorem var_family_leaf_const_neg_absurd (μ : Real) (hμ : 0 < μ) (R₂ : EMLTree)
    (h : ∀ x : Real, 0 < x → exp (R₂.eval x) + μ = exp (exp x - 1 / x)) : False := by
  have hC : exp 1 - log μ < exp (1 + exp (exp 1 - log μ)) :=
    lt_trans_ax (lt_one_add_exp (exp 1 - log μ)) (exp_grows_strictly_thm _)
  have htpos : (0 : Real) < 1 + exp (exp 1 - log μ) := by
    have u := add_lt_add_left (exp_pos (exp 1 - log μ)) 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact lt_trans_ax zero_lt_one_ax u
  have het : (1 : Real) < exp (1 + exp (exp 1 - log μ)) := by
    have hm := exp_lt htpos; rw [exp_zero] at hm; exact hm
  have hepos : (0 : Real) < exp (1 + exp (exp 1 - log μ)) := exp_pos _
  refine exp_add_absurd μ R₂ (fun x => exp (exp x - 1 / x))
    ⟨1 / exp (1 + exp (exp 1 - log μ)), one_div_pos_of_pos hepos, ?_⟩ h
  have hx1 : 1 / exp (1 + exp (exp 1 - log μ)) ≤ 1 :=
    le_of_lt (div_lt_one_of_pos_lt hepos het)
  have hinv : 1 / (1 / exp (1 + exp (exp 1 - log μ))) = exp (1 + exp (exp 1 - log μ)) :=
    one_div_one_div_pos hepos
  show exp (exp (1 / exp (1 + exp (exp 1 - log μ)))
        - 1 / (1 / exp (1 + exp (exp 1 - log μ)))) < μ
  rw [hinv]
  have hmono : exp (1 / exp (1 + exp (exp 1 - log μ))) ≤ exp 1 := exp_monotone hx1
  -- `exp x - exp t ≤ exp 1 - exp t < exp 1 - (exp 1 - log μ) = log μ`
  have hstep1 : exp (1 / exp (1 + exp (exp 1 - log μ)))
        - exp (1 + exp (exp 1 - log μ)) ≤ exp 1 - exp (1 + exp (exp 1 - log μ)) := by
    have u := add_le_add_wit hmono (le_refl (-exp (1 + exp (exp 1 - log μ))))
    have l : exp (1 / exp (1 + exp (exp 1 - log μ))) + -exp (1 + exp (exp 1 - log μ))
           = exp (1 / exp (1 + exp (exp 1 - log μ))) - exp (1 + exp (exp 1 - log μ)) := by
      mach_mpoly [exp (1 / exp (1 + exp (exp 1 - log μ))), exp (1 + exp (exp 1 - log μ))]
    have r : exp 1 + -exp (1 + exp (exp 1 - log μ))
           = exp 1 - exp (1 + exp (exp 1 - log μ)) := by
      mach_mpoly [exp 1, exp (1 + exp (exp 1 - log μ))]
    rw [l, r] at u; exact u
  have hstep2 : exp 1 - exp (1 + exp (exp 1 - log μ)) < log μ := by
    have u := add_lt_add_left hC (exp 1 - (exp 1 - log μ) - exp (1 + exp (exp 1 - log μ)))
    have l : exp 1 - (exp 1 - log μ) - exp (1 + exp (exp 1 - log μ)) + (exp 1 - log μ)
           = exp 1 - exp (1 + exp (exp 1 - log μ)) := by
      mach_mpoly [exp 1, log μ, exp (1 + exp (exp 1 - log μ))]
    have r : exp 1 - (exp 1 - log μ) - exp (1 + exp (exp 1 - log μ))
             + exp (1 + exp (exp 1 - log μ)) = log μ := by
      mach_mpoly [exp 1, log μ, exp (1 + exp (exp 1 - log μ))]
    rw [l, r] at u; exact u
  have hlt := exp_lt (lt_of_le_of_lt hstep1 hstep2)
  rw [exp_log hμ] at hlt
  exact hlt

/-! ## ▸ Split B: the pole moves inside the `exp`

`t = eml L (leaf)` gives `exp(L x) − log(leaf) = 1/x`, so `exp(L x) = 1/x + κ` with
`κ = log(leaf)`. None of the split-A arguments transfer — there the pole sat under a `log`, here it
is under an `exp` — but the triage rule still applies, and it finds the free cell straight away:
`exp` is positive, so `κ < 0` dies the moment `1/x` drops below `−κ`.
-/

/-- **Split B, `leaf = const q` with `log q < 0` (that is `0 < q < 1`): dead by sign, any depth.**
`exp(L x) = 1/x − μ` needs the right-hand side positive everywhere, and it is not: take `x` past
`1/μ`. -/
theorem split_b_leaf_const_neg_absurd (μ : Real) (hμ : 0 < μ) (L : EMLTree)
    (h : ∀ x : Real, 0 < x → exp (L.eval x) = 1 / x - μ) : False := by
  have hiμ : (0 : Real) < 1 / μ := one_div_pos_of_pos hμ
  have hx : (0 : Real) < 1 + 1 / μ := by
    have u := add_lt_add_left hiμ 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact lt_trans_ax zero_lt_one_ax u
  -- `x·μ = μ + 1 > 1`
  have hprod : (1 : Real) < (1 + 1 / μ) * μ := by
    have hinv : (1 / μ) * μ = 1 := by
      have hv := mul_inv μ (ne_of_gt hμ)
      rw [mul_comm] at hv; exact hv
    have hexp : (1 + 1 / μ) * μ = μ + (1 / μ) * μ := by mach_mpoly [μ, (1 / μ : Real)]
    rw [hexp, hinv]
    have u := add_lt_add_left hμ 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    have r : (1 : Real) + μ = μ + 1 := by mach_mpoly [μ]
    rw [l, r] at u; exact u
  -- multiply by `1/x > 0` to get `1/x < μ`
  have hix : (0 : Real) < 1 / (1 + 1 / μ) := one_div_pos_of_pos hx
  have hstep := mul_lt_mul_of_pos_right hprod hix
  have hxinv : (1 + 1 / μ) * (1 / (1 + 1 / μ)) = 1 := mul_inv _ (ne_of_gt hx)
  have hleft : (1 : Real) * (1 / (1 + 1 / μ)) = 1 / (1 + 1 / μ) := by
    mach_mpoly [(1 / (1 + 1 / μ) : Real)]
  have hright : (1 + 1 / μ) * μ * (1 / (1 + 1 / μ))
      = μ * ((1 + 1 / μ) * (1 / (1 + 1 / μ))) := by
    mach_mpoly [μ, (1 / μ : Real), (1 / (1 + 1 / μ) : Real)]
  rw [hleft, hright, hxinv] at hstep
  have hμ1 : μ * 1 = μ := by mach_mpoly [μ]
  rw [hμ1] at hstep
  -- so `1/x - μ < 0`, but it equals `exp (L x) > 0`
  have hneg : 1 / (1 + 1 / μ) - μ < 0 := by
    have u := add_lt_add_left hstep (-μ)
    have l : -μ + 1 / (1 + 1 / μ) = 1 / (1 + 1 / μ) - μ := by
      mach_mpoly [μ, (1 / (1 + 1 / μ) : Real)]
    have r : -μ + μ = 0 := by mach_mpoly [μ]
    rw [l, r] at u; exact u
  have hp := exp_pos (L.eval (1 + 1 / μ))
  rw [h (1 + 1 / μ) hx] at hp
  exact lt_irrefl_ax _ (lt_trans_ax hp hneg)

/-! ## ▸ Split B, `κ = 0`: the `−log x` cell reduces to RIGHT-branching only

The sharpest open cell asks whether a depth-3 path computes `−log x`. Its **left**-branching half
turns out to be free, and one of the two cases is a one-liner — worth checking before assuming a
sign-consistent-looking cell is expensive. Writing `L = eml L₂ (leaf)`:

* `leaf = var` gives `exp(L₂ x) − log x = −log x`, i.e. `exp(L₂ x) = 0`. Immediate.
* `leaf = const q` gives `exp(L₂ x) = λ − log x`, which goes negative once `log x > λ`.

So the `−log x` question lives entirely in the **right**-branching paths `L = eml (leaf) L₂`, where
`log(L₂ x) = exp(ℓ x) + log x`. For `ℓ = const p` that is exactly **`L₂ x = M·x` with
`M = exp(exp p) > 1`** — and `mx_mem_EML` builds `M·x` at depth 4. The cell has become a *gap*
question about a named function: **`M·x ∈ EML₄`; is it in `EML₂`?**
-/

/-- **`L = eml L₂ var` cannot give `−log x`:** it forces `exp(L₂ x) = 0`. -/
theorem neg_log_left_leaf_var_absurd (L₂ : EMLTree)
    (h : ∀ x : Real, 0 < x → exp (L₂.eval x) - log x = -log x) : False := by
  have key := h 1 zero_lt_one_ax
  have hz : exp (L₂.eval 1) = 0 := by
    have e : exp (L₂.eval 1) = (exp (L₂.eval 1) - log 1) + log 1 := by
      mach_mpoly [exp (L₂.eval 1), log (1 : Real)]
    rw [e, key]; mach_mpoly [log (1 : Real)]
  exact lt_irrefl_ax 0 (hz ▸ exp_pos (L₂.eval 1))

/-- **`L = eml L₂ (const q)` cannot give `−log x`:** `exp(L₂ x) = λ − log x` goes negative past
`x = exp(λ+1)`. Holds for every `λ`, so the totalised `log q = 0` case is included. -/
theorem neg_log_left_leaf_const_absurd (lam : Real) (L₂ : EMLTree)
    (h : ∀ x : Real, 0 < x → exp (L₂.eval x) - lam = -log x) : False := by
  have hxpos : (0 : Real) < exp (lam + 1) := exp_pos _
  have key := h (exp (lam + 1)) hxpos
  have hlog : log (exp (lam + 1)) = lam + 1 := log_exp _
  have hval : exp (L₂.eval (exp (lam + 1))) = -(1 : Real) := by
    have e : exp (L₂.eval (exp (lam + 1)))
        = (exp (L₂.eval (exp (lam + 1))) - lam) + lam := by
      mach_mpoly [exp (L₂.eval (exp (lam + 1))), lam]
    rw [e, key, hlog]; mach_mpoly [lam]
  have hp := exp_pos (L₂.eval (exp (lam + 1)))
  rw [hval] at hp
  have hneg : -(1 : Real) < 0 := by
    have u := add_lt_add_left zero_lt_one_ax (-1 : Real)
    have l : -(1 : Real) + 0 = -1 := by mach_ring
    have r : -(1 : Real) + 1 = 0 := by mach_ring
    rw [l, r] at u; exact u
  exact lt_irrefl_ax _ (lt_trans_ax hp hneg)

/-- **The `−log x` cell is right-branching or nothing.** A depth-3 path computing `−log x` must have
its *leaf* on the left, so the whole cell reduces to `log(L₂ x) = exp(ℓ x) + log x`. -/
theorem neg_log_path_is_right_branching (L : EMLTree) (hp : L.isPath)
    (h : ∀ x : Real, 0 < x → L.eval x = -log x) :
    ∃ P Q : EMLTree, L = EMLTree.eml P Q ∧ P.isLeaf := by
  cases L with
  | const c =>
    exfalso
    have h1 := h 1 zero_lt_one_ax
    have he := h (exp 1) (exp_pos 1)
    have e1 : (EMLTree.const c).eval 1 = c := rfl
    have e2 : (EMLTree.const c).eval (exp 1) = c := rfl
    rw [e1] at h1; rw [e2] at he
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hle : log (exp 1) = 1 := log_exp 1
    rw [hl1] at h1; rw [hle] at he
    have h1' : c = 0 := by rw [h1]; mach_ring
    have hbad : (0 : Real) = -1 := by rw [← h1']; exact he
    have hneg : -(1 : Real) < 0 := by
      have u := add_lt_add_left zero_lt_one_ax (-1 : Real)
      have l : -(1 : Real) + 0 = -1 := by mach_ring
      have r : -(1 : Real) + 1 = 0 := by mach_ring
      rw [l, r] at u; exact u
    exact lt_irrefl_ax _ (hbad ▸ hneg)
  | var =>
    exfalso
    have h1 := h 1 zero_lt_one_ax
    have e1 : (EMLTree.var).eval 1 = 1 := rfl
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    rw [e1, hl1] at h1
    have hbad : (1 : Real) = 0 := by rw [h1]; mach_ring
    exact lt_irrefl_ax 0 (hbad ▸ zero_lt_one_ax)
  | eml P Q =>
    refine ⟨P, Q, rfl, ?_⟩
    rcases hp with ⟨hPl, _⟩ | ⟨hQl, _⟩
    · exact hPl
    · exfalso
      have hev : ∀ x : Real, 0 < x →
          exp (P.eval x) - log (Q.eval x) = -log x := fun x hx => h x hx
      cases Q with
      | const q =>
        exact neg_log_left_leaf_const_absurd (log q) P
          (fun x hx => hev x hx)
      | var => exact neg_log_left_leaf_var_absurd P (fun x hx => hev x hx)
      | eml _ _ => exact hQl

/-! ## ▸ Depth-≤1 trees have exactly FIVE closed forms

`depth_le_one_trichotomy` and `depth_le_one_right_tetrachotomy` give *inequalities*. For the
remaining cells that is not enough: `M·x ∈ EML₂?` needs to know what a depth-≤1 subtree **is**, not
what it is bounded by. There are only five forms, and enumerating them turns each remaining branch
into a finite check.

Note what is absent from the list: **`+log x` does not occur.** Only `c − log x` does. That single
observation is what kills the `M·x` cell in the shapes where the `log` side is exactly linear.
-/

/-- **Complete classification of depth-≤1 trees.** Constant, `x`, `c − log x` with `c > 0`,
`exp x − d`, or `exp x − log x`. Nothing else. -/
theorem depth_le_one_classification (A : EMLTree) (hA : A.depth ≤ 1) :
    (∃ α : Real, ∀ x : Real, 0 < x → A.eval x = α)
    ∨ (∀ x : Real, 0 < x → A.eval x = x)
    ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → A.eval x = c - log x)
    ∨ (∃ d : Real, ∀ x : Real, 0 < x → A.eval x = exp x - d)
    ∨ (∀ x : Real, 0 < x → A.eval x = exp x - log x) := by
  cases A with
  | const p => exact Or.inl ⟨p, fun _ _ => rfl⟩
  | var => exact Or.inr (Or.inl (fun _ _ => rfl))
  | eml a b =>
    have ha0 : a.depth = 0 := by
      have := Nat.le_max_left a.depth b.depth
      simp only [EMLTree.depth] at hA; omega
    have hb0 : b.depth = 0 := by
      have := Nat.le_max_right a.depth b.depth
      simp only [EMLTree.depth] at hA; omega
    cases a with
    | eml _ _ => exact absurd ha0 (by simp only [EMLTree.depth]; omega)
    | const p =>
      cases b with
      | eml _ _ => exact absurd hb0 (by simp only [EMLTree.depth]; omega)
      | const q => exact Or.inl ⟨exp p - log q, fun _ _ => rfl⟩
      | var =>
        refine Or.inr (Or.inr (Or.inl ⟨exp p, exp_pos p, fun x _ => rfl⟩))
    | var =>
      cases b with
      | eml _ _ => exact absurd hb0 (by simp only [EMLTree.depth]; omega)
      | const q => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨log q, fun x _ => rfl⟩)))
      | var => exact Or.inr (Or.inr (Or.inr (Or.inr (fun x _ => rfl))))

/-! ### The `M·x` cell: what the classification buys immediately

`log(L₂ x) = exp(ℓ x) + log x` with `ℓ = const p` means `L₂ x = M·x`, `M = exp(exp p) > 1`, and
`L₂ = eml A B` with `A`, `B` of depth ≤ 1. The classification makes one shape fall out at once.

The **`B = exp x − d` with `d = 0`** shape is the only one whose `log` is *exactly* linear:
`log(exp x) = x`. There the equation becomes `exp(A x) = (M+1)·x`, so `A x = log(M+1) + log x` — a
`+log x`, which the classification says depth ≤ 1 does not have. `mx_B_is_exp_absurd` below.

The other shapes need growth arguments at `∞`, which this module does not yet carry: every bound
here is at `0⁺`. That asymmetry is the honest statement of what remains.
-/

/-! `depth_le_one_lower_bound` — every depth-≤1 tree is bounded below on `(0,1]` — **already exists**
in `EMLDepth2InvX`, with the same insight recorded in its docstring: the `−log x` that makes the
upper bound grow only helps a lower bound. Reused rather than rebuilt. (It was rebuilt once here
before grepping; the duplicate is gone.) -/

/-- **`k + log x` is unreachable at depth ≤ 1, for every `k`.** The memorable form of the bound
above: depth 1 offers `c − log x` and never `+log x`. -/
theorem log_plus_const_not_depth_le_1 (k : Real) (A : EMLTree) (hA : A.depth ≤ 1)
    (h : ∀ x : Real, 0 < x → A.eval x = k + log x) : False := by
  obtain ⟨F, hF⟩ := depth_le_one_lower_bound A hA
  have hpt : (0 : Real) < exp (-(1 + exp (k - F))) := exp_pos _
  have hlog : log (exp (-(1 + exp (k - F)))) = -(1 + exp (k - F)) := log_exp _
  have hle1 : exp (-(1 + exp (k - F))) ≤ 1 := by
    have hneg : -(1 + exp (k - F)) ≤ 0 := by
      have hp : (0 : Real) < 1 + exp (k - F) := by
        have u := add_lt_add_left (exp_pos (k - F)) 1
        have l : (1 : Real) + 0 = 1 := by mach_ring
        rw [l] at u; exact lt_trans_ax zero_lt_one_ax u
      have u := neg_le_neg_wit (le_of_lt hp)
      have l : -(0 : Real) = 0 := by mach_ring
      rw [l] at u; exact u
    have hm := exp_monotone hneg; rw [exp_zero] at hm; exact hm
  have hlow := hF _ hpt hle1
  rw [h _ hpt, hlog] at hlow
  -- `F ≤ k − 1 − exp(k−F)` contradicts `k − F < 1 + exp(k−F)`
  have hkey : k - F < 1 + exp (k - F) := lt_one_add_exp (k - F)
  have hbad : (1 : Real) + exp (k - F) ≤ k - F := by
    have u := add_le_add_wit hlow (le_refl (1 + exp (k - F) - F))
    have l : F + (1 + exp (k - F) - F) = 1 + exp (k - F) := by
      mach_mpoly [F, exp (k - F)]
    have r : k + -(1 + exp (k - F)) + (1 + exp (k - F) - F) = k - F := by
      mach_mpoly [k, F, exp (k - F)]
    rw [l, r] at u; exact u
  exact lt_irrefl_ax _ (lt_of_lt_of_le hkey hbad)

/-- **`M·x` is out of reach when the right child is `exp x`.** `log(exp x) = x` exactly, so the
equation forces `exp(A x) = (M+1)·x`. But `exp(A x) ≥ exp F` on `(0,1]` by the lower bound, while
`(M+1)·x` can be driven below `exp F`. -/
theorem mx_B_is_exp_absurd (M : Real) (hM : 0 < M) (A : EMLTree) (hA : A.depth ≤ 1)
    (h : ∀ x : Real, 0 < x → exp (A.eval x) - x = M * x) : False := by
  have hN : (0 : Real) < M + 1 := by
    have u := add_lt_add_left zero_lt_one_ax M
    have l : M + 0 = M := by mach_mpoly [M]
    rw [l] at u; exact lt_trans_ax hM u
  have hval : ∀ x : Real, 0 < x → exp (A.eval x) = (M + 1) * x := by
    intro x hx
    have e : exp (A.eval x) = (exp (A.eval x) - x) + x := by mach_mpoly [exp (A.eval x), x]
    rw [e, h x hx]; mach_mpoly [M, x]
  obtain ⟨F, hF⟩ := depth_le_one_lower_bound A hA
  -- the point: `x = 1 / (1 + (M+1)·exp(−F))`
  have hD : (0 : Real) < 1 + (M + 1) * exp (-F) := by
    have hp : (0 : Real) < (M + 1) * exp (-F) := mul_pos hN (exp_pos _)
    have u := add_lt_add_left hp 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact lt_trans_ax zero_lt_one_ax u
  have hx : (0 : Real) < 1 / (1 + (M + 1) * exp (-F)) := one_div_pos_of_pos hD
  have hx1 : 1 / (1 + (M + 1) * exp (-F)) ≤ 1 := by
    have hge : (1 : Real) ≤ 1 + (M + 1) * exp (-F) := by
      have hp : (0 : Real) ≤ (M + 1) * exp (-F) := le_of_lt (mul_pos hN (exp_pos _))
      have u := add_le_add_wit (le_refl (1 : Real)) hp
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact u
    rcases (le_iff_lt_or_eq (1 : Real) (1 + (M + 1) * exp (-F))).mp hge with hlt | heq
    · exact le_of_lt (div_lt_one_of_pos_lt hD hlt)
    · have e : (1 : Real) / 1 = 1 := by
        have hv := mul_inv (1 : Real) (ne_of_gt zero_lt_one_ax)
        have l : (1 : Real) * (1 / 1) = 1 / 1 := by mach_mpoly [(1 / 1 : Real)]
        rw [l] at hv; exact hv
      rw [← heq, e]; exact le_refl _
  -- `exp F ≤ exp (A x) = (M+1)·x`, yet `(M+1)·x < exp F`
  have hlow : exp F ≤ (M + 1) * (1 / (1 + (M + 1) * exp (-F))) := by
    rw [← hval _ hx]; exact exp_monotone (hF _ hx hx1)
  have hinvD : (1 + (M + 1) * exp (-F)) * (1 / (1 + (M + 1) * exp (-F))) = 1 :=
    mul_inv _ (ne_of_gt hD)
  have hexpF : exp F * exp (-F) = 1 := by
    rw [← exp_add]
    have e : F + -F = 0 := by mach_mpoly [F]
    rw [e, exp_zero]
  have hstep : M + 1 < exp F * (1 + (M + 1) * exp (-F)) := by
    have hrw : exp F * (1 + (M + 1) * exp (-F)) = exp F + (M + 1) * (exp F * exp (-F)) := by
      mach_mpoly [exp F, M, exp (-F)]
    rw [hrw, hexpF]
    have u := add_lt_add_left (exp_pos F) (M + 1)
    have l : M + 1 + 0 = M + 1 := by mach_mpoly [M]
    have r : M + 1 + exp F = exp F + (M + 1) * 1 := by mach_mpoly [M, exp F]
    rw [l, r] at u; exact u
  have hmul := mul_lt_mul_of_pos_right hstep hx
  have hL : (M + 1) * (1 / (1 + (M + 1) * exp (-F)))
      = (M + 1) * (1 / (1 + (M + 1) * exp (-F))) := rfl
  have hR : exp F * (1 + (M + 1) * exp (-F)) * (1 / (1 + (M + 1) * exp (-F)))
      = exp F * ((1 + (M + 1) * exp (-F)) * (1 / (1 + (M + 1) * exp (-F)))) := by
    mach_mpoly [exp F, M, exp (-F), (1 / (1 + (M + 1) * exp (-F)) : Real)]
  rw [hR, hinvD] at hmul
  have hone : exp F * 1 = exp F := by mach_mpoly [exp F]
  rw [hone] at hmul
  exact lt_irrefl_ax _ (lt_of_lt_of_le hmul hlow)

end MachLib