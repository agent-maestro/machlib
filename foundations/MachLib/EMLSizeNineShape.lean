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

/-! ## ▸ The missing side: growth at `∞`

Every bound in this module so far lives on `(0,1]`. The remaining `M·x` shapes need the other end,
and the fact they need is that **a `log` of anything shallow cannot beat linear**: whatever a
depth-≤1 subtree does, its logarithm is under `x + C`. That is what turns
`exp(A x) − log(B x) = M·x` into `exp(A x) ≤ (M+1)·x + C`, where `exp_beats_linear_past` finishes any
`A` that grows.
-/

/-- Padding: `y ≤ x + y` once `0 ≤ x`. -/
private theorem le_add_left_nonneg {x y : Real} (hx : 0 ≤ x) : y ≤ x + y := by
  have u := add_le_add_wit hx (le_refl y)
  have l : (0 : Real) + y = y := by mach_mpoly [y]
  rw [l] at u; exact u

/-- `exp x − d ≤ exp (x + exp (−d))` for `x ≥ 0` — the step that keeps case 4 free of `log_mul`. -/
private theorem exp_sub_le_exp_shift (d : Real) {x : Real} (hx : 0 ≤ x) :
    exp x - d ≤ exp (x + exp (-d)) := by
  have hex1 : (1 : Real) ≤ exp x := by
    have hm := exp_monotone hx; rw [exp_zero] at hm; exact hm
  have hd : -d ≤ exp (-d) := le_of_lt (exp_grows_strictly_thm _)
  have h1 : exp x - d ≤ exp x + exp (-d) := by
    have u := add_le_add_wit (le_refl (exp x)) hd
    have l : exp x + -d = exp x - d := by mach_mpoly [exp x, d]
    rw [l] at u; exact u
  have h2 : exp x + exp (-d) ≤ exp x * exp (exp (-d)) := by
    have he : (1 : Real) + exp (-d) ≤ exp (exp (-d)) := one_add_le_exp _
    have hm := mul_le_mul_of_nonneg_left he (le_of_lt (exp_pos x))
    have l : exp x * (1 + exp (-d)) = exp x + exp (-d) * exp x := by
      mach_mpoly [exp x, exp (-d)]
    rw [l] at hm
    have hgrow : exp (-d) ≤ exp (-d) * exp x := by
      have u := mul_le_mul_of_nonneg_left hex1 (le_of_lt (exp_pos (-d)))
      have e : exp (-d) * 1 = exp (-d) := by mach_mpoly [exp (-d)]
      rw [e] at u; exact u
    have u := add_le_add_wit (le_refl (exp x)) hgrow
    exact le_trans u hm
  rw [exp_add]
  exact le_trans h1 h2

/-- **A depth-≤1 tree's logarithm cannot beat linear.** `log (B x) ≤ x + C` on `[1,∞)`. All five
closed forms are covered, including the totalised branches where `B x ≤ 0` and the log is `0`. -/
theorem depth_le_one_log_le_linear (B : EMLTree) (hB : B.depth ≤ 1) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ x + C := by
  have hx0 : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ x := fun x h1 => le_trans (le_of_lt zero_lt_one_ax) h1
  have hlogx : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ log x := by
    intro x h1
    rcases (le_iff_lt_or_eq (1 : Real) x).mp h1 with hlt | heq
    · exact le_of_lt (by have := log_lt_log zero_lt_one_ax hlt
                         have hl1 : log (1 : Real) = 0 := by
                           have hz : exp (0 : Real) = 1 := exp_zero
                           rw [← hz, log_exp]
                         rw [hl1] at this; exact this)
    · rw [← heq]
      have hl1 : log (1 : Real) = 0 := by
        have hz : exp (0 : Real) = 1 := exp_zero
        rw [← hz, log_exp]
      rw [hl1]; exact le_refl 0
  -- totalised branch, shared by every case: if the argument is ≤ 0 the log is 0
  have hzero : ∀ (y x C : Real), y ≤ 0 → 1 ≤ x → 0 ≤ C → log y ≤ x + C := by
    intro y x C hy h1 hC
    rw [log_nonpos hy]
    exact le_trans hC (le_add_left_nonneg (hx0 x h1))
  rcases depth_le_one_classification B hB with
      ⟨β, hb⟩ | hb | ⟨c, hc0, hb⟩ | ⟨d, hb⟩ | hb
  · refine ⟨exp (log β), fun x h1 => ?_⟩
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax h1)]
    exact le_trans (le_of_lt (exp_grows_strictly_thm (log β)))
      (le_add_left_nonneg (hx0 x h1))
  · refine ⟨0, fun x h1 => ?_⟩
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax h1)]
    have hs := log_le_sub_one_of_one_le h1
    have hpad : x - 1 ≤ x + 0 := by
      have u := add_le_add_wit (le_refl x) (neg_le_neg_wit (le_of_lt zero_lt_one_ax))
      have l : x + -(1 : Real) = x - 1 := by mach_mpoly [x]
      have r : x + -(0 : Real) = x + 0 := by mach_mpoly [x]
      rw [l, r] at u; exact u
    exact le_trans hs hpad
  · refine ⟨exp (log c), fun x h1 => ?_⟩
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax h1)]
    rcases lt_total (c - log x) 0 with hneg | heq | hpos
    · exact hzero _ x _ (le_of_lt hneg) h1 (le_of_lt (exp_pos _))
    · exact hzero _ x _ (le_of_eq heq) h1 (le_of_lt (exp_pos _))
    · have hle : c - log x ≤ c := by
        have u := add_le_add_wit (le_refl c) (neg_le_neg_wit (hlogx x h1))
        have l : c + -log x = c - log x := by mach_mpoly [c, log x]
        have r : c + -(0 : Real) = c := by mach_mpoly [c]
        rw [l, r] at u; exact u
      have hm := log_le_log hpos hle
      exact le_trans hm (le_trans (le_of_lt (exp_grows_strictly_thm (log c)))
        (le_add_left_nonneg (hx0 x h1)))
  · refine ⟨exp (-d), fun x h1 => ?_⟩
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax h1)]
    rcases lt_total (exp x - d) 0 with hneg | heq | hpos
    · exact hzero _ x _ (le_of_lt hneg) h1 (le_of_lt (exp_pos _))
    · exact hzero _ x _ (le_of_eq heq) h1 (le_of_lt (exp_pos _))
    · have hm := log_le_log hpos (exp_sub_le_exp_shift d (hx0 x h1))
      rw [log_exp] at hm; exact hm
  · refine ⟨0, fun x h1 => ?_⟩
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax h1)]
    rcases lt_total (exp x - log x) 0 with hneg | heq | hpos
    · exact hzero _ x _ (le_of_lt hneg) h1 (le_refl 0)
    · exact hzero _ x _ (le_of_eq heq) h1 (le_refl 0)
    · have hle : exp x - log x ≤ exp x := by
        have u := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit (hlogx x h1))
        have l : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
        have r : exp x + -(0 : Real) = exp x := by mach_mpoly [exp x]
        rw [l, r] at u; exact u
      have hm := log_le_log hpos hle
      rw [log_exp] at hm
      have hpad : x ≤ x + 0 := by
        have e : x + (0 : Real) = x := by mach_mpoly [x]
        rw [e]; exact le_refl x
      exact le_trans hm hpad

/-- **`M·x` is out of reach when the left child is `var`.** `exp x − log(B x) = M·x` gives
`exp x ≤ (M+1)·x + C` on `[1,∞)` by the bound above, and `exp_beats_linear_past` refuses it.
Any depth-≤1 `B`, no case analysis on `B` at all — which is the point of having the `∞` bound. -/
theorem mx_A_is_var_absurd (M : Real) (hM : 0 < M) (B : EMLTree) (hB : B.depth ≤ 1)
    (h : ∀ x : Real, 0 < x → exp x - log (B.eval x) = M * x) : False := by
  obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB
  have hα : (0 : Real) ≤ M + 1 := by
    have u := add_le_add_wit (le_of_lt hM) (le_of_lt zero_lt_one_ax)
    have l : (0 : Real) + 0 = 0 := by mach_ring
    rw [l] at u; exact u
  obtain ⟨x, _, hx1, hlt⟩ := exp_beats_linear_past (α := M + 1) (β := C) hα 1
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have key := h x hxpos
  have hlog := hC x hx1
  -- `exp x = M·x + log (B x) ≤ M·x + x + C = (M+1)·x + C`
  have hub : exp x ≤ (M + 1) * x + C := by
    have hval : exp x = M * x + log (B.eval x) := by
      have e : exp x = (exp x - log (B.eval x)) + log (B.eval x) := by
        mach_mpoly [exp x, log (B.eval x)]
      rw [e, key]
    rw [hval]
    have u := add_le_add_wit (le_refl (M * x)) hlog
    have r : M * x + (x + C) = (M + 1) * x + C := by mach_mpoly [M, x, C]
    rw [r] at u; exact u
  exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hub)

/-- **The mirror: a depth-≤1 tree's logarithm is bounded BELOW eventually.** Each form needs its own
threshold — `c − log x` only crosses into the totalised branch past `exp c`, and `exp x − d` only
clears `1` past `exp d` — but past it the bound is uniform, and in four of the five forms it is `0`. -/
theorem depth_le_one_log_lower_at_infinity (B : EMLTree) (hB : B.depth ≤ 1) :
    ∃ Cl X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → Cl ≤ log (B.eval x) := by
  have hl1 : log (1 : Real) = 0 := by
    have hz : exp (0 : Real) = 1 := exp_zero
    rw [← hz, log_exp]
  have hnonneg : ∀ y : Real, 1 ≤ y → (0 : Real) ≤ log y := by
    intro y hy
    have hm := log_le_log zero_lt_one_ax hy
    rw [hl1] at hm; exact hm
  have hone_le : ∀ y : Real, 0 < y → (1 : Real) ≤ 1 + y := by
    intro y hy
    have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt hy)
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  rcases depth_le_one_classification B hB with
      ⟨β, hb⟩ | hb | ⟨c, hc0, hb⟩ | ⟨d, hb⟩ | hb
  · refine ⟨log β, 1, le_refl 1, fun x hx => ?_⟩
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx)]; exact le_refl _
  · refine ⟨0, 1, le_refl 1, fun x hx => ?_⟩
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx)]
    exact hnonneg x hx
  · refine ⟨0, 1 + exp c, hone_le _ (exp_pos c), fun x hx => ?_⟩
    have hx1 : (1 : Real) ≤ x := le_trans (hone_le _ (exp_pos c)) hx
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)]
    have hec : exp c ≤ x := by
      refine le_trans ?_ hx
      have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp c))
      have l : (0 : Real) + exp c = exp c := by mach_mpoly [exp c]
      rw [l] at u; exact u
    have hcl : c ≤ log x := by
      have hm := log_le_log (exp_pos c) hec
      rw [log_exp] at hm; exact hm
    have hle : c - log x ≤ 0 := by
      have u := add_le_add_wit hcl (neg_le_neg_wit (le_refl (log x)))
      have l : c + -log x = c - log x := by mach_mpoly [c, log x]
      have r : log x + -log x = 0 := by mach_mpoly [log x]
      rw [l, r] at u; exact u
    rw [log_nonpos hle]; exact le_refl 0
  · refine ⟨0, 1 + exp d, hone_le _ (exp_pos d), fun x hx => ?_⟩
    have hx1 : (1 : Real) ≤ x := le_trans (hone_le _ (exp_pos d)) hx
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)]
    have hxd : (1 : Real) + d < x :=
      lt_of_lt_of_le (add_lt_add_left (exp_grows_strictly_thm d) 1) hx
    have hone : (1 : Real) ≤ exp x - d := by
      have hchain : (1 : Real) + d < exp x := lt_trans_ax hxd (exp_grows_strictly_thm x)
      have u := add_lt_add_left hchain (-d)
      have l : -d + (1 + d) = 1 := by mach_mpoly [d]
      have r : -d + exp x = exp x - d := by mach_mpoly [d, exp x]
      rw [l, r] at u; exact le_of_lt u
    exact hnonneg _ hone
  · refine ⟨0, 1, le_refl 1, fun x hx => ?_⟩
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx)]
    have hlog : log x ≤ x - 1 := log_le_sub_one_of_one_le hx
    have hexp : (1 : Real) + x ≤ exp x := one_add_le_exp x
    have hone : (1 : Real) ≤ exp x - log x := by
      have u := add_le_add_wit hexp (neg_le_neg_wit hlog)
      have l : (1 : Real) + x + -(x - 1) = 1 + 1 := by mach_mpoly [x]
      have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
      rw [l, r] at u
      exact le_trans (hone_le 1 zero_lt_one_ax) u
    exact hnonneg _ hone

/-- **`M·x` is out of reach when `exp(A x)` is bounded.** Covers both bounded `A`-forms in one
statement — `const α` with `K = exp α`, `c − log x` with `K = exp c` — because the only thing the
argument uses is the bound: `M·x` is unbounded and `K − Cl` is not. -/
theorem mx_A_bounded_absurd (M K : Real) (hM : 0 < M) (A B : EMLTree) (hB : B.depth ≤ 1)
    (hA : ∀ x : Real, 1 ≤ x → exp (A.eval x) ≤ K)
    (h : ∀ x : Real, 1 ≤ x → exp (A.eval x) - log (B.eval x) = M * x) : False := by
  obtain ⟨Cl, X₀, hX₀, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
  have hiM : (0 : Real) < 1 / M := one_div_pos_of_pos hM
  have hE : (0 : Real) < 1 + exp (K - Cl) := by
    have u := add_lt_add_left (exp_pos (K - Cl)) 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact lt_trans_ax zero_lt_one_ax u
  have ht : (0 : Real) < (1 + exp (K - Cl)) * (1 / M) := mul_pos hE hiM
  have hxX : X₀ ≤ X₀ + (1 + exp (K - Cl)) * (1 / M) := by
    have u := add_le_add_wit (le_refl X₀) (le_of_lt ht)
    have l : X₀ + 0 = X₀ := by mach_mpoly [X₀]
    rw [l] at u; exact u
  have hx1 : (1 : Real) ≤ X₀ + (1 + exp (K - Cl)) * (1 / M) := le_trans hX₀ hxX
  
  -- `M·x = M·X₀ + (1 + exp (K−Cl))`, which exceeds `K − Cl`
  have hMinv : M * (1 / M) = 1 := mul_inv M (ne_of_gt hM)
  have hMx : K - Cl < M * (X₀ + (1 + exp (K - Cl)) * (1 / M)) := by
    have hexpand : M * (X₀ + (1 + exp (K - Cl)) * (1 / M))
        = M * X₀ + (1 + exp (K - Cl)) * (M * (1 / M)) := by
      mach_mpoly [M, X₀, exp (K - Cl), (1 / M : Real)]
    rw [hexpand, hMinv]
    have hone : (1 + exp (K - Cl)) * (1 : Real) = 1 + exp (K - Cl) := by
      mach_mpoly [exp (K - Cl)]
    rw [hone]
    have hlt : K - Cl < 1 + exp (K - Cl) := lt_one_add_exp (K - Cl)
    have hpos : (0 : Real) < M * X₀ := mul_pos hM (lt_of_lt_of_le zero_lt_one_ax hX₀)
    have u := add_lt_add_left hlt (M * X₀)
    have l : M * X₀ + (K - Cl) = K - Cl + M * X₀ := by mach_mpoly [M, X₀, K, Cl]
    rw [l] at u
    have v := add_lt_add_left hpos (K - Cl)
    have l2 : K - Cl + 0 = K - Cl := by mach_mpoly [K, Cl]
    rw [l2] at v
    exact lt_trans_ax v u
  -- but the equation caps it at `K − Cl`
  have key := h _ hx1
  have hup : M * (X₀ + (1 + exp (K - Cl)) * (1 / M)) ≤ K - Cl := by
    rw [← key]
    have u := add_le_add_wit (hA _ hx1) (neg_le_neg_wit (hCl _ hxX))
    have l : exp (A.eval (X₀ + (1 + exp (K - Cl)) * (1 / M)))
           + -log (B.eval (X₀ + (1 + exp (K - Cl)) * (1 / M)))
           = exp (A.eval (X₀ + (1 + exp (K - Cl)) * (1 / M)))
           - log (B.eval (X₀ + (1 + exp (K - Cl)) * (1 / M))) := by
      mach_mpoly [exp (A.eval (X₀ + (1 + exp (K - Cl)) * (1 / M))),
                  log (B.eval (X₀ + (1 + exp (K - Cl)) * (1 / M)))]
    have r : K + -Cl = K - Cl := by mach_mpoly [K, Cl]
    rw [l, r] at u; exact u
  exact lt_irrefl_ax _ (lt_of_lt_of_le hMx hup)

/-- `x + x ≤ exp x` on `[0,∞)`: `exp x = exp 1 · exp(x−1) ≥ exp 1 · x ≥ 2x`. The one growth fact the
two fast `A`-forms need, and it avoids any appeal to calculus. -/
private theorem two_mul_le_exp {x : Real} (hx : 0 ≤ x) : x + x ≤ exp x := by
  have he1 : (1 : Real) + 1 ≤ exp 1 := one_add_le_exp 1
  have hsplit : exp x = exp 1 * exp (x - 1) := by
    rw [← exp_add]
    have e : (1 : Real) + (x - 1) = x := by mach_mpoly [x]
    rw [e]
  have hstep : x ≤ exp (x - 1) := by
    have hu := one_add_le_exp (x - 1)
    have e : (1 : Real) + (x - 1) = x := by mach_mpoly [x]
    rw [e] at hu; exact hu
  have h1 : exp 1 * x ≤ exp 1 * exp (x - 1) :=
    mul_le_mul_of_nonneg_left hstep (le_of_lt (exp_pos 1))
  have h2 : x + x ≤ exp 1 * x := by
    have u := mul_le_mul_of_nonneg_right he1 hx
    have l : ((1 : Real) + 1) * x = x + x := by mach_mpoly [x]
    rw [l] at u; exact u
  rw [hsplit]
  exact le_trans h2 h1

/-- **`M·x` is out of reach when `A` eventually dominates `x`.** The `∞` upper bound caps
`exp(A x)` by `(M+1)·x + C`, and `exp_beats_linear_past` produces a point past `T` where `exp x`
already exceeds that cap — so `exp(A x) ≥ exp x` finishes it. Covers both fast `A`-forms. -/
theorem mx_A_grows_absurd (M : Real) (hM : 0 < M) (A B : EMLTree) (hB : B.depth ≤ 1)
    (T : Real) (hA : ∀ x : Real, T ≤ x → x ≤ A.eval x)
    (h : ∀ x : Real, 1 ≤ x → exp (A.eval x) - log (B.eval x) = M * x) : False := by
  obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB
  have hα : (0 : Real) ≤ M + 1 := by
    have u := add_le_add_wit (le_of_lt hM) (le_of_lt zero_lt_one_ax)
    have l : (0 : Real) + 0 = 0 := by mach_ring
    rw [l] at u; exact u
  obtain ⟨x, hxT, hx1, hlt⟩ := exp_beats_linear_past (α := M + 1) (β := C) hα T
  have hub : exp (A.eval x) ≤ (M + 1) * x + C := by
    have hval : exp (A.eval x) = M * x + log (B.eval x) := by
      have e : exp (A.eval x) = (exp (A.eval x) - log (B.eval x)) + log (B.eval x) := by
        mach_mpoly [exp (A.eval x), log (B.eval x)]
      rw [e, h x hx1]
    rw [hval]
    have u := add_le_add_wit (le_refl (M * x)) (hC x hx1)
    have r : M * x + (x + C) = (M + 1) * x + C := by mach_mpoly [M, x, C]
    rw [r] at u; exact u
  have hgrow : exp x ≤ exp (A.eval x) := exp_monotone (hA x hxT)
  exact lt_irrefl_ax _ (lt_of_lt_of_le hlt (le_trans hgrow hub))

/-- **`M·x ∉ EML₂` for every `M > 1`.** All five `A`-forms fall: `var` and the two fast forms to
`mx_A_grows_absurd`, `const` and `c − log x` to `mx_A_bounded_absurd`. `M = 1` is genuinely
excluded — `var` computes `1·x` at depth 0. -/
theorem mx_not_in_eml_depth_le_2 (M : Real) (hM1 : 1 < M) (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 1 ≤ x → t.eval x = M * x) : False := by
  have hM : (0 : Real) < M := lt_trans_ax zero_lt_one_ax hM1
  cases t with
  | const q =>
    have h1 := h 1 (le_refl 1)
    have h2 := h (1 + 1) (by
      have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt zero_lt_one_ax)
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact u)
    have e1 : (EMLTree.const q).eval 1 = q := rfl
    have e2 : (EMLTree.const q).eval (1 + 1) = q := rfl
    rw [e1] at h1; rw [e2] at h2
    have hbad : M = 0 := by
      have hq : M * 1 = M * (1 + 1) := by rw [← h1, h2]
      have l : M * (1 : Real) = M := by mach_mpoly [M]
      have r : M * ((1 : Real) + 1) = M + M := by mach_mpoly [M]
      rw [l, r] at hq
      have u : M + -M = M + M + -M := by rw [← hq]
      have l2 : M + -M = 0 := by mach_mpoly [M]
      have r2 : M + M + -M = M := by mach_mpoly [M]
      rw [l2, r2] at u; exact u.symm
    exact lt_irrefl_ax 0 (hbad ▸ hM)
  | var =>
    have h1 := h 1 (le_refl 1)
    have e1 : (EMLTree.var).eval 1 = 1 := rfl
    rw [e1] at h1
    have hM_eq : M = 1 := by
      have l : M * (1 : Real) = M := by mach_mpoly [M]
      rw [l] at h1; exact h1.symm
    exact lt_irrefl_ax 1 (hM_eq ▸ hM1)
  | eml A B =>
    have hA1 : A.depth ≤ 1 := by
      have := Nat.le_max_left A.depth B.depth
      simp only [EMLTree.depth] at ht; omega
    have hB1 : B.depth ≤ 1 := by
      have := Nat.le_max_right A.depth B.depth
      simp only [EMLTree.depth] at ht; omega
    have heq : ∀ x : Real, 1 ≤ x → exp (A.eval x) - log (B.eval x) = M * x := fun x hx => h x hx
    rcases depth_le_one_classification A hA1 with
        ⟨α, ha⟩ | ha | ⟨c, hc0, ha⟩ | ⟨d, ha⟩ | ha
    · refine mx_A_bounded_absurd M (exp α) hM A B hB1 (fun x hx1 => ?_) heq
      rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]; exact le_refl _
    · refine mx_A_grows_absurd M hM A B hB1 1 (fun x hx1 => ?_) heq
      rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]; exact le_refl _
    · refine mx_A_bounded_absurd M (exp c) hM A B hB1 (fun x hx1 => ?_) heq
      rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
      refine exp_monotone ?_
      have hlx : (0 : Real) ≤ log x := by
        have hm := log_le_log zero_lt_one_ax hx1
        have hl1 : log (1 : Real) = 0 := by
          have hz : exp (0 : Real) = 1 := exp_zero
          rw [← hz, log_exp]
        rw [hl1] at hm; exact hm
      have u := add_le_add_wit (le_refl c) (neg_le_neg_wit hlx)
      have l : c + -log x = c - log x := by mach_mpoly [c, log x]
      have r : c + -(0 : Real) = c := by mach_mpoly [c]
      rw [l, r] at u; exact u
    · refine mx_A_grows_absurd M hM A B hB1 (1 + exp d) (fun x hxT => ?_) heq
      have hx1 : (1 : Real) ≤ x := by
        refine le_trans ?_ hxT
        have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos d))
        have l : (1 : Real) + 0 = 1 := by mach_ring
        rw [l] at u; exact u
      rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
      have hxd : d ≤ x := by
        refine le_trans (le_of_lt (exp_grows_strictly_thm d)) (le_trans ?_ hxT)
        have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp d))
        have l : (0 : Real) + exp d = exp d := by mach_mpoly [exp d]
        rw [l] at u; exact u
      have hxx := two_mul_le_exp (le_trans (le_of_lt zero_lt_one_ax) hx1)
      have u := add_le_add_wit hxx (neg_le_neg_wit hxd)
      have l : x + x + -x = x := by mach_mpoly [x]
      have r : exp x + -d = exp x - d := by mach_mpoly [exp x, d]
      have hchain : x + x + -d ≤ exp x - d := by
        have v := add_le_add_wit hxx (le_refl (-d))
        rw [r] at v; exact v
      refine le_trans ?_ hchain
      have w := add_le_add_wit (le_refl (x + x)) (neg_le_neg_wit hxd)
      have l2 : x + x + -x = x := by mach_mpoly [x]
      rw [l2] at w; exact w
    · refine mx_A_grows_absurd M hM A B hB1 1 (fun x hx1 => ?_) heq
      rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
      have hlog : log x ≤ x - 1 := log_le_sub_one_of_one_le hx1
      have hxx := two_mul_le_exp (le_trans (le_of_lt zero_lt_one_ax) hx1)
      have u := add_le_add_wit hxx (neg_le_neg_wit hlog)
      have l : x + x + -(x - 1) = x + 1 := by mach_mpoly [x]
      have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
      rw [l, r] at u
      refine le_trans ?_ u
      have v := add_le_add_wit (le_refl x) (le_of_lt zero_lt_one_ax)
      have l2 : x + (0 : Real) = x := by mach_mpoly [x]
      rw [l2] at v; exact v

/-- **The `−log x` cell's `ℓ = const p` branch is dead.** Right-branching gives
`log(L₂ x) = exp p + log x`, i.e. `L₂ x = M·x` with `M = exp(exp p) > 1`, and `M·x ∉ EML₂`.

Stated on `[1,∞)` because that is all `mx_not_in_eml_depth_le_2` needs, and it dodges the wrinkle
the totalised `log` creates: `log(L₂ x) = exp p + log x` only forces `L₂ x > 0` away from
`x = exp(−exp p)`, which is `< 1`. -/
theorem neg_log_right_const_absurd (p : Real) (L₂ : EMLTree) (hd : L₂.depth ≤ 2)
    (h : ∀ x : Real, 1 ≤ x → L₂.eval x = exp (exp p) * x) : False := by
  refine mx_not_in_eml_depth_le_2 (exp (exp p)) ?_ L₂ hd h
  have hm := exp_lt (exp_pos p)
  rw [exp_zero] at hm; exact hm

/-! ## ▸ The last `−log x` case: `ℓ = var` and a double exponential

Right-branching with `ℓ = var` gives `log(L₂ x) = exp x + log x`, so `L₂ x = x·exp(exp x)` — a
double exponential *multiplied by `x`*, and that extra factor is the whole obstruction. A depth-≤1
`A` satisfies `A x ≤ exp x + D` (`depth_le_one_le_exp_shift`), so `exp(A x) ≤ exp D·exp(exp x)`:
a **constant** multiple of `exp(exp x)`. The target needs an `x`-growing multiple, and `x` outruns
any constant.
-/

/-- **A depth-≤1 tree is under `exp x + D` on `[1,∞)`.** The value-level companion to
`depth_le_one_log_le_linear`, which bounds its logarithm. -/
theorem depth_le_one_le_exp_shift (A : EMLTree) (hA : A.depth ≤ 1) :
    ∃ D : Real, ∀ x : Real, 1 ≤ x → A.eval x ≤ exp x + D := by
  have hlogx : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ log x := by
    intro x h1
    have hm := log_le_log zero_lt_one_ax h1
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    rw [hl1] at hm; exact hm
  have hpad : ∀ (c x : Real), c ≤ exp x + c := by
    intro c x
    have u := add_le_add_wit (le_of_lt (exp_pos x)) (le_refl c)
    have l : (0 : Real) + c = c := by mach_mpoly [c]
    rw [l] at u; exact u
  rcases depth_le_one_classification A hA with
      ⟨α, ha⟩ | ha | ⟨c, _, ha⟩ | ⟨d, ha⟩ | ha
  · exact ⟨α, fun x h1 => by rw [ha x (lt_of_lt_of_le zero_lt_one_ax h1)]; exact hpad α x⟩
  · refine ⟨0, fun x h1 => ?_⟩
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax h1)]
    have hx := le_of_lt (exp_grows_strictly_thm x)
    have e : exp x + (0 : Real) = exp x := by mach_mpoly [exp x]
    rw [e]; exact hx
  · refine ⟨c, fun x h1 => ?_⟩
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax h1)]
    refine le_trans ?_ (hpad c x)
    have u := add_le_add_wit (le_refl c) (neg_le_neg_wit (hlogx x h1))
    have l : c + -log x = c - log x := by mach_mpoly [c, log x]
    have r : c + -(0 : Real) = c := by mach_mpoly [c]
    rw [l, r] at u; exact u
  · refine ⟨-d, fun x h1 => ?_⟩
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax h1)]
    have e : exp x + -d = exp x - d := by mach_mpoly [exp x, d]
    rw [e]; exact le_refl _
  · refine ⟨0, fun x h1 => ?_⟩
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax h1)]
    have e : exp x + (0 : Real) = exp x := by mach_mpoly [exp x]
    rw [e]
    have u := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit (hlogx x h1))
    have l : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
    have r : exp x + -(0 : Real) = exp x := by mach_mpoly [exp x]
    rw [l, r] at u; exact u

/-- **`x·exp(exp x)` is out of reach at depth 2.** `exp(A x)` is capped by a *constant* multiple of
`exp(exp x)`, and the target's multiple grows with `x`. Closes the last case of the `−log x` cell. -/
theorem x_mul_exp_exp_not_in_eml_depth_le_2 (A B : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (h : ∀ x : Real, 1 ≤ x → exp (A.eval x) - log (B.eval x) = x * exp (exp x)) : False := by
  obtain ⟨D, hD⟩ := depth_le_one_le_exp_shift A hA
  obtain ⟨Cl, X₀, hX₀, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
  -- the point: past `X₀`, past `exp D + 1`, and past `−Cl`
  have hx : (1 : Real) ≤ X₀ + exp D + exp (-Cl) := by
    refine le_trans hX₀ ?_
    have u := add_le_add_wit (add_le_add_wit (le_refl X₀) (le_of_lt (exp_pos D)))
      (le_of_lt (exp_pos (-Cl)))
    have l : X₀ + 0 + 0 = X₀ := by mach_mpoly [X₀]
    rw [l] at u; exact u
  have hxX : X₀ ≤ X₀ + exp D + exp (-Cl) := by
    have u := add_le_add_wit (add_le_add_wit (le_refl X₀) (le_of_lt (exp_pos D)))
      (le_of_lt (exp_pos (-Cl)))
    have l : X₀ + 0 + 0 = X₀ := by mach_mpoly [X₀]
    rw [l] at u; exact u
  have hxpos : (0 : Real) < X₀ + exp D + exp (-Cl) := lt_of_lt_of_le zero_lt_one_ax hx
  -- upper: `exp (A x) ≤ exp D · exp (exp x)`
  have hup : exp (A.eval (X₀ + exp D + exp (-Cl)))
      ≤ exp D * exp (exp (X₀ + exp D + exp (-Cl))) := by
    have hm := exp_monotone (hD _ hx)
    rw [exp_add] at hm
    have e : exp (exp (X₀ + exp D + exp (-Cl))) * exp D
        = exp D * exp (exp (X₀ + exp D + exp (-Cl))) := by
      mach_mpoly [exp D, exp (exp (X₀ + exp D + exp (-Cl)))]
    rw [e] at hm; exact hm
  -- lower: `exp (A x) ≥ x · exp (exp x) + Cl`
  have hlow : (X₀ + exp D + exp (-Cl)) * exp (exp (X₀ + exp D + exp (-Cl))) + Cl
      ≤ exp (A.eval (X₀ + exp D + exp (-Cl))) := by
    have key := h _ hx
    have u := add_le_add_wit (le_refl ((X₀ + exp D + exp (-Cl))
      * exp (exp (X₀ + exp D + exp (-Cl))))) (hCl _ hxX)
    have hrhs : (X₀ + exp D + exp (-Cl)) * exp (exp (X₀ + exp D + exp (-Cl)))
        + log (B.eval (X₀ + exp D + exp (-Cl)))
        = exp (A.eval (X₀ + exp D + exp (-Cl))) := by
      rw [← key]
      mach_mpoly [exp (A.eval (X₀ + exp D + exp (-Cl))),
                  log (B.eval (X₀ + exp D + exp (-Cl)))]
    rw [hrhs] at u; exact u
  -- `(x − exp D)·exp(exp x) ≤ −Cl`, yet `x − exp D ≥ 1` and `exp(exp x) > −Cl`
  have hchain : (X₀ + exp D + exp (-Cl)) * exp (exp (X₀ + exp D + exp (-Cl))) + Cl
      ≤ exp D * exp (exp (X₀ + exp D + exp (-Cl))) := le_trans hlow hup
  have hone : (1 : Real) ≤ X₀ + exp D + exp (-Cl) - exp D := by
    have e : X₀ + exp D + exp (-Cl) - exp D = X₀ + exp (-Cl) := by
      mach_mpoly [X₀, exp D, exp (-Cl)]
    rw [e]
    refine le_trans hX₀ ?_
    have u := add_le_add_wit (le_refl X₀) (le_of_lt (exp_pos (-Cl)))
    have l : X₀ + 0 = X₀ := by mach_mpoly [X₀]
    rw [l] at u; exact u
  have hEE : (0 : Real) < exp (exp (X₀ + exp D + exp (-Cl))) := exp_pos _
  have hprod : exp (exp (X₀ + exp D + exp (-Cl)))
      ≤ (X₀ + exp D + exp (-Cl) - exp D) * exp (exp (X₀ + exp D + exp (-Cl))) := by
    have u := mul_le_mul_of_nonneg_right hone (le_of_lt hEE)
    have l : (1 : Real) * exp (exp (X₀ + exp D + exp (-Cl)))
        = exp (exp (X₀ + exp D + exp (-Cl))) := by
      mach_mpoly [exp (exp (X₀ + exp D + exp (-Cl)))]
    rw [l] at u; exact u
  have hcap : (X₀ + exp D + exp (-Cl) - exp D) * exp (exp (X₀ + exp D + exp (-Cl))) ≤ -Cl := by
    have u := add_le_add_wit hchain (le_refl (-Cl - exp D * exp (exp (X₀ + exp D + exp (-Cl)))))
    have l : (X₀ + exp D + exp (-Cl)) * exp (exp (X₀ + exp D + exp (-Cl))) + Cl
           + (-Cl - exp D * exp (exp (X₀ + exp D + exp (-Cl))))
           = (X₀ + exp D + exp (-Cl) - exp D) * exp (exp (X₀ + exp D + exp (-Cl))) := by
      mach_mpoly [X₀, exp D, exp (-Cl), Cl, exp (exp (X₀ + exp D + exp (-Cl)))]
    have r : exp D * exp (exp (X₀ + exp D + exp (-Cl)))
           + (-Cl - exp D * exp (exp (X₀ + exp D + exp (-Cl)))) = -Cl := by
      mach_mpoly [exp D, Cl, exp (exp (X₀ + exp D + exp (-Cl)))]
    rw [l, r] at u; exact u
  -- but `exp(exp x) > x > −Cl`
  have hgt : -Cl < exp (exp (X₀ + exp D + exp (-Cl))) := by
    have h1 : -Cl < exp (-Cl) := exp_grows_strictly_thm (-Cl)
    have h2 : exp (-Cl) ≤ X₀ + exp D + exp (-Cl) := by
      have u := add_le_add_wit (add_le_add_wit (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hX₀))
        (le_of_lt (exp_pos D))) (le_refl (exp (-Cl)))
      have l : (0 : Real) + 0 + exp (-Cl) = exp (-Cl) := by mach_mpoly [exp (-Cl)]
      rw [l] at u; exact u
    have h3 : X₀ + exp D + exp (-Cl) < exp (X₀ + exp D + exp (-Cl)) :=
      exp_grows_strictly_thm _
    have h4 : exp (X₀ + exp D + exp (-Cl)) < exp (exp (X₀ + exp D + exp (-Cl))) :=
      exp_lt h3
    exact lt_trans_ax (lt_of_lt_of_le h1 h2) (lt_trans_ax h3 h4)
  exact lt_irrefl_ax _ (lt_of_lt_of_le hgt (le_trans hprod hcap))

/-! ## ▸ A gap theorem: depth-1 exponentials are bounded, or they dominate `exp x`

Nothing sits in between. This is the structural fact behind every `M·x` case above — the split into
`mx_A_bounded_absurd` and `mx_A_grows_absurd` was that dichotomy, discovered case by case. Stating
it once makes it available to the cells still open, where the same fork appears.

The two bounded forms are `const α` and `c − log x`; the three growing ones are `x`, `exp x − d` and
`exp x − log x`. There is no depth-1 tree whose exponential grows, say, linearly — which is precisely
why `M·x` is unreachable.
-/

/-- **The gap.** For a depth-≤1 `A`, either `exp (A x)` is bounded on `[1,∞)`, or it eventually
dominates `exp x`. -/
theorem depth_le_one_exp_bounded_or_grows (A : EMLTree) (hA : A.depth ≤ 1) :
    (∃ K : Real, ∀ x : Real, 1 ≤ x → exp (A.eval x) ≤ K)
    ∨ (∃ T : Real, ∀ x : Real, T ≤ x → exp x ≤ exp (A.eval x)) := by
  have hlogx : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ log x := by
    intro x h1
    have hm := log_le_log zero_lt_one_ax h1
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    rw [hl1] at hm; exact hm
  rcases depth_le_one_classification A hA with
      ⟨α, ha⟩ | ha | ⟨c, _, ha⟩ | ⟨d, ha⟩ | ha
  · exact Or.inl ⟨exp α, fun x h1 => by
      rw [ha x (lt_of_lt_of_le zero_lt_one_ax h1)]; exact le_refl _⟩
  · refine Or.inr ⟨1, fun x h1 => ?_⟩
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax h1)]; exact le_refl _
  · refine Or.inl ⟨exp c, fun x h1 => ?_⟩
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax h1)]
    refine exp_monotone ?_
    have u := add_le_add_wit (le_refl c) (neg_le_neg_wit (hlogx x h1))
    have l : c + -log x = c - log x := by mach_mpoly [c, log x]
    have r : c + -(0 : Real) = c := by mach_mpoly [c]
    rw [l, r] at u; exact u
  · refine Or.inr ⟨1 + exp d, fun x hxT => ?_⟩
    have hx1 : (1 : Real) ≤ x := by
      refine le_trans ?_ hxT
      have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos d))
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact u
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
    refine exp_monotone ?_
    have hxd : d ≤ x := by
      refine le_trans (le_of_lt (exp_grows_strictly_thm d)) (le_trans ?_ hxT)
      have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp d))
      have l : (0 : Real) + exp d = exp d := by mach_mpoly [exp d]
      rw [l] at u; exact u
    have hxx := two_mul_le_exp (le_trans (le_of_lt zero_lt_one_ax) hx1)
    have v := add_le_add_wit hxx (le_refl (-d))
    have r : exp x + -d = exp x - d := by mach_mpoly [exp x, d]
    rw [r] at v
    refine le_trans ?_ v
    have w := add_le_add_wit (le_refl (x + x)) (neg_le_neg_wit hxd)
    have l2 : x + x + -x = x := by mach_mpoly [x]
    rw [l2] at w; exact w
  · refine Or.inr ⟨1, fun x hx1 => ?_⟩
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
    refine exp_monotone ?_
    have hlog : log x ≤ x - 1 := log_le_sub_one_of_one_le hx1
    have hxx := two_mul_le_exp (le_trans (le_of_lt zero_lt_one_ax) hx1)
    have u := add_le_add_wit hxx (neg_le_neg_wit hlog)
    have l : x + x + -(x - 1) = x + 1 := by mach_mpoly [x]
    have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
    rw [l, r] at u
    refine le_trans ?_ u
    have v := add_le_add_wit (le_refl x) (le_of_lt zero_lt_one_ax)
    have l2 : x + (0 : Real) = x := by mach_mpoly [x]
    rw [l2] at v; exact v

/-! ## ▸ The log side: bounded above, or unbounded above

**Not the mirror of the exp gap.** The `log` side has *three* growth classes — bounded
(`const β`, `c′ − log x`), **logarithmic** (`var`), and **linear** (`exp x − d`, `exp x − log x`) —
so there is no "bounded or dominates" statement to make: `var` is unbounded yet dominates nothing.
The dichotomy that *is* available, and the one the remaining cells need, is plain
**bounded-above versus unbounded-above**.
-/

/-- `exp (x−1) ≤ exp x − exp (x−1)`, since `exp 1 ≥ 2`. The step both unbounded cases share. -/
private theorem exp_sub_pred_ge (x : Real) : exp (x - 1) ≤ exp x - exp (x - 1) := by
  have hsplit : exp x = exp (x - 1) * exp 1 := by
    rw [← exp_add]
    have e : x - 1 + 1 = x := by mach_mpoly [x]
    rw [e]
  have he2 : (1 : Real) + 1 ≤ exp 1 := one_add_le_exp 1
  have hge : (1 : Real) ≤ exp 1 - 1 := by
    have u := add_le_add_wit he2 (le_refl (-1 : Real))
    have l : (1 : Real) + 1 + -1 = 1 := by mach_ring
    have r : exp 1 + -1 = exp 1 - 1 := by mach_mpoly [exp 1]
    rw [l, r] at u; exact u
  have hmul := mul_le_mul_of_nonneg_left hge (le_of_lt (exp_pos (x - 1)))
  have l : exp (x - 1) * 1 = exp (x - 1) := by mach_mpoly [exp (x - 1)]
  have r : exp (x - 1) * (exp 1 - 1) = exp (x - 1) * exp 1 - exp (x - 1) := by
    mach_mpoly [exp (x - 1), exp 1]
  rw [l, r] at hmul
  rw [hsplit]; exact hmul

/-! The three unbounded forms each need a point past a prescribed `Λ`. Extracted so the dichotomy
and its form-naming companion share them rather than each carrying a copy. -/

private theorem log_var_unbounded_from (S Λ : Real) :
    ∃ x : Real, S ≤ x ∧ 1 ≤ x ∧ Λ < log x := by
  have hnn : (0 : Real) ≤ 1 + exp Λ := by
    have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos Λ))
    have l : (0 : Real) + 0 = 0 := by mach_ring
    rw [l] at u; exact u
  have hstep : exp S ≤ 1 + exp Λ + exp S := le_add_left_nonneg hnn
  have hpos : (0 : Real) < 1 + exp Λ + exp S := lt_of_lt_of_le (exp_pos S) hstep
  have hgrow : (1 : Real) + exp Λ + exp S < exp (1 + exp Λ + exp S) :=
    exp_grows_strictly_thm _
  refine ⟨exp (1 + exp Λ + exp S), ?_, ?_, ?_⟩
  · exact le_of_lt (lt_trans_ax (lt_of_lt_of_le (exp_grows_strictly_thm S) hstep) hgrow)
  · have hm := exp_monotone (le_of_lt hpos); rw [exp_zero] at hm; exact hm
  · rw [log_exp]
    have h1 : Λ < exp Λ := exp_grows_strictly_thm Λ
    have h2 : exp Λ < 1 + exp Λ := by
      have v := add_lt_add_left zero_lt_one_ax (exp Λ)
      have l2 : exp Λ + 0 = exp Λ := by mach_mpoly [exp Λ]
      have r2 : exp Λ + 1 = 1 + exp Λ := by mach_mpoly [exp Λ]
      rw [l2, r2] at v; exact v
    have h3 : (1 : Real) + exp Λ ≤ 1 + exp Λ + exp S := by
      have u := add_le_add_wit (le_refl (1 + exp Λ)) (le_of_lt (exp_pos S))
      have l : (1 : Real) + exp Λ + 0 = 1 + exp Λ := by mach_mpoly [exp Λ]
      rw [l] at u; exact u
    exact lt_of_lt_of_le (lt_trans_ax h1 h2) h3

private theorem log_var_unbounded (Λ : Real) : ∃ x : Real, 1 ≤ x ∧ Λ < log x := by
  obtain ⟨x, _, hx1, hgt⟩ := log_var_unbounded_from 0 Λ
  exact ⟨x, hx1, hgt⟩

private theorem big_point (Λ : Real) : (1 : Real) ≤ 1 + exp (Λ + 1) ∧ Λ < exp (Λ + 1) := by
  refine ⟨?_, ?_⟩
  · have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos (Λ + 1)))
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  · refine lt_trans_ax ?_ (exp_grows_strictly_thm (Λ + 1))
    have u := add_lt_add_left zero_lt_one_ax Λ
    have l : Λ + 0 = Λ := by mach_mpoly [Λ]
    rw [l] at u; exact u

private theorem log_exp_sub_const_unbounded_from (S d Λ : Real) :
    ∃ x : Real, S ≤ x ∧ 1 ≤ x ∧ Λ < log (exp x - d) := by
  have hpos3 : (0 : Real) ≤ exp d + exp (Λ + 1) + exp S := by
    have u := add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos d)) (le_of_lt (exp_pos (Λ + 1))))
      (le_of_lt (exp_pos S))
    have l : (0 : Real) + 0 + 0 = 0 := by mach_ring
    rw [l] at u; exact u
  have hx1 : (1 : Real) ≤ 1 + exp d + exp (Λ + 1) + exp S := by
    have u := add_le_add_wit (le_refl (1 : Real)) hpos3
    have l : (1 : Real) + 0 = 1 := by mach_ring
    have r : (1 : Real) + (exp d + exp (Λ + 1) + exp S)
        = 1 + exp d + exp (Λ + 1) + exp S := by
      mach_mpoly [exp d, exp (Λ + 1), exp S]
    rw [l, r] at u; exact u
  have hpred : (1 : Real) + exp d + exp (Λ + 1) + exp S - 1
      = exp d + exp (Λ + 1) + exp S := by mach_mpoly [exp d, exp (Λ + 1), exp S]
  have hSle : exp S ≤ exp d + exp (Λ + 1) + exp S := by
    have u := add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos d))
      (le_of_lt (exp_pos (Λ + 1)))) (le_refl (exp S))
    have l : (0 : Real) + 0 + exp S = exp S := by mach_mpoly [exp S]
    rw [l] at u; exact u
  refine ⟨1 + exp d + exp (Λ + 1) + exp S, ?_, hx1, ?_⟩
  · refine le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (exp_grows_strictly_thm S) hSle) ?_)
    have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp d + exp (Λ + 1) + exp S))
    have l : (0 : Real) + (exp d + exp (Λ + 1) + exp S) = exp d + exp (Λ + 1) + exp S := by
      mach_mpoly [exp d, exp (Λ + 1), exp S]
    have r : (1 : Real) + (exp d + exp (Λ + 1) + exp S)
        = 1 + exp d + exp (Λ + 1) + exp S := by
      mach_mpoly [exp d, exp (Λ + 1), exp S]
    rw [l, r] at u; exact u
  · have hdle : d ≤ exp (1 + exp d + exp (Λ + 1) + exp S - 1) := by
      rw [hpred]
      refine le_trans (le_of_lt (exp_grows_strictly_thm d)) ?_
      refine le_trans ?_ (le_of_lt (exp_grows_strictly_thm (exp d + exp (Λ + 1) + exp S)))
      have u := add_le_add_wit (add_le_add_wit (le_refl (exp d))
        (le_of_lt (exp_pos (Λ + 1)))) (le_of_lt (exp_pos S))
      have l : exp d + 0 + 0 = exp d := by mach_mpoly [exp d]
      rw [l] at u; exact u
    have hge : exp (1 + exp d + exp (Λ + 1) + exp S - 1)
        ≤ exp (1 + exp d + exp (Λ + 1) + exp S) - d := by
      refine le_trans (exp_sub_pred_ge _) ?_
      have u := add_le_add_wit (le_refl (exp (1 + exp d + exp (Λ + 1) + exp S)))
        (neg_le_neg_wit hdle)
      have l : exp (1 + exp d + exp (Λ + 1) + exp S)
          + -exp (1 + exp d + exp (Λ + 1) + exp S - 1)
          = exp (1 + exp d + exp (Λ + 1) + exp S)
            - exp (1 + exp d + exp (Λ + 1) + exp S - 1) := by
        mach_mpoly [exp (1 + exp d + exp (Λ + 1) + exp S),
          exp (1 + exp d + exp (Λ + 1) + exp S - 1)]
      have r : exp (1 + exp d + exp (Λ + 1) + exp S) + -d
          = exp (1 + exp d + exp (Λ + 1) + exp S) - d := by
        mach_mpoly [exp (1 + exp d + exp (Λ + 1) + exp S), d]
      rw [l, r] at u; exact u
    have hm := log_le_log (exp_pos _) hge
    rw [log_exp, hpred] at hm
    refine lt_of_lt_of_le ?_ hm
    refine lt_of_lt_of_le (big_point Λ).2 ?_
    have u := add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos d)) (le_refl (exp (Λ + 1))))
      (le_of_lt (exp_pos S))
    have l : (0 : Real) + exp (Λ + 1) + 0 = exp (Λ + 1) := by mach_mpoly [exp (Λ + 1)]
    rw [l] at u; exact u

private theorem log_exp_sub_const_unbounded (d Λ : Real) :
    ∃ x : Real, 1 ≤ x ∧ Λ < log (exp x - d) := by
  obtain ⟨x, _, hx1, hgt⟩ := log_exp_sub_const_unbounded_from 0 d Λ
  exact ⟨x, hx1, hgt⟩

private theorem log_exp_sub_log_unbounded_from (S Λ : Real) :
    ∃ x : Real, S ≤ x ∧ 1 ≤ x ∧ Λ < log (exp x - log x) := by
  -- ask the `exp x − d` lemma for a point past `Λ + 1`, so `Λ < x − 1`
  obtain ⟨x, hxS, hx1, hgt⟩ := log_exp_sub_const_unbounded_from S 0 (Λ + 1)
  refine ⟨x, hxS, hx1, ?_⟩
  have hlx : log x ≤ exp (x - 1) := by
    refine le_trans (log_le_sub_one_of_one_le hx1) ?_
    exact le_of_lt (exp_grows_strictly_thm _)
  have hge : exp (x - 1) ≤ exp x - log x := by
    refine le_trans (exp_sub_pred_ge x) ?_
    have u := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit hlx)
    have l : exp x + -exp (x - 1) = exp x - exp (x - 1) := by
      mach_mpoly [exp x, exp (x - 1)]
    have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
    rw [l, r] at u; exact u
  have hm := log_le_log (exp_pos _) hge
  rw [log_exp] at hm
  refine lt_of_lt_of_le ?_ hm
  -- `Λ < x − 1` follows from the witness being past `exp (Λ+1)`
  have hz : exp x - (0 : Real) = exp x := by mach_mpoly [exp x]
  rw [hz] at hgt
  have hxx : log (exp x) = x := log_exp x
  rw [hxx] at hgt
  have u := add_lt_add_left hgt (-1 : Real)
  have l : (-1 : Real) + (Λ + 1) = Λ := by mach_mpoly [Λ]
  have r : (-1 : Real) + x = x - 1 := by mach_mpoly [x]
  rw [l, r] at u; exact u

private theorem log_exp_sub_log_unbounded (Λ : Real) :
    ∃ x : Real, 1 ≤ x ∧ Λ < log (exp x - log x) := by
  obtain ⟨x, _, hx1, hgt⟩ := log_exp_sub_log_unbounded_from 0 Λ
  exact ⟨x, hx1, hgt⟩

/-- Cap for the `c − log x` form on `[1,∞)`: `c + 1`, valid including the totalised branch. -/
private theorem log_c_sub_log_cap {c : Real} (hc0 : 0 < c) :
    ∀ x : Real, 1 ≤ x → log (c - log x) ≤ c + 1 := by
  have hl1 : log (1 : Real) = 0 := by
    have hz : exp (0 : Real) = 1 := exp_zero
    rw [← hz, log_exp]
  have hnn : (0 : Real) ≤ c + 1 := by
    have u := add_le_add_wit (le_of_lt hc0) (le_of_lt zero_lt_one_ax)
    have l : (0 : Real) + 0 = 0 := by mach_ring
    rw [l] at u; exact u
  have hc1 : log c ≤ c + 1 := by
    rcases lt_total c 1 with hlt | heq | hgt
    · exact le_trans (log_nonpos_of_le_one' (le_of_lt hlt)) hnn
    · rw [heq, hl1]
      have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt zero_lt_one_ax)
      have l : (0 : Real) + 0 = 0 := by mach_ring
      rw [l] at u; exact u
    · refine le_trans (log_le_sub_one_of_one_le (le_of_lt hgt)) ?_
      have u := add_le_add_wit (le_refl c) (le_of_lt (lt_trans_ax
        (by have v := add_lt_add_left zero_lt_one_ax (-1 : Real)
            have l : (-1 : Real) + 0 = -1 := by mach_ring
            have r : (-1 : Real) + 1 = 0 := by mach_ring
            rw [l, r] at v; exact v) zero_lt_one_ax))
      have l : c + -1 = c - 1 := by mach_mpoly [c]
      rw [l] at u; exact u
  intro x h1
  have hlogx : (0 : Real) ≤ log x := by
    have hm := log_le_log zero_lt_one_ax h1; rw [hl1] at hm; exact hm
  rcases lt_total (c - log x) 0 with hneg | heq | hpos
  · rw [log_nonpos (le_of_lt hneg)]; exact hnn
  · rw [heq, log_zero_totalised]; exact hnn
  · refine le_trans (log_le_log hpos ?_) hc1
    have u := add_le_add_wit (le_refl c) (neg_le_neg_wit hlogx)
    have l : c + -log x = c - log x := by mach_mpoly [c, log x]
    have r : c + -(0 : Real) = c := by mach_mpoly [c]
    rw [l, r] at u; exact u

/-- **The log dichotomy.** For a depth-≤1 `B`, `log (B x)` is either bounded above on `[1,∞)` or
unbounded above. -/
theorem depth_le_one_log_bounded_or_unbounded (B : EMLTree) (hB : B.depth ≤ 1) :
    (∃ Λ : Real, ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ Λ)
    ∨ (∀ Λ : Real, ∃ x : Real, 1 ≤ x ∧ Λ < log (B.eval x)) := by
  rcases depth_le_one_classification B hB with
      ⟨β, hb⟩ | hb | ⟨c, hc0, hb⟩ | ⟨d, hb⟩ | hb
  · exact Or.inl ⟨log β, fun x h1 => by
      rw [hb x (lt_of_lt_of_le zero_lt_one_ax h1)]; exact le_refl _⟩
  · refine Or.inr (fun Λ => ?_)
    obtain ⟨x, hx1, hgt⟩ := log_var_unbounded Λ
    exact ⟨x, hx1, by rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)]; exact hgt⟩
  · exact Or.inl ⟨c + 1, fun x h1 => by
      rw [hb x (lt_of_lt_of_le zero_lt_one_ax h1)]; exact log_c_sub_log_cap hc0 x h1⟩
  · refine Or.inr (fun Λ => ?_)
    obtain ⟨x, hx1, hgt⟩ := log_exp_sub_const_unbounded d Λ
    exact ⟨x, hx1, by rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)]; exact hgt⟩
  · refine Or.inr (fun Λ => ?_)
    obtain ⟨x, hx1, hgt⟩ := log_exp_sub_log_unbounded Λ
    exact ⟨x, hx1, by rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)]; exact hgt⟩

/-- **The forms lemma on an arbitrary ray.** Split-A right-branching needs it: `R₂`'s lower bound
holds off a single point, so the ray must start past that point rather than at `1`. -/
theorem depth_le_one_log_bounded_forms_from (B : EMLTree) (hB : B.depth ≤ 1) (S Λ : Real)
    (h : ∀ x : Real, S ≤ x → 1 ≤ x → log (B.eval x) ≤ Λ) :
    (∃ β : Real, ∀ x : Real, 0 < x → B.eval x = β)
    ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → B.eval x = c - log x) := by
  rcases depth_le_one_classification B hB with
      ⟨β, hb⟩ | hb | ⟨c, hc0, hb⟩ | ⟨d, hb⟩ | hb
  · exact Or.inl ⟨β, hb⟩
  · exfalso
    obtain ⟨x, hxS, hx1, hgt⟩ := log_var_unbounded_from S Λ
    have hcap := h x hxS hx1
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)] at hcap
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hcap)
  · exact Or.inr ⟨c, hc0, hb⟩
  · exfalso
    obtain ⟨x, hxS, hx1, hgt⟩ := log_exp_sub_const_unbounded_from S d Λ
    have hcap := h x hxS hx1
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)] at hcap
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hcap)
  · exfalso
    obtain ⟨x, hxS, hx1, hgt⟩ := log_exp_sub_log_unbounded_from S Λ
    have hcap := h x hxS hx1
    rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)] at hcap
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hcap)

/-- **The composable form: a bounded log names the shape.** The dichotomy above says *whether* the
log is bounded; the open cells need to know *which tree* that leaves, and the answer is exactly two
of the five forms. -/
theorem depth_le_one_log_bounded_forms (B : EMLTree) (hB : B.depth ≤ 1) (Λ : Real)
    (h : ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ Λ) :
    (∃ β : Real, ∀ x : Real, 0 < x → B.eval x = β)
    ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → B.eval x = c - log x) :=
  depth_le_one_log_bounded_forms_from B hB 0 Λ (fun x _ hx1 => h x hx1)

/-! ## ▸ The exp side needs the same treatment

`depth_le_one_exp_bounded_or_grows` has the identical defect the log dichotomy had: its bounded
branch says *a bound exists*, not *which tree*. Same fix, applied without a second round trip this
time — the two domination steps become private lemmas, and the structural version is stated
alongside.
-/

/-- `x ≤ exp x − d` once `x ≥ 1 + exp d`. -/
private theorem le_exp_sub_const (d : Real) {x : Real} (hx : 1 + exp d ≤ x) : x ≤ exp x - d := by
  have hx1 : (1 : Real) ≤ x := by
    refine le_trans ?_ hx
    have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos d))
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have hxd : d ≤ x := by
    refine le_trans (le_of_lt (exp_grows_strictly_thm d)) (le_trans ?_ hx)
    have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp d))
    have l : (0 : Real) + exp d = exp d := by mach_mpoly [exp d]
    rw [l] at u; exact u
  have hxx := two_mul_le_exp (le_trans (le_of_lt zero_lt_one_ax) hx1)
  have v := add_le_add_wit hxx (le_refl (-d))
  have r : exp x + -d = exp x - d := by mach_mpoly [exp x, d]
  rw [r] at v
  refine le_trans ?_ v
  have w := add_le_add_wit (le_refl (x + x)) (neg_le_neg_wit hxd)
  have l2 : x + x + -x = x := by mach_mpoly [x]
  rw [l2] at w; exact w

/-- `x ≤ exp x − log x` on `[1,∞)`. -/
private theorem le_exp_sub_log {x : Real} (hx1 : 1 ≤ x) : x ≤ exp x - log x := by
  have hlog : log x ≤ x - 1 := log_le_sub_one_of_one_le hx1
  have hxx := two_mul_le_exp (le_trans (le_of_lt zero_lt_one_ax) hx1)
  have u := add_le_add_wit hxx (neg_le_neg_wit hlog)
  have l : x + x + -(x - 1) = x + 1 := by mach_mpoly [x]
  have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
  rw [l, r] at u
  refine le_trans ?_ u
  have v := add_le_add_wit (le_refl x) (le_of_lt zero_lt_one_ax)
  have l2 : x + (0 : Real) = x := by mach_mpoly [x]
  rw [l2] at v; exact v

/-- **The composable exp version: a bounded exponential names the shape.** Mirror of
`depth_le_one_log_bounded_forms`, and the same two forms survive. -/
theorem depth_le_one_exp_bounded_forms (A : EMLTree) (hA : A.depth ≤ 1) (Kb : Real)
    (h : ∀ x : Real, 1 ≤ x → exp (A.eval x) ≤ Kb) :
    (∃ α : Real, ∀ x : Real, 0 < x → A.eval x = α)
    ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → A.eval x = c - log x) := by
  -- a point past any threshold where `exp x` already exceeds `Kb`
  have hbig : ∀ T : Real, ∃ x : Real, T ≤ x ∧ 1 ≤ x ∧ Kb < exp x := by
    intro T
    obtain ⟨x, hxT, hx1, hlt⟩ := exp_beats_linear_past (α := 0) (β := Kb) (le_refl 0) T
    refine ⟨x, hxT, hx1, ?_⟩
    have l : (0 : Real) * x + Kb = Kb := by mach_mpoly [x, Kb]
    rw [l] at hlt; exact hlt
  rcases depth_le_one_classification A hA with
      ⟨α, ha⟩ | ha | ⟨c, hc0, ha⟩ | ⟨d, ha⟩ | ha
  · exact Or.inl ⟨α, ha⟩
  · exfalso
    obtain ⟨x, _, hx1, hlt⟩ := hbig 1
    have hb := h x hx1
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)] at hb
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hb)
  · exact Or.inr ⟨c, hc0, ha⟩
  · exfalso
    obtain ⟨x, hxT, hx1, hlt⟩ := hbig (1 + exp d)
    have hb := h x hx1
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)] at hb
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlt
      (le_trans (exp_monotone (le_exp_sub_const d hxT)) hb))
  · exfalso
    obtain ⟨x, _, hx1, hlt⟩ := hbig 1
    have hb := h x hx1
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)] at hb
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlt
      (le_trans (exp_monotone (le_exp_sub_log hx1)) hb))

/-! ## ▸ Split-A `q > 1`: assembling the kit

`exp(R₂ x) = exp(K − 1/x) + λ` with `λ > 0`. The argument is now pure assembly:

* `R₂` is **strictly increasing** — `K − 1/x` is, and `exp` preserves and reflects order.
* `R₂` is **bounded**: below by `log λ` (the `+λ` never leaves), above by `log(exp K + λ)`
  (since `K − 1/x < K`).
* Bounded above ⟹ `exp(A x)` is under a line ⟹ `A ∈ {const α, c − log x}`
  (`depth_le_one_exp_bounded_forms`), and both are **non-increasing**.
* Then `log(B x) = exp(A x) − R₂ x` is **strictly decreasing** — a non-increasing term minus a
  strictly increasing one — and bounded, so `B ∈ {const β, c′ − log x}`
  (`depth_le_one_log_bounded_forms`), where `log(B x)` is **eventually constant**.

Strictly decreasing and eventually constant: two points finish it.
-/

private theorem one_div_antitone {x y : Real} (hx : 0 < x) (hxy : x ≤ y) : 1 / y ≤ 1 / x := by
  have hy : (0 : Real) < y := lt_of_lt_of_le hx hxy
  have hix : (0 : Real) < 1 / x := one_div_pos_of_pos hx
  have hiy : (0 : Real) < 1 / y := one_div_pos_of_pos hy
  have hmx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hx)
  have hmy : y * (1 / y) = 1 := mul_inv y (ne_of_gt hy)
  have u := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hxy (le_of_lt hix)) (le_of_lt hiy)
  have l : x * (1 / x) * (1 / y) = 1 * (1 / y) := by rw [hmx]
  have r : y * (1 / x) * (1 / y) = 1 / x * (y * (1 / y)) := by
    mach_mpoly [x, y, (1 / x : Real), (1 / y : Real)]
  rw [l, r, hmy] at u
  have l2 : (1 : Real) * (1 / y) = 1 / y := by mach_mpoly [(1 / y : Real)]
  have r2 : (1 : Real) / x * 1 = 1 / x := by mach_mpoly [(1 / x : Real)]
  rw [l2, r2] at u; exact u

private theorem exp_c_sub_log_eq (c : Real) {x : Real} (hx : 0 < x) :
    exp (c - log x) = exp c * (1 / x) := by
  have e : c - log x = c + -log x := by mach_mpoly [c, log x]
  rw [e, exp_add, exp_neg_inv, exp_log hx]

/-- `exp` reflects strict order. -/
private theorem lt_of_exp_lt {a b : Real} (h : exp a < exp b) : a < b := by
  rcases lt_total a b with hl | he | hg
  · exact hl
  · exfalso; rw [he] at h; exact lt_irrefl_ax _ h
  · exfalso; exact lt_irrefl_ax _ (lt_trans_ax h (exp_lt hg))

/-- **`R₂` is strictly increasing.** -/
private theorem qpos_strict_mono {K lam : Real} {R₂ : EMLTree}
    (h : ∀ x : Real, 0 < x → exp (R₂.eval x) = exp (K - 1 / x) + lam)
    {x y : Real} (hx : 0 < x) (hxy : x < y) : R₂.eval x < R₂.eval y := by
  have hy : (0 : Real) < y := lt_trans_ax hx hxy
  have hiy : 1 / y ≤ 1 / x := one_div_antitone hx (le_of_lt hxy)
  have hne : 1 / y ≠ 1 / x := by
    intro heq
    have hmx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hx)
    have hmy : y * (1 / y) = 1 := mul_inv y (ne_of_gt hy)
    rw [heq] at hmy
    have hcancel : x = y := by
      have hix : (0 : Real) < 1 / x := one_div_pos_of_pos hx
      have hxy2 : x * (1 / x) = y * (1 / x) := hmx.trans hmy.symm
      have hc : (1 / x) * x = (1 / x) * y := by
        rw [mul_comm (1 / x) x, mul_comm (1 / x) y]; exact hxy2
      exact mul_left_cancel (ne_of_gt hix) hc
    rw [hcancel] at hxy; exact lt_irrefl_ax _ hxy
  have hstrict : 1 / y < 1 / x := by
    rcases (le_iff_lt_or_eq (1 / y) (1 / x)).mp hiy with hlt | heq
    · exact hlt
    · exact absurd heq hne
  have harg : K - 1 / x < K - 1 / y := by
    have u := add_lt_add_left hstrict (K - 1 / x - 1 / y)
    have l : K - 1 / x - 1 / y + 1 / y = K - 1 / x := by
      mach_mpoly [K, (1 / x : Real), (1 / y : Real)]
    have r : K - 1 / x - 1 / y + 1 / x = K - 1 / y := by
      mach_mpoly [K, (1 / x : Real), (1 / y : Real)]
    rw [l, r] at u; exact u
  have hexp := exp_lt harg
  have hplus := add_lt_add_left hexp lam
  have l : lam + exp (K - 1 / x) = exp (K - 1 / x) + lam := by
    mach_mpoly [lam, exp (K - 1 / x)]
  have r : lam + exp (K - 1 / y) = exp (K - 1 / y) + lam := by
    mach_mpoly [lam, exp (K - 1 / y)]
  rw [l, r, ← h x hx, ← h y hy] at hplus
  exact lt_of_exp_lt hplus

/-- **Split-A `q > 1` is dead.** `exp(R₂ x) = exp(K − 1/x) + λ` with `λ > 0` makes `R₂` strictly
increasing and bounded; the kit forces `A` and `B` into the two capped forms; and there
`log (B x) = exp (A x) − R₂ x` is strictly decreasing while also eventually constant. -/
theorem split_a_qpos_absurd (K lam : Real) (hlam : 0 < lam) (R₂ : EMLTree) (hd : R₂.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → exp (R₂.eval x) = exp (K - 1 / x) + lam) : False := by
  have hEK : (0 : Real) < exp K + lam := by
    have u := add_lt_add_left hlam (exp K)
    have l : exp K + 0 = exp K := by mach_mpoly [exp K]
    rw [l] at u; exact lt_trans_ax (exp_pos K) u
  -- bounds on `R₂`
  have hlow : ∀ x : Real, 0 < x → log lam < R₂.eval x := by
    intro x hx
    refine lt_of_exp_lt ?_
    rw [exp_log hlam, h x hx]
    have u := add_lt_add_left (exp_pos (K - 1 / x)) lam
    have l : lam + 0 = lam := by mach_mpoly [lam]
    have r : lam + exp (K - 1 / x) = exp (K - 1 / x) + lam := by
      mach_mpoly [lam, exp (K - 1 / x)]
    rw [l, r] at u; exact u
  have hupper : ∀ x : Real, 0 < x → R₂.eval x < log (exp K + lam) := by
    intro x hx
    refine lt_of_exp_lt ?_
    rw [exp_log hEK, h x hx]
    have hargs : K - 1 / x < K := by
      have u := add_lt_add_left (one_div_pos_of_pos hx) (K - 1 / x)
      have l : K - 1 / x + 0 = K - 1 / x := by mach_mpoly [K, (1 / x : Real)]
      have r : K - 1 / x + 1 / x = K := by mach_mpoly [K, (1 / x : Real)]
      rw [l, r] at u; exact u
    have u := add_lt_add_left (exp_lt hargs) lam
    have l : lam + exp (K - 1 / x) = exp (K - 1 / x) + lam := by
      mach_mpoly [lam, exp (K - 1 / x)]
    have r : lam + exp K = exp K + lam := by mach_mpoly [lam, exp K]
    rw [l, r] at u; exact u
  cases R₂ with
  | const q =>
    have h12 : (1 : Real) < 1 + 1 := by
      have u := add_lt_add_left zero_lt_one_ax 1
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact u
    have h1 := qpos_strict_mono h zero_lt_one_ax h12
    have e1 : (EMLTree.const q).eval 1 = q := rfl
    have e2 : (EMLTree.const q).eval (1 + 1) = q := rfl
    rw [e1, e2] at h1; exact lt_irrefl_ax _ h1
  | var =>
    have hM := hupper (exp (log (exp K + lam) + 1)) (exp_pos _)
    have e : (EMLTree.var).eval (exp (log (exp K + lam) + 1))
        = exp (log (exp K + lam) + 1) := rfl
    rw [e] at hM
    have hgt : log (exp K + lam) < exp (log (exp K + lam) + 1) := by
      refine lt_trans_ax ?_ (exp_grows_strictly_thm _)
      have u := add_lt_add_left zero_lt_one_ax (log (exp K + lam))
      have l : log (exp K + lam) + 0 = log (exp K + lam) := by
        mach_mpoly [log (exp K + lam)]
      rw [l] at u; exact u
    exact lt_irrefl_ax _ (lt_trans_ax hgt hM)
  | eml A B =>
    have hA1 : A.depth ≤ 1 := by
      have := Nat.le_max_left A.depth B.depth
      simp only [EMLTree.depth] at hd; omega
    have hB1 : B.depth ≤ 1 := by
      have := Nat.le_max_right A.depth B.depth
      simp only [EMLTree.depth] at hd; omega
    have hev : ∀ x : Real, (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) :=
      fun _ => rfl
    -- `exp (A x)` is bounded: otherwise it dominates `exp x` while sitting under a line
    have hAbnd : ∃ Kb : Real, ∀ x : Real, 1 ≤ x → exp (A.eval x) ≤ Kb := by
      rcases depth_le_one_exp_bounded_or_grows A hA1 with hb | ⟨T, hT⟩
      · exact hb
      · exfalso
        obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB1
        have hα : (0 : Real) ≤ 1 := le_of_lt zero_lt_one_ax
        obtain ⟨x, hxT, hx1, hlt⟩ :=
          exp_beats_linear_past (α := 1) (β := log (exp K + lam) + C) hα T
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        have hval : exp (A.eval x) = (EMLTree.eml A B).eval x + log (B.eval x) := by
          rw [hev]; mach_mpoly [exp (A.eval x), log (B.eval x)]
        have hcap : exp (A.eval x) < log (exp K + lam) + (x + C) := by
          rw [hval]
          have u := add_lt_add_left (hupper x hxpos) (log (B.eval x))
          have v := add_le_add_wit (le_refl (log (exp K + lam))) (hC x hx1)
          have l : log (B.eval x) + (EMLTree.eml A B).eval x
              = (EMLTree.eml A B).eval x + log (B.eval x) := by
            mach_mpoly [log (B.eval x), (EMLTree.eml A B).eval x]
          have r : log (B.eval x) + log (exp K + lam)
              = log (exp K + lam) + log (B.eval x) := by
            mach_mpoly [log (B.eval x), log (exp K + lam)]
          rw [l, r] at u
          exact lt_of_lt_of_le u v
        have hlin : (1 : Real) * x + (log (exp K + lam) + C)
            = log (exp K + lam) + (x + C) := by
          mach_mpoly [x, log (exp K + lam), C]
        rw [hlin] at hlt
        exact lt_irrefl_ax _ (lt_trans_ax (lt_of_lt_of_le hlt (hT x hxT)) hcap)
    obtain ⟨Kb, hKb⟩ := hAbnd
    -- shapes
    have hAform := depth_le_one_exp_bounded_forms A hA1 Kb hKb
    have hlogB : ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ Kb - log lam := by
      intro x hx1
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hval : log (B.eval x) = exp (A.eval x) - (EMLTree.eml A B).eval x := by
        rw [hev]; mach_mpoly [exp (A.eval x), log (B.eval x)]
      rw [hval]
      have u := add_le_add_wit (hKb x hx1) (neg_le_neg_wit (le_of_lt (hlow x hxpos)))
      have l : exp (A.eval x) + -(EMLTree.eml A B).eval x
          = exp (A.eval x) - (EMLTree.eml A B).eval x := by
        mach_mpoly [exp (A.eval x), (EMLTree.eml A B).eval x]
      have r : Kb + -log lam = Kb - log lam := by mach_mpoly [Kb, log lam]
      rw [l, r] at u; exact u
    have hBform := depth_le_one_log_bounded_forms B hB1 (Kb - log lam) hlogB
    -- `exp (A x)` non-increasing on `[1,∞)`
    have hAmono : ∀ x y : Real, 1 ≤ x → x ≤ y → exp (A.eval y) ≤ exp (A.eval x) := by
      intro x y hx1 hxy
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hypos : (0 : Real) < y := lt_of_lt_of_le hxpos hxy
      rcases hAform with ⟨α, ha⟩ | ⟨c, hc0, ha⟩
      · rw [ha x hxpos, ha y hypos]; exact le_refl _
      · rw [ha x hxpos, ha y hypos, exp_c_sub_log_eq c hxpos, exp_c_sub_log_eq c hypos]
        exact mul_le_mul_of_nonneg_left (one_div_antitone hxpos hxy) (le_of_lt (exp_pos c))
    -- `log (B x)` eventually constant
    have hBconst : ∃ T : Real, 1 ≤ T ∧ ∀ x y : Real, T ≤ x → T ≤ y →
        log (B.eval x) = log (B.eval y) := by
      rcases hBform with ⟨β, hb⟩ | ⟨c, hc0, hb⟩
      · exact ⟨1, le_refl 1, fun x y hx hy => by
          rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx), hb y (lt_of_lt_of_le zero_lt_one_ax hy)]⟩
      · refine ⟨1 + exp c, ?_, fun x y hx hy => ?_⟩
        · have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos c))
          have l : (1 : Real) + 0 = 1 := by mach_ring
          rw [l] at u; exact u
        · have hz : ∀ z : Real, 1 + exp c ≤ z → log (B.eval z) = 0 := by
            intro z hz1
            have hzpos : (0 : Real) < z := by
              refine lt_of_lt_of_le zero_lt_one_ax (le_trans ?_ hz1)
              have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos c))
              have l : (1 : Real) + 0 = 1 := by mach_ring
              rw [l] at u; exact u
            rw [hb z hzpos]
            have hec : exp c ≤ z := by
              refine le_trans ?_ hz1
              have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp c))
              have l : (0 : Real) + exp c = exp c := by mach_mpoly [exp c]
              rw [l] at u; exact u
            have hcl : c ≤ log z := by
              have hm := log_le_log (exp_pos c) hec
              rw [log_exp] at hm; exact hm
            have hle : c - log z ≤ 0 := by
              have u := add_le_add_wit hcl (neg_le_neg_wit (le_refl (log z)))
              have l : c + -log z = c - log z := by mach_mpoly [c, log z]
              have r : log z + -log z = 0 := by mach_mpoly [log z]
              rw [l, r] at u; exact u
            rw [log_nonpos hle]
          rw [hz x hx, hz y hy]
    -- the two points
    obtain ⟨T, hT1, hTconst⟩ := hBconst
    have hTpos : (0 : Real) < T := lt_of_lt_of_le zero_lt_one_ax hT1
    have hTT : T < T + 1 := by
      have u := add_lt_add_left zero_lt_one_ax T
      have l : T + 0 = T := by mach_mpoly [T]
      rw [l] at u; exact u
    have heq := hTconst T (T + 1) (le_refl T) (le_of_lt hTT)
    have hval : ∀ z : Real, 0 < z →
        log (B.eval z) = exp (A.eval z) - (EMLTree.eml A B).eval z := by
      intro z _; rw [hev]; mach_mpoly [exp (A.eval z), log (B.eval z)]
    rw [hval T hTpos, hval (T + 1) (lt_trans_ax hTpos hTT)] at heq
    have hAle := hAmono T (T + 1) hT1 (le_of_lt hTT)
    have hRlt := qpos_strict_mono h hTpos hTT
    -- `exp (A (T+1)) − R₂ (T+1) < exp (A T) − R₂ T`, contradicting equality
    have hstrict : exp (A.eval (T + 1)) - (EMLTree.eml A B).eval (T + 1)
        < exp (A.eval T) - (EMLTree.eml A B).eval T := by
      have u := add_lt_add_left hRlt (-(EMLTree.eml A B).eval (T + 1)
        + -(EMLTree.eml A B).eval T)
      have l : -(EMLTree.eml A B).eval (T + 1) + -(EMLTree.eml A B).eval T
          + (EMLTree.eml A B).eval T = -(EMLTree.eml A B).eval (T + 1) := by
        mach_mpoly [(EMLTree.eml A B).eval T, (EMLTree.eml A B).eval (T + 1)]
      have r : -(EMLTree.eml A B).eval (T + 1) + -(EMLTree.eml A B).eval T
          + (EMLTree.eml A B).eval (T + 1) = -(EMLTree.eml A B).eval T := by
        mach_mpoly [(EMLTree.eml A B).eval T, (EMLTree.eml A B).eval (T + 1)]
      rw [l, r] at u
      have step1 := add_le_add_wit hAle (le_refl (-(EMLTree.eml A B).eval (T + 1)))
      have step2 := add_lt_add_left u (exp (A.eval T))
      have v := lt_of_le_of_lt step1 step2
      have l2 : exp (A.eval (T + 1)) + -(EMLTree.eml A B).eval (T + 1)
          = exp (A.eval (T + 1)) - (EMLTree.eml A B).eval (T + 1) := by
        mach_mpoly [exp (A.eval (T + 1)), (EMLTree.eml A B).eval (T + 1)]
      have r2 : exp (A.eval T) + -(EMLTree.eml A B).eval T
          = exp (A.eval T) - (EMLTree.eml A B).eval T := by
        mach_mpoly [exp (A.eval T), (EMLTree.eml A B).eval T]
      rw [l2, r2] at v
      exact v
    rw [heq] at hstrict
    exact lt_irrefl_ax _ hstrict

/-! ## ▸ The `ℓ = var` family at `q > 1`: the fast `A`-forms

Here `exp(R₂ x) = exp(exp x − 1/x) + λ`, which is **not** bounded — so the previous argument does not
port. What survives is an upper bound: `R₂ x ≤ exp x + λ`, because `exp(exp x) + λ ≤ exp(exp x + λ)`.

That caps `exp (A x)` by `exp x + λ + x + C`, which the two **fast** forms break at once: both give
`A x ≥ x + 1` eventually, hence `exp (A x) ≥ 2·exp x`, and `exp x` outruns `λ + x + C`. Only
`A = var` survives, where `exp (A x) = exp x` exactly and the cap is not violated.
-/

/-- `exp x + exp x ≤ exp (x+1)`, since `exp 1 ≥ 2`. -/
private theorem exp_succ_ge_two_mul (x : Real) : exp x + exp x ≤ exp (x + 1) := by
  have he2 : (1 : Real) + 1 ≤ exp 1 := one_add_le_exp 1
  have hm := mul_le_mul_of_nonneg_left he2 (le_of_lt (exp_pos x))
  have l : exp x * (1 + 1) = exp x + exp x := by mach_mpoly [exp x]
  rw [l] at hm
  rw [exp_add]; exact hm

/-- `exp` reflects `≤`. -/
private theorem le_of_exp_le {a b : Real} (h : exp a ≤ exp b) : a ≤ b := by
  rcases lt_total a b with hl | he | hg
  · exact le_of_lt hl
  · exact le_of_eq he
  · exact absurd h (fun hc => lt_irrefl_ax _ (lt_of_lt_of_le (exp_lt hg) hc))

/-- **The `ℓ = var`, `q > 1` cell dies for every fast `A`.** Covers `exp x − d` and `exp x − log x`
in one statement, via the hypothesis they both satisfy: `A x ≥ x + 1` past a threshold. -/
theorem var_family_qpos_A_fast_absurd (lam : Real) (hlam : 0 < lam) (A B : EMLTree)
    (hB : B.depth ≤ 1) (T : Real) (hfast : ∀ x : Real, T ≤ x → x + 1 ≤ A.eval x)
    (h : ∀ x : Real, 1 ≤ x →
      exp (exp (A.eval x) - log (B.eval x)) = exp (exp x - 1 / x) + lam) : False := by
  obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB
  have hα : (0 : Real) ≤ 1 := le_of_lt zero_lt_one_ax
  obtain ⟨x, hxT, hx1, hlt⟩ := exp_beats_linear_past (α := 1) (β := lam + C) hα T
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  -- upper bound on `R₂`
  have hup : exp (A.eval x) - log (B.eval x) ≤ exp x + lam := by
    refine le_of_exp_le ?_
    rw [h x hx1, exp_add]
    have hstep1 : exp (exp x - 1 / x) ≤ exp (exp x) := by
      refine exp_monotone ?_
      have u := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit (le_of_lt (one_div_pos_of_pos hxpos)))
      have l : exp x + -(1 / x) = exp x - 1 / x := by mach_mpoly [exp x, (1 / x : Real)]
      have r : exp x + -(0 : Real) = exp x := by mach_mpoly [exp x]
      rw [l, r] at u; exact u
    have hEE : (1 : Real) ≤ exp (exp x) := by
      have hm := exp_monotone (le_of_lt (exp_pos x)); rw [exp_zero] at hm; exact hm
    have hstep2 : exp (exp x) + lam ≤ exp (exp x) * exp lam := by
      have hl1 : (1 : Real) + lam ≤ exp lam := one_add_le_exp lam
      have hm := mul_le_mul_of_nonneg_left hl1 (le_of_lt (exp_pos (exp x)))
      have l : exp (exp x) * (1 + lam) = exp (exp x) + lam * exp (exp x) := by
        mach_mpoly [exp (exp x), lam]
      rw [l] at hm
      refine le_trans ?_ hm
      have u := add_le_add_wit (le_refl (exp (exp x)))
        (mul_le_mul_of_nonneg_left hEE (le_of_lt hlam))
      have r : lam * 1 = lam := by mach_mpoly [lam]
      rw [r] at u; exact u
    have u := add_le_add_wit hstep1 (le_refl lam)
    exact le_trans u hstep2
  -- lower bound from the fast form
  have hlow : exp x + exp x ≤ exp (A.eval x) :=
    le_trans (exp_succ_ge_two_mul x) (exp_monotone (hfast x hxT))
  -- and the cap `exp (A x) ≤ exp x + lam + (x + C)`
  have hcap : exp (A.eval x) ≤ exp x + lam + (x + C) := by
    have hval : exp (A.eval x)
        = (exp (A.eval x) - log (B.eval x)) + log (B.eval x) := by
      mach_mpoly [exp (A.eval x), log (B.eval x)]
    rw [hval]
    exact add_le_add_wit hup (hC x hx1)
  have hchain : exp x + exp x ≤ exp x + lam + (x + C) := le_trans hlow hcap
  have hlin : (1 : Real) * x + (lam + C) = lam + (x + C) := by mach_mpoly [x, lam, C]
  rw [hlin] at hlt
  -- `exp x ≤ lam + (x + C) < exp x`
  have hfinal : exp x ≤ lam + (x + C) := by
    have u := add_le_add_wit hchain (le_refl (-exp x))
    have l : exp x + exp x + -exp x = exp x := by mach_mpoly [exp x]
    have r : exp x + lam + (x + C) + -exp x = lam + (x + C) := by
      mach_mpoly [exp x, lam, x, C]
    rw [l, r] at u; exact u
  exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hfinal)

/-! ## ▸ `A = var`: the limit argument, done with an explicit inequality

Writing `W := exp(exp x)`, the equation is `W·(exp(−L) − exp(−1/x)) = λ` once `log (B x)` has settled
to a constant `L`. The natural reading is a limit — `exp(−1/x) → 1` forces `L = 0`, then
`1 − exp(−1/x) ≈ 1/x` loses to `W`. Neither step needs a limit:

* `L > 0` dies at a **single point**: `log (B x) < 1/x` always, so `L < 1/x`, false once `x ≥ 1/L`.
* `L ≤ 0` dies by **`one_sub_exp_neg_ge`**: `u·exp(−u) ≤ 1 − exp(−u)`, straight from
  `1 + u ≤ exp u` multiplied by `exp(−u)`. With `u = 1/x` that gives
  `1 − exp(−1/x) ≥ exp(−1)/x` on `[1,∞)`, and `W ≥ exp x` finishes against `exp_beats_linear_past`.
-/

/-- `u·exp(−u) ≤ 1 − exp(−u)`: multiply `1 + u ≤ exp u` by `exp(−u)`. -/
private theorem one_sub_exp_neg_ge (u : Real) : u * exp (-u) ≤ 1 - exp (-u) := by
  have h1 : (1 : Real) + u ≤ exp u := one_add_le_exp u
  have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt (exp_pos (-u)))
  have hone : exp u * exp (-u) = 1 := by
    rw [← exp_add]
    have e : u + -u = 0 := by mach_mpoly [u]
    rw [e, exp_zero]
  rw [hone] at hm
  have l : ((1 : Real) + u) * exp (-u) = exp (-u) + u * exp (-u) := by
    mach_mpoly [u, exp (-u)]
  rw [l] at hm
  have v := add_le_add_wit hm (le_refl (-exp (-u)))
  have l2 : exp (-u) + u * exp (-u) + -exp (-u) = u * exp (-u) := by
    mach_mpoly [u, exp (-u)]
  have r2 : (1 : Real) + -exp (-u) = 1 - exp (-u) := by mach_mpoly [exp (-u)]
  rw [l2, r2] at v; exact v

/-- The `L ≤ 0` half: `exp(−L) ≥ 1`, so the bracket is at least `1 − exp(−1/x) ≥ exp(−1)/x`, and
`exp(exp x) ≥ exp x` makes the product outrun `λ`. -/
private theorem var_family_qpos_L_nonpos (lam : Real) (hlam : 0 < lam) (B : EMLTree)
    (T L : Real) (hT1 : 1 ≤ T) (hL : ∀ x : Real, T ≤ x → log (B.eval x) = L)
    (h : ∀ x : Real, 1 ≤ x → exp (exp x - log (B.eval x)) = exp (exp x - 1 / x) + lam)
    (hLle : L ≤ 0) : False := by
  have hEL : (1 : Real) ≤ exp (-L) := by
    have hnn : (0 : Real) ≤ -L := by
      have u := neg_le_neg_wit hLle
      have l : -(0 : Real) = 0 := by mach_ring
      rw [l] at u; exact u
    have hm := exp_monotone hnn; rw [exp_zero] at hm; exact hm
  have hα : (0 : Real) ≤ lam * exp 1 := le_of_lt (mul_pos hlam (exp_pos 1))
  obtain ⟨x, hxT, hx1, hlt⟩ := exp_beats_linear_past (α := lam * exp 1) (β := 0) hα T
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hix : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hmx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
  -- the equation with `log (B x)` replaced by `L`
  have key := h x hx1
  rw [hL x hxT] at key
  have hsplit1 : exp (exp x - L) = exp (exp x) * exp (-L) := by
    rw [← exp_add]; have e : exp x + -L = exp x - L := by mach_mpoly [exp x, L]
    rw [e]
  have hsplit2 : exp (exp x - 1 / x) = exp (exp x) * exp (-(1 / x)) := by
    rw [← exp_add]
    have e : exp x + -(1 / x) = exp x - 1 / x := by mach_mpoly [exp x, (1 / x : Real)]
    rw [e]
  rw [hsplit1, hsplit2] at key
  -- `lam = exp(exp x) * (exp(-L) - exp(-1/x)) ≥ exp(exp x) * (1/x) * exp(-1)`
  have hbr : (1 / x) * exp (-1 : Real) ≤ exp (-L) - exp (-(1 / x)) := by
    have hstep1 : (1 / x) * exp (-(1 / x)) ≤ 1 - exp (-(1 / x)) := one_sub_exp_neg_ge (1 / x)
    have hle1 : exp (-1 : Real) ≤ exp (-(1 / x)) := by
      refine exp_monotone ?_
      have hx1' : 1 / x ≤ 1 := by
        have u := mul_le_mul_of_nonneg_right hx1 (le_of_lt hix)
        have l : (1 : Real) * (1 / x) = 1 / x := by mach_mpoly [(1 / x : Real)]
        rw [l, hmx] at u; exact u
      have u := neg_le_neg_wit hx1'; exact u
    have hstep0 : (1 / x) * exp (-1 : Real) ≤ (1 / x) * exp (-(1 / x)) :=
      mul_le_mul_of_nonneg_left hle1 (le_of_lt hix)
    have hstep2 : (1 : Real) - exp (-(1 / x)) ≤ exp (-L) - exp (-(1 / x)) := by
      have u := add_le_add_wit hEL (le_refl (-exp (-(1 / x))))
      have l : (1 : Real) + -exp (-(1 / x)) = 1 - exp (-(1 / x)) := by
        mach_mpoly [exp (-(1 / x))]
      have r : exp (-L) + -exp (-(1 / x)) = exp (-L) - exp (-(1 / x)) := by
        mach_mpoly [exp (-L), exp (-(1 / x))]
      rw [l, r] at u; exact u
    exact le_trans (le_trans hstep0 hstep1) hstep2
  have hlamval : lam = exp (exp x) * (exp (-L) - exp (-(1 / x))) := by
    have u : exp (exp x) * exp (-L) + -(exp (exp x) * exp (-(1 / x)))
        = exp (exp x) * exp (-(1 / x)) + lam + -(exp (exp x) * exp (-(1 / x))) := by rw [key]
    have l : exp (exp x) * exp (-L) + -(exp (exp x) * exp (-(1 / x)))
        = exp (exp x) * (exp (-L) - exp (-(1 / x))) := by
      mach_mpoly [exp (exp x), exp (-L), exp (-(1 / x))]
    have r : exp (exp x) * exp (-(1 / x)) + lam + -(exp (exp x) * exp (-(1 / x))) = lam := by
      mach_mpoly [exp (exp x), exp (-(1 / x)), lam]
    rw [l, r] at u; exact u.symm
  have hEE : exp x ≤ exp (exp x) := exp_monotone (le_of_lt (exp_grows_strictly_thm x))
  have hlow : exp x * ((1 / x) * exp (-1 : Real)) ≤ lam := by
    have hblow : (0 : Real) ≤ (1 / x) * exp (-1 : Real) :=
      le_of_lt (mul_pos hix (exp_pos (-1)))
    have s1 : exp x * ((1 / x) * exp (-1 : Real))
        ≤ exp (exp x) * ((1 / x) * exp (-1 : Real)) :=
      mul_le_mul_of_nonneg_right hEE hblow
    have s2 : exp (exp x) * ((1 / x) * exp (-1 : Real))
        ≤ exp (exp x) * (exp (-L) - exp (-(1 / x))) :=
      mul_le_mul_of_nonneg_left hbr (le_of_lt (exp_pos (exp x)))
    rw [hlamval]; exact le_trans s1 s2
  -- multiply by `x * exp 1`
  have hpos : (0 : Real) ≤ x * exp 1 := le_of_lt (mul_pos hxpos (exp_pos 1))
  have hmul := mul_le_mul_of_nonneg_right hlow hpos
  have he1 : exp (-1 : Real) * exp 1 = 1 := by
    rw [← exp_add]; have e : (-1 : Real) + 1 = 0 := by mach_ring
    rw [e, exp_zero]
  have hlhs : exp x * ((1 / x) * exp (-1 : Real)) * (x * exp 1)
      = exp x * (x * (1 / x)) * (exp (-1 : Real) * exp 1) := by
    mach_mpoly [exp x, x, (1 / x : Real), exp (-1 : Real), exp 1]
  rw [hlhs, hmx, he1] at hmul
  have hclean : exp x * 1 * 1 = exp x := by mach_mpoly [exp x]
  rw [hclean] at hmul
  have hrhs : lam * (x * exp 1) = lam * exp 1 * x + 0 := by mach_mpoly [lam, x, exp 1]
  rw [hrhs] at hmul
  exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hmul)

/-- **`A = var` dies too, so the `ℓ = var`, `q > 1` cell is closed.** -/
theorem var_family_qpos_A_var_absurd (lam : Real) (hlam : 0 < lam) (B : EMLTree)
    (hB : B.depth ≤ 1)
    (h : ∀ x : Real, 1 ≤ x → exp (exp x - log (B.eval x)) = exp (exp x - 1 / x) + lam) :
    False := by
  -- `log (B x) < 1/x` on `[1,∞)`
  have hlt : ∀ x : Real, 1 ≤ x → log (B.eval x) < 1 / x := by
    intro x hx1
    have hgt : exp (exp x - 1 / x) < exp (exp x - log (B.eval x)) := by
      rw [h x hx1]
      have u := add_lt_add_left hlam (exp (exp x - 1 / x))
      have l : exp (exp x - 1 / x) + 0 = exp (exp x - 1 / x) := by
        mach_mpoly [exp (exp x - 1 / x)]
      rw [l] at u; exact u
    have hgt2 := lt_of_exp_lt hgt
    have u := add_lt_add_left hgt2 (-exp x + 1 / x + log (B.eval x))
    have l : -exp x + 1 / x + log (B.eval x) + (exp x - 1 / x) = log (B.eval x) := by
      mach_mpoly [exp x, (1 / x : Real), log (B.eval x)]
    have r : -exp x + 1 / x + log (B.eval x) + (exp x - log (B.eval x)) = 1 / x := by
      mach_mpoly [exp x, (1 / x : Real), log (B.eval x)]
    rw [l, r] at u; exact u
  -- so it is bounded above by 1, and the shape follows
  have hbnd : ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ 1 := by
    intro x hx1
    refine le_trans (le_of_lt (hlt x hx1)) ?_
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    have hone : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
    have u := mul_le_mul_of_nonneg_right hx1 (le_of_lt (one_div_pos_of_pos hxpos))
    have l : (1 : Real) * (1 / x) = 1 / x := by mach_mpoly [(1 / x : Real)]
    rw [l, hone] at u; exact u
  -- `log (B x)` settles to a constant `L` past some `T ≥ 1`
  have hsettle : ∃ T L : Real, 1 ≤ T ∧ ∀ x : Real, T ≤ x → log (B.eval x) = L := by
    rcases depth_le_one_log_bounded_forms B hB 1 hbnd with ⟨β, hb⟩ | ⟨c, hc0, hb⟩
    · exact ⟨1, log β, le_refl 1, fun x hx => by
        rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx)]⟩
    · refine ⟨1 + exp c, 0, ?_, fun x hx => ?_⟩
      · have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos c))
        have l : (1 : Real) + 0 = 1 := by mach_ring
        rw [l] at u; exact u
      · have hx1 : (1 : Real) ≤ x := by
          refine le_trans ?_ hx
          have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos c))
          have l : (1 : Real) + 0 = 1 := by mach_ring
          rw [l] at u; exact u
        rw [hb x (lt_of_lt_of_le zero_lt_one_ax hx1)]
        have hec : exp c ≤ x := by
          refine le_trans ?_ hx
          have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp c))
          have l : (0 : Real) + exp c = exp c := by mach_mpoly [exp c]
          rw [l] at u; exact u
        have hcl : c ≤ log x := by
          have hm := log_le_log (exp_pos c) hec; rw [log_exp] at hm; exact hm
        have hle : c - log x ≤ 0 := by
          have u := add_le_add_wit hcl (neg_le_neg_wit (le_refl (log x)))
          have l : c + -log x = c - log x := by mach_mpoly [c, log x]
          have r : log x + -log x = 0 := by mach_mpoly [log x]
          rw [l, r] at u; exact u
        rw [log_nonpos hle]
  obtain ⟨T, L, hT1, hL⟩ := hsettle
  have hTpos : (0 : Real) < T := lt_of_lt_of_le zero_lt_one_ax hT1
  rcases lt_total 0 L with hLpos | hLzero | hLneg
  · -- `L > 0` fails at `x = T + 1/L`
    have hiL : (0 : Real) < 1 / L := one_div_pos_of_pos hLpos
    have hx1 : (1 : Real) ≤ T + 1 / L := by
      refine le_trans hT1 ?_
      have u := add_le_add_wit (le_refl T) (le_of_lt hiL)
      have l : T + 0 = T := by mach_mpoly [T]
      rw [l] at u; exact u
    have hxT : T ≤ T + 1 / L := by
      have u := add_le_add_wit (le_refl T) (le_of_lt hiL)
      have l : T + 0 = T := by mach_mpoly [T]
      rw [l] at u; exact u
    have hge : 1 / L ≤ T + 1 / L := by
      have u := add_le_add_wit (le_of_lt hTpos) (le_refl (1 / L))
      have l : (0 : Real) + 1 / L = 1 / L := by mach_mpoly [(1 / L : Real)]
      rw [l] at u; exact u
    have hsmall : 1 / (T + 1 / L) ≤ L := by
      have hm := one_div_antitone hiL hge
      rw [one_div_one_div_pos hLpos] at hm; exact hm
    have hbad := hlt (T + 1 / L) hx1
    rw [hL (T + 1 / L) hxT] at hbad
    exact lt_irrefl_ax _ (lt_of_lt_of_le hbad hsmall)
  · -- `L = 0`: the `L ≤ 0` argument, with `exp (−L) = 1`
    exact var_family_qpos_L_nonpos lam hlam B T L hT1 hL h (le_of_eq hLzero.symm)
  · exact var_family_qpos_L_nonpos lam hlam B T L hT1 hL h (le_of_lt hLneg)

/-! ## ▸ A depth-2 tree bounded above has a **constant** left child

Every tool above works at `∞`. Split-A right-branching needs one at `0⁺`, and this is it: the two
`A`-forms surviving the `∞` argument are `const α` and `c − log x`, and the second blows up at `0⁺` —
`exp (c − log x) = exp c · (1/x)` against a `log (B x)` that can only reach `E − log x − 1`. A
reciprocal beats a logarithm, so boundedness kills it.

Reusable across all four `(ℓ, ℓ₂)` combinations of split-A right-branching: each supplies exactly
this hypothesis, `R₂` bounded above.
-/

/-- The `0⁺` blowup, at a supplied point. Separating the evaluation from the construction of `t`
keeps both readable; the caller picks `t` large enough that `t·(exp c − 1)` clears `M + E`. -/
private theorem c_sub_log_blowup_at (c M E t : Real) (hE1 : 1 ≤ E) (ht1 : 1 ≤ t)
    (hbig : M + E < t * (exp c - 1)) (B : EMLTree)
    (hEb : ∀ x : Real, 0 < x → x ≤ 1 → B.eval x ≤ E - log x)
    (hbnd : ∀ x : Real, 0 < x → exp c * (1 / x) - log (B.eval x) ≤ M) : False := by
  have htpos : (0 : Real) < t := lt_of_lt_of_le zero_lt_one_ax ht1
  have hxpos : (0 : Real) < 1 / t := one_div_pos_of_pos htpos
  have hmt : t * (1 / t) = 1 := mul_inv t (ne_of_gt htpos)
  have hx1 : 1 / t ≤ 1 := by
    have u := mul_le_mul_of_nonneg_right ht1 (le_of_lt hxpos)
    have l : (1 : Real) * (1 / t) = 1 / t := by mach_mpoly [(1 / t : Real)]
    rw [l, hmt] at u; exact u
  have hinv : 1 / (1 / t) = t := one_div_one_div_pos htpos
  have hlogx : log (1 / t) = -log t := by
    have e : exp (-log t) = 1 / t := by rw [exp_neg_inv, exp_log htpos]
    rw [← e, log_exp]
  have hlogt : (0 : Real) ≤ log t := by
    have hm := log_le_log zero_lt_one_ax ht1
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    rw [hl1] at hm; exact hm
  -- `log (B x) ≤ E + t − 2`
  have hnn : (0 : Real) ≤ E + t - 1 - 1 := by
    have u := add_le_add_wit (add_le_add_wit hE1 ht1) (le_refl (-1 + -1 : Real))
    have l : (1 : Real) + 1 + (-1 + -1) = 0 := by mach_ring
    have r : E + t + (-1 + -1 : Real) = E + t - 1 - 1 := by mach_mpoly [E, t]
    rw [l, r] at u; exact u
  have hBcap : log (B.eval (1 / t)) ≤ E + t - 1 - 1 := by
    have hb := hEb _ hxpos hx1
    rw [hlogx] at hb
    rcases lt_total (B.eval (1 / t)) 0 with hbneg | hbzero | hbpos
    · rw [log_nonpos (le_of_lt hbneg)]; exact hnn
    · rw [hbzero, log_zero_totalised]; exact hnn
    · have hge1 : (1 : Real) ≤ E - -log t := by
        refine le_trans hE1 ?_
        have u := add_le_add_wit (le_refl E) hlogt
        have l : E + 0 = E := by mach_mpoly [E]
        have r : E + log t = E - -log t := by mach_mpoly [E, log t]
        rw [l, r] at u; exact u
      have hchain := le_trans (log_le_log hbpos hb) (log_le_sub_one_of_one_le hge1)
      refine le_trans hchain ?_
      have hlt := log_le_sub_one_of_one_le ht1
      have u := add_le_add_wit (le_refl E) hlt
      have l : E + log t = E - -log t := by mach_mpoly [E, log t]
      have r : E + (t - 1) = E + t - 1 := by mach_mpoly [E, t]
      rw [l, r] at u
      have v := add_le_add_wit u (le_refl (-1 : Real))
      have l2 : E - -log t + -1 = E - -log t - 1 := by mach_mpoly [E, log t]
      have r2 : E + t - 1 + -1 = E + t - 1 - 1 := by mach_mpoly [E, t]
      rw [l2, r2] at v; exact v
  -- `exp c · t − (E + t − 2) ≤ M`
  have hcap := hbnd _ hxpos
  rw [hinv] at hcap
  have hstep : exp c * t - (E + t - 1 - 1) ≤ M := by
    refine le_trans ?_ hcap
    have u := add_le_add_wit (le_refl (exp c * t)) (neg_le_neg_wit hBcap)
    have l : exp c * t + -(E + t - 1 - 1) = exp c * t - (E + t - 1 - 1) := by
      mach_mpoly [exp c, t, E]
    have r : exp c * t + -log (B.eval (1 / t)) = exp c * t - log (B.eval (1 / t)) := by
      mach_mpoly [exp c, t, log (B.eval (1 / t))]
    rw [l, r] at u; exact u
  -- rearrange to `t·(exp c − 1) ≤ M + E`
  have hfinal : t * (exp c - 1) ≤ M + E := by
    have e : exp c * t - (E + t - 1 - 1) = t * (exp c - 1) - E + 1 + 1 := by
      mach_mpoly [exp c, t, E]
    rw [e] at hstep
    have u := add_le_add_wit hstep (le_refl (E - 1 - 1))
    have l : t * (exp c - 1) - E + 1 + 1 + (E - 1 - 1) = t * (exp c - 1) := by
      mach_mpoly [exp c, t, E]
    have r : M + (E - 1 - 1) = M + E - 1 - 1 := by mach_mpoly [M, E]
    rw [l, r] at u
    refine le_trans u ?_
    have v := add_le_add_wit (le_refl (M + E))
      (neg_le_neg_wit (le_of_lt (lt_trans_ax zero_lt_one_ax (lt_one_add_exp 1))))
    have l2 : M + E - 1 - 1 = M + E + -(1 + 1) := by mach_mpoly [M, E]
    rw [l2]
    have w := add_le_add_wit (le_refl (M + E)) (by
      have hnn : (0 : Real) ≤ 1 + 1 := by
        have u2 := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt zero_lt_one_ax)
        have l3 : (0 : Real) + 0 = 0 := by mach_ring
        rw [l3] at u2; exact u2
      have u3 := neg_le_neg_wit hnn
      have l4 : -(0 : Real) = 0 := by mach_ring
      rw [l4] at u3; exact u3 : -((1 : Real) + 1) ≤ 0)
    have r3 : M + E + (0 : Real) = M + E := by mach_mpoly [M, E]
    rw [r3] at w; exact w
  exact lt_irrefl_ax _ (lt_of_lt_of_le hbig hfinal)

/-- **A depth-2 tree bounded above on `(0,∞)` has a constant left child.** -/
theorem depth_le_two_bounded_left_is_const (A B : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (M : Real) (hbnd : ∀ x : Real, 0 < x → exp (A.eval x) - log (B.eval x) ≤ M) :
    ∃ α : Real, ∀ x : Real, 0 < x → A.eval x = α := by
  have hAbnd : ∃ Kb : Real, ∀ x : Real, 1 ≤ x → exp (A.eval x) ≤ Kb := by
    rcases depth_le_one_exp_bounded_or_grows A hA with hb | ⟨T, hT⟩
    · exact hb
    · exfalso
      obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB
      obtain ⟨x, hxT, hx1, hlt⟩ :=
        exp_beats_linear_past (α := 1) (β := M + C) (le_of_lt zero_lt_one_ax) T
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hcap : exp (A.eval x) ≤ M + (x + C) := by
        have hval : exp (A.eval x)
            = (exp (A.eval x) - log (B.eval x)) + log (B.eval x) := by
          mach_mpoly [exp (A.eval x), log (B.eval x)]
        rw [hval]; exact add_le_add_wit (hbnd x hxpos) (hC x hx1)
      have hlin : (1 : Real) * x + (M + C) = M + (x + C) := by mach_mpoly [x, M, C]
      rw [hlin] at hlt
      exact lt_irrefl_ax _ (lt_of_lt_of_le hlt (le_trans (hT x hxT) hcap))
  obtain ⟨Kb, hKb⟩ := hAbnd
  rcases depth_le_one_exp_bounded_forms A hA Kb hKb with hconst | ⟨c, hc0, ha⟩
  · exact hconst
  · exfalso
    obtain ⟨E, hE1, hE⟩ := depth_le_one_upper_log_bound B hB
    have hd : (0 : Real) < exp c - 1 := by
      have h1c : (1 : Real) < exp c := by
        have hm := exp_lt hc0; rw [exp_zero] at hm; exact hm
      have u := add_lt_add_left h1c (-1 : Real)
      have l : (-1 : Real) + 1 = 0 := by mach_ring
      have r : (-1 : Real) + exp c = exp c - 1 := by mach_mpoly [exp c]
      rw [l, r] at u; exact u
    have hid : (0 : Real) < 1 / (exp c - 1) := one_div_pos_of_pos hd
    have hEpos : (0 : Real) < 1 + exp (M + E) := by
      have u := add_lt_add_left (exp_pos (M + E)) 1
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact lt_trans_ax zero_lt_one_ax u
    refine c_sub_log_blowup_at c M E (1 + (1 + exp (M + E)) * (1 / (exp c - 1))) hE1 ?_ ?_ B
      hE (fun x hx => by rw [← exp_c_sub_log_eq c hx, ← ha x hx]; exact hbnd x hx)
    · have u := add_le_add_wit (le_refl (1 : Real))
        (le_of_lt (mul_pos hEpos hid))
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact u
    · have hmul : (exp c - 1) * (1 / (exp c - 1)) = 1 := mul_inv _ (ne_of_gt hd)
      have hexpand : (1 + (1 + exp (M + E)) * (1 / (exp c - 1))) * (exp c - 1)
          = (exp c - 1) + (1 + exp (M + E)) * ((exp c - 1) * (1 / (exp c - 1))) := by
        mach_mpoly [exp c, exp (M + E), (1 / (exp c - 1) : Real)]
      rw [hexpand, hmul]
      have hone : (1 + exp (M + E)) * (1 : Real) = 1 + exp (M + E) := by
        mach_mpoly [exp (M + E)]
      rw [hone]
      have hlt : M + E < 1 + exp (M + E) := lt_one_add_exp (M + E)
      have u := add_lt_add_left hlt (exp c - 1)
      have l : exp c - 1 + (M + E) = M + E + (exp c - 1) := by mach_mpoly [exp c, M, E]
      rw [l] at u
      refine lt_trans_ax ?_ u
      have v := add_lt_add_left hd (M + E)
      have l2 : M + E + 0 = M + E := by mach_mpoly [M, E]
      rw [l2] at v; exact v

/-! ## ▸ Split-A right-branching: the shape step

With `ℓ₂ = const p` the equation is `exp p − log (R₂ x) = exp(K − 1/x)`, so
`log (R₂ x) = exp p − exp(K − 1/x)`: **bounded above by `exp p` and strictly decreasing**. Bounded
above transfers to `R₂` itself (`R₂ x < exp(exp p)`, and trivially so where `R₂ x ≤ 0`), which is
exactly the hypothesis `depth_le_two_bounded_left_is_const` wants.

The leaf cases fall first and differently: `var` to the bound, `const q` to the strict decrease.
-/

/-- **`R₂` must be `exp α − log (B x)` with `α` constant.** The structural step for split-A
right-branching at `ℓ₂ = const p`. -/
theorem split_a_right_const_shape (K p : Real) (R₂ : EMLTree) (hd : R₂.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → exp p - log (R₂.eval x) = exp (K - 1 / x)) :
    ∃ (α : Real) (B : EMLTree), B.depth ≤ 1
      ∧ ∀ x : Real, 0 < x → R₂.eval x = exp α - log (B.eval x) := by
  have hlogR : ∀ x : Real, 0 < x → log (R₂.eval x) = exp p - exp (K - 1 / x) := by
    intro x hx
    have hk := h x hx
    have u : exp p - log (R₂.eval x) + (log (R₂.eval x) - exp (K - 1 / x))
        = exp (K - 1 / x) + (log (R₂.eval x) - exp (K - 1 / x)) := by rw [hk]
    have l : exp p - log (R₂.eval x) + (log (R₂.eval x) - exp (K - 1 / x))
        = exp p - exp (K - 1 / x) := by
      mach_mpoly [exp p, log (R₂.eval x), exp (K - 1 / x)]
    have r : exp (K - 1 / x) + (log (R₂.eval x) - exp (K - 1 / x)) = log (R₂.eval x) := by
      mach_mpoly [log (R₂.eval x), exp (K - 1 / x)]
    rw [l, r] at u; exact u.symm
  -- `R₂` is bounded above by `exp (exp p)`
  have hbnd : ∀ x : Real, 0 < x → R₂.eval x ≤ exp (exp p) := by
    intro x hx
    rcases lt_total (R₂.eval x) 0 with hneg | hzero | hpos
    · exact le_of_lt (lt_trans_ax hneg (exp_pos (exp p)))
    · rw [hzero]; exact le_of_lt (exp_pos (exp p))
    · have hlt : log (R₂.eval x) < exp p := by
        rw [hlogR x hx]
        have u := add_lt_add_left (exp_pos (K - 1 / x)) (exp p - exp (K - 1 / x))
        have l : exp p - exp (K - 1 / x) + 0 = exp p - exp (K - 1 / x) := by
          mach_mpoly [exp p, exp (K - 1 / x)]
        have r : exp p - exp (K - 1 / x) + exp (K - 1 / x) = exp p := by
          mach_mpoly [exp p, exp (K - 1 / x)]
        rw [l, r] at u; exact u
      have hm := exp_lt hlt
      rw [exp_log hpos] at hm; exact le_of_lt hm
  -- strict decrease of `log (R₂ x)`, used only by the `const` leaf case
  have hhalf : (1 : Real) / (1 + 1) < 1 := by
    have h12 : (1 : Real) < 1 + 1 := by
      have u := add_lt_add_left zero_lt_one_ax 1
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact u
    exact div_lt_one_of_pos_lt (lt_trans_ax zero_lt_one_ax h12) h12
  cases R₂ with
  | const q =>
    exfalso
    have e1 : (EMLTree.const q).eval 1 = q := rfl
    have e2 : (EMLTree.const q).eval (1 + 1) = q := rfl
    have h1 := hlogR 1 zero_lt_one_ax
    have h2 := hlogR (1 + 1) (by
      have u := add_lt_add_left zero_lt_one_ax 1
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact lt_trans_ax zero_lt_one_ax u)
    rw [e1] at h1; rw [e2] at h2
    have hone : (1 : Real) / 1 = 1 := by
      have hv := mul_inv (1 : Real) (ne_of_gt zero_lt_one_ax)
      have l : (1 : Real) * (1 / 1) = 1 / 1 := by mach_mpoly [(1 / 1 : Real)]
      rw [l] at hv; exact hv
    rw [hone] at h1
    have harg : K - 1 < K - 1 / (1 + 1) := by
      have u := add_lt_add_left hhalf (K - 1 - 1 / (1 + 1))
      have l : K - 1 - 1 / (1 + 1) + 1 / (1 + 1) = K - 1 := by
        mach_mpoly [K, (1 / (1 + 1) : Real)]
      have r : K - 1 - 1 / (1 + 1) + 1 = K - 1 / (1 + 1) := by
        mach_mpoly [K, (1 / (1 + 1) : Real)]
      rw [l, r] at u; exact u
    have hne := exp_lt harg
    have heq : exp (K - 1) = exp (K - 1 / (1 + 1)) := by
      have u : exp p - exp (K - 1) = exp p - exp (K - 1 / (1 + 1)) := by rw [← h1, h2]
      have v := add_le_add_wit (le_of_eq u) (le_refl (exp (K - 1) + exp (K - 1 / (1 + 1))))
      have l : exp p - exp (K - 1) + (exp (K - 1) + exp (K - 1 / (1 + 1)))
          = exp p + exp (K - 1 / (1 + 1)) := by
        mach_mpoly [exp p, exp (K - 1), exp (K - 1 / (1 + 1))]
      have r : exp p - exp (K - 1 / (1 + 1)) + (exp (K - 1) + exp (K - 1 / (1 + 1)))
          = exp p + exp (K - 1) := by
        mach_mpoly [exp p, exp (K - 1), exp (K - 1 / (1 + 1))]
      rw [l, r] at v
      have u2 : exp p - exp (K - 1 / (1 + 1)) = exp p - exp (K - 1) := u.symm
      have v2 := add_le_add_wit (le_of_eq u2) (le_refl (exp (K - 1) + exp (K - 1 / (1 + 1))))
      rw [r, l] at v2
      have hcancel : exp (K - 1 / (1 + 1)) ≤ exp (K - 1) := by
        have w := add_le_add_wit v (le_refl (-exp p))
        have l3 : exp p + exp (K - 1 / (1 + 1)) + -exp p = exp (K - 1 / (1 + 1)) := by
          mach_mpoly [exp p, exp (K - 1 / (1 + 1))]
        have r3 : exp p + exp (K - 1) + -exp p = exp (K - 1) := by
          mach_mpoly [exp p, exp (K - 1)]
        rw [l3, r3] at w; exact w
      exact absurd hcancel (fun hc => lt_irrefl_ax _ (lt_of_lt_of_le hne hc))
    exact lt_irrefl_ax _ (heq ▸ hne)
  | var =>
    exfalso
    have hbig : (0 : Real) < exp (exp p) + 1 := by
      have u := add_lt_add_left zero_lt_one_ax (exp (exp p))
      have l : exp (exp p) + 0 = exp (exp p) := by mach_mpoly [exp (exp p)]
      rw [l] at u; exact lt_trans_ax (exp_pos (exp p)) u
    have hcap := hbnd (exp (exp p) + 1) hbig
    have e : (EMLTree.var).eval (exp (exp p) + 1) = exp (exp p) + 1 := rfl
    rw [e] at hcap
    have hgt : exp (exp p) < exp (exp p) + 1 := by
      have u := add_lt_add_left zero_lt_one_ax (exp (exp p))
      have l : exp (exp p) + 0 = exp (exp p) := by mach_mpoly [exp (exp p)]
      rw [l] at u; exact u
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hcap)
  | eml A B =>
    have hA1 : A.depth ≤ 1 := by
      have := Nat.le_max_left A.depth B.depth
      simp only [EMLTree.depth] at hd; omega
    have hB1 : B.depth ≤ 1 := by
      have := Nat.le_max_right A.depth B.depth
      simp only [EMLTree.depth] at hd; omega
    obtain ⟨α, hα⟩ := depth_le_two_bounded_left_is_const A B hA1 hB1 (exp (exp p))
      (fun x hx => hbnd x hx)
    exact ⟨α, B, hB1, fun x hx => by
      show exp (A.eval x) - log (B.eval x) = exp α - log (B.eval x)
      rw [hα x hx]⟩

/-! ## ▸ Split-A right-branching, `ℓ₂ = const p`: the finish

`log (R₂ x) = exp p − exp(K − 1/x)` is **strictly decreasing**, so `R₂` is **injective**. And once
`R₂` is bounded below on a ray, `log (B x) = exp α − R₂ x` is bounded above there, so `B`'s shape is
pinned and `log (B x)` is eventually **constant** — making `R₂` eventually constant. Injective and
eventually constant cannot both hold.

The lower bound is the only delicate part: `R₂ x > 0` fails only where `log (R₂ x) = 0`, i.e. at the
single `x` with `1/x = K − p`. Past it — or everywhere, when `K ≤ p` — the totalised `log` cannot be
`0`, so `R₂ x > 0` and the bound follows from `log (R₂ x) > exp p − exp K`.
-/

/-- `R₂` is bounded below by a positive constant on a ray. -/
private theorem right_const_lower (K p : Real) (R₂ : EMLTree)
    (hlogR : ∀ x : Real, 0 < x → log (R₂.eval x) = exp p - exp (K - 1 / x)) :
    ∃ S m : Real, 1 ≤ S ∧ ∀ x : Real, S ≤ x → m ≤ R₂.eval x := by
  -- on the ray, `log (R₂ x) ≠ 0`, hence `R₂ x > 0`, hence the bound
  have hbound : ∀ x : Real, 0 < x → log (R₂.eval x) ≠ 0 →
      exp (exp p - exp K) ≤ R₂.eval x := by
    intro x hx hne
    have hpos : (0 : Real) < R₂.eval x := by
      rcases lt_total (R₂.eval x) 0 with hneg | hzero | hp
      · exact absurd (log_nonpos (le_of_lt hneg)) hne
      · exact absurd (by rw [hzero]; exact log_zero_totalised) hne
      · exact hp
    have hgt : exp p - exp K < log (R₂.eval x) := by
      rw [hlogR x hx]
      have hargs : K - 1 / x < K := by
        have u := add_lt_add_left (one_div_pos_of_pos hx) (K - 1 / x)
        have l : K - 1 / x + 0 = K - 1 / x := by mach_mpoly [K, (1 / x : Real)]
        have r : K - 1 / x + 1 / x = K := by mach_mpoly [K, (1 / x : Real)]
        rw [l, r] at u; exact u
      have hexp := exp_lt hargs
      have u := add_lt_add_left hexp (exp p - exp K - exp (K - 1 / x))
      have l : exp p - exp K - exp (K - 1 / x) + exp (K - 1 / x) = exp p - exp K := by
        mach_mpoly [exp p, exp K, exp (K - 1 / x)]
      have r : exp p - exp K - exp (K - 1 / x) + exp K = exp p - exp (K - 1 / x) := by
        mach_mpoly [exp p, exp K, exp (K - 1 / x)]
      rw [l, r] at u; exact u
    have hm := exp_lt hgt
    rw [exp_log hpos] at hm; exact le_of_lt hm
  rcases lt_total 0 (K - p) with hkp | hkp | hkp
  · -- past `1/(K−p)` the log is strictly negative
    refine ⟨1 + 1 / (K - p), exp (exp p - exp K), ?_, fun x hxS => ?_⟩
    · have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (one_div_pos_of_pos hkp))
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at u; exact u
    · have hx1 : (1 : Real) ≤ x := by
        refine le_trans ?_ hxS
        have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (one_div_pos_of_pos hkp))
        have l : (1 : Real) + 0 = 1 := by mach_ring
        rw [l] at u; exact u
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      refine hbound x hxpos ?_
      -- `1/x < K − p`, so `log (R₂ x) < 0`
      have hxk : (1 : Real) < x * (K - p) := by
        have hinv : (1 / (K - p)) * (K - p) = 1 := by
          have hv := mul_inv (K - p) (ne_of_gt hkp)
          rw [mul_comm] at hv; exact hv
        have u := mul_le_mul_of_nonneg_right hxS (le_of_lt hkp)
        have l : (1 + 1 / (K - p)) * (K - p) = (K - p) + (1 / (K - p)) * (K - p) := by
          mach_mpoly [K, p, (1 / (K - p) : Real)]
        rw [l, hinv] at u
        refine lt_of_lt_of_le ?_ u
        have v := add_lt_add_left hkp (1 : Real)
        have l2 : (1 : Real) + 0 = 1 := by mach_ring
        have r2 : (1 : Real) + (K - p) = K - p + 1 := by mach_mpoly [K, p]
        rw [l2, r2] at v; exact v
      have hlt : 1 / x < K - p := by
        have hix : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
        have hmx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
        have u := mul_lt_mul_of_pos_right hxk hix
        have l : (1 : Real) * (1 / x) = 1 / x := by mach_mpoly [(1 / x : Real)]
        have r : x * (K - p) * (1 / x) = (K - p) * (x * (1 / x)) := by
          mach_mpoly [x, K, p, (1 / x : Real)]
        rw [l, r, hmx] at u
        have r2 : (K - p) * (1 : Real) = K - p := by mach_mpoly [K, p]
        rw [r2] at u; exact u
      have hargs : p < K - 1 / x := by
        have u := add_lt_add_left hlt (K - 1 / x - (K - p))
        have l : K - 1 / x - (K - p) + 1 / x = p := by mach_mpoly [K, p, (1 / x : Real)]
        have r : K - 1 / x - (K - p) + (K - p) = K - 1 / x := by
          mach_mpoly [K, p, (1 / x : Real)]
        rw [l, r] at u; exact u
      rw [hlogR x hxpos]
      intro hz
      have hEq : exp p = exp (K - 1 / x) := by
        have u : exp p - exp (K - 1 / x) + exp (K - 1 / x) = 0 + exp (K - 1 / x) := by rw [hz]
        have l : exp p - exp (K - 1 / x) + exp (K - 1 / x) = exp p := by
          mach_mpoly [exp p, exp (K - 1 / x)]
        have r : (0 : Real) + exp (K - 1 / x) = exp (K - 1 / x) := by
          mach_mpoly [exp (K - 1 / x)]
        rw [l, r] at u; exact u
      exact lt_irrefl_ax _ (hEq ▸ exp_lt hargs)
  · -- `K = p`: the log is strictly positive everywhere
    refine ⟨1, exp (exp p - exp K), le_refl 1, fun x hx1 => ?_⟩
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    refine hbound x hxpos ?_
    rw [hlogR x hxpos]
    have hargs : K - 1 / x < p := by
      have hkp' : K = p := by
        have u : K - p + p = 0 + p := by rw [← hkp]
        have l : K - p + p = K := by mach_mpoly [K, p]
        have r : (0 : Real) + p = p := by mach_mpoly [p]
        rw [l, r] at u; exact u
      rw [← hkp']
      have u := add_lt_add_left (one_div_pos_of_pos hxpos) (K - 1 / x)
      have l : K - 1 / x + 0 = K - 1 / x := by mach_mpoly [K, (1 / x : Real)]
      have r : K - 1 / x + 1 / x = K := by mach_mpoly [K, (1 / x : Real)]
      rw [l, r] at u; exact u
    have hexp := exp_lt hargs
    intro hz
    have hEq : exp p = exp (K - 1 / x) := by
      have u : exp p - exp (K - 1 / x) + exp (K - 1 / x) = 0 + exp (K - 1 / x) := by rw [hz]
      have l : exp p - exp (K - 1 / x) + exp (K - 1 / x) = exp p := by
        mach_mpoly [exp p, exp (K - 1 / x)]
      have r : (0 : Real) + exp (K - 1 / x) = exp (K - 1 / x) := by
        mach_mpoly [exp (K - 1 / x)]
      rw [l, r] at u; exact u
    exact lt_irrefl_ax _ (hEq ▸ hexp)
  · -- `K < p`: same, the log stays strictly positive
    refine ⟨1, exp (exp p - exp K), le_refl 1, fun x hx1 => ?_⟩
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    refine hbound x hxpos ?_
    rw [hlogR x hxpos]
    have hargs : K - 1 / x < p := by
      have hKp : K < p := by
        have u := add_lt_add_left hkp p
        have l : p + (K - p) = K := by mach_mpoly [K, p]
        have r : p + 0 = p := by mach_mpoly [p]
        rw [l, r] at u; exact u
      refine lt_trans_ax ?_ hKp
      have u := add_lt_add_left (one_div_pos_of_pos hxpos) (K - 1 / x)
      have l : K - 1 / x + 0 = K - 1 / x := by mach_mpoly [K, (1 / x : Real)]
      have r : K - 1 / x + 1 / x = K := by mach_mpoly [K, (1 / x : Real)]
      rw [l, r] at u; exact u
    have hexp := exp_lt hargs
    intro hz
    have hEq : exp p = exp (K - 1 / x) := by
      have u : exp p - exp (K - 1 / x) + exp (K - 1 / x) = 0 + exp (K - 1 / x) := by rw [hz]
      have l : exp p - exp (K - 1 / x) + exp (K - 1 / x) = exp p := by
        mach_mpoly [exp p, exp (K - 1 / x)]
      have r : (0 : Real) + exp (K - 1 / x) = exp (K - 1 / x) := by
        mach_mpoly [exp (K - 1 / x)]
      rw [l, r] at u; exact u
    exact lt_irrefl_ax _ (hEq ▸ hexp)

/-- **Split-A right-branching with `ℓ₂ = const p` is dead.** -/
theorem split_a_right_const_absurd (K p : Real) (R₂ : EMLTree) (hd : R₂.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → exp p - log (R₂.eval x) = exp (K - 1 / x)) : False := by
  have hlogR : ∀ x : Real, 0 < x → log (R₂.eval x) = exp p - exp (K - 1 / x) := by
    intro x hx
    have hk := h x hx
    have u : exp p - log (R₂.eval x) + (log (R₂.eval x) - exp (K - 1 / x))
        = exp (K - 1 / x) + (log (R₂.eval x) - exp (K - 1 / x)) := by rw [hk]
    have l : exp p - log (R₂.eval x) + (log (R₂.eval x) - exp (K - 1 / x))
        = exp p - exp (K - 1 / x) := by
      mach_mpoly [exp p, log (R₂.eval x), exp (K - 1 / x)]
    have r : exp (K - 1 / x) + (log (R₂.eval x) - exp (K - 1 / x)) = log (R₂.eval x) := by
      mach_mpoly [log (R₂.eval x), exp (K - 1 / x)]
    rw [l, r] at u; exact u.symm
  obtain ⟨α, B, hB1, hR⟩ := split_a_right_const_shape K p R₂ hd h
  obtain ⟨S, m, hS1, hm⟩ := right_const_lower K p R₂ hlogR
  -- `log (B x) = exp α − R₂ x ≤ exp α − m` on the ray
  have hlogB : ∀ x : Real, S ≤ x → 1 ≤ x → log (B.eval x) ≤ exp α - m := by
    intro x hxS hx1
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    have hval : log (B.eval x) = exp α - R₂.eval x := by
      rw [hR x hxpos]; mach_mpoly [exp α, log (B.eval x)]
    rw [hval]
    have u := add_le_add_wit (le_refl (exp α)) (neg_le_neg_wit (hm x hxS))
    have l : exp α + -R₂.eval x = exp α - R₂.eval x := by
      mach_mpoly [exp α, R₂.eval x]
    have r : exp α + -m = exp α - m := by mach_mpoly [exp α, m]
    rw [l, r] at u; exact u
  -- `log (B x)` is eventually constant
  have hconst : ∃ T : Real, S ≤ T ∧ 1 ≤ T ∧ ∀ y z : Real, T ≤ y → T ≤ z →
      log (B.eval y) = log (B.eval z) := by
    rcases depth_le_one_log_bounded_forms_from B hB1 S (exp α - m) hlogB with
        ⟨β, hb⟩ | ⟨c, hc0, hb⟩
    · exact ⟨S, le_refl S, hS1, fun y z hy hz => by
        rw [hb y (lt_of_lt_of_le zero_lt_one_ax (le_trans hS1 hy)),
            hb z (lt_of_lt_of_le zero_lt_one_ax (le_trans hS1 hz))]⟩
    · refine ⟨S + (1 + exp c), ?_, ?_, fun y z hy hz => ?_⟩
      · have u := add_le_add_wit (le_refl S) (le_of_lt (by
          have v := add_lt_add_left (exp_pos c) 1
          have l : (1 : Real) + 0 = 1 := by mach_ring
          rw [l] at v; exact lt_trans_ax zero_lt_one_ax v))
        have l : S + 0 = S := by mach_mpoly [S]
        rw [l] at u; exact u
      · refine le_trans hS1 ?_
        have u := add_le_add_wit (le_refl S) (le_of_lt (by
          have v := add_lt_add_left (exp_pos c) 1
          have l : (1 : Real) + 0 = 1 := by mach_ring
          rw [l] at v; exact lt_trans_ax zero_lt_one_ax v))
        have l : S + 0 = S := by mach_mpoly [S]
        rw [l] at u; exact u
      · have hz0 : ∀ w : Real, S + (1 + exp c) ≤ w → log (B.eval w) = 0 := by
          intro w hw
          have hw1 : (1 : Real) ≤ w := by
            refine le_trans hS1 (le_trans ?_ hw)
            have u := add_le_add_wit (le_refl S) (le_of_lt (by
              have v := add_lt_add_left (exp_pos c) 1
              have l : (1 : Real) + 0 = 1 := by mach_ring
              rw [l] at v; exact lt_trans_ax zero_lt_one_ax v))
            have l : S + 0 = S := by mach_mpoly [S]
            rw [l] at u; exact u
          rw [hb w (lt_of_lt_of_le zero_lt_one_ax hw1)]
          have hec : exp c ≤ w := by
            refine le_trans ?_ hw
            have u := add_le_add_wit (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hS1))
              (le_of_lt (by
                have v := add_lt_add_left (exp_pos c) 1
                have l : (1 : Real) + 0 = 1 := by mach_ring
                rw [l] at v
                have w2 := add_lt_add_left zero_lt_one_ax (exp c)
                have l2 : exp c + 0 = exp c := by mach_mpoly [exp c]
                have r2 : exp c + 1 = 1 + exp c := by mach_mpoly [exp c]
                rw [l2, r2] at w2; exact w2))
            have l : (0 : Real) + exp c = exp c := by mach_mpoly [exp c]
            rw [l] at u; exact u
          have hcl : c ≤ log w := by
            have hmm := log_le_log (exp_pos c) hec; rw [log_exp] at hmm; exact hmm
          have hle : c - log w ≤ 0 := by
            have u := add_le_add_wit hcl (neg_le_neg_wit (le_refl (log w)))
            have l : c + -log w = c - log w := by mach_mpoly [c, log w]
            have r : log w + -log w = 0 := by mach_mpoly [log w]
            rw [l, r] at u; exact u
          rw [log_nonpos hle]
        rw [hz0 y hy, hz0 z hz]
  obtain ⟨T, hTS, hT1, hTc⟩ := hconst
  have hTpos : (0 : Real) < T := lt_of_lt_of_le zero_lt_one_ax hT1
  have hTT : T < T + 1 := by
    have u := add_lt_add_left zero_lt_one_ax T
    have l : T + 0 = T := by mach_mpoly [T]
    rw [l] at u; exact u
  have hT1pos : (0 : Real) < T + 1 := lt_trans_ax hTpos hTT
  -- `R₂` takes the same value at `T` and `T+1`
  have hsame : R₂.eval T = R₂.eval (T + 1) := by
    rw [hR T hTpos, hR (T + 1) hT1pos, hTc T (T + 1) (le_refl T) (le_of_lt hTT)]
  -- but its log strictly decreases
  have hstrict : 1 / (T + 1) < 1 / T := by
    have hix : (0 : Real) < 1 / T := one_div_pos_of_pos hTpos
    have hxk : (1 : Real) < (T + 1) * (1 / T) := by
      have hmt : T * (1 / T) = 1 := mul_inv T (ne_of_gt hTpos)
      have u := mul_lt_mul_of_pos_right hTT hix
      rw [hmt] at u; exact u
    have hiy : (0 : Real) < 1 / (T + 1) := one_div_pos_of_pos hT1pos
    have u := mul_lt_mul_of_pos_right hxk hiy
    have hmy : (T + 1) * (1 / (T + 1)) = 1 := mul_inv _ (ne_of_gt hT1pos)
    have l : (1 : Real) * (1 / (T + 1)) = 1 / (T + 1) := by
      mach_mpoly [(1 / (T + 1) : Real)]
    have r : (T + 1) * (1 / T) * (1 / (T + 1)) = (1 / T) * ((T + 1) * (1 / (T + 1))) := by
      mach_mpoly [T, (1 / T : Real), (1 / (T + 1) : Real)]
    rw [l, r, hmy] at u
    have r2 : (1 : Real) / T * 1 = 1 / T := by mach_mpoly [(1 / T : Real)]
    rw [r2] at u; exact u
  have hargs : K - 1 / T < K - 1 / (T + 1) := by
    have u := add_lt_add_left hstrict (K - 1 / T - 1 / (T + 1))
    have l : K - 1 / T - 1 / (T + 1) + 1 / (T + 1) = K - 1 / T := by
      mach_mpoly [K, (1 / T : Real), (1 / (T + 1) : Real)]
    have r : K - 1 / T - 1 / (T + 1) + 1 / T = K - 1 / (T + 1) := by
      mach_mpoly [K, (1 / T : Real), (1 / (T + 1) : Real)]
    rw [l, r] at u; exact u
  have hlogdiff : log (R₂.eval (T + 1)) < log (R₂.eval T) := by
    rw [hlogR T hTpos, hlogR (T + 1) hT1pos]
    have hexp := exp_lt hargs
    have u := add_lt_add_left hexp (exp p - exp (K - 1 / T) - exp (K - 1 / (T + 1)))
    have l : exp p - exp (K - 1 / T) - exp (K - 1 / (T + 1)) + exp (K - 1 / T)
        = exp p - exp (K - 1 / (T + 1)) := by
      mach_mpoly [exp p, exp (K - 1 / T), exp (K - 1 / (T + 1))]
    have r : exp p - exp (K - 1 / T) - exp (K - 1 / (T + 1)) + exp (K - 1 / (T + 1))
        = exp p - exp (K - 1 / T) := by
      mach_mpoly [exp p, exp (K - 1 / T), exp (K - 1 / (T + 1))]
    rw [l, r] at u; exact u
  rw [hsame] at hlogdiff
  exact lt_irrefl_ax _ hlogdiff

/-! ## ▸ Split-A right-branching, `ℓ₂ = var`: `R₂` is double-exponential

Here `exp x − log (R₂ x) = exp(K − 1/x)`, so `log (R₂ x) = exp x − exp(K − 1/x)` — and since
`exp(K − 1/x)` lives strictly inside `(0, exp K)`, the log is **sandwiched between `exp x − exp K`
and `exp x`**. Exponentiating, `R₂` sits strictly between `exp(exp x − exp K)` and `exp(exp x)`: a
double exponential up to a bounded factor.

Past `1 + exp K` the log is strictly positive, which is what rules out the totalised branch and lets
the sandwich be stated at all. That threshold is not cosmetic — below it `R₂ x ≤ 0` is not excluded,
since `log (R₂ x) = 0` is then consistent with the equation.
-/

theorem right_var_sandwich (K : Real) (R₂ : EMLTree)
    (h : ∀ x : Real, 0 < x → exp x - log (R₂.eval x) = exp (K - 1 / x)) :
    ∀ x : Real, 1 + exp K ≤ x →
      exp (exp x - exp K) < R₂.eval x ∧ R₂.eval x < exp (exp x) := by
  have hlogR : ∀ x : Real, 0 < x → log (R₂.eval x) = exp x - exp (K - 1 / x) := by
    intro x hx
    have hk := h x hx
    have u : exp x - log (R₂.eval x) + (log (R₂.eval x) - exp (K - 1 / x))
        = exp (K - 1 / x) + (log (R₂.eval x) - exp (K - 1 / x)) := by rw [hk]
    have l : exp x - log (R₂.eval x) + (log (R₂.eval x) - exp (K - 1 / x))
        = exp x - exp (K - 1 / x) := by
      mach_mpoly [exp x, log (R₂.eval x), exp (K - 1 / x)]
    have r : exp (K - 1 / x) + (log (R₂.eval x) - exp (K - 1 / x)) = log (R₂.eval x) := by
      mach_mpoly [log (R₂.eval x), exp (K - 1 / x)]
    rw [l, r] at u; exact u.symm
  intro x hxS
  have hS1 : (1 : Real) ≤ 1 + exp K := by
    have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos K))
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have hx1 : (1 : Real) ≤ x := le_trans hS1 hxS
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  -- `exp K < exp x`, because `K < exp K < 1 + exp K ≤ x`
  have hKx : K < x := by
    refine lt_of_lt_of_le (lt_trans_ax (exp_grows_strictly_thm K) ?_) hxS
    have u := add_lt_add_left (exp_pos K) (0 : Real)
    have l : (0 : Real) + 0 = 0 := by mach_ring
    rw [l] at u
    have v := add_lt_add_left zero_lt_one_ax (exp K)
    have l2 : exp K + 0 = exp K := by mach_mpoly [exp K]
    have r2 : exp K + 1 = 1 + exp K := by mach_mpoly [exp K]
    rw [l2, r2] at v; exact v
  have hEK : exp K < exp x := exp_lt hKx
  -- upper: `exp (K − 1/x) > 0`, so the log is below `exp x`
  have hupper : log (R₂.eval x) < exp x := by
    rw [hlogR x hxpos]
    have u := add_lt_add_left (exp_pos (K - 1 / x)) (exp x - exp (K - 1 / x))
    have l : exp x - exp (K - 1 / x) + 0 = exp x - exp (K - 1 / x) := by
      mach_mpoly [exp x, exp (K - 1 / x)]
    have r : exp x - exp (K - 1 / x) + exp (K - 1 / x) = exp x := by
      mach_mpoly [exp x, exp (K - 1 / x)]
    rw [l, r] at u; exact u
  -- lower: `exp (K − 1/x) < exp K`
  have hlower : exp x - exp K < log (R₂.eval x) := by
    rw [hlogR x hxpos]
    have hargs : K - 1 / x < K := by
      have u := add_lt_add_left (one_div_pos_of_pos hxpos) (K - 1 / x)
      have l : K - 1 / x + 0 = K - 1 / x := by mach_mpoly [K, (1 / x : Real)]
      have r : K - 1 / x + 1 / x = K := by mach_mpoly [K, (1 / x : Real)]
      rw [l, r] at u; exact u
    have hexp := exp_lt hargs
    have u := add_lt_add_left hexp (exp x - exp K - exp (K - 1 / x))
    have l : exp x - exp K - exp (K - 1 / x) + exp (K - 1 / x) = exp x - exp K := by
      mach_mpoly [exp x, exp K, exp (K - 1 / x)]
    have r : exp x - exp K - exp (K - 1 / x) + exp K = exp x - exp (K - 1 / x) := by
      mach_mpoly [exp x, exp K, exp (K - 1 / x)]
    rw [l, r] at u; exact u
  -- the log is strictly positive, so `R₂ x > 0` and the totalised branch is out
  have hlogpos : (0 : Real) < log (R₂.eval x) := by
    refine lt_trans_ax ?_ hlower
    have u := add_lt_add_left hEK (-exp K)
    have l : -exp K + exp K = 0 := by mach_mpoly [exp K]
    have r : -exp K + exp x = exp x - exp K := by mach_mpoly [exp x, exp K]
    rw [l, r] at u; exact u
  have hRpos : (0 : Real) < R₂.eval x := by
    rcases lt_total (R₂.eval x) 0 with hneg | hzero | hp
    · exfalso; rw [log_nonpos (le_of_lt hneg)] at hlogpos
      exact lt_irrefl_ax _ hlogpos
    · exfalso; rw [hzero, log_zero_totalised] at hlogpos
      exact lt_irrefl_ax _ hlogpos
    · exact hp
  refine ⟨?_, ?_⟩
  · have hm := exp_lt hlower; rw [exp_log hRpos] at hm; exact hm
  · have hm := exp_lt hupper; rw [exp_log hRpos] at hm; exact hm

/-! ## ▸ …and the three slow `A`-forms cannot reach it

The sandwich says `R₂` is double-exponential. The three slow forms all satisfy one bound —
**`exp (A x) ≤ exp x + K_A`** (`const α` and `c − log x` because their exponentials are bounded,
`var` because its exponential *is* `exp x`) — and a single exponential plus a constant cannot exceed
`exp(exp x − exp K)`. One lemma covers all three; the fast forms fail the hypothesis, which is
exactly the separation wanted.
-/

theorem right_var_A_slow_absurd (K Cl KA S : Real) (A B : EMLTree)
    (hCl : ∀ x : Real, S ≤ x → Cl ≤ log (B.eval x))
    (hA : ∀ x : Real, 1 ≤ x → exp (A.eval x) ≤ exp x + KA)
    (hsand : ∀ x : Real, S ≤ x → 1 ≤ x →
      exp (exp x - exp K) < exp (A.eval x) - log (B.eval x)) : False := by
  obtain ⟨x, hxS, hx1, hlt⟩ := exp_beats_linear_past
    (α := 1) (β := 1 + exp K + exp (KA - Cl)) (le_of_lt zero_lt_one_ax) S
  have hlin : (1 : Real) * x + (1 + exp K + exp (KA - Cl))
      = x + 1 + exp K + exp (KA - Cl) := by mach_mpoly [x, exp K, exp (KA - Cl)]
  rw [hlin] at hlt
  -- `exp x − exp K ≥ x + 1`
  have hstep : x + 1 ≤ exp x - exp K := by
    have u := add_le_add_wit (le_of_lt hlt) (le_refl (-exp K - exp (KA - Cl)))
    have l : x + 1 + exp K + exp (KA - Cl) + (-exp K - exp (KA - Cl)) = x + 1 := by
      mach_mpoly [x, exp K, exp (KA - Cl)]
    have r : exp x + (-exp K - exp (KA - Cl)) = exp x - exp K - exp (KA - Cl) := by
      mach_mpoly [exp x, exp K, exp (KA - Cl)]
    rw [l, r] at u
    refine le_trans u ?_
    have v := add_le_add_wit (le_refl (exp x - exp K)) (neg_le_neg_wit
      (le_of_lt (exp_pos (KA - Cl))))
    have l2 : exp x - exp K + -exp (KA - Cl) = exp x - exp K - exp (KA - Cl) := by
      mach_mpoly [exp x, exp K, exp (KA - Cl)]
    have r2 : exp x - exp K + -(0 : Real) = exp x - exp K := by
      mach_mpoly [exp x, exp K]
    rw [l2, r2] at v; exact v
  -- so `exp (exp x − exp K) ≥ exp (x+1) ≥ 2·exp x`
  have hbig : exp x + exp x ≤ exp (exp x - exp K) :=
    le_trans (exp_succ_ge_two_mul x) (exp_monotone hstep)
  -- but the sandwich caps it by `exp x + K_A − Cl`
  have hcap : exp (exp x - exp K) < exp x + KA - Cl := by
    refine lt_of_lt_of_le (hsand x hxS hx1) ?_
    have u := add_le_add_wit (hA x hx1) (neg_le_neg_wit (hCl x hxS))
    have l : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
      mach_mpoly [exp (A.eval x), log (B.eval x)]
    have r : exp x + KA + -Cl = exp x + KA - Cl := by mach_mpoly [exp x, KA, Cl]
    rw [l, r] at u; exact u
  -- `exp x < KA − Cl`, yet `exp x > exp (KA − Cl) > KA − Cl`
  have hsmall : exp x < KA - Cl := by
    have u := add_lt_add_left (lt_of_le_of_lt hbig hcap) (-exp x)
    have l : -exp x + (exp x + exp x) = exp x := by mach_mpoly [exp x]
    have r : -exp x + (exp x + KA - Cl) = KA - Cl := by mach_mpoly [exp x, KA, Cl]
    rw [l, r] at u; exact u
  have hgt : KA - Cl < exp x := by
    refine lt_trans_ax (exp_grows_strictly_thm (KA - Cl)) (lt_of_le_of_lt ?_ hlt)
    have hnn : (0 : Real) ≤ x + 1 + exp K := by
      have u := add_le_add_wit (add_le_add_wit
        (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hx1)) (le_of_lt zero_lt_one_ax))
        (le_of_lt (exp_pos K))
      have l : (0 : Real) + 0 + 0 = 0 := by mach_ring
      rw [l] at u; exact u
    exact le_add_left_nonneg hnn
  exact lt_irrefl_ax _ (lt_trans_ax hsmall hgt)

/-! ## ▸ The finisher for both fast `A`-forms

With `A` fast, `exp (A x)` and `R₂ x` are both `exp(exp x)` times a factor, so
`log (B x) = exp(exp x)·(γ(x) − δ(x))`. In every surviving branch that bracket is **negative and at
least `ρ/x` in magnitude** — a constant when `d ≠ exp K`, and `~ρ/x` at the boundary `d = exp K`,
where `one_sub_exp_neg_ge` supplies the rate. Either way `log (B x) ≤ −exp(exp x)·ρ/x`, and
`depth_le_one_log_lower_at_infinity` says `log (B x)` is bounded **below**. `exp(exp x)/x` outruns
any constant.

Stating it with the `ρ/x` shape rather than a constant `ρ` is what lets the boundary case reuse it.
-/

theorem log_le_neg_double_exp_absurd (ρ S : Real) (hρ : 0 < ρ) (B : EMLTree) (hB : B.depth ≤ 1)
    (h : ∀ x : Real, S ≤ x → 1 ≤ x →
      log (B.eval x) ≤ -(exp (exp x) * (ρ * (1 / x)))) : False := by
  obtain ⟨Cl, X₀, hX₀1, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
  have hiρ : (0 : Real) < 1 / ρ := one_div_pos_of_pos hρ
  have hα : (0 : Real) ≤ exp (-Cl) * (1 / ρ) := le_of_lt (mul_pos (exp_pos _) hiρ)
  obtain ⟨x, hxT, hx1, hlt⟩ := exp_beats_linear_past
    (α := exp (-Cl) * (1 / ρ)) (β := 0) hα (exp S + exp X₀)
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hix : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hmx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
  have hmρ : (1 / ρ) * ρ = 1 := by
    have hv := mul_inv ρ (ne_of_gt hρ); rw [mul_comm] at hv; exact hv
  -- the point clears both thresholds
  have hxS : S ≤ x := by
    refine le_of_lt (lt_of_lt_of_le (exp_grows_strictly_thm S) (le_trans ?_ hxT))
    have u := add_le_add_wit (le_refl (exp S)) (le_of_lt (exp_pos X₀))
    have l : exp S + 0 = exp S := by mach_mpoly [exp S]
    rw [l] at u; exact u
  have hxX : X₀ ≤ x := by
    refine le_of_lt (lt_of_lt_of_le (exp_grows_strictly_thm X₀) (le_trans ?_ hxT))
    have u := add_le_add_wit (le_of_lt (exp_pos S)) (le_refl (exp X₀))
    have l : (0 : Real) + exp X₀ = exp X₀ := by mach_mpoly [exp X₀]
    rw [l] at u; exact u
  -- `exp (−Cl) < exp x · (ρ · (1/x))`
  have hlin : exp (-Cl) * (1 / ρ) * x + 0 = exp (-Cl) * (1 / ρ) * x := by
    mach_mpoly [exp (-Cl), (1 / ρ : Real), x]
  rw [hlin] at hlt
  have hscale := mul_lt_mul_of_pos_right hlt (mul_pos hρ hix)
  have hL : exp (-Cl) * (1 / ρ) * x * (ρ * (1 / x))
      = exp (-Cl) * ((1 / ρ) * ρ) * (x * (1 / x)) := by
    mach_mpoly [exp (-Cl), (1 / ρ : Real), x, ρ, (1 / x : Real)]
  rw [hL, hmρ, hmx] at hscale
  have hclean : exp (-Cl) * (1 : Real) * 1 = exp (-Cl) := by mach_mpoly [exp (-Cl)]
  rw [hclean] at hscale
  -- push `exp x` up to `exp (exp x)`
  have hEE : exp x * (ρ * (1 / x)) ≤ exp (exp x) * (ρ * (1 / x)) :=
    mul_le_mul_of_nonneg_right (exp_monotone (le_of_lt (exp_grows_strictly_thm x)))
      (le_of_lt (mul_pos hρ hix))
  have hkey : -Cl < exp (exp x) * (ρ * (1 / x)) :=
    lt_of_lt_of_le (lt_trans_ax (exp_grows_strictly_thm (-Cl)) hscale) hEE
  -- so the cap is strictly below `Cl`, contradicting the lower bound
  have hup := h x hxS hx1
  have hlow := hCl x hxX
  have hbad : Cl < Cl := by
    refine lt_of_le_of_lt (le_trans hlow hup) ?_
    have u := add_lt_add_left hkey (Cl - exp (exp x) * (ρ * (1 / x)))
    have l : Cl - exp (exp x) * (ρ * (1 / x)) + -Cl
        = -(exp (exp x) * (ρ * (1 / x))) := by
      mach_mpoly [Cl, exp (exp x), ρ, (1 / x : Real)]
    have r : Cl - exp (exp x) * (ρ * (1 / x)) + exp (exp x) * (ρ * (1 / x)) = Cl := by
      mach_mpoly [Cl, exp (exp x), ρ, (1 / x : Real)]
    rw [l, r] at u; exact u
  exact lt_irrefl_ax _ hbad

end MachLib