import MachLib.EMLDepth2InvX
import MachLib.EMLNetlistDepth
import MachLib.EMLDepthTameness

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

/-! ## ▸ Instantiating the finishers: the shared conversion

All four fast branches need the same two steps first: `R₂` in closed form on the ray, and
`log (B x)` as `exp(exp x)` times a bracket. Factoring them out means each branch supplies only its
bracket bound.
-/

/-- `R₂` in closed form on the ray, from the sandwich's positivity. -/
theorem right_var_value (K : Real) (R₂ : EMLTree)
    (h : ∀ x : Real, 0 < x → exp x - log (R₂.eval x) = exp (K - 1 / x)) :
    ∀ x : Real, 1 + exp K ≤ x → R₂.eval x = exp (exp x - exp (K - 1 / x)) := by
  intro x hxS
  have hS1 : (1 : Real) ≤ 1 + exp K := by
    have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos K))
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have hx1 : (1 : Real) ≤ x := le_trans hS1 hxS
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  obtain ⟨hlo, _⟩ := right_var_sandwich K R₂ h x hxS
  have hRpos : (0 : Real) < R₂.eval x := lt_trans_ax (exp_pos _) hlo
  have hlogR : log (R₂.eval x) = exp x - exp (K - 1 / x) := by
    have hk := h x hxpos
    have u : exp x - log (R₂.eval x) + (log (R₂.eval x) - exp (K - 1 / x))
        = exp (K - 1 / x) + (log (R₂.eval x) - exp (K - 1 / x)) := by rw [hk]
    have l : exp x - log (R₂.eval x) + (log (R₂.eval x) - exp (K - 1 / x))
        = exp x - exp (K - 1 / x) := by
      mach_mpoly [exp x, log (R₂.eval x), exp (K - 1 / x)]
    have r : exp (K - 1 / x) + (log (R₂.eval x) - exp (K - 1 / x)) = log (R₂.eval x) := by
      mach_mpoly [log (R₂.eval x), exp (K - 1 / x)]
    rw [l, r] at u; exact u.symm
  rw [← hlogR, exp_log hRpos]

/-- `log (B x)` as `exp(exp x)` times a bracket. -/
theorem right_var_logB (K : Real) (A B : EMLTree)
    (h : ∀ x : Real, 0 < x → exp x - log ((EMLTree.eml A B).eval x) = exp (K - 1 / x)) :
    ∀ x : Real, 1 + exp K ≤ x →
      log (B.eval x) = exp (A.eval x) - exp (exp x) * exp (-exp (K - 1 / x)) := by
  intro x hxS
  have hval := right_var_value K (EMLTree.eml A B) h x hxS
  have hev : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  rw [hev] at hval
  have hsplit : exp (exp x - exp (K - 1 / x)) = exp (exp x) * exp (-exp (K - 1 / x)) := by
    rw [← exp_add]
    have e : exp x + -exp (K - 1 / x) = exp x - exp (K - 1 / x) := by
      mach_mpoly [exp x, exp (K - 1 / x)]
    rw [e]
  rw [hsplit] at hval
  have u : exp (A.eval x) - log (B.eval x) + (log (B.eval x)
      - exp (exp x) * exp (-exp (K - 1 / x)))
      = exp (exp x) * exp (-exp (K - 1 / x))
        + (log (B.eval x) - exp (exp x) * exp (-exp (K - 1 / x))) := by rw [hval]
  have l : exp (A.eval x) - log (B.eval x) + (log (B.eval x)
      - exp (exp x) * exp (-exp (K - 1 / x)))
      = exp (A.eval x) - exp (exp x) * exp (-exp (K - 1 / x)) := by
    mach_mpoly [exp (A.eval x), log (B.eval x), exp (exp x), exp (-exp (K - 1 / x))]
  have r : exp (exp x) * exp (-exp (K - 1 / x))
      + (log (B.eval x) - exp (exp x) * exp (-exp (K - 1 / x))) = log (B.eval x) := by
    mach_mpoly [log (B.eval x), exp (exp x), exp (-exp (K - 1 / x))]
  rw [l, r] at u; exact u.symm

/-- Branch `d > exp K`: the bracket is a **negative constant**. -/
theorem right_var_exp_sub_const_gt (K d : Real) (hd : exp K < d) (A B : EMLTree)
    (hB : B.depth ≤ 1) (hA : ∀ x : Real, 0 < x → A.eval x = exp x - d)
    (h : ∀ x : Real, 0 < x → exp x - log ((EMLTree.eml A B).eval x) = exp (K - 1 / x)) :
    False := by
  have hρ : (0 : Real) < exp (-exp K) - exp (-d) := by
    have hn : -d < -exp K := by
      have u := add_lt_add_left hd (-d - exp K)
      have l : -d - exp K + exp K = -d := by mach_mpoly [d, exp K]
      have r : -d - exp K + d = -exp K := by mach_mpoly [d, exp K]
      rw [l, r] at u; exact u
    have hm := exp_lt hn
    have u := add_lt_add_left hm (-exp (-d))
    have l : -exp (-d) + exp (-d) = 0 := by mach_mpoly [exp (-d)]
    have r : -exp (-d) + exp (-exp K) = exp (-exp K) - exp (-d) := by
      mach_mpoly [exp (-d), exp (-exp K)]
    rw [l, r] at u; exact u
  refine log_le_neg_double_exp_absurd (exp (-exp K) - exp (-d)) (1 + exp K) hρ B hB
    (fun x hxS hx1 => ?_)
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  rw [right_var_logB K A B h x hxS, hA x hxpos]
  have hsplitA : exp (exp x - d) = exp (exp x) * exp (-d) := by
    rw [← exp_add]
    have e : exp x + -d = exp x - d := by mach_mpoly [exp x, d]
    rw [e]
  rw [hsplitA]
  -- bracket `≤ −ρ`, and `ρ·(1/x) ≤ ρ`
  have hlt : exp (-exp K) < exp (-exp (K - 1 / x)) := by
    refine exp_lt ?_
    have hargs : K - 1 / x < K := by
      have u := add_lt_add_left (one_div_pos_of_pos hxpos) (K - 1 / x)
      have l : K - 1 / x + 0 = K - 1 / x := by mach_mpoly [K, (1 / x : Real)]
      have r : K - 1 / x + 1 / x = K := by mach_mpoly [K, (1 / x : Real)]
      rw [l, r] at u; exact u
    have hm := exp_lt hargs
    have u := add_lt_add_left hm (-exp (K - 1 / x) - exp K)
    have l : -exp (K - 1 / x) - exp K + exp (K - 1 / x) = -exp K := by
      mach_mpoly [exp (K - 1 / x), exp K]
    have r : -exp (K - 1 / x) - exp K + exp K = -exp (K - 1 / x) := by
      mach_mpoly [exp (K - 1 / x), exp K]
    rw [l, r] at u; exact u
  have hbr : exp (-d) - exp (-exp (K - 1 / x))
      ≤ -((exp (-exp K) - exp (-d)) * (1 / x)) := by
    have hix : 1 / x ≤ 1 := by
      have hmx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
      have u := mul_le_mul_of_nonneg_right hx1 (le_of_lt (one_div_pos_of_pos hxpos))
      have l : (1 : Real) * (1 / x) = 1 / x := by mach_mpoly [(1 / x : Real)]
      rw [l, hmx] at u; exact u
    have hshrink : (exp (-exp K) - exp (-d)) * (1 / x) ≤ exp (-exp K) - exp (-d) := by
      have u := mul_le_mul_of_nonneg_left hix (le_of_lt hρ)
      have l : (exp (-exp K) - exp (-d)) * (1 : Real) = exp (-exp K) - exp (-d) := by
        mach_mpoly [exp (-exp K), exp (-d)]
      rw [l] at u; exact u
    have hneg := neg_le_neg_wit hshrink
    refine le_trans ?_ hneg
    have u := add_le_add_wit (le_refl (exp (-d))) (neg_le_neg_wit (le_of_lt hlt))
    have l : exp (-d) + -exp (-exp (K - 1 / x)) = exp (-d) - exp (-exp (K - 1 / x)) := by
      mach_mpoly [exp (-d), exp (-exp (K - 1 / x))]
    have r : exp (-d) + -exp (-exp K) = -(exp (-exp K) - exp (-d)) := by
      mach_mpoly [exp (-d), exp (-exp K)]
    rw [l, r] at u; exact u
  have hmul := mul_le_mul_of_nonneg_left hbr (le_of_lt (exp_pos (exp x)))
  have l : exp (exp x) * (exp (-d) - exp (-exp (K - 1 / x)))
      = exp (exp x) * exp (-d) - exp (exp x) * exp (-exp (K - 1 / x)) := by
    mach_mpoly [exp (exp x), exp (-d), exp (-exp (K - 1 / x))]
  have r : exp (exp x) * -((exp (-exp K) - exp (-d)) * (1 / x))
      = -(exp (exp x) * ((exp (-exp K) - exp (-d)) * (1 / x))) := by
    mach_mpoly [exp (exp x), exp (-exp K), exp (-d), (1 / x : Real)]
  rw [l, r] at hmul; exact hmul

/-- Branch `A = exp x − log x`: the bracket `1/x − exp(−exp(K−1/x))` also settles to a **negative
constant**, once `1/x` is pushed below `exp(−exp K)`. Ray start `1 + exp K + 2·exp(exp K)`. -/
theorem right_var_exp_sub_log (K : Real) (A B : EMLTree) (hB : B.depth ≤ 1)
    (hA : ∀ x : Real, 0 < x → A.eval x = exp x - log x)
    (h : ∀ x : Real, 0 < x → exp x - log ((EMLTree.eml A B).eval x) = exp (K - 1 / x)) :
    False := by
  have hEE : exp (exp K) * exp (-exp K) = 1 := by
    rw [← exp_add]
    have e : exp K + -exp K = 0 := by mach_mpoly [exp K]
    rw [e, exp_zero]
  refine log_le_neg_double_exp_absurd 1 (1 + exp K + (1 + 1) * exp (exp K))
    zero_lt_one_ax B hB (fun x hxS hx1 => ?_)
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hix : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hmx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
  -- the ray also clears `1 + exp K`, which `right_var_logB` needs
  have hxK : 1 + exp K ≤ x := by
    refine le_trans ?_ hxS
    have u := add_le_add_wit (le_refl (1 + exp K))
      (le_of_lt (mul_pos (lt_trans_ax zero_lt_one_ax (by
        have v := add_lt_add_left zero_lt_one_ax 1
        have l : (1 : Real) + 0 = 1 := by mach_ring
        rw [l] at v; exact v)) (exp_pos (exp K))))
    have l : (1 : Real) + exp K + 0 = 1 + exp K := by mach_mpoly [exp K]
    rw [l] at u; exact u
  rw [right_var_logB K A B h x hxK, hA x hxpos]
  have hsplitA : exp (exp x - log x) = exp (exp x) * (1 / x) := by
    have e : exp x - log x = exp x + -log x := by mach_mpoly [exp x, log x]
    rw [e, exp_add, exp_neg_inv, exp_log hxpos]
  rw [hsplitA]
  -- `(1/x) + (1/x) ≤ exp (−exp K)`
  have hxbig : (1 + 1) * exp (exp K) ≤ x := by
    refine le_trans ?_ hxS
    have u := add_le_add_wit (le_of_lt (lt_of_lt_of_le zero_lt_one_ax
      (by have v := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos K))
          have l : (1 : Real) + 0 = 1 := by mach_ring
          rw [l] at v; exact v))) (le_refl ((1 + 1) * exp (exp K)))
    have l : (0 : Real) + (1 + 1) * exp (exp K) = (1 + 1) * exp (exp K) := by
      mach_mpoly [exp (exp K)]
    rw [l] at u; exact u
  have hkey : (1 / x) + (1 / x) ≤ exp (-exp K) := by
    have u := mul_le_mul_of_nonneg_right hxbig (le_of_lt (mul_pos hix (exp_pos (-exp K))))
    have l : (1 + 1) * exp (exp K) * ((1 / x) * exp (-exp K))
        = (1 + 1) * (1 / x) * (exp (exp K) * exp (-exp K)) := by
      mach_mpoly [exp (exp K), (1 / x : Real), exp (-exp K)]
    have r : x * ((1 / x) * exp (-exp K)) = (x * (1 / x)) * exp (-exp K) := by
      mach_mpoly [x, (1 / x : Real), exp (-exp K)]
    rw [l, r, hEE, hmx] at u
    have l2 : (1 + 1) * (1 / x) * (1 : Real) = 1 / x + 1 / x := by
      mach_mpoly [(1 / x : Real)]
    have r2 : (1 : Real) * exp (-exp K) = exp (-exp K) := by mach_mpoly [exp (-exp K)]
    rw [l2, r2] at u; exact u
  -- bracket `≤ −(1·(1/x))`
  have hlt : exp (-exp K) < exp (-exp (K - 1 / x)) := by
    refine exp_lt ?_
    have hargs : K - 1 / x < K := by
      have u := add_lt_add_left hix (K - 1 / x)
      have l : K - 1 / x + 0 = K - 1 / x := by mach_mpoly [K, (1 / x : Real)]
      have r : K - 1 / x + 1 / x = K := by mach_mpoly [K, (1 / x : Real)]
      rw [l, r] at u; exact u
    have hm := exp_lt hargs
    have u := add_lt_add_left hm (-exp (K - 1 / x) - exp K)
    have l : -exp (K - 1 / x) - exp K + exp (K - 1 / x) = -exp K := by
      mach_mpoly [exp (K - 1 / x), exp K]
    have r : -exp (K - 1 / x) - exp K + exp K = -exp (K - 1 / x) := by
      mach_mpoly [exp (K - 1 / x), exp K]
    rw [l, r] at u; exact u
  have hbr : (1 / x) - exp (-exp (K - 1 / x)) ≤ -((1 : Real) * (1 / x)) := by
    have u := add_le_add_wit (le_refl (1 / x : Real)) (neg_le_neg_wit (le_of_lt hlt))
    have l : (1 : Real) / x + -exp (-exp (K - 1 / x))
        = 1 / x - exp (-exp (K - 1 / x)) := by
      mach_mpoly [(1 / x : Real), exp (-exp (K - 1 / x))]
    rw [l] at u
    refine le_trans u ?_
    have v := add_le_add_wit (le_refl (1 / x : Real)) (neg_le_neg_wit hkey)
    have l2 : (1 : Real) / x + -(1 / x + 1 / x) = -(1 * (1 / x)) := by
      mach_mpoly [(1 / x : Real)]
    rw [l2] at v; exact v
  have hmul := mul_le_mul_of_nonneg_left hbr (le_of_lt (exp_pos (exp x)))
  have l : exp (exp x) * ((1 / x) - exp (-exp (K - 1 / x)))
      = exp (exp x) * (1 / x) - exp (exp x) * exp (-exp (K - 1 / x)) := by
    mach_mpoly [exp (exp x), (1 / x : Real), exp (-exp (K - 1 / x))]
  have r : exp (exp x) * -((1 : Real) * (1 / x))
      = -(exp (exp x) * (1 * (1 / x))) := by
    mach_mpoly [exp (exp x), (1 / x : Real)]
  rw [l, r] at hmul; exact hmul

/-- Branch `d = exp K`: the bracket vanishes in the limit, so a **rate** is needed.
`exp(−exp(K−1/x)) = exp(−exp K)·exp u` with `u = exp K·(1 − exp(−1/x)) ≥ exp K·exp(−1)·(1/x)`, and
`exp u ≥ 1 + u` turns that into the `ρ/x` shape the first finisher wants. -/
theorem right_var_exp_sub_const_eq (K : Real) (A B : EMLTree) (hB : B.depth ≤ 1)
    (hA : ∀ x : Real, 0 < x → A.eval x = exp x - exp K)
    (h : ∀ x : Real, 0 < x → exp x - log ((EMLTree.eml A B).eval x) = exp (K - 1 / x)) :
    False := by
  have hρ : (0 : Real) < exp (-exp K) * (exp K * exp (-1 : Real)) :=
    mul_pos (exp_pos _) (mul_pos (exp_pos K) (exp_pos _))
  refine log_le_neg_double_exp_absurd (exp (-exp K) * (exp K * exp (-1 : Real)))
    (1 + exp K) hρ B hB (fun x hxS hx1 => ?_)
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hix : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hmx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
  rw [right_var_logB K A B h x hxS, hA x hxpos]
  have hsplitA : exp (exp x - exp K) = exp (exp x) * exp (-exp K) := by
    have e : exp x - exp K = exp x + -exp K := by mach_mpoly [exp x, exp K]
    rw [e, exp_add]
  rw [hsplitA]
  -- `u := exp K − exp (K − 1/x)`, and `exp (−exp (K−1/x)) = exp (−exp K) · exp u`
  have hKsplit : exp (K - 1 / x) = exp K * exp (-(1 / x)) := by
    have e : K - 1 / x = K + -(1 / x) := by mach_mpoly [K, (1 / x : Real)]
    rw [e, exp_add]
  have hushape : -exp (K - 1 / x) = -exp K + (exp K - exp (K - 1 / x)) := by
    mach_mpoly [exp K, exp (K - 1 / x)]
  have hexpu : exp (-exp (K - 1 / x))
      = exp (-exp K) * exp (exp K - exp (K - 1 / x)) := by
    rw [hushape, exp_add]
  -- `u ≥ exp K · exp (−1) · (1/x)`
  have hxinv1 : exp (-1 : Real) ≤ exp (-(1 / x)) := by
    refine exp_monotone ?_
    have hle : 1 / x ≤ 1 := by
      have u := mul_le_mul_of_nonneg_right hx1 (le_of_lt hix)
      have l : (1 : Real) * (1 / x) = 1 / x := by mach_mpoly [(1 / x : Real)]
      rw [l, hmx] at u; exact u
    exact neg_le_neg_wit hle
  have hulow : exp K * (exp (-1 : Real) * (1 / x)) ≤ exp K - exp (K - 1 / x) := by
    have hstep : (1 / x) * exp (-(1 / x)) ≤ 1 - exp (-(1 / x)) := one_sub_exp_neg_ge (1 / x)
    have hstep0 : (1 / x) * exp (-1 : Real) ≤ (1 / x) * exp (-(1 / x)) :=
      mul_le_mul_of_nonneg_left hxinv1 (le_of_lt hix)
    have hchain := le_trans hstep0 hstep
    have hmul := mul_le_mul_of_nonneg_left hchain (le_of_lt (exp_pos K))
    have l : exp K * ((1 / x) * exp (-1 : Real)) = exp K * (exp (-1 : Real) * (1 / x)) := by
      mach_mpoly [exp K, (1 / x : Real), exp (-1 : Real)]
    have r : exp K * (1 - exp (-(1 / x))) = exp K - exp K * exp (-(1 / x)) := by
      mach_mpoly [exp K, exp (-(1 / x))]
    rw [l, r, ← hKsplit] at hmul; exact hmul
  -- `exp u ≥ 1 + u`, so the bracket is at most `−exp(−exp K)·u`
  have hexpge : (1 : Real) + (exp K - exp (K - 1 / x))
      ≤ exp (exp K - exp (K - 1 / x)) := one_add_le_exp _
  have hbr : exp (-exp K) - exp (-exp (K - 1 / x))
      ≤ -(exp (-exp K) * (exp K * exp (-1 : Real)) * (1 / x)) := by
    rw [hexpu]
    have hm := mul_le_mul_of_nonneg_left hexpge (le_of_lt (exp_pos (-exp K)))
    have l : exp (-exp K) * (1 + (exp K - exp (K - 1 / x)))
        = exp (-exp K) + exp (-exp K) * (exp K - exp (K - 1 / x)) := by
      mach_mpoly [exp (-exp K), exp K, exp (K - 1 / x)]
    rw [l] at hm
    -- so `exp(−exp K) − exp(−exp K)·exp u ≤ −exp(−exp K)·u`
    have hstep1 : exp (-exp K) - exp (-exp K) * exp (exp K - exp (K - 1 / x))
        ≤ -(exp (-exp K) * (exp K - exp (K - 1 / x))) := by
      have u := add_le_add_wit (le_refl (exp (-exp K))) (neg_le_neg_wit hm)
      have l2 : exp (-exp K) + -(exp (-exp K) + exp (-exp K)
          * (exp K - exp (K - 1 / x)))
          = -(exp (-exp K) * (exp K - exp (K - 1 / x))) := by
        mach_mpoly [exp (-exp K), exp K, exp (K - 1 / x)]
      have r2 : exp (-exp K) + -(exp (-exp K)
          * exp (exp K - exp (K - 1 / x)))
          = exp (-exp K) - exp (-exp K) * exp (exp K - exp (K - 1 / x)) := by
        mach_mpoly [exp (-exp K), exp (exp K - exp (K - 1 / x))]
      rw [l2, r2] at u; exact u
    refine le_trans hstep1 ?_
    have hm2 := mul_le_mul_of_nonneg_left hulow (le_of_lt (exp_pos (-exp K)))
    have hneg := neg_le_neg_wit hm2
    refine le_trans hneg ?_
    have e : exp (-exp K) * (exp K * (exp (-1 : Real) * (1 / x)))
        = exp (-exp K) * (exp K * exp (-1 : Real)) * (1 / x) := by
      mach_mpoly [exp (-exp K), exp K, exp (-1 : Real), (1 / x : Real)]
    rw [e]; exact le_refl _
  have hmul := mul_le_mul_of_nonneg_left hbr (le_of_lt (exp_pos (exp x)))
  have l : exp (exp x) * (exp (-exp K) - exp (-exp (K - 1 / x)))
      = exp (exp x) * exp (-exp K) - exp (exp x) * exp (-exp (K - 1 / x)) := by
    mach_mpoly [exp (exp x), exp (-exp K), exp (-exp (K - 1 / x))]
  have r : exp (exp x) * -(exp (-exp K) * (exp K * exp (-1 : Real)) * (1 / x))
      = -(exp (exp x) * (exp (-exp K) * (exp K * exp (-1 : Real)) * (1 / x))) := by
    mach_mpoly [exp (exp x), exp (-exp K), exp K, exp (-1 : Real), (1 / x : Real)]
  rw [l, r] at hmul; exact hmul

/-- Branch `d < exp K`: the bracket is a **positive constant** on a ray, so `log (B x)` runs to
`+∞` and the *mirror* finisher applies. The ray start avoids splitting on the sign of `d`:
`exp K − exp(K − 1/S) ≤ exp K·(1/S)` by `one_sub_exp_neg_le`, so `S = 1 + exp K·(1/(exp K − d))`
already forces `d < exp(K − 1/S)`. -/
theorem right_var_exp_sub_const_lt (K d : Real) (hd : d < exp K) (A B : EMLTree)
    (hB : B.depth ≤ 1) (hA : ∀ x : Real, 0 < x → A.eval x = exp x - d)
    (h : ∀ x : Real, 0 < x → exp x - log ((EMLTree.eml A B).eval x) = exp (K - 1 / x)) :
    False := by
  have hδ : (0 : Real) < exp K - d := by
    have u := add_lt_add_left hd (-d)
    have l : -d + d = 0 := by mach_mpoly [d]
    have r : -d + exp K = exp K - d := by mach_mpoly [d, exp K]
    rw [l, r] at u; exact u
  have hiδ : (0 : Real) < 1 / (exp K - d) := one_div_pos_of_pos hδ
  have hmδ : (exp K - d) * (1 / (exp K - d)) = 1 := mul_inv _ (ne_of_gt hδ)
  have hS1 : (1 : Real) ≤ 1 + exp K * (1 / (exp K - d)) := by
    have u := add_le_add_wit (le_refl (1 : Real))
      (le_of_lt (mul_pos (exp_pos K) hiδ))
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have hSpos : (0 : Real) < 1 + exp K * (1 / (exp K - d)) :=
    lt_of_lt_of_le zero_lt_one_ax hS1
  have hiS : (0 : Real) < 1 / (1 + exp K * (1 / (exp K - d))) := one_div_pos_of_pos hSpos
  have hmS : (1 + exp K * (1 / (exp K - d)))
      * (1 / (1 + exp K * (1 / (exp K - d)))) = 1 := mul_inv _ (ne_of_gt hSpos)
  -- `exp K · (1/S) < exp K − d`
  have hδS : exp K * (1 / (1 + exp K * (1 / (exp K - d)))) < exp K - d := by
    have hprod : exp K < (exp K - d) * (1 + exp K * (1 / (exp K - d))) := by
      have e : (exp K - d) * (1 + exp K * (1 / (exp K - d)))
          = (exp K - d) + exp K * ((exp K - d) * (1 / (exp K - d))) := by
        mach_mpoly [exp K, d, (1 / (exp K - d) : Real)]
      rw [e, hmδ]
      have hone : exp K * (1 : Real) = exp K := by mach_mpoly [exp K]
      rw [hone]
      have u := add_lt_add_left hδ (exp K)
      have l : exp K + 0 = exp K := by mach_mpoly [exp K]
      have r : exp K + (exp K - d) = exp K - d + exp K := by mach_mpoly [exp K, d]
      rw [l, r] at u; exact u
    have u := mul_lt_mul_of_pos_right hprod hiS
    have l : (exp K - d) * (1 + exp K * (1 / (exp K - d)))
        * (1 / (1 + exp K * (1 / (exp K - d))))
        = (exp K - d) * ((1 + exp K * (1 / (exp K - d)))
          * (1 / (1 + exp K * (1 / (exp K - d))))) := by
      mach_mpoly [exp K, d, (1 / (exp K - d) : Real),
        (1 / (1 + exp K * (1 / (exp K - d))) : Real)]
    rw [l, hmS] at u
    have r : (exp K - d) * (1 : Real) = exp K - d := by mach_mpoly [exp K, d]
    rw [r] at u; exact u
  -- `d < exp (K − 1/S)`
  have hKS : d < exp (K - 1 / (1 + exp K * (1 / (exp K - d)))) := by
    have hsplit : exp (K - 1 / (1 + exp K * (1 / (exp K - d))))
        = exp K * exp (-(1 / (1 + exp K * (1 / (exp K - d))))) := by
      have e : K - 1 / (1 + exp K * (1 / (exp K - d)))
          = K + -(1 / (1 + exp K * (1 / (exp K - d)))) := by
        mach_mpoly [K, (1 / (1 + exp K * (1 / (exp K - d))) : Real)]
      rw [e, exp_add]
    rw [hsplit]
    have hge : (1 : Real) - 1 / (1 + exp K * (1 / (exp K - d)))
        ≤ exp (-(1 / (1 + exp K * (1 / (exp K - d))))) := by
      have hu := one_add_le_exp (-(1 / (1 + exp K * (1 / (exp K - d)))))
      have l : (1 : Real) + -(1 / (1 + exp K * (1 / (exp K - d))))
          = 1 - 1 / (1 + exp K * (1 / (exp K - d))) := by
        mach_mpoly [(1 / (1 + exp K * (1 / (exp K - d))) : Real)]
      rw [l] at hu; exact hu
    have hm := mul_le_mul_of_nonneg_left hge (le_of_lt (exp_pos K))
    refine lt_of_lt_of_le ?_ hm
    have e : exp K * (1 - 1 / (1 + exp K * (1 / (exp K - d))))
        = exp K - exp K * (1 / (1 + exp K * (1 / (exp K - d)))) := by
      mach_mpoly [exp K, (1 / (1 + exp K * (1 / (exp K - d))) : Real)]
    rw [e]
    have u := add_lt_add_left hδS (exp K - (exp K - d)
      - exp K * (1 / (1 + exp K * (1 / (exp K - d)))))
    have l : exp K - (exp K - d) - exp K * (1 / (1 + exp K * (1 / (exp K - d))))
        + exp K * (1 / (1 + exp K * (1 / (exp K - d)))) = d := by
      mach_mpoly [exp K, d, (1 / (1 + exp K * (1 / (exp K - d))) : Real)]
    have r : exp K - (exp K - d) - exp K * (1 / (1 + exp K * (1 / (exp K - d))))
        + (exp K - d) = exp K - exp K * (1 / (1 + exp K * (1 / (exp K - d)))) := by
      mach_mpoly [exp K, d, (1 / (1 + exp K * (1 / (exp K - d))) : Real)]
    rw [l, r] at u; exact u
  -- the bracket is at least `ε` on the ray
  have hε : (0 : Real) < exp (-d)
      - exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d))))) := by
    have hn : -exp (K - 1 / (1 + exp K * (1 / (exp K - d)))) < -d := by
      have u := add_lt_add_left hKS
        (-d - exp (K - 1 / (1 + exp K * (1 / (exp K - d)))))
      have l : -d - exp (K - 1 / (1 + exp K * (1 / (exp K - d)))) + d
          = -exp (K - 1 / (1 + exp K * (1 / (exp K - d)))) := by
        mach_mpoly [d, exp (K - 1 / (1 + exp K * (1 / (exp K - d))))]
      have r : -d - exp (K - 1 / (1 + exp K * (1 / (exp K - d))))
          + exp (K - 1 / (1 + exp K * (1 / (exp K - d)))) = -d := by
        mach_mpoly [d, exp (K - 1 / (1 + exp K * (1 / (exp K - d))))]
      rw [l, r] at u; exact u
    have hm := exp_lt hn
    have u := add_lt_add_left hm
      (-exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d))))))
    have l : -exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d)))))
        + exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d))))) = 0 := by
      mach_mpoly [exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d)))))]
    have r : -exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d))))) + exp (-d)
        = exp (-d) - exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d))))) := by
      mach_mpoly [exp (-d), exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d)))))]
    rw [l, r] at u; exact u
  refine log_ge_double_exp_const_absurd
    (exp (-d) - exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d))))))
    (1 + exp K * (1 / (exp K - d)) + (1 + exp K)) hε B hB (fun x hxS hx1 => ?_)
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hxK : 1 + exp K ≤ x := by
    refine le_trans ?_ hxS
    have u := add_le_add_wit (le_of_lt hSpos) (le_refl (1 + exp K))
    have l : (0 : Real) + (1 + exp K) = 1 + exp K := by mach_mpoly [exp K]
    rw [l] at u; exact u
  have hxS' : 1 + exp K * (1 / (exp K - d)) ≤ x := by
    refine le_trans ?_ hxS
    have u := add_le_add_wit (le_refl (1 + exp K * (1 / (exp K - d))))
      (le_of_lt (lt_of_lt_of_le zero_lt_one_ax (by
        have v := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos K))
        have l : (1 : Real) + 0 = 1 := by mach_ring
        rw [l] at v; exact v)))
    have l : (1 : Real) + exp K * (1 / (exp K - d)) + 0
        = 1 + exp K * (1 / (exp K - d)) := by
      mach_mpoly [exp K, (1 / (exp K - d) : Real)]
    rw [l] at u; exact u
  rw [right_var_logB K A B h x hxK, hA x hxpos]
  have hsplitA : exp (exp x - d) = exp (exp x) * exp (-d) := by
    have e : exp x - d = exp x + -d := by mach_mpoly [exp x, d]
    rw [e, exp_add]
  rw [hsplitA]
  -- `exp(−exp(K−1/x)) ≤ exp(−exp(K−1/S))`
  have hmono : exp (-exp (K - 1 / x))
      ≤ exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d))))) := by
    refine exp_monotone ?_
    refine neg_le_neg_wit (exp_monotone ?_)
    have hiv := one_div_antitone hSpos hxS'
    have u := add_le_add_wit (le_refl K) (neg_le_neg_wit hiv)
    have l : K + -(1 / (1 + exp K * (1 / (exp K - d))))
        = K - 1 / (1 + exp K * (1 / (exp K - d))) := by
      mach_mpoly [K, (1 / (1 + exp K * (1 / (exp K - d))) : Real)]
    have r : K + -(1 / x) = K - 1 / x := by mach_mpoly [K, (1 / x : Real)]
    rw [l, r] at u; exact u
  have hbr : exp (-d) - exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d)))))
      ≤ exp (-d) - exp (-exp (K - 1 / x)) := by
    have u := add_le_add_wit (le_refl (exp (-d))) (neg_le_neg_wit hmono)
    have l : exp (-d) + -exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d)))))
        = exp (-d) - exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d))))) := by
      mach_mpoly [exp (-d), exp (-exp (K - 1 / (1 + exp K * (1 / (exp K - d)))))]
    have r : exp (-d) + -exp (-exp (K - 1 / x)) = exp (-d) - exp (-exp (K - 1 / x)) := by
      mach_mpoly [exp (-d), exp (-exp (K - 1 / x))]
    rw [l, r] at u; exact u
  have hmul := mul_le_mul_of_nonneg_left hbr (le_of_lt (exp_pos (exp x)))
  have r : exp (exp x) * (exp (-d) - exp (-exp (K - 1 / x)))
      = exp (exp x) * exp (-d) - exp (exp x) * exp (-exp (K - 1 / x)) := by
    mach_mpoly [exp (exp x), exp (-d), exp (-exp (K - 1 / x))]
  rw [r] at hmul; exact hmul

/-- **Split-A right-branching with `ℓ₂ = var` is dead.** The leaf cases fall to the sandwich's lower
bound; `eml A B` splits by the five-form classification into the slow forms (one lemma) and the two
fast ones (four bracket branches). -/
theorem split_a_right_var_absurd (K : Real) (R₂ : EMLTree) (hdep : R₂.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → exp x - log (R₂.eval x) = exp (K - 1 / x)) : False := by
  have hS1 : (1 : Real) ≤ 1 + exp K := by
    have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos K))
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  -- a point past `1 + exp K` where `exp x` clears a prescribed line
  have hpoint : ∀ (a b : Real), 0 ≤ a → ∃ x : Real, 1 + exp K ≤ x ∧ 1 ≤ x
      ∧ a * x + b < exp x := by
    intro a b ha
    obtain ⟨x, hxT, hx1, hlt⟩ := exp_beats_linear_past (α := a) (β := b) ha (1 + exp K)
    exact ⟨x, hxT, hx1, hlt⟩
  cases R₂ with
  | const q =>
    obtain ⟨x, hxS, hx1, hlt⟩ := hpoint 0 (q + exp K) (le_refl 0)
    obtain ⟨hlo, _⟩ := right_var_sandwich K (EMLTree.const q) h x hxS
    have e : (EMLTree.const q).eval x = q := rfl
    rw [e] at hlo
    have hlin : (0 : Real) * x + (q + exp K) = q + exp K := by mach_mpoly [x, q, exp K]
    rw [hlin] at hlt
    have hgt : q < exp x - exp K := by
      have u := add_lt_add_left hlt (-exp K)
      have l : -exp K + (q + exp K) = q := by mach_mpoly [q, exp K]
      have r : -exp K + exp x = exp x - exp K := by mach_mpoly [exp x, exp K]
      rw [l, r] at u; exact u
    exact lt_irrefl_ax _ (lt_trans_ax (lt_trans_ax hgt
      (exp_grows_strictly_thm (exp x - exp K))) hlo)
  | var =>
    obtain ⟨x, hxS, hx1, hlt⟩ := hpoint 1 (exp K) (le_of_lt zero_lt_one_ax)
    obtain ⟨hlo, _⟩ := right_var_sandwich K EMLTree.var h x hxS
    have e : (EMLTree.var).eval x = x := rfl
    rw [e] at hlo
    have hlin : (1 : Real) * x + exp K = x + exp K := by mach_mpoly [x, exp K]
    rw [hlin] at hlt
    have hgt : x < exp x - exp K := by
      have u := add_lt_add_left hlt (-exp K)
      have l : -exp K + (x + exp K) = x := by mach_mpoly [x, exp K]
      have r : -exp K + exp x = exp x - exp K := by mach_mpoly [exp x, exp K]
      rw [l, r] at u; exact u
    exact lt_irrefl_ax _ (lt_trans_ax (lt_trans_ax hgt
      (exp_grows_strictly_thm (exp x - exp K))) hlo)
  | eml A B =>
    have hA1 : A.depth ≤ 1 := by
      have := Nat.le_max_left A.depth B.depth
      simp only [EMLTree.depth] at hdep; omega
    have hB1 : B.depth ≤ 1 := by
      have := Nat.le_max_right A.depth B.depth
      simp only [EMLTree.depth] at hdep; omega
    obtain ⟨Cl, X₀, hX₀1, hCl⟩ := depth_le_one_log_lower_at_infinity B hB1
    have hsand : ∀ x : Real, 1 + exp K ≤ x → 1 ≤ x →
        exp (exp x - exp K) < exp (A.eval x) - log (B.eval x) := by
      intro x hxS _
      obtain ⟨hlo, _⟩ := right_var_sandwich K (EMLTree.eml A B) h x hxS
      exact hlo
    rcases depth_le_one_classification A hA1 with
        ⟨α, ha⟩ | ha | ⟨c, hc0, ha⟩ | ⟨d, ha⟩ | ha
    · -- `const α`: slow
      refine right_var_A_slow_absurd K Cl (exp α) (X₀ + (1 + exp K)) A B ?_ ?_ ?_
      · intro x hx; exact hCl x (le_trans (by
          have u := add_le_add_wit (le_refl X₀) (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hS1))
          have l : X₀ + 0 = X₀ := by mach_mpoly [X₀]
          rw [l] at u; exact u) hx)
      · intro x hx1
        rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
        have u := add_le_add_wit (le_of_lt (exp_pos x)) (le_refl (exp α))
        have l : (0 : Real) + exp α = exp α := by mach_mpoly [exp α]
        rw [l] at u; exact u
      · intro x hx hx1
        exact hsand x (le_trans (by
          have u := add_le_add_wit (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hX₀1))
            (le_refl (1 + exp K))
          have l : (0 : Real) + (1 + exp K) = 1 + exp K := by mach_mpoly [exp K]
          rw [l] at u; exact u) hx) hx1
    · -- `var`: slow
      refine right_var_A_slow_absurd K Cl 0 (X₀ + (1 + exp K)) A B ?_ ?_ ?_
      · intro x hx; exact hCl x (le_trans (by
          have u := add_le_add_wit (le_refl X₀) (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hS1))
          have l : X₀ + 0 = X₀ := by mach_mpoly [X₀]
          rw [l] at u; exact u) hx)
      · intro x hx1
        rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
        have e : exp x + (0 : Real) = exp x := by mach_mpoly [exp x]
        rw [e]; exact le_refl _
      · intro x hx hx1
        exact hsand x (le_trans (by
          have u := add_le_add_wit (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hX₀1))
            (le_refl (1 + exp K))
          have l : (0 : Real) + (1 + exp K) = 1 + exp K := by mach_mpoly [exp K]
          rw [l] at u; exact u) hx) hx1
    · -- `c − log x`: slow
      refine right_var_A_slow_absurd K Cl (exp c) (X₀ + (1 + exp K)) A B ?_ ?_ ?_
      · intro x hx; exact hCl x (le_trans (by
          have u := add_le_add_wit (le_refl X₀) (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hS1))
          have l : X₀ + 0 = X₀ := by mach_mpoly [X₀]
          rw [l] at u; exact u) hx)
      · intro x hx1
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        rw [ha x hxpos]
        have hle : exp (c - log x) ≤ exp c := by
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
        refine le_trans hle ?_
        have u := add_le_add_wit (le_of_lt (exp_pos x)) (le_refl (exp c))
        have l : (0 : Real) + exp c = exp c := by mach_mpoly [exp c]
        rw [l] at u; exact u
      · intro x hx hx1
        exact hsand x (le_trans (by
          have u := add_le_add_wit (le_of_lt (lt_of_lt_of_le zero_lt_one_ax hX₀1))
            (le_refl (1 + exp K))
          have l : (0 : Real) + (1 + exp K) = 1 + exp K := by mach_mpoly [exp K]
          rw [l] at u; exact u) hx) hx1
    · -- `exp x − d`: three bracket branches
      rcases lt_total d (exp K) with hlt | heq | hgt
      · exact right_var_exp_sub_const_lt K d hlt A B hB1 ha h
      · exact right_var_exp_sub_const_eq K A B hB1 (fun x hx => by
          rw [ha x hx, heq]) h
      · exact right_var_exp_sub_const_gt K d hgt A B hB1 ha h
    · -- `exp x − log x`
      exact right_var_exp_sub_log K A B hB1 ha h

end MachLib
