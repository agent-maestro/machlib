import MachLib.EMLDepth2InvX
import MachLib.EMLSizeCost

/-!
# Quantitative tameness of shallow EML expressions

Finite EML depth imposes **quantitative** restrictions on behaviour. Not merely "shallow expressions
are tame" — o-minimality of the real exponential field already gives qualitative finiteness — but
explicit statements about which growth, decay, singularity and cancellation behaviours are
*impossible* at a given depth, and where the exceptional regimes sit.

This module collects that theory. It was discovered while attacking `s(1/x) ∈ {9,11}`, and for a
while it lived inside that case analysis; the dependency now runs the right way round, with
`EMLSizeNineShape` importing this file as one application.

## Organisation

* **Depth-≤1 classification.** `depth_le_one_classification` — five closed forms, and nothing else.
  What the list *omits* is load-bearing: there is no `+log x`, hence
  `log_plus_const_not_depth_le_1`.
* **Growth at `∞`.** `depth_le_one_log_le_linear` (`log (B x) ≤ x + C`),
  `depth_le_one_log_lower_at_infinity` (`Cl ≤ log (B x)`), `depth_le_one_le_exp_shift`
  (`A x ≤ exp x + D`).
* **Behaviour at `0⁺`.** `depth_le_one_upper_log_bound`, and `depth_le_two_bounded_left_is_const` —
  a depth-2 tree bounded above has a **constant** left child, because a reciprocal beats a logarithm.
* **The exponential gap.** `depth_le_one_exp_bounded_or_grows`: `exp (A x)` is bounded, or it
  eventually dominates `exp x`. **Nothing sits in between** — which is why no depth-≤1 exponential
  grows linearly. `depth_le_one_exp_bounded_forms` names the two bounded forms, and
  `boundedEmlCell_left_forms` feeds the open bounded cell's own cap into that chain — a cap on an
  exponential caps its argument for free, so the obligation admits two shapes for `A`, not five.
* **The logarithmic dichotomy.** `depth_le_one_log_bounded_or_unbounded` — deliberately weaker than
  the exp gap, because the log side has *three* growth classes (bounded, logarithmic, linear) and the
  mirror statement would be false. `depth_le_one_log_bounded_forms(_from)` names the bounded forms,
  on `[1,∞)` or on any ray.
* **Pole obstruction.** `no_pole_at_depth_le_2`: no depth-≤2 tree is capped by `C − 1/x` near `0`.
  Stated as an upper bound so it applies however the pole is dressed.
* **Decay floors.** `depth_le_two_log_decay_floor`: a depth-≤2 tree falls at most *logarithmically*
  at `0⁺`, with **no positivity hypothesis** — the companion to `rung2_positive_floor` in
  `EMLDepth2InvX`, which needs positivity and bounds below by `C·x²`.
* **Exclusions for named functions.** `mx_not_in_eml_depth_le_2` (`M·x ∉ EML₂` for every `M > 1`;
  `M = 1` is genuinely excluded, since `var` computes `1·x` at depth 0),
  `x_mul_exp_exp_not_in_eml_depth_le_2`, `shifted_inv_not_in_eml_depth_le_2`.

`rung2_positive_floor`, `depth_le_one_lower_bound`, `depth_le_one_trichotomy` and
`depth_le_one_right_tetrachotomy` live in `EMLDepth2InvX` and are **referenced, not restated**.
-/

namespace MachLib

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
theorem one_div_one_div_pos {y : Real} (hy : 0 < y) : 1 / (1 / y) = y := by
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
theorem lt_one_add_exp (y : Real) : y < 1 + exp y := by
  have h1 : y < exp y := exp_grows_strictly_thm y
  have h2 : exp y < 1 + exp y := by
    have u := add_lt_add_left zero_lt_one_ax (exp y)
    have l : exp y + 0 = exp y := by mach_mpoly [exp y]
    have r : exp y + 1 = 1 + exp y := by mach_mpoly [exp y]
    rw [l, r] at u; exact u
  exact lt_trans_ax h1 h2

/-- A pole point: `1/x` exceeds any prescribed `C` somewhere on `(0,∞)`. -/
theorem pole_point (C : Real) : ∃ x : Real, 0 < x ∧ C < 1 / x := by
  refine ⟨1 / exp (1 + exp C), one_div_pos_of_pos (exp_pos _), ?_⟩
  rw [one_div_one_div_pos (exp_pos _)]
  exact lt_trans_ax (lt_one_add_exp C) (exp_grows_strictly_thm _)

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
theorem le_add_left_nonneg {x y : Real} (hx : 0 ≤ x) : y ≤ x + y := by
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
theorem two_mul_le_exp {x : Real} (hx : 0 ≤ x) : x + x ≤ exp x := by
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

theorem one_div_antitone {x y : Real} (hx : 0 < x) (hxy : x ≤ y) : 1 / y ≤ 1 / x := by
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

theorem exp_c_sub_log_eq (c : Real) {x : Real} (hx : 0 < x) :
    exp (c - log x) = exp c * (1 / x) := by
  have e : c - log x = c + -log x := by mach_mpoly [c, log x]
  rw [e, exp_add, exp_neg_inv, exp_log hx]

/-- `exp` reflects strict order. -/
theorem lt_of_exp_lt {a b : Real} (h : exp a < exp b) : a < b := by
  rcases lt_total a b with hl | he | hg
  · exact hl
  · exfalso; rw [he] at h; exact lt_irrefl_ax _ h
  · exfalso; exact lt_irrefl_ax _ (lt_trans_ax h (exp_lt hg))

/-! ## ▸ The `ℓ = var` family at `q > 1`: the fast `A`-forms

Here `exp(R₂ x) = exp(exp x − 1/x) + λ`, which is **not** bounded — so the previous argument does not
port. What survives is an upper bound: `R₂ x ≤ exp x + λ`, because `exp(exp x) + λ ≤ exp(exp x + λ)`.

That caps `exp (A x)` by `exp x + λ + x + C`, which the two **fast** forms break at once: both give
`A x ≥ x + 1` eventually, hence `exp (A x) ≥ 2·exp x`, and `exp x` outruns `λ + x + C`. Only
`A = var` survives, where `exp (A x) = exp x` exactly and the cap is not violated.
-/

/-- `exp x + exp x ≤ exp (x+1)`, since `exp 1 ≥ 2`. -/
theorem exp_succ_ge_two_mul (x : Real) : exp x + exp x ≤ exp (x + 1) := by
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
theorem one_sub_exp_neg_ge (u : Real) : u * exp (-u) ≤ 1 - exp (-u) := by
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

/-- **A cap on a depth-2 node forces its left child into the bounded branch — on a RAY.**

The dichotomy `depth_le_one_exp_bounded_or_grows` says `exp (A x)` is either bounded on `[1,∞)` or
eventually **at least `exp x`**, with nothing in between. The growing branch cannot survive any
finite ceiling on `exp (A x) − log (B x)`, because `depth_le_one_log_le_linear` caps the right child's
logarithm at `x + C` — so a bound `M` would force `exp x ≤ M + x + C`, which `exp_beats_linear_past`
refutes at one point.

**Only a ray of the hypothesis is used**, and that is the whole reason this is stated separately from
`depth_le_two_bounded_left_is_const`. That theorem needs agreement on all of `(0,∞)` to reach its
*stronger* conclusion (`A` is **constant**), because the remaining bounded form `c − log x` blows up
as `x → 0⁺` and is only excluded by looking near zero. On a ray `c − log x` is perfectly bounded, so
the constancy conclusion is **false** there — but the boundedness conclusion still holds, and
boundedness is what a cap-on-a-ray consumer actually needs.

Witness threshold is `exp T + exp XM`, clearing both `T` (the dichotomy's) and `XM` (the caller's)
via `self_le_exp` on each summand — the usual division-free way to take a maximum in this base. -/
theorem depth_le_two_bounded_left_exp_bounded (A B : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (M XM : Real) (hbnd : ∀ x : Real, XM ≤ x → 1 ≤ x → exp (A.eval x) - log (B.eval x) ≤ M) :
    ∃ Kb : Real, ∀ x : Real, 1 ≤ x → exp (A.eval x) ≤ Kb := by
  rcases depth_le_one_exp_bounded_or_grows A hA with hb | ⟨T, hT⟩
  · exact hb
  · exfalso
    obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB
    obtain ⟨x, hxT, hx1, hlt⟩ :=
      exp_beats_linear_past (α := 1) (β := M + C) (le_of_lt zero_lt_one_ax) (exp T + exp XM)
    have hsplit1 : exp T ≤ exp T + exp XM := by
      have v : exp T + 0 ≤ exp T + exp XM :=
        add_le_add_wit (le_refl _) (le_of_lt (exp_pos XM))
      have e : exp T + (0 : Real) = exp T := by mach_ring
      rw [e] at v; exact v
    have hsplit2 : exp XM ≤ exp T + exp XM := by
      have v : (0 : Real) + exp XM ≤ exp T + exp XM :=
        add_le_add_wit (le_of_lt (exp_pos T)) (le_refl _)
      have e : (0 : Real) + exp XM = exp XM := by mach_ring
      rw [e] at v; exact v
    have hTx : T ≤ x :=
      le_trans (le_trans (le_of_lt (exp_grows_strictly_thm T)) hsplit1) hxT
    have hXMx : XM ≤ x :=
      le_trans (le_trans (le_of_lt (exp_grows_strictly_thm XM)) hsplit2) hxT
    have hcap : exp (A.eval x) ≤ M + (x + C) := by
      have hval : exp (A.eval x)
          = (exp (A.eval x) - log (B.eval x)) + log (B.eval x) := by
        mach_mpoly [exp (A.eval x), log (B.eval x)]
      rw [hval]; exact add_le_add_wit (hbnd x hXMx hx1) (hC x hx1)
    have hlin : (1 : Real) * x + (M + C) = M + (x + C) := by mach_mpoly [x, M, C]
    rw [hlin] at hlt
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlt (le_trans (hT x hTx) hcap))

/-- **A depth-2 tree bounded above on `(0,∞)` has a constant left child.** -/
theorem depth_le_two_bounded_left_is_const (A B : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (M : Real) (hbnd : ∀ x : Real, 0 < x → exp (A.eval x) - log (B.eval x) ≤ M) :
    ∃ α : Real, ∀ x : Real, 0 < x → A.eval x = α := by
  obtain ⟨Kb, hKb⟩ := depth_le_two_bounded_left_exp_bounded A B hA hB M 1
    (fun x _ h1 => hbnd x (lt_of_lt_of_le zero_lt_one_ax h1))
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

/-! ## ▸ The mirror: `log (B x)` cannot blow up *positive* either

The `ρ/x` finisher handles the branches where the bracket is negative. When `d < exp K` the bracket
is a **positive constant** instead, so `log (B x)` runs to `+∞` double-exponentially and the
contradiction is with `depth_le_one_log_le_linear`'s *upper* bound rather than the lower one.

Because the bracket is constant here — no `1/x` — the argument stays linear: `exp(exp x) ≥ exp x`
turns `exp(exp x)·ε ≤ x + C` into `exp x ≤ (1/ε)·x + C·(1/ε)`, which `exp_beats_linear_past`
refuses. Reaching for the `ρ/x` shape here would have forced a quadratic comparison for nothing.
-/

theorem log_ge_double_exp_const_absurd (ε S : Real) (hε : 0 < ε) (B : EMLTree) (hB : B.depth ≤ 1)
    (h : ∀ x : Real, S ≤ x → 1 ≤ x → exp (exp x) * ε ≤ log (B.eval x)) : False := by
  obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB
  have hiε : (0 : Real) < 1 / ε := one_div_pos_of_pos hε
  have hmε : (1 / ε) * ε = 1 := by
    have hv := mul_inv ε (ne_of_gt hε); rw [mul_comm] at hv; exact hv
  obtain ⟨x, hxS, hx1, hlt⟩ := exp_beats_linear_past
    (α := 1 / ε) (β := C * (1 / ε)) (le_of_lt hiε) S
  -- `exp x · ε ≤ exp (exp x) · ε ≤ log (B x) ≤ x + C`
  have hEE : exp x * ε ≤ exp (exp x) * ε :=
    mul_le_mul_of_nonneg_right (exp_monotone (le_of_lt (exp_grows_strictly_thm x)))
      (le_of_lt hε)
  have hchain : exp x * ε ≤ x + C :=
    le_trans (le_trans hEE (h x hxS hx1)) (hC x hx1)
  -- scale by `1/ε`
  have hscale := mul_le_mul_of_nonneg_right hchain (le_of_lt hiε)
  have hL : exp x * ε * (1 / ε) = exp x * (ε * (1 / ε)) := by
    mach_mpoly [exp x, ε, (1 / ε : Real)]
  have hmε' : ε * (1 / ε) = 1 := mul_inv ε (ne_of_gt hε)
  rw [hL, hmε'] at hscale
  have hclean : exp x * (1 : Real) = exp x := by mach_mpoly [exp x]
  rw [hclean] at hscale
  have hR : (x + C) * (1 / ε) = 1 / ε * x + C * (1 / ε) := by
    mach_mpoly [x, C, (1 / ε : Real)]
  rw [hR] at hscale
  exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hscale)

/-- `1 − exp(−u) ≤ u` for `u ≥ 0` — the companion to `one_sub_exp_neg_ge`, used to place the ray
start for the `d < exp K` branch without splitting on the sign of `d`. -/
private theorem one_sub_exp_neg_le {u : Real} : 1 - exp (-u) ≤ u := by
  have h1 : (1 : Real) + -u ≤ exp (-u) := one_add_le_exp (-u)
  have v := add_le_add_wit h1 (le_refl (u - exp (-u)))
  have l : (1 : Real) + -u + (u - exp (-u)) = 1 - exp (-u) := by mach_mpoly [u, exp (-u)]
  have r : exp (-u) + (u - exp (-u)) = u := by mach_mpoly [u, exp (-u)]
  rw [l, r] at v; exact v

/-! ### The growth/decay pair, at the first level where it is forced

Everything above bounds depth-≤1 trees. Going one level up is where a *single* envelope provably
fails: at `eml A B` the value is `exp (A x) − log (B x)`, and no upper bound on `B` controls
`−log (B x)`, which blows up as `B x → 0⁺`. That is the obstruction the `LogSafe` work ran into.

The fix is to carry **two** quantities and let the asymmetric children consume different ones:

* the **growth** half bounds the left child — `depth_le_one_le_exp_shift : A x ≤ exp x + D`;
* the **decay** half bounds the right child *from below* —
  `depth_le_one_log_lower_at_infinity : Cl ≤ log (B x)` on a ray.

Both halves already existed; this is the first place they are used together. The result is that one
level of nesting buys exactly one exponential. -/

/-- **The depth-≤2 growth envelope.** `t x ≤ exp (exp x + K) + M` on a ray.

The constants are unavoidable and both are earned: `K` is the left child's exponential shift, `M` is
the *negated* decay floor of the right child. The ray is unavoidable too — the decay bound is only
eventual, since `c − log x` passes through `0` at `x = exp c`. -/
theorem depth_le_two_growth_envelope (t : EMLTree) (ht : t.depth ≤ 2) :
    ∃ K M X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → t.eval x ≤ exp (exp x + K) + M := by
  cases t with
  | const c =>
      refine ⟨0, c, 1, le_refl 1, ?_⟩
      intro x _
      show c ≤ exp (exp x + 0) + c
      have hp : (0 : Real) ≤ exp (exp x + 0) := le_of_lt (exp_pos _)
      have t1 : c + 0 ≤ c + exp (exp x + 0) := add_le_add_left hp c
      have e1 : c + (0 : Real) = c := by mach_ring
      have e2 : c + exp (exp x + 0) = exp (exp x + 0) + c := by mach_ring
      rw [e1, e2] at t1; exact t1
  | var =>
      refine ⟨0, 0, 1, le_refl 1, ?_⟩
      intro x _
      show x ≤ exp (exp x + 0) + 0
      have e : exp x + (0 : Real) = exp x := by mach_ring
      rw [e]
      have h1 : 1 + exp x ≤ exp (exp x) := one_add_le_exp (exp x)
      have h2 : 1 + x ≤ exp x := one_add_le_exp x
      have h3 : 1 + (1 + x) ≤ 1 + exp x := add_le_add_left h2 1
      have h4 : x ≤ 1 + (1 + x) := by
        have hz : (0 : Real) ≤ 1 + 1 := le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax)
          zero_lt_one_ax)
        have t1 : x + 0 ≤ x + (1 + 1) := add_le_add_left hz x
        have e1 : x + (0 : Real) = x := by mach_ring
        have e2 : x + ((1 : Real) + 1) = 1 + (1 + x) := by mach_ring
        rw [e1, e2] at t1; exact t1
      have h5 : x ≤ exp (exp x) := le_trans h4 (le_trans h3 h1)
      have e2 : exp (exp x) + (0 : Real) = exp (exp x) := by mach_ring
      rw [e2]; exact h5
  | eml A B =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      obtain ⟨D, hD⟩ := depth_le_one_le_exp_shift A hA
      obtain ⟨Cl, X₀, hX1, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
      refine ⟨D, -Cl, X₀, hX1, ?_⟩
      intro x hx
      have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
      show exp (A.eval x) - log (B.eval x) ≤ exp (exp x + D) + -Cl
      have h1 : exp (A.eval x) ≤ exp (exp x + D) := exp_monotone (hD x hx1)
      have h2 : -log (B.eval x) ≤ -Cl := neg_le_neg_wit (hCl x hx)
      have h3 : exp (A.eval x) + -log (B.eval x) ≤ exp (exp x + D) + -Cl := add_le_add_wit h1 h2
      have e : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
      rw [e] at h3; exact h3


/-- **Depth-≤1 lower bound on a ray**, in the shape the decay bound needs: `A x ≥ −C − log x`.

The companion `depth_le_one_lower_bound` (in `EMLDepth2InvX`) bounds a depth-≤1 tree on `(0,1]`;
this is the other end. `−log x` is the right comparison because it is exactly the worst form's
shape — `c − log x` attains it with equality, and every other form clears it easily. -/
theorem depth_le_one_lower_on_ray (A : EMLTree) (hA : A.depth ≤ 1) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → -C - log x ≤ A.eval x := by
  have hlog0 : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ log x := by
    intro x hx
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hm := log_le_log zero_lt_one_ax hx
    rw [hl1] at hm; exact hm
  have hxpos : ∀ x : Real, 1 ≤ x → (0 : Real) < x := fun x hx =>
    lt_of_lt_of_le zero_lt_one_ax hx
  rcases depth_le_one_classification A hA with
      ⟨α, hb⟩ | hb | ⟨c, _, hb⟩ | ⟨d, hb⟩ | hb
  · refine ⟨-α, ?_⟩
    intro x hx
    rw [hb x (hxpos x hx)]
    have t := neg_le_neg_wit (hlog0 x hx)
    have e0 : -(0 : Real) = 0 := by mach_ring
    rw [e0] at t
    have h2 : α + -log x ≤ α + 0 := add_le_add_left t α
    have e1 : α + -log x = - -α - log x := by mach_ring
    have e2 : α + (0 : Real) = α := by mach_ring
    rw [e1, e2] at h2; exact h2
  · refine ⟨0, ?_⟩
    intro x hx
    rw [hb x (hxpos x hx)]
    have t := neg_le_neg_wit (hlog0 x hx)
    have e0 : -(0 : Real) = 0 := by mach_ring
    rw [e0] at t
    have e1 : -(0 : Real) - log x = -log x := by mach_ring
    rw [e1]
    exact le_trans t (le_trans (le_of_lt zero_lt_one_ax) hx)
  · refine ⟨-c, ?_⟩
    intro x hx
    rw [hb x (hxpos x hx)]
    have e : - -c - log x = c - log x := by mach_ring
    rw [e]
    exact le_refl _
  · refine ⟨d, ?_⟩
    intro x hx
    rw [hb x (hxpos x hx)]
    have t := neg_le_neg_wit (hlog0 x hx)
    have e0 : -(0 : Real) = 0 := by mach_ring
    rw [e0] at t
    have h1 : -log x ≤ exp x := le_trans t (le_of_lt (exp_pos x))
    have h2 : -d + -log x ≤ -d + exp x := add_le_add_left h1 (-d)
    have e1 : -d + -log x = -d - log x := by mach_ring
    have e2 : -d + exp x = exp x - d := by mach_ring
    rw [e1, e2] at h2; exact h2
  · refine ⟨0, ?_⟩
    intro x hx
    rw [hb x (hxpos x hx)]
    have h1 : (0 : Real) ≤ exp x := le_of_lt (exp_pos x)
    have h2 : -log x + 0 ≤ -log x + exp x := add_le_add_left h1 (-log x)
    have e1 : -log x + (0 : Real) = -(0 : Real) - log x := by mach_ring
    have e2 : -log x + exp x = exp x - log x := by mach_ring
    rw [e1, e2] at h2; exact h2

/-- **The worst cell of the `V₂` table, discharged.**

The paper analysis (`monogate-research/.../V2_DECAY_BOUND_ANALYSIS.md`) tabulates the 25 shape
combinations of `exp (A x)` against `log (B x)` and finds exactly one that decays: `e^c/x`, reached
when the right child contributes nothing (`log (B x) ≤ 0`). Every other cell grows or is bounded
below by a positive constant.

This is that cell. Note it needs **no hypothesis on `B` at all** beyond the sign of its log — the
decay is entirely the left child's, and `depth_le_one_lower_on_ray` is what caps it at `1/x`. -/
theorem depth_le_two_decay_log_nonpos (A B : EMLTree) (hA : A.depth ≤ 1) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ 0 →
      exp (-C - log x) ≤ exp (A.eval x) - log (B.eval x) := by
  obtain ⟨C, hC⟩ := depth_le_one_lower_on_ray A hA
  refine ⟨C, ?_⟩
  intro x hx hB
  have h1 : exp (-C - log x) ≤ exp (A.eval x) := exp_monotone (hC x hx)
  have h2 : (0 : Real) ≤ -log (B.eval x) := by
    have t := neg_le_neg_wit hB
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at t; exact t
  have h3 : exp (A.eval x) + 0 ≤ exp (A.eval x) + -log (B.eval x) :=
    add_le_add_left h2 (exp (A.eval x))
  have e1 : exp (A.eval x) + (0 : Real) = exp (A.eval x) := by mach_ring
  have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
  rw [e1, e2] at h3
  exact le_trans h1 h3

/-- The same fact in the shape the induction consumes: a **logarithmic decay bound**,
`−log t(x) ≤ C + log x`. This is `V₂` on the branch where it is not vacuous. -/
theorem depth_le_two_V2_log_nonpos (A B : EMLTree) (hA : A.depth ≤ 1) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ 0 →
      -log (exp (A.eval x) - log (B.eval x)) ≤ C + log x := by
  obtain ⟨C, hC⟩ := depth_le_two_decay_log_nonpos A B hA
  refine ⟨C, ?_⟩
  intro x hx hB
  have hlow := hC x hx hB
  have hpos : (0 : Real) < exp (-C - log x) := exp_pos _
  have hmono : log (exp (-C - log x)) ≤ log (exp (A.eval x) - log (B.eval x)) :=
    log_le_log hpos hlow
  rw [log_exp] at hmono
  have t := neg_le_neg_wit hmono
  have e : -(-C - log x) = C + log x := by mach_ring
  rw [e] at t; exact t


/-! ### Eventual-largeness helpers for the `V₂` case analysis

Every vacuous cell of the decay table is vacuous for the same reason: past an explicit point the
right child's log outgrows the left child's bounded exponential, so the node goes negative and the
positivity hypothesis cannot fire. These three lemmas supply "past an explicit point" for the three
unbounded shapes of `log (B x)`. -/

/-- `log x` clears any `K` past `exp (K+1) + 1`. -/
theorem eventually_log_gt (K : Real) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → K < log x := by
  have hp : (0 : Real) < exp (K + 1) := exp_pos _
  refine ⟨exp (K + 1) + 1, ?_, ?_⟩
  · have t : (0 : Real) + 1 ≤ exp (K + 1) + 1 := add_le_add_wit (le_of_lt hp) (le_refl 1)
    have e : (0 : Real) + 1 = 1 := by mach_ring
    rw [e] at t; exact t
  · intro x hx
    have hX0 : (0 : Real) < exp (K + 1) + 1 := by
      have t : (0 : Real) + 0 < exp (K + 1) + 1 :=
        lt_of_lt_of_le (add_lt_add_left zero_lt_one_ax 0)
          (add_le_add_wit (le_of_lt hp) (le_refl 1))
      have e : (0 : Real) + 0 = 0 := by mach_ring
      rw [e] at t; exact t
    have hlt : exp (K + 1) < exp (K + 1) + 1 := by
      have t : exp (K + 1) + 0 < exp (K + 1) + 1 := add_lt_add_left zero_lt_one_ax _
      have e : exp (K + 1) + (0 : Real) = exp (K + 1) := by mach_ring
      rw [e] at t; exact t
    have h1 : K + 1 < log (exp (K + 1) + 1) := by
      have s := log_lt_log hp hlt
      rw [log_exp] at s; exact s
    have h2 : log (exp (K + 1) + 1) ≤ log x := log_le_log hX0 hx
    have h3 : K < K + 1 := by
      have t : K + 0 < K + 1 := add_lt_add_left zero_lt_one_ax K
      have e : K + (0 : Real) = K := by mach_ring
      rw [e] at t; exact t
    exact lt_of_lt_of_le (lt_trans_ax h3 h1) h2

/-- `a < a + 1`. Written out because this corpus has `OfNat` only for `0` and `1`. -/
private theorem lt_succ_self (a : Real) : a < a + 1 := by
  have t : a + 0 < a + 1 := add_lt_add_left zero_lt_one_ax a
  have e : a + (0 : Real) = a := by mach_ring
  rw [e] at t; exact t

private theorem le_one_add (a : Real) : a ≤ 1 + a := by
  have t := le_of_lt (lt_succ_self a)
  have e : a + (1 : Real) = 1 + a := by mach_ring
  rw [e] at t; exact t

/-- `log x ≤ x` on `[1,∞)`. (`EMLTree.log_le_id_at_one` says this but sits in another namespace
and is not in this module's import closure.) -/
private theorem log_le_self_on_ray {x : Real} (hx : 1 ≤ x) : log x ≤ x := by
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
  have h1 : x ≤ exp x := le_trans (le_one_add x) (one_add_le_exp x)
  have h2 : log x ≤ log (exp x) := log_le_log hx0 h1
  rw [log_exp] at h2; exact h2

/-- `log (exp x − d)` clears any `K` past an explicit point. The threshold carries `exp d` rather
than `d` so that it survives arbitrarily negative `d`. -/
theorem eventually_log_exp_sub_gt (K d : Real) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → K < log (exp x - d) := by
  have hpK : (0 : Real) < exp (K + 1) := exp_pos _
  have hpd : (0 : Real) < exp d := exp_pos _
  refine ⟨exp (K + 1) + exp d + 1, ?_, ?_⟩
  · have t : (0 : Real) + 0 + 1 ≤ exp (K + 1) + exp d + 1 :=
      add_le_add_wit (add_le_add_wit (le_of_lt hpK) (le_of_lt hpd)) (le_refl 1)
    have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
    rw [e] at t; exact t
  · intro x hx
    have hdd : d ≤ exp d := le_trans (le_one_add d) (one_add_le_exp d)
    have s2 : exp (K + 1) + d + 1 ≤ exp (K + 1) + exp d + 1 :=
      add_le_add_wit (add_le_add_wit (le_refl (exp (K + 1))) hdd) (le_refl 1)
    have s4 : exp (K + 1) + d + 1 ≤ x := le_trans s2 hx
    have s5 : x ≤ exp x := le_trans (le_one_add x) (one_add_le_exp x)
    have s6 : exp (K + 1) + d + 1 ≤ exp x := le_trans s4 s5
    have hgt : exp (K + 1) + d < exp x := lt_of_lt_of_le (lt_succ_self _) s6
    have hsub : exp (K + 1) < exp x - d := by
      have t := add_lt_add_left hgt (-d)
      have e1 : -d + (exp (K + 1) + d) = exp (K + 1) := by mach_ring
      have e2 : -d + exp x = exp x - d := by mach_ring
      rw [e1, e2] at t; exact t
    have hlog := log_lt_log hpK hsub
    rw [log_exp] at hlog
    exact lt_trans_ax (lt_succ_self K) hlog

/-- `log (exp x − log x)` clears any `K` past `exp (K+1) + 1`, because `exp x − log x ≥ x`. -/
theorem eventually_log_exp_sub_log_gt (K : Real) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → K < log (exp x - log x) := by
  have hpK : (0 : Real) < exp (K + 1) := exp_pos _
  have hX1 : (1 : Real) ≤ exp (K + 1) + 1 := by
    have t : (0 : Real) + 1 ≤ exp (K + 1) + 1 := add_le_add_wit (le_of_lt hpK) (le_refl 1)
    have e : (0 : Real) + 1 = 1 := by mach_ring
    rw [e] at t; exact t
  refine ⟨exp (K + 1) + 1, hX1, ?_⟩
  intro x hx
  have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hlogx : log x ≤ x := log_le_self_on_ray hx1
  have hdouble : x + x ≤ exp x := two_mul_le_exp hx0
  have hge : x ≤ exp x - log x := by
    have s1 : -x + (x + x) ≤ -x + exp x := add_le_add_left hdouble (-x)
    have e1 : -x + (x + x) = x := by mach_ring
    have e2 : -x + exp x = exp x - x := by mach_ring
    rw [e1, e2] at s1
    have s2 : exp x + -x ≤ exp x + -log x :=
      add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit hlogx)
    have e3 : exp x + -x = exp x - x := by mach_ring
    have e4 : exp x + -log x = exp x - log x := by mach_ring
    rw [e3, e4] at s2
    exact le_trans s1 s2
  have hgt : exp (K + 1) < exp x - log x :=
    lt_of_lt_of_le (lt_of_lt_of_le (lt_succ_self _) hx) hge
  have hlog := log_lt_log hpK hgt
  rw [log_exp] at hlog
  exact lt_trans_ax (lt_succ_self K) hlog

private theorem le_add_nonneg_r' {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have t := add_le_add_left hb a
  have e : a + (0 : Real) = a := by mach_ring
  rw [e] at t; exact t

/-- **`V₂` — the decay bound at depth 2.**

For every `t` of depth ≤ 2 there is a ray and a constant with
`−log t(x) ≤ C + log x` wherever `t` is positive. This is the decay half of the growth/decay pair at
the first level where it is not already available, and it completes the table analysed in
`monogate-research/exploration/eml_depth_induction_2026_08_13/`.

**Why the ray is not a convenience.** Near a point where `t` crosses zero from above, `t(x) → 0⁺`
and `−log t(x) → +∞`, so no fixed `C` survives. The statement is rescued only by choosing `X₀` past
the last sign change — a *finiteness of sign changes* requirement, which at depth 2 is discharged by
hand because each depth-≤1 form crosses zero at most once, at an explicitly computable point. That,
and not cancellation, is what this proof actually consumes.

Of the twenty-five cells: one decays (`depth_le_two_V2_log_nonpos`), one is a positive constant, and
the rest are vacuous on a far enough ray. -/
theorem depth_le_two_decay_on_ray (t : EMLTree) (ht : t.depth ≤ 2) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < t.eval x →
      -log (t.eval x) ≤ C + log x := by
  have hlog0 : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ log x := by
    intro x hx
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hm := log_le_log zero_lt_one_ax hx
    rw [hl1] at hm; exact hm
  have hxpos : ∀ x : Real, 1 ≤ x → (0 : Real) < x := fun x hx =>
    lt_of_lt_of_le zero_lt_one_ax hx
  cases t with
  | const c =>
      refine ⟨-log c, 1, le_refl 1, ?_⟩
      intro x hx _
      show -log c ≤ -log c + log x
      exact le_add_nonneg_r' (hlog0 x hx)
  | var =>
      refine ⟨0, 1, le_refl 1, ?_⟩
      intro x hx _
      show -log x ≤ 0 + log x
      have h1 : -log x ≤ 0 := by
        have t1 := neg_le_neg_wit (hlog0 x hx)
        have e : -(0 : Real) = 0 := by mach_ring
        rw [e] at t1; exact t1
      have h2 : (0 : Real) ≤ 0 + log x := by
        have e : (0 : Real) + log x = log x := by mach_ring
        rw [e]; exact hlog0 x hx
      exact le_trans h1 h2
  | eml A B =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      -- The proved cell, available in every branch where the right child contributes nothing.
      obtain ⟨C0, hC0⟩ := depth_le_two_V2_log_nonpos A B hA
      rcases depth_le_one_exp_bounded_or_grows A hA with ⟨K, hK⟩ | ⟨T, hT⟩
      · -- LEFT CHILD BOUNDED. Classify the right child; all but one cell dies on a ray.
        rcases depth_le_one_classification B hB with
            ⟨β, hb⟩ | hb | ⟨c', hc'0, hb⟩ | ⟨d, hb⟩ | hb
        · -- `B = const β`.
          rcases lt_total (log β) 0 with hlb | hlb | hlb
          · -- `log β < 0`: the proved cell.
            refine ⟨C0, 1, le_refl 1, ?_⟩
            intro x hx _
            exact hC0 x hx (by rw [hb x (hxpos x hx)]; exact le_of_lt hlb)
          · -- `log β = 0`: also the proved cell.
            refine ⟨C0, 1, le_refl 1, ?_⟩
            intro x hx _
            exact hC0 x hx (by rw [hb x (hxpos x hx)]; exact le_of_eq hlb)
          · -- `log β > 0`: the only surviving cell. Split the left child.
            rcases depth_le_one_exp_bounded_forms A hA K hK with ⟨α, ha⟩ | ⟨c, _, ha⟩
            · -- `A = const α`: the node is a constant.
              refine ⟨-log (exp α - log β), 1, le_refl 1, ?_⟩
              intro x hx _
              show -log (exp (A.eval x) - log (B.eval x)) ≤ -log (exp α - log β) + log x
              rw [ha x (hxpos x hx), hb x (hxpos x hx)]
              exact le_add_nonneg_r' (hlog0 x hx)
            · -- `A = c − log x`: `exp (A x) → 0` while `log β > 0`, so the node goes negative.
              obtain ⟨X₀, hX1, hX⟩ := eventually_log_gt (c - log (log β))
              refine ⟨0, X₀, hX1, ?_⟩
              intro x hx hpos
              exfalso
              have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
              have hgt := hX x hx
              -- `c − log x < log (log β)`, so `exp (A x) < log β`.
              have hlt : c - log x < log (log β) := by
                have t1 := add_lt_add_left hgt (c - (c - log (log β)))
                have e1 : c - (c - log (log β)) + (c - log (log β)) = c := by
                  mach_mpoly [c, log (log β)]
                have e2 : c - (c - log (log β)) + log x = log (log β) + log x := by
                  mach_mpoly [c, log (log β), log x]
                rw [e1, e2] at t1
                have t2 := add_lt_add_left t1 (-log x)
                have e3 : -log x + c = c - log x := by mach_ring
                have e4 : -log x + (log (log β) + log x) = log (log β) := by mach_ring
                rw [e3, e4] at t2; exact t2
              have hexp : exp (c - log x) < log β := by
                have t1 := exp_lt hlt
                rw [exp_log hlb] at t1; exact t1
              have hneg : exp (A.eval x) - log (B.eval x) < 0 := by
                rw [ha x (hxpos x hx1), hb x (hxpos x hx1)]
                have t1 := add_lt_add_left hexp (-log β)
                have e1 : -log β + exp (c - log x) = exp (c - log x) - log β := by mach_ring
                have e2 : -log β + log β = 0 := by mach_ring
                rw [e1, e2] at t1; exact t1
              exact lt_irrefl_ax _ (lt_trans_ax hpos hneg)
        · -- `B = var`: `log x` outgrows the bounded left child.
          obtain ⟨X₀, hX1, hX⟩ := eventually_log_gt K
          refine ⟨0, X₀, hX1, ?_⟩
          intro x hx hpos
          exfalso
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          have hneg : exp (A.eval x) - log (B.eval x) < 0 := by
            rw [hb x (hxpos x hx1)]
            have t1 : exp (A.eval x) < log x := lt_of_le_of_lt (hK x hx1) (hX x hx)
            have t2 := add_lt_add_left t1 (-log x)
            have e1 : -log x + exp (A.eval x) = exp (A.eval x) - log x := by mach_ring
            have e2 : -log x + log x = 0 := by mach_ring
            rw [e1, e2] at t2; exact t2
          exact lt_irrefl_ax _ (lt_trans_ax hpos hneg)
        · -- `B = c′ − log x`: totalised to `0` past `exp c′`, so the proved cell applies.
          obtain ⟨X₀, hX1, hX⟩ := eventually_log_gt c'
          refine ⟨C0, X₀, hX1, ?_⟩
          intro x hx _
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          refine hC0 x hx1 ?_
          rw [hb x (hxpos x hx1)]
          have hle : c' - log x ≤ 0 := by
            have t1 := add_lt_add_left (hX x hx) (-log x)
            have e1 : -log x + c' = c' - log x := by mach_ring
            have e2 : -log x + log x = 0 := by mach_ring
            rw [e1, e2] at t1
            exact le_of_lt t1
          rw [log_nonpos hle]
          exact le_refl 0
        · -- `B = exp x − d`.
          obtain ⟨X₀, hX1, hX⟩ := eventually_log_exp_sub_gt K d
          refine ⟨0, X₀, hX1, ?_⟩
          intro x hx hpos
          exfalso
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          have hneg : exp (A.eval x) - log (B.eval x) < 0 := by
            rw [hb x (hxpos x hx1)]
            have t1 : exp (A.eval x) < log (exp x - d) := lt_of_le_of_lt (hK x hx1) (hX x hx)
            have t2 := add_lt_add_left t1 (-log (exp x - d))
            have e1 : -log (exp x - d) + exp (A.eval x) = exp (A.eval x) - log (exp x - d) := by
              mach_ring
            have e2 : -log (exp x - d) + log (exp x - d) = 0 := by mach_ring
            rw [e1, e2] at t2; exact t2
          exact lt_irrefl_ax _ (lt_trans_ax hpos hneg)
        · -- `B = exp x − log x`.
          obtain ⟨X₀, hX1, hX⟩ := eventually_log_exp_sub_log_gt K
          refine ⟨0, X₀, hX1, ?_⟩
          intro x hx hpos
          exfalso
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          have hneg : exp (A.eval x) - log (B.eval x) < 0 := by
            rw [hb x (hxpos x hx1)]
            have t1 : exp (A.eval x) < log (exp x - log x) := lt_of_le_of_lt (hK x hx1) (hX x hx)
            have t2 := add_lt_add_left t1 (-log (exp x - log x))
            have e1 : -log (exp x - log x) + exp (A.eval x)
                = exp (A.eval x) - log (exp x - log x) := by mach_ring
            have e2 : -log (exp x - log x) + log (exp x - log x) = 0 := by mach_ring
            rw [e1, e2] at t2; exact t2
          exact lt_irrefl_ax _ (lt_trans_ax hpos hneg)
      · -- LEFT CHILD GROWS: the node exceeds `1` eventually, so the bound is trivial.
        obtain ⟨CB, hCB⟩ := depth_le_one_log_le_linear B hB
        have hTp : (0 : Real) < exp T := exp_pos T
        have hCp : (0 : Real) < exp CB := exp_pos CB
        refine ⟨0, exp T + exp CB + 1, ?_, ?_⟩
        · have t1 : (0 : Real) + 0 + 1 ≤ exp T + exp CB + 1 :=
            add_le_add_wit (add_le_add_wit (le_of_lt hTp) (le_of_lt hCp)) (le_refl 1)
          have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
          rw [e] at t1; exact t1
        · intro x hx _
          have hX1 : (1 : Real) ≤ exp T + exp CB + 1 := by
            have t1 : (0 : Real) + 0 + 1 ≤ exp T + exp CB + 1 :=
              add_le_add_wit (add_le_add_wit (le_of_lt hTp) (le_of_lt hCp)) (le_refl 1)
            have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
            rw [e] at t1; exact t1
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
          -- `x ≥ T` and `x ≥ CB + 1`
          have hxT : T ≤ x := by
            have hTe : T ≤ exp T := le_trans (le_one_add T) (one_add_le_exp T)
            have t1 : exp T ≤ exp T + exp CB + 1 :=
              le_trans (le_add_nonneg_r' (le_of_lt hCp)) (le_add_nonneg_r' (le_of_lt zero_lt_one_ax))
            exact le_trans hTe (le_trans t1 hx)
          have hxC : CB + 1 ≤ x := by
            have hCe : CB + 1 ≤ exp CB + 1 :=
              add_le_add_wit (le_trans (le_one_add CB) (one_add_le_exp CB)) (le_refl 1)
            have t1 : exp CB + 1 ≤ exp T + exp CB + 1 := by
              have u : (0 : Real) + exp CB + 1 ≤ exp T + exp CB + 1 :=
                add_le_add_wit (add_le_add_wit (le_of_lt hTp) (le_refl (exp CB))) (le_refl 1)
              have e : (0 : Real) + exp CB + 1 = exp CB + 1 := by mach_ring
              rw [e] at u; exact u
            exact le_trans hCe (le_trans t1 hx)
          -- `t x ≥ (x + x) − (x + CB) = x − CB ≥ 1`
          have hone : (1 : Real) ≤ exp (A.eval x) - log (B.eval x) := by
            have g1 : exp x ≤ exp (A.eval x) := hT x hxT
            have g2 : log (B.eval x) ≤ x + CB := hCB x hx1
            have g3 : x + x ≤ exp x := two_mul_le_exp hx0
            have g4 : x + x ≤ exp (A.eval x) := le_trans g3 g1
            have g5 : (x + x) - (x + CB) ≤ exp (A.eval x) - log (B.eval x) := by
              have u3 : (x + x) - (x + CB) ≤ exp (A.eval x) - (x + CB) := by
                have v := add_le_add_wit g4 (le_refl (-(x + CB)))
                have ev1 : x + x + -(x + CB) = (x + x) - (x + CB) := by mach_ring
                have ev2 : exp (A.eval x) + -(x + CB) = exp (A.eval x) - (x + CB) := by mach_ring
                rw [ev1, ev2] at v; exact v
              have u4 : exp (A.eval x) - (x + CB) ≤ exp (A.eval x) - log (B.eval x) := by
                have v := add_le_add_wit (le_refl (exp (A.eval x))) (neg_le_neg_wit g2)
                have ev1 : exp (A.eval x) + -(x + CB) = exp (A.eval x) - (x + CB) := by mach_ring
                have ev2 : exp (A.eval x) + -log (B.eval x)
                    = exp (A.eval x) - log (B.eval x) := by mach_ring
                rw [ev1, ev2] at v; exact v
              exact le_trans u3 u4
            have g6 : (1 : Real) ≤ (x + x) - (x + CB) := by
              have v : CB + 1 + -CB ≤ x + -CB := add_le_add_wit hxC (le_refl (-CB))
              have ev1 : CB + 1 + -CB = 1 := by mach_ring
              have ev2 : x + -CB = (x + x) - (x + CB) := by mach_mpoly [x, CB]
              rw [ev1, ev2] at v; exact v
            exact le_trans g6 g5
          show -log (exp (A.eval x) - log (B.eval x)) ≤ 0 + log x
          have hlogpos : (0 : Real) ≤ log (exp (A.eval x) - log (B.eval x)) := by
            have hl1 : log (1 : Real) = 0 := by
              have hz : exp (0 : Real) = 1 := exp_zero
              rw [← hz, log_exp]
            have m := log_le_log zero_lt_one_ax hone
            rw [hl1] at m; exact m
          have h1 : -log (exp (A.eval x) - log (B.eval x)) ≤ 0 := by
            have t1 := neg_le_neg_wit hlogpos
            have e : -(0 : Real) = 0 := by mach_ring
            rw [e] at t1; exact t1
          have h2 : (0 : Real) ≤ 0 + log x := by
            have e : (0 : Real) + log x = log x := by mach_ring
            rw [e]; exact hlog0 x hx1
          exact le_trans h1 h2


/-- `a ≤ exp a`, everywhere. -/
theorem self_le_exp (a : Real) : a ≤ exp a :=
  le_trans (le_one_add a) (one_add_le_exp a)

/-- `exp a + exp a ≤ exp (a + 1)`: one unit of exponent is a factor of `e ≥ 2`. -/
theorem exp_add_one_doubles (a : Real) : exp a + exp a ≤ exp (a + 1) := by
  have h1 : exp a * (1 + 1) ≤ exp a * exp 1 :=
    mul_le_mul_of_nonneg_left (one_add_le_exp 1) (le_of_lt (exp_pos a))
  have e1 : exp a * ((1 : Real) + 1) = exp a + exp a := by mach_ring
  have e2 : exp (a + 1) = exp a * exp 1 := exp_add _ _
  rw [e1] at h1; rw [e2]; exact h1

/-- **The depth-≤3 growth envelope — the pair, iterated.**

`U₃` is built from `U₂` (`depth_le_two_growth_envelope`) and `V₂` (`depth_le_two_decay_on_ray`),
both of which are now theorems rather than hand-built inputs. That is the point of this statement:
`d(T₃) = 3` was proved with a *hand-built* depth-≤1 decay bound, so it did not show the construction
iterates. This one consumes only proved halves.

The right child needs both branches of the totalisation: where `B x ≤ 0` the log is `0` and
contributes nothing; where `B x > 0`, `V₂` caps `−log (B x)` at `C + log x`. The `log x` is then
absorbed into the exponent by `exp_add_one_doubles`. -/
theorem depth_le_three_growth_envelope (t : EMLTree) (ht : t.depth ≤ 3) :
    ∃ K M N X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      t.eval x ≤ exp (exp (exp x + K) + M) + N := by
  have hlog0 : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ log x := by
    intro x hx
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hm := log_le_log zero_lt_one_ax hx
    rw [hl1] at hm; exact hm
  cases t with
  | const c =>
      refine ⟨0, 0, c, 1, le_refl 1, ?_⟩
      intro x _
      show c ≤ exp (exp (exp x + 0) + 0) + c
      have t := le_add_nonneg_r' (a := c) (le_of_lt (exp_pos (exp (exp x + 0) + 0)))
      have e : c + exp (exp (exp x + 0) + 0) = exp (exp (exp x + 0) + 0) + c := by mach_ring
      rw [e] at t; exact t
  | var =>
      refine ⟨0, 0, 0, 1, le_refl 1, ?_⟩
      intro x hx
      show x ≤ exp (exp (exp x + 0) + 0) + 0
      have e1 : exp x + (0 : Real) = exp x := by mach_ring
      have e2 : exp (exp x) + (0 : Real) = exp (exp x) := by mach_ring
      rw [e1, e2]
      have c1 : x ≤ exp x := self_le_exp x
      have c2 : exp x ≤ exp (exp x) := self_le_exp _
      have c3 : exp (exp x) ≤ exp (exp (exp x)) := self_le_exp _
      have e3 : exp (exp (exp x)) + (0 : Real) = exp (exp (exp x)) := by mach_ring
      rw [e3]
      exact le_trans c1 (le_trans c2 c3)
  | eml A B =>
      have hA : A.depth ≤ 2 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 2 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      obtain ⟨K, M, XA, hXA1, hU⟩ := depth_le_two_growth_envelope A hA
      obtain ⟨C, XB, hXB1, hV⟩ := depth_le_two_decay_on_ray B hB
      -- The `exp (-(K+M))` term is not padding: without it the absorption step below is FALSE,
      -- since `exp (exp (exp x + K) + M)` can be tiny for very negative `M`.
      refine ⟨K, M + 1, exp C, XA + XB + exp (-(K + M)), ?_, ?_⟩
      · have t1 : (1 : Real) + 0 + 0 ≤ XA + XB + exp (-(K + M)) :=
          add_le_add_wit (add_le_add_wit hXA1 (le_trans (le_of_lt zero_lt_one_ax) hXB1))
            (le_of_lt (exp_pos _))
        have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
        rw [e] at t1; exact t1
      · intro x hx
        have hXBnn : (0 : Real) ≤ XB := le_trans (le_of_lt zero_lt_one_ax) hXB1
        have hXAnn : (0 : Real) ≤ XA := le_trans (le_of_lt zero_lt_one_ax) hXA1
        have hEnn : (0 : Real) ≤ exp (-(K + M)) := le_of_lt (exp_pos _)
        have hXA : XA ≤ x := by
          have v : XA + 0 + 0 ≤ XA + XB + exp (-(K + M)) :=
            add_le_add_wit (add_le_add_wit (le_refl XA) hXBnn) hEnn
          have e : XA + (0 : Real) + 0 = XA := by mach_ring
          rw [e] at v; exact le_trans v hx
        have hXB : XB ≤ x := by
          have v : (0 : Real) + XB + 0 ≤ XA + XB + exp (-(K + M)) :=
            add_le_add_wit (add_le_add_wit hXAnn (le_refl XB)) hEnn
          have e : (0 : Real) + XB + 0 = XB := by mach_ring
          rw [e] at v; exact le_trans v hx
        have hXE : exp (-(K + M)) ≤ x := by
          have v : (0 : Real) + 0 + exp (-(K + M)) ≤ XA + XB + exp (-(K + M)) :=
            add_le_add_wit (add_le_add_wit hXAnn hXBnn) (le_refl _)
          have e : (0 : Real) + 0 + exp (-(K + M)) = exp (-(K + M)) := by mach_ring
          rw [e] at v; exact le_trans v hx
        have hx1 : (1 : Real) ≤ x := le_trans hXA1 hXA
        have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
        have hAx : A.eval x ≤ exp (exp x + K) + M := hU x hXA
        have hexpA : exp (A.eval x) ≤ exp (exp (exp x + K) + M) := exp_monotone hAx
        have hBx : -log (B.eval x) ≤ exp C + log x := by
          rcases lt_total 0 (B.eval x) with hp | hp | hp
          · exact le_trans (hV x hXB hp)
              (add_le_add_wit (le_trans (le_one_add C) (one_add_le_exp C)) (le_refl (log x)))
          · rw [log_nonpos (le_of_eq hp.symm)]
            have e : -(0 : Real) = 0 := by mach_ring
            rw [e]
            exact le_trans (le_of_lt (exp_pos C)) (le_add_nonneg_r' (hlog0 x hx1))
          · rw [log_nonpos (le_of_lt hp)]
            have e : -(0 : Real) = 0 := by mach_ring
            rw [e]
            exact le_trans (le_of_lt (exp_pos C)) (le_add_nonneg_r' (hlog0 x hx1))
        show exp (A.eval x) - log (B.eval x) ≤ exp (exp (exp x + (K)) + (M + 1)) + exp C
        -- Absorption: `log x ≤ x ≤ exp (exp (exp x + K) + M)`, valid because `x ≥ exp (-(K+M))`.
        have habs : log x ≤ exp (exp (exp x + K) + M) := by
          have g1 : x + x ≤ exp x := two_mul_le_exp hx0
          have g2 : 1 + (exp x + K) ≤ exp (exp x + K) := one_add_le_exp _
          have g3 : 1 + (exp (exp x + K) + M) ≤ exp (exp (exp x + K) + M) := one_add_le_exp _
          have gKM : -(K + M) ≤ x := le_trans (le_trans (le_one_add _) (one_add_le_exp _)) hXE
          -- `x ≤ 1 + (exp (exp x + K) + M)`
          have w : (0 : Real) ≤ x + (K + M) := by
            have u := add_le_add_wit gKM (le_refl (K + M))
            have eu : -(K + M) + (K + M) = (0 : Real) := by mach_mpoly [K, M]
            rw [eu] at u; exact u
          have htwo : (0 : Real) ≤ 1 + 1 :=
            le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax)
          have s1 : x ≤ x + x + (K + M) + 1 + 1 := by
            have u1 : x + 0 + 0 ≤ x + (x + (K + M)) + (1 + 1) :=
              add_le_add_wit (add_le_add_wit (le_refl x) w) htwo
            have e1 : x + (0 : Real) + 0 = x := by mach_ring
            have e2 : x + (x + (K + M)) + ((1 : Real) + 1) = x + x + (K + M) + 1 + 1 := by
              mach_ring
            rw [e1, e2] at u1; exact u1
          have s2 : x + x + (K + M) + 1 + 1 ≤ exp x + (K + M) + 1 + 1 :=
            add_le_add_wit (add_le_add_wit (add_le_add_wit g1 (le_refl (K + M))) (le_refl 1))
              (le_refl 1)
          have s3 : exp x + (K + M) + 1 + 1 ≤ 1 + (exp (exp x + K) + M) := by
            have v := add_le_add_wit g2 (le_refl M)
            have e1 : 1 + (exp x + K) + M = exp x + (K + M) + 1 := by mach_ring
            rw [e1] at v
            have u := add_le_add_wit v (le_refl (1 : Real))
            have e2 : exp (exp x + K) + M + 1 = 1 + (exp (exp x + K) + M) := by mach_ring
            rw [e2] at u; exact u
          have hxle : x ≤ exp (exp (exp x + K) + M) :=
            le_trans s1 (le_trans s2 (le_trans s3 g3))
          exact le_trans (log_le_self_on_ray hx1) hxle
        have hsum : exp (A.eval x) + (exp C + log x)
            ≤ exp (exp (exp x + K) + (M + 1)) + exp C := by
          have d1 : exp (A.eval x) + log x
              ≤ exp (exp (exp x + K) + M) + exp (exp (exp x + K) + M) :=
            add_le_add_wit hexpA habs
          have d2 : exp (exp (exp x + K) + M) + exp (exp (exp x + K) + M)
              ≤ exp (exp (exp x + K) + M + 1) := exp_add_one_doubles _
          have d3 : exp (A.eval x) + log x ≤ exp (exp (exp x + K) + (M + 1)) := by
            have e : exp (exp x + K) + M + 1 = exp (exp x + K) + (M + 1) := by mach_ring
            rw [e] at d2; exact le_trans d1 d2
          have d4 := add_le_add_wit d3 (le_refl (exp C))
          have e1 : exp (A.eval x) + log x + exp C = exp (A.eval x) + (exp C + log x) := by
            mach_ring
          rw [e1] at d4; exact d4
        have hfin : exp (A.eval x) - log (B.eval x) ≤ exp (A.eval x) + (exp C + log x) := by
          have v := add_le_add_wit (le_refl (exp (A.eval x))) hBx
          have e : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
            mach_ring
          rw [e] at v; exact v
        exact le_trans hfin hsum

/-! ### The remaining obstruction, isolated

`V₂`'s proof consumed *finiteness of sign changes*: it works only because `X₀` can be pushed past
the last crossing, and at depth 2 that is a hand check over five closed forms. Making the induction
general means proving it at every depth. This section reduces that to **one** statement, so the gap
is a named proposition rather than a vague blocker. -/

/-- **Eventually of constant sign** — positive on a ray, or non-positive on a ray.

Non-positive rather than negative because the totalisation makes `0` a perfectly ordinary value:
`log y = 0` for `y ≤ 0`, so a subtree sitting at exactly `0` behaves like a negative one. -/
def EvSign (f : Real → Real) : Prop :=
  (∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < f x)
  ∨ (∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → f x ≤ 0)

/-- **The one case the induction cannot discharge**: a genuine difference of log-exp functions,
`exp (A x) − log (B x)` on a ray where the right child is *positive* so its log is the real one.

This is the point where Hardy-field / o-minimality machinery would apply, and it is stated with the
positivity of `B` as a hypothesis precisely because that is the branch where the totalisation stops
helping. -/
def SignHardCase : Prop :=
  ∀ (A B : EMLTree) (X₀ : Real), 1 ≤ X₀ → (∀ x : Real, X₀ ≤ x → 0 < B.eval x) →
    EvSign (fun x => exp (A.eval x) - log (B.eval x))

/-- **The reduction.** One statement about differences of log-exp functions gives eventual
sign-definiteness for *every* EML tree, at every depth.

Two things are worth noticing in the proof.

**Totalisation helps rather than hurts.** Where the right child is eventually non-positive, its log
is identically `0` on that ray, so the node is `exp (A x)`, which is **positive** — sign-definite for
free. The convention that looked like a wart is what makes this branch trivial.

**The left child is never inspected.** The induction hypothesis is used only on `B`. Whatever `A`
does, the node's sign is decided by whether the right child's log is real or totalised away. -/
theorem evSign_of_hard (h : SignHardCase) : ∀ t : EMLTree, EvSign t.eval := by
  intro t
  induction t with
  | const c =>
      rcases lt_total 0 c with hc | hc | hc
      · exact Or.inl ⟨1, le_refl 1, fun x _ => hc⟩
      · exact Or.inr ⟨1, le_refl 1, fun x _ => le_of_eq hc.symm⟩
      · exact Or.inr ⟨1, le_refl 1, fun x _ => le_of_lt hc⟩
  | var =>
      exact Or.inl ⟨1, le_refl 1, fun x hx => lt_of_lt_of_le zero_lt_one_ax hx⟩
  | eml A B _ ihB =>
      rcases ihB with ⟨XB, hXB1, hpos⟩ | ⟨XB, hXB1, hnp⟩
      · -- right child eventually positive: the hard case, assumed
        exact h A B XB hXB1 hpos
      · -- right child eventually non-positive: its log is totalised to `0`, so the node is `exp (A x)`
        refine Or.inl ⟨XB, hXB1, ?_⟩
        intro x hx
        show 0 < exp (A.eval x) - log (B.eval x)
        rw [log_nonpos (hnp x hx)]
        have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
        rw [e]
        exact exp_pos _


/-! ### Headline: depth-2 intermediate-growth exclusion

`mx_not_in_eml_depth_le_2` excludes `M·x` at depth ≤ 2. Reading its proof, nothing in it is about
multiplication: it only uses where `M·x` sits in the growth order. The theorem below is that
argument stated for the *band* rather than the example, and `M·x`, `x²`, `x³`, … become
applications.

**On the third hypothesis — do not paraphrase it as "sub-exponential".** The condition is
`∃` arbitrarily large `x` with `f x < exp x − x − C`, for every `C`. That is **not** the asymptotic
assertion `f = o(exp x)`: it demands nothing eventually, only *infinitely often*, and it is
implied by — but strictly weaker than — the usual growth statement. The theorem is more interesting
for it, because it requires no regularity of `f` whatsoever.

Likewise "unbounded" means unbounded above *on every ray*, and "superlinear" means above the
identity at arbitrarily large points, not eventually. -/

/-- **Depth-2 intermediate-growth exclusion.** No function that is unbounded above, is above the
identity at arbitrarily large points, and drops below `exp x − x − C` at arbitrarily large points
for every `C`, is computed by any EML tree of depth ≤ 2.

The three hypotheses are each consumed by exactly one branch, and each is *necessary* — dropping any
one admits a depth-≤2 member:

* `H1` (unbounded above on every ray) kills `const` and, in the `eml` case, the branch where the
  left child's exponential is bounded — there the node is trapped between a constant ceiling and the
  right child's log floor.
* `H3` (eventually above `x`) kills `var`. Without it `f = x` satisfies everything else and sits at
  depth 0.
* `H2` (below `exp x − x − C` at arbitrarily large points, for every `C`) kills the branch where the
  left child's exponential dominates `exp x`, since the right child's log is at most linear. Note
  again that this is an *infinitely often* condition, not an eventual one.

Note what is *not* assumed: nothing about continuity, monotonicity, or `f` being given by a formula. -/
theorem superlinear_subexp_not_depth_le_two (f : Real → Real)
    (H1 : ∀ K X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ K < f x)
    (H2 : ∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ f x < exp x - x - C)
    (H3 : ∀ X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ x < f x)
    (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = f x) : False := by
  cases t with
  | const c =>
      obtain ⟨x, _, hx1, hlt⟩ := H1 c 1
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hv : c = f x := h x hx0
      rw [← hv] at hlt; exact lt_irrefl_ax c hlt
  | var =>
      obtain ⟨x, _, hx1, hlt⟩ := H3 1
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hv : x = f x := h x hx0
      rw [← hv] at hlt; exact lt_irrefl_ax x hlt
  | eml A B =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      rcases depth_le_one_exp_bounded_or_grows A hA with ⟨K, hK⟩ | ⟨T, hT⟩
      · -- left child's exponential bounded: the node is capped by `K − Cl`
        obtain ⟨Cl, X₀, hX1, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
        obtain ⟨x, hxX, hx1, hlt⟩ := H1 (K - Cl) X₀
        have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        have hv : exp (A.eval x) - log (B.eval x) = f x := h x hx0
        have hcap : f x ≤ K - Cl := by
          rw [← hv]
          have v := add_le_add_wit (hK x hx1) (neg_le_neg_wit (hCl x hxX))
          have e1 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
            mach_ring
          have e2 : K + -Cl = K - Cl := by mach_ring
          rw [e1, e2] at v; exact v
        exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hcap)
      · -- left child's exponential dominates `exp x`: the node is floored by `exp x − x − C`
        obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB
        obtain ⟨x, hxT, hx1, hlt⟩ := H2 C T
        have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        have hv : exp (A.eval x) - log (B.eval x) = f x := h x hx0
        have hfloor : exp x - x - C ≤ f x := by
          rw [← hv]
          have v := add_le_add_wit (hT x hxT) (neg_le_neg_wit (hC x hx1))
          have e1 : exp x + -(x + C) = exp x - x - C := by mach_mpoly [exp x, x, C]
          have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
            mach_ring
          rw [e1, e2] at v; exact v
        exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hfloor)


/-- **`M·x` re-derived from the band.** `mx_not_in_eml_depth_le_2` was proved directly; this obtains
it from `superlinear_subexp_not_depth_le_two` with no reasoning about multiplication at all — the
three hypotheses are discharged by `exp t ≥ 1 + t`, `1 < M`, and `exp_beats_linear_past`.

The point is the same one the netlist theorems made: the bespoke proof was doing no work the band
argument does not do. -/
theorem mx_not_depth_le_two_via_band (M : Real) (hM1 : 1 < M) (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = M * x) : False := by
  have hMpos : (0 : Real) < M := lt_trans_ax zero_lt_one_ax hM1
  refine superlinear_subexp_not_depth_le_two (fun x => M * x) ?_ ?_ ?_ t ht h
  · -- unbounded: `M·x ≥ x` and `x` clears any `K`
    intro K X
    refine ⟨1 + exp K + exp X, ?_, ?_, ?_⟩
    · have hX : X ≤ exp X := le_trans (le_one_add X) (one_add_le_exp X)
      have v : (0 : Real) + 0 + exp X ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos K)))
          (le_refl (exp X))
      have e : (0 : Real) + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans hX v
    · have v : (1 : Real) + 0 + 0 ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos K)))
          (le_of_lt (exp_pos X))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    · have hxpos : (0 : Real) < 1 + exp K + exp X :=
        add_pos_of_nonneg_pos
          (le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) (exp_pos K))) (exp_pos X)
      have hKx : K < 1 + exp K + exp X := by
        have hK : K < exp K := by
          have tK := one_add_le_exp K
          have eK : (1 : Real) + K = K + 1 := by mach_ring
          rw [eK] at tK
          exact lt_of_lt_of_le (lt_succ_self K) tK
        have v : (0 : Real) + exp K + 0 ≤ 1 + exp K + exp X :=
          add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp K)))
            (le_of_lt (exp_pos X))
        have e : (0 : Real) + exp K + 0 = exp K := by mach_ring
        rw [e] at v
        exact lt_of_lt_of_le (lt_of_lt_of_le hK (le_of_eq (by mach_ring : exp K = exp K))) v
      have hgrow : 1 + exp K + exp X < M * (1 + exp K + exp X) := by
        have v := mul_lt_mul_of_pos_right hM1 hxpos
        have e : (1 : Real) * (1 + exp K + exp X) = 1 + exp K + exp X := by mach_ring
        rw [e] at v; exact v
      exact lt_trans_ax hKx hgrow
  · -- sub-exponential: `M·x < exp x − x − C` is `(M+1)·x + C < exp x`
    intro C X
    have hMp : (0 : Real) ≤ M + 1 :=
      le_of_lt (add_pos_of_nonneg_pos (le_of_lt hMpos) zero_lt_one_ax)
    obtain ⟨x, hxX, hx1, hlt⟩ := exp_beats_linear_past (α := M + 1) (β := C) hMp X
    refine ⟨x, hxX, hx1, ?_⟩
    have e : (M + 1) * x + C = M * x + x + C := by mach_ring
    rw [e] at hlt
    have v := add_lt_add_left hlt (-x - C)
    have e1 : -x - C + (M * x + x + C) = M * x := by mach_mpoly [M, x, C]
    have e2 : -x - C + exp x = exp x - x - C := by mach_mpoly [exp x, x, C]
    rw [e1, e2] at v; exact v
  · -- superlinear: `x < M·x` since `M > 1`
    intro X
    refine ⟨1 + exp X, ?_, ?_, ?_⟩
    · have hX : X ≤ exp X := le_trans (le_one_add X) (one_add_le_exp X)
      exact le_trans hX (le_one_add (exp X))
    · have v : (1 : Real) + 0 ≤ 1 + exp X := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos X))
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    · have hxpos : (0 : Real) < 1 + exp X :=
        add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) (exp_pos X)
      have v := mul_lt_mul_of_pos_right hM1 hxpos
      have e : (1 : Real) * (1 + exp X) = 1 + exp X := by mach_ring
      rw [e] at v; exact v


/-! ### `exp` beats every fixed power — once, not once per degree

The band theorem's third hypothesis for `f = xⁿ` is `xⁿ + x + C < exp x` at arbitrarily large
points. The naive route is a ladder of `exp_beats_quadratic`, `exp_beats_cubic`, … — exactly the
per-example pattern the band theorem exists to escape.

It is avoidable. Because the hypothesis only asks for the inequality *somewhere large*, the witness
can be **chosen**, and choosing `x = exp w` collapses the problem: `(exp w)ⁿ = exp (n·w)`, so
`xⁿ < exp x` becomes `n·w < exp w` — beating a **linear** function, which `exp_beats_linear_past`
already does for arbitrary real slope. One lemma, every degree.

`n·w` is built additively (`natMul`) rather than by a `Nat → Real` cast, and the witness is never
halved, so no division enters. -/

/-- `n` copies of `w` summed. Additive so that no `Nat → Real` cast is needed. -/
noncomputable def natMul : Nat → Real → Real
  | 0, _ => 0
  | (n + 1), w => w + natMul n w

/-- `xⁿ` by recursion. -/
noncomputable def powNat (x : Real) : Nat → Real
  | 0 => 1
  | (n + 1) => x * powNat x n

theorem natMul_nonneg : ∀ n : Nat, (0 : Real) ≤ natMul n 1 := by
  intro n
  induction n with
  | zero => exact le_refl 0
  | succ k ih =>
      show (0 : Real) ≤ 1 + natMul k 1
      have v : (0 : Real) + 0 ≤ 1 + natMul k 1 :=
        add_le_add_wit (le_of_lt zero_lt_one_ax) ih
      have e : (0 : Real) + 0 = 0 := by mach_ring
      rw [e] at v; exact v

/-- `natMul n w = (natMul n 1) · w` — the cast-free way to say `n·w`. -/
theorem natMul_eq (w : Real) : ∀ n : Nat, natMul n w = natMul n 1 * w := by
  intro n
  induction n with
  | zero => show (0 : Real) = 0 * w; mach_ring
  | succ k ih =>
      show w + natMul k w = (1 + natMul k 1) * w
      rw [ih]; mach_ring

/-- `exp (n·w) = (exp w)ⁿ`. -/
theorem exp_natMul (w : Real) : ∀ n : Nat, exp (natMul n w) = powNat (exp w) n := by
  intro n
  induction n with
  | zero => show exp (0 : Real) = 1; exact exp_zero
  | succ k ih =>
      show exp (w + natMul k w) = exp w * powNat (exp w) k
      rw [exp_add, ih]

theorem one_le_powNat {x : Real} (hx : 1 ≤ x) : ∀ n : Nat, 1 ≤ powNat x n := by
  intro n
  induction n with
  | zero => exact le_refl 1
  | succ k ih =>
      show (1 : Real) ≤ x * powNat x k
      have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx
      have h1 : x * 1 ≤ x * powNat x k := mul_le_mul_of_nonneg_left ih hx0
      have e : x * (1 : Real) = x := by mach_ring
      rw [e] at h1
      exact le_trans hx h1

/-- **`exp` beats `x^(k+2) + x + C` at arbitrarily large points, for every `k`.**

Degree-uniform: one theorem, not a ladder. The exponent is written `k + 2` because degree ≤ 1 is
genuinely excluded — `x` itself is EML at depth 0. -/
theorem exp_beats_powNat (k : Nat) (C X : Real) :
    ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ powNat x (k + 2) + x + C < exp x := by
  have hNn : (0 : Real) ≤ natMul (k + 2) 1 := natMul_nonneg _
  obtain ⟨w, hwT, hw1, hw⟩ :=
    exp_beats_linear_past (α := natMul (k + 2) 1) (β := 1) hNn (exp X + exp C + 1)
  -- the witness
  have hxpos : (0 : Real) < exp w := exp_pos w
  have hwe : 1 + w ≤ exp w := one_add_le_exp w
  have hbig : exp X + exp C + 1 + 1 ≤ exp w := by
    have v := add_le_add_wit (le_refl (1 : Real)) hwT
    have e : (1 : Real) + (exp X + exp C + 1) = exp X + exp C + 1 + 1 := by mach_ring
    rw [e] at v; exact le_trans v hwe
  have hx1 : (1 : Real) ≤ exp w := by
    have hXp : (0 : Real) < exp X := exp_pos X
    have hCp : (0 : Real) < exp C := exp_pos C
    have v : (0 : Real) + 0 + 1 + 0 ≤ exp X + exp C + 1 + 1 :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt hXp) (le_of_lt hCp)) (le_refl 1))
        (le_of_lt zero_lt_one_ax)
    have e : (0 : Real) + 0 + 1 + 0 = 1 := by mach_ring
    rw [e] at v; exact le_trans v hbig
  have hxX : X ≤ exp w := by
    have hXe : X ≤ exp X := self_le_exp X
    have v : exp X + 0 + 0 + 0 ≤ exp X + exp C + 1 + 1 :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl (exp X)) (le_of_lt (exp_pos C)))
        (le_of_lt zero_lt_one_ax)) (le_of_lt zero_lt_one_ax)
    have e : exp X + (0 : Real) + 0 + 0 = exp X := by mach_ring
    rw [e] at v; exact le_trans hXe (le_trans v hbig)
  have hxC : C + 1 + 1 ≤ exp w := by
    have hCe : C ≤ exp C := self_le_exp C
    have v : (0 : Real) + C + 1 + 1 ≤ exp X + exp C + 1 + 1 :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos X)) hCe) (le_refl 1))
        (le_refl 1)
    have e : (0 : Real) + C + 1 + 1 = C + 1 + 1 := by mach_ring
    rw [e] at v; exact le_trans v hbig
  refine ⟨exp w, hxX, hx1, ?_⟩
  -- `x^(k+2) = exp (Nn · w)`
  have hpow : powNat (exp w) (k + 2) = exp (natMul (k + 2) 1 * w) := by
    rw [← natMul_eq w (k + 2), exp_natMul]
  -- `exp x ≥ x^(k+2) + x^(k+2)`
  have hdouble : powNat (exp w) (k + 2) + powNat (exp w) (k + 2) ≤ exp (exp w) := by
    rw [hpow]
    have hstep : natMul (k + 2) 1 * w + 1 ≤ exp w := le_of_lt hw
    exact le_trans (exp_add_one_doubles _) (exp_monotone hstep)
  -- `x + C < x^(k+2)`, since the degree is at least two
  have hsq : exp w * exp w ≤ powNat (exp w) (k + 2) := by
    show exp w * exp w ≤ exp w * (exp w * powNat (exp w) k)
    have h1 : exp w * 1 ≤ exp w * powNat (exp w) k :=
      mul_le_mul_of_nonneg_left (one_le_powNat hx1 k) (le_of_lt hxpos)
    have e : exp w * (1 : Real) = exp w := by mach_ring
    rw [e] at h1
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hxpos)
  have hlin : exp w + C < exp w * exp w := by
    have hEm1 : (0 : Real) ≤ exp w - 1 := by
      have v := add_le_add_wit hx1 (le_refl (-1 : Real))
      have e1 : (1 : Real) + -1 = 0 := by mach_ring
      have e2 : exp w + -1 = exp w - 1 := by mach_ring
      rw [e1, e2] at v; exact v
    have h1 : (exp w - 1) * 1 ≤ (exp w - 1) * exp w := mul_le_mul_of_nonneg_left hx1 hEm1
    have e1 : (exp w - 1) * (1 : Real) = exp w - 1 := by mach_ring
    have e2 : (exp w - 1) * exp w = exp w * exp w - exp w := by mach_ring
    rw [e1, e2] at h1
    have h2 : C + 1 ≤ exp w - 1 := by
      have v := add_le_add_wit hxC (le_refl (-1 : Real))
      have e3 : C + 1 + 1 + -1 = C + 1 := by mach_ring
      have e4 : exp w + -1 = exp w - 1 := by mach_ring
      rw [e3, e4] at v; exact v
    have h3 : C + 1 ≤ exp w * exp w - exp w := le_trans h2 h1
    have h4 : exp w + C < exp w + (C + 1) := add_lt_add_left (lt_succ_self C) (exp w)
    have h5 : exp w + (C + 1) ≤ exp w + (exp w * exp w - exp w) := add_le_add_left h3 (exp w)
    have e5 : exp w + (exp w * exp w - exp w) = exp w * exp w := by mach_mpoly [exp w]
    rw [e5] at h5
    exact lt_of_lt_of_le h4 h5
  have hfin : exp w + C < powNat (exp w) (k + 2) := lt_of_lt_of_le hlin hsq
  have hv : powNat (exp w) (k + 2) + (exp w + C)
      < powNat (exp w) (k + 2) + powNat (exp w) (k + 2) := add_lt_add_left hfin _
  have e : powNat (exp w) (k + 2) + (exp w + C)
      = powNat (exp w) (k + 2) + exp w + C := by mach_ring
  rw [e] at hv
  exact lt_of_lt_of_le hv hdouble


theorem self_le_powNat_succ2 {x : Real} (hx : 1 ≤ x) (k : Nat) : x ≤ powNat x (k + 2) := by
  show x ≤ x * (x * powNat x k)
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx
  have e : x * (1 : Real) = x := by mach_ring
  have u : x * 1 ≤ x * powNat x k := mul_le_mul_of_nonneg_left (one_le_powNat hx k) hx0
  rw [e] at u
  have v : x * 1 ≤ x * (x * powNat x k) :=
    mul_le_mul_of_nonneg_left (le_trans hx u) hx0
  rw [e] at v; exact v

theorem self_lt_powNat_succ2 {x : Real} (hx : 1 < x) (k : Nat) : x < powNat x (k + 2) := by
  show x < x * (x * powNat x k)
  have hx0 : (0 : Real) < x := lt_trans_ax zero_lt_one_ax hx
  have hx1 : (1 : Real) ≤ x := le_of_lt hx
  have e : x * (1 : Real) = x := by mach_ring
  have u : x * 1 ≤ x * powNat x k :=
    mul_le_mul_of_nonneg_left (one_le_powNat hx1 k) (le_of_lt hx0)
  rw [e] at u
  have hxx : x < x * x := by
    have v := mul_lt_mul_of_pos_right hx hx0
    have e1 : (1 : Real) * x = x := by mach_ring
    rw [e1] at v; exact v
  exact lt_of_lt_of_le hxx (mul_le_mul_of_nonneg_left u (le_of_lt hx0))

/-- **Every fixed power `x^(k+2)` is excluded at depth ≤ 2 — one proof for all degrees.**

`exp_beats_powNat` supplies the band theorem's third hypothesis degree-uniformly, so `x²`, `x³`, …
are all instances of `superlinear_subexp_not_depth_le_two`. No per-degree argument appears anywhere
below, and the exponent `k` is never inspected. -/
theorem powNat_not_depth_le_two (k : Nat) (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = powNat x (k + 2)) : False := by
  refine superlinear_subexp_not_depth_le_two (fun x => powNat x (k + 2)) ?_ ?_ ?_ t ht h
  · -- unbounded: `K < x ≤ x^(k+2)`
    intro K X
    have hKe : K < exp K := by
      have t1 := one_add_le_exp K
      have e : (1 : Real) + K = K + 1 := by mach_ring
      rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self K) t1
    have hXe : X ≤ exp X := self_le_exp X
    refine ⟨1 + exp K + exp X, ?_, ?_, ?_⟩
    · have v : (0 : Real) + 0 + exp X ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos K)))
          (le_refl (exp X))
      have e : (0 : Real) + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans hXe v
    · have v : (1 : Real) + 0 + 0 ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos K)))
          (le_of_lt (exp_pos X))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    · have hx1 : (1 : Real) ≤ 1 + exp K + exp X := by
        have v : (1 : Real) + 0 + 0 ≤ 1 + exp K + exp X :=
          add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos K)))
            (le_of_lt (exp_pos X))
        have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
        rw [e] at v; exact v
      have hKx : K < 1 + exp K + exp X := by
        have v : (0 : Real) + exp K + 0 ≤ 1 + exp K + exp X :=
          add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp K)))
            (le_of_lt (exp_pos X))
        have e : (0 : Real) + exp K + 0 = exp K := by mach_ring
        rw [e] at v; exact lt_of_lt_of_le hKe v
      exact lt_of_lt_of_le hKx (self_le_powNat_succ2 hx1 k)
  · -- sub-exponential, degree-uniformly
    intro C X
    obtain ⟨x, hxX, hx1, hlt⟩ := exp_beats_powNat k C X
    refine ⟨x, hxX, hx1, ?_⟩
    have v := add_lt_add_left hlt (-x - C)
    have e1 : -x - C + (powNat x (k + 2) + x + C) = powNat x (k + 2) := by
      mach_mpoly [powNat x (k + 2), x, C]
    have e2 : -x - C + exp x = exp x - x - C := by mach_mpoly [exp x, x, C]
    rw [e1, e2] at v; exact v
  · -- superlinear: `x < x^(k+2)` once `x > 1`
    intro X
    have hXe : X ≤ exp X := self_le_exp X
    have hgt : (1 : Real) < 1 + 1 + exp X := by
      have v : (1 : Real) + 0 + 0 < 1 + 1 + exp X :=
        lt_of_lt_of_le (add_lt_add_left (exp_pos X) ((1 : Real) + 0))
          (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt zero_lt_one_ax))
            (le_refl (exp X)))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      have e2 : (1 : Real) + 0 + exp X = 1 + 0 + exp X := rfl
      rw [e] at v; exact v
    refine ⟨1 + 1 + exp X, ?_, le_of_lt hgt, self_lt_powNat_succ2 hgt k⟩
    have v : (0 : Real) + 0 + exp X ≤ 1 + 1 + exp X :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt zero_lt_one_ax))
        (le_refl (exp X))
    have e : (0 : Real) + 0 + exp X = exp X := by mach_ring
    rw [e] at v; exact le_trans hXe v

/-- **`x²` is not EML at depth ≤ 2.** An instance of the band at `k = 0`.

Combined with `EMLDepthCost.mulPos_var_var_depth` (the constructed witness sits at depth **24**),
this brackets `3 ≤ d(x²) ≤ 24`. The gap is not a defect of the lower bound: the same constructor
library builds `1/x` at depth 6 where the optimal witness `invX4` is at depth 4, so the generic
combinators are known to overshoot even where the answer is settled. -/
theorem x_sq_not_depth_le_two (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = x * x) : False := by
  refine powNat_not_depth_le_two 0 t ht ?_
  intro x hx
  rw [h x hx]
  show x * x = x * (x * 1)
  mach_ring


/-- `x + x + C ≤ exp x` on a ray, for any `C`. Via `exp x = exp 1 · exp (x−1) ≥ 4(x−1)`, because
the exp gap needs a **ray** and `exp_beats_linear_past` only supplies a point. -/
theorem two_mul_add_le_exp (C : Real) : ∃ T : Real, ∀ x : Real, T ≤ x → x + x + C ≤ exp x := by
  refine ⟨exp C + 1 + 1 + 1 + 1, ?_⟩
  intro x hx
  have hCp : (0 : Real) < exp C := exp_pos C
  have hC : C ≤ exp C := self_le_exp C
  have hstep : ∀ a b : Real, a ≤ b → a + 1 + 1 + 1 + 1 ≤ b + 1 + 1 + 1 + 1 := by
    intro a b hab
    exact add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit hab (le_refl 1))
      (le_refl 1)) (le_refl 1)) (le_refl 1)
  have hCx : C + 1 + 1 + 1 + 1 ≤ x := le_trans (hstep C (exp C) hC) hx
  have h0x : (0 : Real) + 1 + 1 + 1 + 1 ≤ x := le_trans (hstep 0 (exp C) (le_of_lt hCp)) hx
  have hx0 : (0 : Real) ≤ x := by
    have hfour : (0 : Real) ≤ 0 + 1 + 1 + 1 + 1 := by
      have e : (0 : Real) + 1 + 1 + 1 + 1 = 1 + 1 + 1 + 1 := by mach_ring
      rw [e]
      exact le_of_lt (add_pos_of_nonneg_pos (le_of_lt (add_pos_of_nonneg_pos
        (le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax))
        zero_lt_one_ax)) zero_lt_one_ax)
    exact le_trans hfour h0x
  have hx1 : (1 : Real) ≤ x := by
    have hone : (1 : Real) ≤ 0 + 1 + 1 + 1 + 1 := by
      have e : (0 : Real) + 1 + 1 + 1 + 1 = 1 + 1 + 1 + 1 := by mach_ring
      rw [e]
      exact le_trans (le_of_lt (lt_succ_self 1)) (le_trans (le_of_lt (lt_succ_self (1 + 1)))
        (le_of_lt (lt_succ_self (1 + 1 + 1))))
    exact le_trans hone h0x
  have hxm1 : (0 : Real) ≤ x - 1 := by
    have v := add_le_add_wit hx1 (le_refl (-1 : Real))
    have e1 : (1 : Real) + -1 = 0 := by mach_ring
    have e2 : x + -1 = x - 1 := by mach_ring
    rw [e1, e2] at v; exact v
  -- `exp x ≥ (1+1) · ((x−1)+(x−1))`
  have hdb : (x - 1) + (x - 1) ≤ exp (x - 1) := two_mul_le_exp hxm1
  have hsplit : exp x = exp 1 * exp (x - 1) := by
    have e : x = 1 + (x - 1) := by mach_ring
    rw [e, exp_add]
    have e2 : (1 : Real) + (x - 1) - 1 = x - 1 := by mach_ring
    rw [e2]
  have htwo : (0 : Real) ≤ 1 + 1 :=
    le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax)
  have hprod : (1 + 1) * ((x - 1) + (x - 1)) ≤ exp x := by
    rw [hsplit]
    have p1 : ((1 : Real) + 1) * ((x - 1) + (x - 1)) ≤ (1 + 1) * exp (x - 1) :=
      mul_le_mul_of_nonneg_left hdb htwo
    have p2 : ((1 : Real) + 1) * exp (x - 1) ≤ exp 1 * exp (x - 1) := by
      have q : exp (x - 1) * (1 + 1) ≤ exp (x - 1) * exp 1 :=
        mul_le_mul_of_nonneg_left (one_add_le_exp 1) (le_of_lt (exp_pos _))
      have e1 : exp (x - 1) * ((1 : Real) + 1) = (1 + 1) * exp (x - 1) := by mach_ring
      have e2 : exp (x - 1) * exp 1 = exp 1 * exp (x - 1) := by mach_ring
      rw [e1, e2] at q; exact q
    exact le_trans p1 p2
  -- `x + x + C ≤ (1+1)·((x−1)+(x−1))`, i.e. `x + x ≥ C + 4`
  have hcore : C + 1 + 1 + 1 + 1 ≤ x + x := by
    have v := add_le_add_wit hCx hx0
    have e : C + 1 + 1 + 1 + 1 + (0 : Real) = C + 1 + 1 + 1 + 1 := by mach_ring
    rw [e] at v; exact v
  have hslack : (0 : Real) ≤ (x + x) - (C + 1 + 1 + 1 + 1) := by
    have v := add_le_add_wit hcore (le_refl (-(C + 1 + 1 + 1 + 1)))
    have e1 : C + 1 + 1 + 1 + 1 + -(C + 1 + 1 + 1 + 1) = (0 : Real) := by mach_mpoly [C]
    have e2 : x + x + -(C + 1 + 1 + 1 + 1) = (x + x) - (C + 1 + 1 + 1 + 1) := by
      mach_mpoly [x, C]
    rw [e1, e2] at v; exact v
  have hlin : x + x + C ≤ (1 + 1) * ((x - 1) + (x - 1)) := by
    have edecomp : ((1 : Real) + 1) * ((x - 1) + (x - 1))
        = x + x + C + ((x + x) - (C + 1 + 1 + 1 + 1)) := by mach_mpoly [x, C]
    rw [edecomp]
    exact le_add_nonneg_r' hslack
  exact le_trans hlin hprod

/-- **The exp gap, one level up.** For `A` of depth ≤ 2, `exp (A x)` is either bounded above on a
ray or eventually dominates `exp x` — the same dichotomy `depth_le_one_exp_bounded_or_grows` gives at
depth 1, and the brick a depth-3 band argument needs on its left child. -/
theorem depth_le_two_exp_bounded_or_grows (A : EMLTree) (hA : A.depth ≤ 2) :
    (∃ K X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → exp (A.eval x) ≤ K)
    ∨ (∃ T : Real, ∀ x : Real, T ≤ x → exp x ≤ exp (A.eval x)) := by
  cases A with
  | const c => exact Or.inl ⟨exp c, 1, le_refl 1, fun x _ => le_refl _⟩
  | var => exact Or.inr ⟨1, fun x _ => le_refl _⟩
  | eml A' B' =>
      have hA' : A'.depth ≤ 1 := by
        simp only [EMLTree.depth] at hA
        have := Nat.le_max_left A'.depth B'.depth; omega
      have hB' : B'.depth ≤ 1 := by
        simp only [EMLTree.depth] at hA
        have := Nat.le_max_right A'.depth B'.depth; omega
      rcases depth_le_one_exp_bounded_or_grows A' hA' with ⟨K, hK⟩ | ⟨T, hT⟩
      · obtain ⟨Cl, X₀, hX1, hCl⟩ := depth_le_one_log_lower_at_infinity B' hB'
        refine Or.inl ⟨exp (K - Cl), X₀, hX1, ?_⟩
        intro x hx
        have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
        refine exp_monotone ?_
        show exp (A'.eval x) - log (B'.eval x) ≤ K - Cl
        have v := add_le_add_wit (hK x hx1) (neg_le_neg_wit (hCl x hx))
        have e1 : exp (A'.eval x) + -log (B'.eval x) = exp (A'.eval x) - log (B'.eval x) := by
          mach_ring
        have e2 : K + -Cl = K - Cl := by mach_ring
        rw [e1, e2] at v; exact v
      · obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B' hB'
        obtain ⟨T2, hT2⟩ := two_mul_add_le_exp C
        refine Or.inr ⟨exp T + exp T2 + 1, ?_⟩
        intro x hx
        have hTx : T ≤ x := by
          have v : exp T + 0 + 0 ≤ exp T + exp T2 + 1 :=
            add_le_add_wit (add_le_add_wit (le_refl (exp T)) (le_of_lt (exp_pos T2)))
              (le_of_lt zero_lt_one_ax)
          have e : exp T + (0 : Real) + 0 = exp T := by mach_ring
          rw [e] at v
          exact le_trans (self_le_exp T) (le_trans v hx)
        have hT2x : T2 ≤ x := by
          have v : (0 : Real) + exp T2 + 0 ≤ exp T + exp T2 + 1 :=
            add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T)) (le_refl (exp T2)))
              (le_of_lt zero_lt_one_ax)
          have e : (0 : Real) + exp T2 + 0 = exp T2 := by mach_ring
          rw [e] at v
          exact le_trans (self_le_exp T2) (le_trans v hx)
        have hx1 : (1 : Real) ≤ x := by
          have v : (0 : Real) + 0 + 1 ≤ exp T + exp T2 + 1 :=
            add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T)) (le_of_lt (exp_pos T2)))
              (le_refl 1)
          have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
          rw [e] at v; exact le_trans v hx
        refine exp_monotone ?_
        show x ≤ exp (A'.eval x) - log (B'.eval x)
        have g1 : exp x ≤ exp (A'.eval x) := hT x hTx
        have g2 : log (B'.eval x) ≤ x + C := hC x hx1
        have g3 : x + x + C ≤ exp x := hT2 x hT2x
        have s1 : exp x - (x + C) ≤ exp (A'.eval x) - log (B'.eval x) := by
          have v := add_le_add_wit g1 (neg_le_neg_wit g2)
          have e1 : exp x + -(x + C) = exp x - (x + C) := by mach_ring
          have e2 : exp (A'.eval x) + -log (B'.eval x)
              = exp (A'.eval x) - log (B'.eval x) := by mach_ring
          rw [e1, e2] at v; exact v
        have s2 : x ≤ exp x - (x + C) := by
          have v := add_le_add_wit g3 (le_refl (-(x + C)))
          have e1 : x + x + C + -(x + C) = x := by mach_mpoly [x, C]
          have e2 : exp x + -(x + C) = exp x - (x + C) := by mach_ring
          rw [e1, e2] at v; exact v
        exact le_trans s2 s1

/-- **The log ceiling, one level up — and it is at the *exponential* scale.**

`depth_le_one_log_le_linear` caps a depth-≤1 tree's log at `x + C`, **linear**. This is the depth-2
mirror, and the answer is `exp x + K`: one level of nesting moves the log ceiling from linear to
exponential.

**That single change is why the growth band does not lift to depth 3.** At depth 2 the band argument
works because the left child's exponential floor (`exp x`, from
`depth_le_one_exp_bounded_or_grows`) and the right child's log ceiling (`x + C`) sit at *different
scales*, so the node cannot cancel. One level up, `depth_le_two_exp_bounded_or_grows` still gives the
floor `exp x` — but the ceiling here is also `exp x + K`. **The scales meet, and cancellation becomes
possible.** The obstruction is a measured statement rather than a worry. -/
theorem depth_le_two_log_le_exp (B : EMLTree) (hB : B.depth ≤ 2) :
    ∃ K X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → log (B.eval x) ≤ exp x + K := by
  obtain ⟨K', M, XB, hXB1, hU⟩ := depth_le_two_growth_envelope B hB
  refine ⟨exp K' + 1, XB + exp (M - K'), ?_, ?_⟩
  · have v : XB + 0 ≤ XB + exp (M - K') := add_le_add_wit (le_refl XB) (le_of_lt (exp_pos _))
    have e : XB + (0 : Real) = XB := by mach_ring
    rw [e] at v; exact le_trans hXB1 v
  · intro x hx
    have hXBx : XB ≤ x := by
      have v : XB + 0 ≤ XB + exp (M - K') := add_le_add_wit (le_refl XB) (le_of_lt (exp_pos _))
      have e : XB + (0 : Real) = XB := by mach_ring
      rw [e] at v; exact le_trans v hx
    have hMKx : exp (M - K') ≤ x := by
      have v : (0 : Real) + exp (M - K') ≤ XB + exp (M - K') :=
        add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hXB1) (le_refl _)
      have e : (0 : Real) + exp (M - K') = exp (M - K') := by mach_ring
      rw [e] at v; exact le_trans v hx
    have hbound := hU x hXBx
    have hMle : M ≤ exp (exp x + K') := by
      have a2 : M - K' ≤ x := le_trans (self_le_exp _) hMKx
      have a4 : M - K' ≤ exp x := le_trans a2 (self_le_exp x)
      have a5 : M ≤ exp x + K' := by
        have v := add_le_add_wit a4 (le_refl K')
        have e1 : M - K' + K' = M := by mach_mpoly [M, K']
        rw [e1] at v; exact v
      exact le_trans a5 (self_le_exp _)
    have hdbl : B.eval x ≤ exp (exp x + K' + 1) := by
      have v : exp (exp x + K') + M ≤ exp (exp x + K') + exp (exp x + K') :=
        add_le_add_left hMle _
      exact le_trans hbound (le_trans v (exp_add_one_doubles _))
    have htarget : exp x + K' + 1 ≤ exp x + (exp K' + 1) := by
      have v := add_le_add_wit (add_le_add_wit (le_refl (exp x)) (self_le_exp K'))
        (le_refl (1 : Real))
      have e : exp x + exp K' + 1 = exp x + (exp K' + 1) := by mach_ring
      rw [e] at v; exact v
    have hpos : (0 : Real) < exp x + (exp K' + 1) :=
      add_pos_of_nonneg_pos (le_of_lt (exp_pos x))
        (add_pos_of_nonneg_pos (le_of_lt (exp_pos K')) zero_lt_one_ax)
    rcases lt_total 0 (B.eval x) with hp | hp | hp
    · exact le_trans (le_trans (log_le_log hp hdbl) (le_of_eq (log_exp _))) htarget
    · rw [log_nonpos (le_of_eq hp.symm)]; exact le_of_lt hpos
    · rw [log_nonpos (le_of_lt hp)]; exact le_of_lt hpos


/-! ### The first depth-3 exclusion — `V₂` used as a lower-bound tool

The scale table (`depth_le_two_log_le_exp`) says the *floor/ceiling* argument cannot lift the band to
depth 3, because the right child's log ceiling rises onto the left child's exponential floor. That is
a statement about one architecture, and this section goes around it on the branch where the floor
does not apply at all.

If the left child's exponential is **bounded**, the node can only reach a large value by the right
child's log going to `−∞` — that is, by `B` *decaying*. And `V₂` (`depth_le_two_decay_on_ray`) caps
how fast a positive depth-≤2 tree may decay: `−log (B x) ≤ C + log x`. So the node cannot outrun
`K + C + log x`. Anything that does is excluded.

This is the first use of `V₂` for a **lower bound**; every previous consumer used it to build an
upper envelope. -/

/-- **No depth-3 node with a bounded-exponential left child computes a superlogarithmic function.**

`Hlog` says `f` exceeds `C + log x` at arbitrarily large points, for every `C` — *infinitely often*,
not eventually, matching the band theorem's style. Both branches of the totalisation are handled:
where `B x ≤ 0` its log is `0` and the node is just `exp (A x) ≤ K`. -/
theorem depth_three_bounded_left_not_superlog (f : Real → Real) (A B : EMLTree)
    (hB : B.depth ≤ 2) (K XA : Real) (hXA : 1 ≤ XA)
    (hK : ∀ x : Real, XA ≤ x → exp (A.eval x) ≤ K)
    (Hlog : ∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ C + log x < f x)
    (h : ∀ x : Real, 0 < x → exp (A.eval x) - log (B.eval x) = f x) : False := by
  obtain ⟨C, XB, hXB1, hV⟩ := depth_le_two_decay_on_ray B hB
  obtain ⟨x, hxX, hx1, hlt⟩ := Hlog (C + K) (XA + XB + exp (-C))
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hnnB : (0 : Real) ≤ XB := le_trans (le_of_lt zero_lt_one_ax) hXB1
  have hnnA : (0 : Real) ≤ XA := le_trans (le_of_lt zero_lt_one_ax) hXA
  have hE : (0 : Real) ≤ exp (-C) := le_of_lt (exp_pos _)
  have hXAx : XA ≤ x := by
    have v : XA + 0 + 0 ≤ XA + XB + exp (-C) :=
      add_le_add_wit (add_le_add_wit (le_refl XA) hnnB) hE
    have e : XA + (0 : Real) + 0 = XA := by mach_ring
    rw [e] at v; exact le_trans v hxX
  have hXBx : XB ≤ x := by
    have v : (0 : Real) + XB + 0 ≤ XA + XB + exp (-C) :=
      add_le_add_wit (add_le_add_wit hnnA (le_refl XB)) hE
    have e : (0 : Real) + XB + 0 = XB := by mach_ring
    rw [e] at v; exact le_trans v hxX
  have hECx : exp (-C) ≤ x := by
    have v : (0 : Real) + 0 + exp (-C) ≤ XA + XB + exp (-C) :=
      add_le_add_wit (add_le_add_wit hnnA hnnB) (le_refl _)
    have e : (0 : Real) + 0 + exp (-C) = exp (-C) := by mach_ring
    rw [e] at v; exact le_trans v hxX
  -- `x ≥ exp (−C)` forces `C + log x ≥ 0`
  have hClog : (0 : Real) ≤ C + log x := by
    -- `exp (-C) ≤ x` gives `-C ≤ log x` by pushing `log` through `exp`
    have a4 : -C ≤ log x := by
      have m := log_le_log (exp_pos (-C)) hECx
      rw [log_exp] at m; exact m
    have v := add_le_add_wit a4 (le_refl C)
    have e1 : -C + C = (0 : Real) := by mach_ring
    have e2 : log x + C = C + log x := by mach_ring
    rw [e1, e2] at v; exact v
  have hval : exp (A.eval x) - log (B.eval x) = f x := h x hx0
  have hKx : exp (A.eval x) ≤ K := hK x hXAx
  rcases lt_total 0 (B.eval x) with hp | hp | hp
  · -- right child positive: `V₂` caps its decay, so the node is capped by `K + C + log x`
    have hdec : -log (B.eval x) ≤ C + log x := hV x hXBx hp
    have hcap : f x ≤ K + (C + log x) := by
      rw [← hval]
      have v := add_le_add_wit hKx hdec
      have e : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
      rw [e] at v; exact v
    have e2 : C + K + log x = K + (C + log x) := by mach_ring
    rw [e2] at hlt
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hcap)
  · -- right child zero: its log is totalised away, so the node is `exp (A x) ≤ K`
    have hz : log (B.eval x) = 0 := log_nonpos (le_of_eq hp.symm)
    have hcap : f x ≤ K := by
      rw [← hval, hz]
      have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
      rw [e]; exact hKx
    have hKlt : K < f x := by
      have v : K + 0 ≤ K + (C + log x) := add_le_add_left hClog K
      have e : K + (0 : Real) = K := by mach_ring
      rw [e] at v
      have e2 : C + K + log x = K + (C + log x) := by mach_ring
      rw [e2] at hlt
      exact lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt v hlt) (le_refl (f x))) (le_refl (f x))
    exact lt_irrefl_ax _ (lt_of_lt_of_le hKlt hcap)
  · -- right child negative: same, totalised away
    have hz : log (B.eval x) = 0 := log_nonpos (le_of_lt hp)
    have hcap : f x ≤ K := by
      rw [← hval, hz]
      have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
      rw [e]; exact hKx
    have hKlt : K < f x := by
      have v : K + 0 ≤ K + (C + log x) := add_le_add_left hClog K
      have e : K + (0 : Real) = K := by mach_ring
      rw [e] at v
      have e2 : C + K + log x = K + (C + log x) := by mach_ring
      rw [e2] at hlt
      exact lt_of_le_of_lt v hlt
    exact lt_irrefl_ax _ (lt_of_lt_of_le hKlt hcap)


/-! ### A depth-2 `eml` node cannot approximate the identity

The other branch of a depth-3 exclusion is a **squeeze**: if the left child's exponential dominates
`exp x` while the node computes something small, the depth-2 log ceiling forces
`exp x ≤ exp (A x) ≤ exp x + f x + K`, which pins `A x` to within an additive constant of `x`.

The pleasant surprise is that ruling that out needs no case analysis over shapes. If `A x ≤ x + c`
then the right child's log, being at most linear, forces `exp (A' x) ≤ 2x + c + D` — *sub*-exponential
— so the depth-1 exp gap puts `exp (A' x)` in its **bounded** class. But then `A x` is bounded by a
constant, and it was supposed to be at least `x`.

`var` does approximate the identity — it *is* the identity — which is why the statement is about
`eml` nodes specifically. That is the honest boundary of this argument. -/

/-- **No depth-2 `eml` node is squeezed between `x` and `x + c`.** -/
theorem depth_two_eml_not_near_identity (A' B' : EMLTree) (hA' : A'.depth ≤ 1) (hB' : B'.depth ≤ 1)
    (c X₀ : Real) (hX1 : 1 ≤ X₀)
    (hlow : ∀ x : Real, X₀ ≤ x → x ≤ exp (A'.eval x) - log (B'.eval x))
    (hhigh : ∀ x : Real, X₀ ≤ x → exp (A'.eval x) - log (B'.eval x) ≤ x + c) : False := by
  obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B' hB'
  obtain ⟨Cl, XL, hXL1, hCl⟩ := depth_le_one_log_lower_at_infinity B' hB'
  rcases depth_le_one_exp_bounded_or_grows A' hA' with ⟨K, hK⟩ | ⟨T, hT⟩
  · -- left child's exponential bounded ⟹ the node is bounded, contradicting `≥ x`
    have hpick : X₀ + XL + exp (K - Cl) ≤ X₀ + XL + exp (K - Cl) := le_refl _
    have hE : (0 : Real) ≤ exp (K - Cl) := le_of_lt (exp_pos _)
    have hX0n : (0 : Real) ≤ X₀ := le_trans (le_of_lt zero_lt_one_ax) hX1
    have hXLn : (0 : Real) ≤ XL := le_trans (le_of_lt zero_lt_one_ax) hXL1
    have hxX0 : X₀ ≤ X₀ + XL + exp (K - Cl) := by
      have v : X₀ + 0 + 0 ≤ X₀ + XL + exp (K - Cl) :=
        add_le_add_wit (add_le_add_wit (le_refl X₀) hXLn) hE
      have e : X₀ + (0 : Real) + 0 = X₀ := by mach_ring
      rw [e] at v; exact v
    have hxXL : XL ≤ X₀ + XL + exp (K - Cl) := by
      have v : (0 : Real) + XL + 0 ≤ X₀ + XL + exp (K - Cl) :=
        add_le_add_wit (add_le_add_wit hX0n (le_refl XL)) hE
      have e : (0 : Real) + XL + 0 = XL := by mach_ring
      rw [e] at v; exact v
    have hxE : exp (K - Cl) ≤ X₀ + XL + exp (K - Cl) := by
      have v : (0 : Real) + 0 + exp (K - Cl) ≤ X₀ + XL + exp (K - Cl) :=
        add_le_add_wit (add_le_add_wit hX0n hXLn) (le_refl _)
      have e : (0 : Real) + 0 + exp (K - Cl) = exp (K - Cl) := by mach_ring
      rw [e] at v; exact v
    have hx1 : (1 : Real) ≤ X₀ + XL + exp (K - Cl) := le_trans hX1 hxX0
    -- the node is at most `K − Cl`
    have hcap : exp (A'.eval (X₀ + XL + exp (K - Cl)))
        - log (B'.eval (X₀ + XL + exp (K - Cl))) ≤ K - Cl := by
      have v := add_le_add_wit (hK _ hx1) (neg_le_neg_wit (hCl _ hxXL))
      have e1 : exp (A'.eval (X₀ + XL + exp (K - Cl)))
          + -log (B'.eval (X₀ + XL + exp (K - Cl)))
          = exp (A'.eval (X₀ + XL + exp (K - Cl)))
            - log (B'.eval (X₀ + XL + exp (K - Cl))) := by mach_ring
      have e2 : K + -Cl = K - Cl := by mach_ring
      rw [e1, e2] at v; exact v
    -- but it is at least `x`, and `x` exceeds `K − Cl`
    have hbig : K - Cl < X₀ + XL + exp (K - Cl) :=
      lt_of_lt_of_le (lt_of_lt_of_le (lt_succ_self (K - Cl))
        (le_trans (le_of_eq (by mach_ring : K - Cl + 1 = 1 + (K - Cl)))
          (one_add_le_exp (K - Cl)))) hxE
    exact lt_irrefl_ax _ (lt_of_lt_of_le hbig (le_trans (hlow _ hxX0) hcap))
  · -- left child's exponential dominates `exp x` ⟹ the node exceeds `x + c`
    have hMp : (0 : Real) ≤ 1 + 1 :=
      le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax)
    obtain ⟨x, hxT, hx1, hlt⟩ :=
      exp_beats_linear_past (α := 1 + 1) (β := c + D) hMp (X₀ + exp T)
    have hX0n : (0 : Real) ≤ X₀ := le_trans (le_of_lt zero_lt_one_ax) hX1
    -- `exp T` rather than `T` in the threshold: `T` may be very negative.
    have hxX0 : X₀ ≤ x :=
      le_trans (le_add_nonneg_r' (le_of_lt (exp_pos T))) hxT
    have hTx : T ≤ x := by
      have w : exp T ≤ X₀ + exp T := by
        have u : X₀ + exp T = exp T + X₀ := by mach_ring
        rw [u]; exact le_add_nonneg_r' hX0n
      exact le_trans (self_le_exp T) (le_trans w hxT)
    have g1 : exp x ≤ exp (A'.eval x) := hT x hTx
    have g2 : log (B'.eval x) ≤ x + D := hD x hx1
    have hfloor : exp x - (x + D) ≤ exp (A'.eval x) - log (B'.eval x) := by
      have v := add_le_add_wit g1 (neg_le_neg_wit g2)
      have e1 : exp x + -(x + D) = exp x - (x + D) := by mach_ring
      have e2 : exp (A'.eval x) + -log (B'.eval x)
          = exp (A'.eval x) - log (B'.eval x) := by mach_ring
      rw [e1, e2] at v; exact v
    have hcap := hhigh x hxX0
    have hchain : exp x - (x + D) ≤ x + c := le_trans hfloor hcap
    have hbad : exp x ≤ (1 + 1) * x + (c + D) := by
      have v := add_le_add_wit hchain (le_refl (x + D))
      have e1 : exp x - (x + D) + (x + D) = exp x := by mach_mpoly [exp x, x, D]
      have e2 : x + c + (x + D) = (1 + 1) * x + (c + D) := by mach_mpoly [x, c, D]
      rw [e1, e2] at v; exact v
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hbad)


/-! ### The `A = var` sub-case of the depth-3 exclusion

`depth_three_bounded_left_not_superlog` and `depth_two_eml_not_near_identity` close every branch of
`t = eml A B` except `A = var`, which survives because `var` *is* the identity and so sits exactly at
the bottom of the squeeze. That sub-case reduces to `Log (⟦B⟧ x) = exp x − f x`, and `B`'s three
shapes are handled here — two discharged, one named. -/

/-- The one shape left in the whole depth-3 exclusion: right child an `eml` node.

Named rather than assumed away. The plan for it is in
`monogate-research/exploration/eml_depth3_exclusion_2026_08_13/`: squeeze `A''` to within `1` of
`exp x − f x`, then kill the five depth-1 shapes, each against exactly one band hypothesis. -/
def VarLeftEmlRightHard (f : Real → Real) : Prop :=
  ∀ A'' B'' : EMLTree, A''.depth ≤ 1 → B''.depth ≤ 1 →
    (∀ x : Real, 0 < x → exp x - log (exp (A''.eval x) - log (B''.eval x)) = f x) → False

/-- **The `A = var` sub-case, modulo one named shape.** `B = const` and `B = var` are discharged
outright; both die against sub-exponentiality alone. -/
theorem var_left_not_band (f : Real → Real) (B : EMLTree) (hB : B.depth ≤ 2)
    (Hsub : ∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ f x < exp x - x - C)
    (Hard : VarLeftEmlRightHard f)
    (h : ∀ x : Real, 0 < x → exp x - log (B.eval x) = f x) : False := by
  cases B with
  | const c =>
      -- `log c` is constant; sub-exponentiality forces `x < log c + log c`
      obtain ⟨x, hxX, hx1, hlt⟩ := Hsub (-log c) (exp (log c + log c))
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hval : exp x - log c = f x := h x hx0
      rw [← hval] at hlt
      have v := add_lt_add_left hlt (-exp x + log c + x)
      have e1 : -exp x + log c + x + (exp x - log c) = x := by mach_mpoly [exp x, log c, x]
      have e2 : -exp x + log c + x + (exp x - x - -log c) = log c + log c := by
        mach_mpoly [exp x, log c, x]
      rw [e1, e2] at v
      exact lt_irrefl_ax _ (lt_of_lt_of_le v (le_trans (self_le_exp _) hxX))
  | var =>
      -- `log x ≤ x` makes `x + 1 < log x` impossible
      obtain ⟨x, _, hx1, hlt⟩ := Hsub 1 1
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hval : exp x - log x = f x := h x hx0
      rw [← hval] at hlt
      have v := add_lt_add_left hlt (-exp x + log x + x)
      have e1 : -exp x + log x + x + (exp x - log x) = x := by mach_mpoly [exp x, log x, x]
      have e2 : -exp x + log x + x + (exp x - x - 1) = log x - 1 := by
        mach_mpoly [exp x, log x, x]
      rw [e1, e2] at v
      -- `x < log x − 1 ≤ x − 1` is absurd
      have hle : log x - 1 ≤ x - 1 := by
        have v := add_le_add_wit (log_le_self_on_ray hx1) (le_refl (-1 : Real))
        have e3 : log x + -1 = log x - 1 := by mach_ring
        have e4 : x + -1 = x - 1 := by mach_ring
        rw [e3, e4] at v; exact v
      have hxx : x < x - 1 := lt_of_lt_of_le v hle
      have hbad : x < x := by
        have w : x - 1 < x := by
          have t := add_lt_add_left zero_lt_one_ax (x - 1)
          have e3 : x - 1 + (0 : Real) = x - 1 := by mach_ring
          have e4 : x - 1 + (1 : Real) = x := by mach_ring
          rw [e3, e4] at t; exact t
        exact lt_trans_ax hxx w
      exact lt_irrefl_ax _ hbad
  | eml A'' B'' =>
      have hA'' : A''.depth ≤ 1 := by
        simp only [EMLTree.depth] at hB
        have := Nat.le_max_left A''.depth B''.depth; omega
      have hB'' : B''.depth ≤ 1 := by
        simp only [EMLTree.depth] at hB
        have := Nat.le_max_right A''.depth B''.depth; omega
      exact Hard A'' B'' hA'' hB'' h


/-- `log t ≤ t` on **all** of `(0,∞)`, not just `[1,∞)`. Below `1` the log is negative and the
bound is free; the ray version `log_le_self_on_ray` covers the rest. -/
theorem log_le_self_pos {t : Real} (ht : 0 < t) : log t ≤ t := by
  have hl1 : log (1 : Real) = 0 := by
    have hz : exp (0 : Real) = 1 := exp_zero
    rw [← hz, log_exp]
  rcases lt_total t 1 with hlt | heq | hgt
  · have v := log_lt_log ht hlt
    rw [hl1] at v
    exact le_trans (le_of_lt v) (le_of_lt ht)
  · rw [heq, hl1]; exact le_of_lt zero_lt_one_ax
  · exact log_le_self_on_ray (le_of_lt hgt)

/-- **`VarLeftEmlRightHard`, bounded-left branch.**

If the surviving shape's own left child has a bounded exponential, the node `eml A'' B''` is bounded
above by `K − Cl`, so *its* logarithm is bounded by a constant. But that logarithm must equal
`exp x − f x`, which sub-exponentiality forces above `x`. A constant cannot dominate `x`.

This is the same move as `depth_three_bounded_left_not_superlog` one level down, and it needs only
sub-exponentiality — neither unboundedness nor superlogarithmicity appears. -/
theorem varLeftEmlRight_bounded_left (f : Real → Real) (A'' B'' : EMLTree)
    (hB'' : B''.depth ≤ 1) (K : Real) (hK : ∀ x : Real, 1 ≤ x → exp (A''.eval x) ≤ K)
    (Hsub : ∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ f x < exp x - x - C)
    (h : ∀ x : Real, 0 < x → exp x - log (exp (A''.eval x) - log (B''.eval x)) = f x) :
    False := by
  obtain ⟨Cl, XL, hXL1, hCl⟩ := depth_le_one_log_lower_at_infinity B'' hB''
  obtain ⟨x, hxX, hx1, hlt⟩ := Hsub 0 (exp (exp (K - Cl)) + XL)
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hXLn : (0 : Real) ≤ XL := le_trans (le_of_lt zero_lt_one_ax) hXL1
  have hEn : (0 : Real) ≤ exp (exp (K - Cl)) := le_of_lt (exp_pos _)
  have hxXL : XL ≤ x := by
    have v : (0 : Real) + XL ≤ exp (exp (K - Cl)) + XL := add_le_add_wit hEn (le_refl XL)
    have e : (0 : Real) + XL = XL := by mach_ring
    rw [e] at v; exact le_trans v hxX
  have hxL : exp (K - Cl) ≤ x := by
    have v : exp (exp (K - Cl)) + 0 ≤ exp (exp (K - Cl)) + XL :=
      add_le_add_wit (le_refl _) hXLn
    have e : exp (exp (K - Cl)) + (0 : Real) = exp (exp (K - Cl)) := by mach_ring
    rw [e] at v
    exact le_trans (self_le_exp _) (le_trans v hxX)
  -- the node is bounded above by `K − Cl`
  have hnode : exp (A''.eval x) - log (B''.eval x) ≤ K - Cl := by
    have v := add_le_add_wit (hK x hx1) (neg_le_neg_wit (hCl x hxXL))
    have e1 : exp (A''.eval x) + -log (B''.eval x)
        = exp (A''.eval x) - log (B''.eval x) := by mach_ring
    have e2 : K + -Cl = K - Cl := by mach_ring
    rw [e1, e2] at v; exact v
  -- hence so is its logarithm, by `log t ≤ t` and totalisation below zero
  have hlogcap : log (exp (A''.eval x) - log (B''.eval x)) ≤ exp (K - Cl) := by
    rcases lt_total 0 (exp (A''.eval x) - log (B''.eval x)) with hp | hp | hp
    · exact le_trans (le_trans (log_le_self_pos hp) hnode) (self_le_exp _)
    · rw [log_nonpos (le_of_eq hp.symm)]; exact le_of_lt (exp_pos _)
    · rw [log_nonpos (le_of_lt hp)]; exact le_of_lt (exp_pos _)
  -- but it must equal `exp x − f x`, which sub-exponentiality forces above `x`
  have hval : exp x - log (exp (A''.eval x) - log (B''.eval x)) = f x := h x hx0
  have hgt : x < log (exp (A''.eval x) - log (B''.eval x)) := by
    rw [← hval] at hlt
    have v := add_lt_add_left hlt (-exp x + log (exp (A''.eval x) - log (B''.eval x)) + x)
    have e1 : -exp x + log (exp (A''.eval x) - log (B''.eval x)) + x
        + (exp x - log (exp (A''.eval x) - log (B''.eval x))) = x := by
      mach_mpoly [exp x, log (exp (A''.eval x) - log (B''.eval x)), x]
    have e2 : -exp x + log (exp (A''.eval x) - log (B''.eval x)) + x + (exp x - x - 0)
        = log (exp (A''.eval x) - log (B''.eval x)) := by
      mach_mpoly [exp x, log (exp (A''.eval x) - log (B''.eval x)), x]
    rw [e1, e2] at v; exact v
  exact lt_irrefl_ax _ (lt_of_lt_of_le (lt_of_le_of_lt hxL hgt) hlogcap)


/-- **`log (exp a − s)` is pinned within `1` of `a`** once `s` is small relative to `exp a`.

The workhorse of the surviving depth-3 branch, used three times with `a` taken as `x`,
`exp x − d` and `exp x − log x`. Both side conditions are one application of
`exp_add_one_doubles`: `exp (a−1) + exp (a−1) ≤ exp a` gives the floor, `exp a + exp a ≤ exp (a+1)`
the ceiling. -/
theorem log_exp_sub_pinned {a s : Real} (hlo : s ≤ exp (a - 1)) (hhi : -exp a ≤ s) :
    a - 1 ≤ log (exp a - s) ∧ log (exp a - s) ≤ a + 1 := by
  have hdbl : exp (a - 1) + exp (a - 1) ≤ exp a := by
    have v := exp_add_one_doubles (a - 1)
    have e : a - 1 + 1 = a := by mach_ring
    rw [e] at v; exact v
  -- floor: `exp a − s ≥ exp (a−1)`
  have hfloor : exp (a - 1) ≤ exp a - s := by
    have v : exp (a - 1) + s ≤ exp (a - 1) + exp (a - 1) := add_le_add_left hlo _
    have w : exp (a - 1) + s ≤ exp a := le_trans v hdbl
    have u := add_le_add_wit w (le_refl (-s))
    have e1 : exp (a - 1) + s + -s = exp (a - 1) := by mach_mpoly [exp (a - 1), s]
    have e2 : exp a + -s = exp a - s := by mach_ring
    rw [e1, e2] at u; exact u
  have hpos : (0 : Real) < exp a - s := lt_of_lt_of_le (exp_pos _) hfloor
  -- ceiling: `exp a − s ≤ exp (a+1)`
  have hceil : exp a - s ≤ exp (a + 1) := by
    have hns : -s ≤ exp a := by
      have t := neg_le_neg_wit hhi
      have e : -(-exp a) = exp a := by mach_ring
      rw [e] at t; exact t
    have v : exp a + -s ≤ exp a + exp a := add_le_add_left hns _
    have e : exp a + -s = exp a - s := by mach_ring
    rw [e] at v
    exact le_trans v (exp_add_one_doubles a)
  refine ⟨?_, ?_⟩
  · have m := log_le_log (exp_pos (a - 1)) hfloor
    rw [log_exp] at m; exact m
  · have m := log_le_log hpos hceil
    rw [log_exp] at m; exact m


/-- Packaging of `log_exp_sub_pinned` at a point where the right child's log is known to be small. -/
private theorem pin_at {A'' B'' : EMLTree} {D Cl a x : Real}
    (hsu : log (B''.eval x) ≤ x + D) (hsl : Cl ≤ log (B''.eval x))
    (hup : x + D ≤ exp (a - 1)) (hlo : -exp a ≤ Cl) (haa : A''.eval x = a) :
    a - 1 ≤ log (exp (A''.eval x) - log (B''.eval x))
    ∧ log (exp (A''.eval x) - log (B''.eval x)) ≤ a + 1 := by
  rw [haa]
  exact log_exp_sub_pinned (le_trans hsu hup) (le_trans hlo hsl)

/-- `-exp a ≤ Cl` whenever `exp a` is at least `-Cl`; the form the three shapes need. -/
private theorem neg_exp_le_of {a Cl : Real} (h : -Cl ≤ exp a) : -exp a ≤ Cl := by
  have v := add_le_add_wit h (le_refl (Cl - exp a))
  have e1 : -Cl + (Cl - exp a) = -exp a := by mach_mpoly [Cl, exp a]
  have e2 : exp a + (Cl - exp a) = Cl := by mach_mpoly [Cl, exp a]
  rw [e1, e2] at v; exact v

/-- **`VarLeftEmlRightHard` holds for every band target.**

The last branch of the depth-3 exclusion. `A''` ranges over the five depth-1 shapes: the two with a
bounded exponential go to `varLeftEmlRight_bounded_left`, and the three unbounded ones are pinned by
`log_exp_sub_pinned` and then refuted, **each by exactly one band hypothesis** — `var` by
sub-exponentiality, `exp x − d` by unboundedness, `exp x − log x` by superlogarithmicity. -/
theorem varLeftEmlRightHard_of_band (f : Real → Real)
    (Hunb : ∀ K X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ K < f x)
    (Hlog : ∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ C + log x < f x)
    (Hsub : ∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ f x < exp x - x - C) :
    VarLeftEmlRightHard f := by
  intro A'' B'' hA'' hB'' h
  obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B'' hB''
  obtain ⟨Cl, XL, hXL1, hCl⟩ := depth_le_one_log_lower_at_infinity B'' hB''
  have hXLn : (0 : Real) ≤ XL := le_trans (le_of_lt zero_lt_one_ax) hXL1
  rcases depth_le_one_classification A'' hA'' with ⟨α, ha⟩ | ha | ⟨c, _, ha⟩ | ⟨d, ha⟩ | ha
  · -- `A'' = const α` : bounded exponential
    refine varLeftEmlRight_bounded_left f A'' B'' hB'' (exp α) ?_ Hsub h
    intro x hx1
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
    exact le_refl _
  · -- `A'' = var` : pinned at `a = x`, refuted by sub-exponentiality
    obtain ⟨T, hT⟩ := two_mul_add_le_exp (D + 1 + 1)
    obtain ⟨x, hxX, hx1, hcon⟩ := Hsub (1 + 1) (XL + exp T + exp (-Cl) + 1 + 1)
    have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    have hpiece : ∀ u v w : Real, 0 ≤ u → 0 ≤ v → 0 ≤ w →
        u ≤ XL + exp T + exp (-Cl) + 1 + 1 → True := fun _ _ _ _ _ _ _ => trivial
    have hxXL : XL ≤ x := by
      have v : XL + 0 + 0 + 0 + 0 ≤ XL + exp T + exp (-Cl) + 1 + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl XL)
          (le_of_lt (exp_pos T))) (le_of_lt (exp_pos _))) (le_of_lt zero_lt_one_ax))
          (le_of_lt zero_lt_one_ax)
      have e : XL + (0 : Real) + 0 + 0 + 0 = XL := by mach_ring
      rw [e] at v; exact le_trans v hxX
    have hxT : T + 1 ≤ x := by
      have v : (0 : Real) + exp T + 0 + 1 + 0 ≤ XL + exp T + exp (-Cl) + 1 + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit hXLn (le_refl (exp T)))
          (le_of_lt (exp_pos _))) (le_refl 1)) (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + exp T + 0 + 1 + 0 = exp T + 1 := by mach_ring
      rw [e] at v
      exact le_trans (add_le_add_wit (self_le_exp T) (le_refl (1 : Real))) (le_trans v hxX)
    have hxC : exp (-Cl) ≤ x := by
      have v : (0 : Real) + 0 + exp (-Cl) + 0 + 0 ≤ XL + exp T + exp (-Cl) + 1 + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit hXLn
          (le_of_lt (exp_pos T))) (le_refl _)) (le_of_lt zero_lt_one_ax))
          (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + 0 + exp (-Cl) + 0 + 0 = exp (-Cl) := by mach_ring
      rw [e] at v; exact le_trans v hxX
    -- side conditions
    have hup : x + D ≤ exp (x - 1) := by
      have hxm1 : T ≤ x - 1 := by
        have v := add_le_add_wit hxT (le_refl (-1 : Real))
        have e1 : T + 1 + -1 = T := by mach_ring
        have e2 : x + -1 = x - 1 := by mach_ring
        rw [e1, e2] at v; exact v
      have hb := hT (x - 1) hxm1
      have e : x - 1 + (x - 1) + (D + 1 + 1) = x + x + D := by mach_mpoly [x, D]
      rw [e] at hb
      have hxn : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
      have w : x + D ≤ x + x + D := by
        have u : x + 0 + D ≤ x + x + D := add_le_add_wit (add_le_add_wit (le_refl x) hxn)
          (le_refl D)
        have e2 : x + (0 : Real) + D = x + D := by mach_ring
        rw [e2] at u; exact u
      exact le_trans w hb
    have hlo : -exp x ≤ Cl := by
      refine neg_exp_le_of ?_
      exact le_trans (le_trans (self_le_exp (-Cl)) hxC) (self_le_exp x)
    obtain ⟨_, hpu⟩ := pin_at (D := D) (Cl := Cl) (a := x)
      (hD x hx1) (hCl x hxXL) hup hlo (ha x hx0)
    -- combine with the equation
    have hL : log (exp (A''.eval x) - log (B''.eval x)) = exp x - f x := by
      have t := h x hx0
      rw [← t]; mach_mpoly [exp x, log (exp (A''.eval x) - log (B''.eval x))]
    rw [hL] at hpu
    have hgt : x + 1 + 1 < exp x - f x := by
      have v := add_lt_add_left hcon (-f x + x + 1 + 1)
      have e1 : -f x + x + 1 + 1 + f x = x + 1 + 1 := by mach_mpoly [f x, x]
      have e2 : -f x + x + 1 + 1 + (exp x - x - (1 + 1)) = exp x - f x := by
        mach_mpoly [f x, x, exp x]
      rw [e1, e2] at v; exact v
    exact lt_irrefl_ax _ (lt_trans_ax (lt_of_lt_of_le hgt hpu) (lt_succ_self (x + 1)))
  · -- `A'' = c − log x` : bounded exponential
    refine varLeftEmlRight_bounded_left f A'' B'' hB'' (exp c) ?_ Hsub h
    intro x hx1
    rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx1)]
    refine exp_monotone ?_
    have hlogx : (0 : Real) ≤ log x := by
      have hl1 : log (1 : Real) = 0 := by
        have hz : exp (0 : Real) = 1 := exp_zero
        rw [← hz, log_exp]
      have hm := log_le_log zero_lt_one_ax hx1
      rw [hl1] at hm; exact hm
    have v := add_le_add_wit (le_refl c) (neg_le_neg_wit hlogx)
    have e1 : c + -log x = c - log x := by mach_ring
    have e2 : c + -(0 : Real) = c := by mach_ring
    rw [e1, e2] at v; exact v
  · -- `A'' = exp x − d` : pinned at `a = exp x − d`, refuted by unboundedness
    obtain ⟨T, hT⟩ := two_mul_add_le_exp (D + d + 1)
    obtain ⟨x, hxX, hx1, hcon⟩ := Hunb (d + 1) (XL + exp T + exp (-Cl + d) + 1)
    have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    have hxXL : XL ≤ x := by
      have v : XL + 0 + 0 + 0 ≤ XL + exp T + exp (-Cl + d) + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl XL) (le_of_lt (exp_pos T)))
          (le_of_lt (exp_pos _))) (le_of_lt zero_lt_one_ax)
      have e : XL + (0 : Real) + 0 + 0 = XL := by mach_ring
      rw [e] at v; exact le_trans v hxX
    have hxT : T ≤ x := by
      have v : (0 : Real) + exp T + 0 + 0 ≤ XL + exp T + exp (-Cl + d) + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit hXLn (le_refl (exp T)))
          (le_of_lt (exp_pos _))) (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + exp T + 0 + 0 = exp T := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp T) (le_trans v hxX)
    have hxC : exp (-Cl + d) ≤ x := by
      have v : (0 : Real) + 0 + exp (-Cl + d) + 0 ≤ XL + exp T + exp (-Cl + d) + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit hXLn (le_of_lt (exp_pos T)))
          (le_refl _)) (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + 0 + exp (-Cl + d) + 0 = exp (-Cl + d) := by mach_ring
      rw [e] at v; exact le_trans v hxX
    -- `x + D ≤ exp x − d ≤ exp (exp x − d − 1)`
    have hbig : x + D + d ≤ exp x := by
      have hb := hT x hxT
      have e : x + x + (D + d + 1) = x + x + D + d + 1 := by mach_mpoly [x, D, d]
      rw [e] at hb
      have hxn : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
      have w : x + D + d ≤ x + x + D + d + 1 := by
        have u : x + 0 + D + d + 0 ≤ x + x + D + d + 1 :=
          add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl x) hxn)
            (le_refl D)) (le_refl d)) (le_of_lt zero_lt_one_ax)
        have e2 : x + (0 : Real) + D + d + 0 = x + D + d := by mach_ring
        rw [e2] at u; exact u
      exact le_trans w hb
    have hup : x + D ≤ exp (exp x - d - 1) := by
      have g : 1 + (exp x - d - 1) ≤ exp (exp x - d - 1) := one_add_le_exp _
      have e : (1 : Real) + (exp x - d - 1) = exp x - d := by mach_mpoly [exp x, d]
      rw [e] at g
      have w : x + D ≤ exp x - d := by
        have u := add_le_add_wit hbig (le_refl (-d))
        have e1 : x + D + d + -d = x + D := by mach_mpoly [x, D, d]
        have e2 : exp x + -d = exp x - d := by mach_ring
        rw [e1, e2] at u; exact u
      exact le_trans w g
    have hlo : -exp (exp x - d) ≤ Cl := by
      refine neg_exp_le_of ?_
      have g : 1 + (exp x - d) ≤ exp (exp x - d) := one_add_le_exp _
      have w : -Cl ≤ 1 + (exp x - d) := by
        have a1 : -Cl + d ≤ exp (-Cl + d) := self_le_exp _
        have a2 : -Cl + d ≤ x := le_trans a1 hxC
        have a3 : x ≤ exp x := self_le_exp x
        have a4 : -Cl + d ≤ exp x := le_trans a2 a3
        have u := add_le_add_wit a4 (le_refl (-d))
        have e1 : -Cl + d + -d = -Cl := by mach_mpoly [Cl, d]
        have e2 : exp x + -d = exp x - d := by mach_ring
        rw [e1, e2] at u
        exact le_trans u (le_one_add _)
      exact le_trans w g
    obtain ⟨hpl, _⟩ := pin_at (D := D) (Cl := Cl) (a := exp x - d)
      (hD x hx1) (hCl x hxXL) hup hlo (ha x hx0)
    have hL : log (exp (A''.eval x) - log (B''.eval x)) = exp x - f x := by
      have t := h x hx0
      rw [← t]; mach_mpoly [exp x, log (exp (A''.eval x) - log (B''.eval x))]
    rw [hL] at hpl
    -- `exp x − d − 1 ≤ exp x − f x` gives `f x ≤ d + 1`
    have hfle : f x ≤ d + 1 := by
      have v := add_le_add_wit hpl (le_refl (f x - exp x + d + 1))
      have e1 : exp x - d - 1 + (f x - exp x + d + 1) = f x := by mach_mpoly [exp x, d, f x]
      have e2 : exp x - f x + (f x - exp x + d + 1) = d + 1 := by mach_mpoly [exp x, d, f x]
      rw [e1, e2] at v; exact v
    exact lt_irrefl_ax _ (lt_of_lt_of_le hcon hfle)
  · -- `A'' = exp x − log x` : pinned there, refuted by superlogarithmicity
    obtain ⟨T, hT⟩ := two_mul_add_le_exp (D + 1)
    obtain ⟨x, hxX, hx1, hcon⟩ := Hlog (1 + 1) (XL + exp T + exp (-Cl) + 1)
    have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    have hxXL : XL ≤ x := by
      have v : XL + 0 + 0 + 0 ≤ XL + exp T + exp (-Cl) + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl XL) (le_of_lt (exp_pos T)))
          (le_of_lt (exp_pos _))) (le_of_lt zero_lt_one_ax)
      have e : XL + (0 : Real) + 0 + 0 = XL := by mach_ring
      rw [e] at v; exact le_trans v hxX
    have hxT : T ≤ x := by
      have v : (0 : Real) + exp T + 0 + 0 ≤ XL + exp T + exp (-Cl) + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit hXLn (le_refl (exp T)))
          (le_of_lt (exp_pos _))) (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + exp T + 0 + 0 = exp T := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp T) (le_trans v hxX)
    have hxC : exp (-Cl) ≤ x := by
      have v : (0 : Real) + 0 + exp (-Cl) + 0 ≤ XL + exp T + exp (-Cl) + 1 :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit hXLn (le_of_lt (exp_pos T)))
          (le_refl _)) (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + 0 + exp (-Cl) + 0 = exp (-Cl) := by mach_ring
      rw [e] at v; exact le_trans v hxX
    have hlogx : log x ≤ x := log_le_self_pos hx0
    have hbig : x + D + x ≤ exp x := by
      have hb := hT x hxT
      have e : x + x + (D + 1) = x + D + x + 1 := by mach_mpoly [x, D]
      rw [e] at hb
      have w : x + D + x ≤ x + D + x + 1 := le_add_nonneg_r' (le_of_lt zero_lt_one_ax)
      exact le_trans w hb
    have hxn : (0 : Real) ≤ x := le_of_lt hx0
    have hdb : x + x ≤ exp x := two_mul_le_exp hxn
    have hxle : x ≤ exp x - log x := by
      have u := add_le_add_wit hdb (neg_le_neg_wit hlogx)
      have e1 : x + x + -x = x := by mach_mpoly [x]
      have e2 : exp x + -log x = exp x - log x := by mach_ring
      rw [e1, e2] at u; exact u
    have hup : x + D ≤ exp (exp x - log x - 1) := by
      have g : 1 + (exp x - log x - 1) ≤ exp (exp x - log x - 1) := one_add_le_exp _
      have e : (1 : Real) + (exp x - log x - 1) = exp x - log x := by
        mach_mpoly [exp x, log x]
      rw [e] at g
      have w : x + D ≤ exp x - log x := by
        have u := add_le_add_wit hbig (neg_le_neg_wit hlogx)
        have e1 : x + D + x + -x = x + D := by mach_mpoly [x, D]
        have e2 : exp x + -log x = exp x - log x := by mach_ring
        rw [e1, e2] at u; exact u
      exact le_trans w g
    have hlo : -exp (exp x - log x) ≤ Cl := by
      refine neg_exp_le_of ?_
      have g : 1 + (exp x - log x) ≤ exp (exp x - log x) := one_add_le_exp _
      have a2 : -Cl ≤ x := le_trans (self_le_exp (-Cl)) hxC
      have a4 : -Cl ≤ exp x - log x := le_trans a2 hxle
      exact le_trans a4 (le_trans (le_one_add _) g)
    obtain ⟨hpl, _⟩ := pin_at (D := D) (Cl := Cl) (a := exp x - log x)
      (hD x hx1) (hCl x hxXL) hup hlo (ha x hx0)
    have hL : log (exp (A''.eval x) - log (B''.eval x)) = exp x - f x := by
      have t := h x hx0
      rw [← t]; mach_mpoly [exp x, log (exp (A''.eval x) - log (B''.eval x))]
    rw [hL] at hpl
    have hfle : f x ≤ log x + 1 := by
      have v := add_le_add_wit hpl (le_refl (f x - exp x + log x + 1))
      have e1 : exp x - log x - 1 + (f x - exp x + log x + 1) = f x := by
        mach_mpoly [exp x, log x, f x]
      have e2 : exp x - f x + (f x - exp x + log x + 1) = log x + 1 := by
        mach_mpoly [exp x, log x, f x]
      rw [e1, e2] at v; exact v
    have hgt : log x + 1 < f x := by
      have v : (1 : Real) + 1 + log x = log x + 1 + 1 := by mach_ring
      rw [v] at hcon
      exact lt_of_lt_of_le (lt_succ_self (log x + 1)) (le_of_lt hcon)
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hfle)


/-- **Depth-3 intermediate-growth exclusion.** The band theorem, one level up.

Same three hypotheses as `superlinear_subexp_not_depth_le_two`, same arbitrary `f`. Assembled from
every branch proved above; the `A = eml` case inlines its squeeze **at a point chosen from `Hsub`**
rather than calling `depth_two_eml_not_near_identity`, because that theorem wants the squeeze on a
*ray* and sub-exponentiality only supplies it *infinitely often*. -/
theorem superlinear_subexp_not_depth_le_three (f : Real → Real)
    (H1 : ∀ K X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ K < f x)
    (H2 : ∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ f x < exp x - x - C)
    (H3 : ∀ X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ x < f x)
    (Hlog : ∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ C + log x < f x)
    (t : EMLTree) (ht : t.depth ≤ 3)
    (h : ∀ x : Real, 0 < x → t.eval x = f x) : False := by
  cases t with
  | const c =>
      obtain ⟨x, _, hx1, hlt⟩ := H1 c 1
      have hv : c = f x := h x (lt_of_lt_of_le zero_lt_one_ax hx1)
      rw [← hv] at hlt; exact lt_irrefl_ax c hlt
  | var =>
      obtain ⟨x, _, hx1, hlt⟩ := H3 1
      have hv : x = f x := h x (lt_of_lt_of_le zero_lt_one_ax hx1)
      rw [← hv] at hlt; exact lt_irrefl_ax x hlt
  | eml A B =>
      have hA : A.depth ≤ 2 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 2 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      rcases depth_le_two_exp_bounded_or_grows A hA with ⟨K, X₀, hX1, hK⟩ | ⟨T, hT⟩
      · exact depth_three_bounded_left_not_superlog f A B hB K X₀ hX1 hK Hlog h
      · -- the left child's exponential dominates `exp x`
        have hTn : T ≤ exp T := self_le_exp T
        cases A with
        | const c =>
            -- `exp x ≤ exp c` forces `x ≤ c`
            obtain ⟨x, hxX, hx1, _⟩ := H1 0 (exp T + exp c + 1)
            have hxT : T ≤ x := by
              have v : exp T + 0 + 0 ≤ exp T + exp c + 1 :=
                add_le_add_wit (add_le_add_wit (le_refl _) (le_of_lt (exp_pos c)))
                  (le_of_lt zero_lt_one_ax)
              have e : exp T + (0 : Real) + 0 = exp T := by mach_ring
              rw [e] at v; exact le_trans hTn (le_trans v hxX)
            have hxc : exp c < x := by
              have v : (0 : Real) + exp c + 0 ≤ exp T + exp c + 1 :=
                add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T)) (le_refl _))
                  (le_of_lt zero_lt_one_ax)
              have e : (0 : Real) + exp c + 0 = exp c := by mach_ring
              rw [e] at v
              have w : exp c + 1 ≤ exp T + exp c + 1 := by
                have u : (0 : Real) + exp c + 1 ≤ exp T + exp c + 1 :=
                  add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T)) (le_refl _)) (le_refl 1)
                have e2 : (0 : Real) + exp c + 1 = exp c + 1 := by mach_ring
                rw [e2] at u; exact u
              exact lt_of_lt_of_le (lt_succ_self (exp c)) (le_trans w hxX)
            have hge := hT x hxT
            have hcc : exp x ≤ exp c := hge
            have hlt2 : exp c < exp x := exp_lt (lt_of_le_of_lt (self_le_exp c) hxc)
            exact lt_irrefl_ax _ (lt_of_lt_of_le hlt2 hcc)
        | var =>
            exact var_left_not_band f B hB H2 (varLeftEmlRightHard_of_band f H1 Hlog H2) h
        | eml A' B' =>
            have hA' : A'.depth ≤ 1 := by
              simp only [EMLTree.depth] at hA
              have := Nat.le_max_left A'.depth B'.depth; omega
            have hB' : B'.depth ≤ 1 := by
              simp only [EMLTree.depth] at hA
              have := Nat.le_max_right A'.depth B'.depth; omega
            obtain ⟨D', hD'⟩ := depth_le_one_log_le_linear B' hB'
            obtain ⟨Cl', XL', hXL'1, hCl'⟩ := depth_le_one_log_lower_at_infinity B' hB'
            have hXL'n : (0 : Real) ≤ XL' := le_trans (le_of_lt zero_lt_one_ax) hXL'1
            -- `x ≤ ⟦A⟧(x)` on the ray, from the exp gap
            have hxle : ∀ x : Real, T ≤ x → x ≤ exp (A'.eval x) - log (B'.eval x) := by
              intro x hxT
              rcases lt_total (exp (A'.eval x) - log (B'.eval x)) x with hp | hp | hp
              · exact absurd (hT x hxT) (fun hh =>
                  lt_irrefl_ax _ (lt_of_lt_of_le (exp_lt hp) hh))
              · exact le_of_eq hp.symm
              · exact le_of_lt hp
            rcases depth_le_one_exp_bounded_or_grows A' hA' with ⟨K', hK'⟩ | ⟨T', hT'⟩
            · -- `⟦A⟧` is bounded by a constant but must exceed `x`
              obtain ⟨x, hxX, hx1, _⟩ := H1 0 (exp T + XL' + exp (K' - Cl') + 1)
              have hxT : T ≤ x := by
                have v : exp T + 0 + 0 + 0 ≤ exp T + XL' + exp (K' - Cl') + 1 :=
                  add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl _) hXL'n)
                    (le_of_lt (exp_pos _))) (le_of_lt zero_lt_one_ax)
                have e : exp T + (0 : Real) + 0 + 0 = exp T := by mach_ring
                rw [e] at v; exact le_trans hTn (le_trans v hxX)
              have hxL : XL' ≤ x := by
                have v : (0 : Real) + XL' + 0 + 0 ≤ exp T + XL' + exp (K' - Cl') + 1 :=
                  add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T))
                    (le_refl _)) (le_of_lt (exp_pos _))) (le_of_lt zero_lt_one_ax)
                have e : (0 : Real) + XL' + 0 + 0 = XL' := by mach_ring
                rw [e] at v; exact le_trans v hxX
              have hxE1 : exp (K' - Cl') + 1 ≤ x := by
                have v : (0 : Real) + 0 + exp (K' - Cl') + 1
                    ≤ exp T + XL' + exp (K' - Cl') + 1 :=
                  add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T)) hXL'n)
                    (le_refl _)) (le_refl 1)
                have e : (0 : Real) + 0 + exp (K' - Cl') + 1 = exp (K' - Cl') + 1 := by mach_ring
                rw [e] at v; exact le_trans v hxX
              have hcap : exp (A'.eval x) - log (B'.eval x) ≤ K' - Cl' := by
                have v := add_le_add_wit (hK' x hx1) (neg_le_neg_wit (hCl' x hxL))
                have e1 : exp (A'.eval x) + -log (B'.eval x)
                    = exp (A'.eval x) - log (B'.eval x) := by mach_ring
                have e2 : K' + -Cl' = K' - Cl' := by mach_ring
                rw [e1, e2] at v; exact v
              have hbig : K' - Cl' < x :=
                lt_of_lt_of_le (lt_of_le_of_lt (self_le_exp (K' - Cl')) (lt_succ_self _)) hxE1
              exact lt_irrefl_ax _ (lt_of_lt_of_le hbig (le_trans (hxle x hxT) hcap))
            · -- `⟦A⟧ ≥ exp x − x − D'` but the squeeze caps it at `x + 1`
              obtain ⟨K₂, XC, hXC1, hC2⟩ := depth_le_two_log_le_exp B hB
              obtain ⟨T₂, hT₂⟩ := two_mul_add_le_exp (1 + D' + 1)
              obtain ⟨x, hxX, hx1, hsub⟩ := H2 (K₂) (exp T + exp T' + XC + exp T₂ + 1)
              have hxT : T ≤ x := by
                have v : exp T + 0 + 0 + 0 + 0 ≤ exp T + exp T' + XC + exp T₂ + 1 :=
                  add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl _)
                    (le_of_lt (exp_pos T'))) (le_trans (le_of_lt zero_lt_one_ax) hXC1))
                    (le_of_lt (exp_pos T₂))) (le_of_lt zero_lt_one_ax)
                have e : exp T + (0 : Real) + 0 + 0 + 0 = exp T := by mach_ring
                rw [e] at v; exact le_trans hTn (le_trans v hxX)
              have hxT' : T' ≤ x := by
                have v : (0 : Real) + exp T' + 0 + 0 + 0 ≤ exp T + exp T' + XC + exp T₂ + 1 :=
                  add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit
                    (le_of_lt (exp_pos T)) (le_refl _))
                    (le_trans (le_of_lt zero_lt_one_ax) hXC1)) (le_of_lt (exp_pos T₂)))
                    (le_of_lt zero_lt_one_ax)
                have e : (0 : Real) + exp T' + 0 + 0 + 0 = exp T' := by mach_ring
                rw [e] at v; exact le_trans (self_le_exp T') (le_trans v hxX)
              have hxC : XC ≤ x := by
                have v : (0 : Real) + 0 + XC + 0 + 0 ≤ exp T + exp T' + XC + exp T₂ + 1 :=
                  add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit
                    (le_of_lt (exp_pos T)) (le_of_lt (exp_pos T'))) (le_refl _))
                    (le_of_lt (exp_pos T₂))) (le_of_lt zero_lt_one_ax)
                have e : (0 : Real) + 0 + XC + 0 + 0 = XC := by mach_ring
                rw [e] at v; exact le_trans v hxX
              have hxT₂ : T₂ ≤ x := by
                have v : (0 : Real) + 0 + 0 + exp T₂ + 0 ≤ exp T + exp T' + XC + exp T₂ + 1 :=
                  add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit
                    (le_of_lt (exp_pos T)) (le_of_lt (exp_pos T')))
                    (le_trans (le_of_lt zero_lt_one_ax) hXC1)) (le_refl _))
                    (le_of_lt zero_lt_one_ax)
                have e : (0 : Real) + 0 + 0 + exp T₂ + 0 = exp T₂ := by mach_ring
                rw [e] at v; exact le_trans (self_le_exp T₂) (le_trans v hxX)
              have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
              -- lower: `⟦A⟧(x) ≥ exp x − x − D'`
              have hlow : exp x - x - D' ≤ exp (A'.eval x) - log (B'.eval x) := by
                have g1 : exp x ≤ exp (A'.eval x) := hT' x hxT'
                have g2 : log (B'.eval x) ≤ x + D' := hD' x hx1
                have v := add_le_add_wit g1 (neg_le_neg_wit g2)
                have e1 : exp x + -(x + D') = exp x - x - D' := by mach_mpoly [exp x, x, D']
                have e2 : exp (A'.eval x) + -log (B'.eval x)
                    = exp (A'.eval x) - log (B'.eval x) := by mach_ring
                rw [e1, e2] at v; exact v
              -- upper: at this point the squeeze holds, capping `⟦A⟧(x)` at `x + 1`
              have hval : exp (exp (A'.eval x) - log (B'.eval x)) - log (B.eval x) = f x :=
                h x hx0
              have hupper : exp (A'.eval x) - log (B'.eval x) ≤ x + 1 := by
                have hce : log (B.eval x) ≤ exp x + K₂ := hC2 x hxC
                have hsum : exp (exp (A'.eval x) - log (B'.eval x)) ≤ exp x + exp x := by
                  have v : exp (exp (A'.eval x) - log (B'.eval x))
                      = f x + log (B.eval x) := by
                    rw [← hval]; mach_mpoly [exp (exp (A'.eval x) - log (B'.eval x)),
                      log (B.eval x)]
                  rw [v]
                  have w := add_le_add_wit (le_of_lt hsub) hce
                  have e : exp x - x - K₂ + (exp x + K₂) = exp x + exp x - x := by
                    mach_mpoly [exp x, x, K₂]
                  rw [e] at w
                  have z : exp x + exp x - x ≤ exp x + exp x := by
                    have u := add_le_add_wit (le_refl (exp x + exp x))
                      (neg_le_neg_wit (le_of_lt hx0))
                    have e1 : exp x + exp x + -x = exp x + exp x - x := by mach_ring
                    have e2 : exp x + exp x + -(0 : Real) = exp x + exp x := by mach_ring
                    rw [e1, e2] at u; exact u
                  exact le_trans w z
                have hmono : exp (exp (A'.eval x) - log (B'.eval x)) ≤ exp (x + 1) :=
                  le_trans hsum (exp_add_one_doubles x)
                rcases lt_total (exp (A'.eval x) - log (B'.eval x)) (x + 1) with hp | hp | hp
                · exact le_of_lt hp
                · exact le_of_eq hp
                · exact absurd hmono (fun hh => lt_irrefl_ax _ (lt_of_lt_of_le (exp_lt hp) hh))
              -- combine: `exp x ≤ 2x + 1 + D'`, refuted on the ray
              have hchain : exp x - x - D' ≤ x + 1 := le_trans hlow hupper
              have hbad : exp x ≤ x + x + (1 + D') := by
                have v := add_le_add_wit hchain (le_refl (x + D'))
                have e1 : exp x - x - D' + (x + D') = exp x := by mach_mpoly [exp x, x, D']
                have e2 : x + 1 + (x + D') = x + x + (1 + D') := by mach_mpoly [x, D']
                rw [e1, e2] at v; exact v
              have hstrict : x + x + (1 + D') + 1 ≤ exp x := by
                have v := hT₂ x hxT₂
                have e : x + x + (1 + D' + 1) = x + x + (1 + D') + 1 := by mach_mpoly [x, D']
                rw [e] at v; exact v
              exact lt_irrefl_ax _
                (lt_of_lt_of_le (lt_of_lt_of_le (lt_succ_self (x + x + (1 + D'))) hstrict) hbad)

/-! ### The depth-3 band exclusion is **sharp** -/

/-- **The intermediate-growth band, as one proposition rather than four arguments.**

`superlinear_subexp_not_depth_le_three` takes its four conditions as separate hypotheses. That is
why the sharpness defect of 2026-08-19 was possible: a refutation certified three of them, the
exclusion consumed four, both theorems were individually valid, and **the composition was not**.
Nothing could notice, because the band existed only as an argument list — there was no object for
the two sides to disagree about.

Naming it makes the mismatch a type error instead of a reading error. A witness must now produce
`IntermediateBand f`; it cannot produce three quarters of it.

The four conditions are each required only **infinitely often**, not on a ray, which is what makes
the exclusion strong: a target need merely *visit* the band to be excluded. -/
def IntermediateBand (f : Real → Real) : Prop :=
  (∀ K X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ K < f x)
  ∧ (∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ f x < exp x - x - C)
  ∧ (∀ X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ x < f x)
  ∧ (∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ C + log x < f x)

/-- **The depth-≤3 exclusion, stated against the named band.** Definitionally the same theorem as
`superlinear_subexp_not_depth_le_three`; this is the form new results should consume.

The raw four-argument form is deliberately kept rather than replaced. Its registered claim pins
`statement_mentions` including `exp`, which folding the conditions into a definition would hide from
the auditor — so the raw statement stays as the audited surface and this is the composable one. -/
theorem intermediateBand_not_depth_le_three (f : Real → Real) (hf : IntermediateBand f)
    (t : EMLTree) (ht : t.depth ≤ 3) (h : ∀ x : Real, 0 < x → t.eval x = f x) : False :=
  superlinear_subexp_not_depth_le_three f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 t ht h

/-- **`x + 1` is in the band** — all four conditions, which is the whole point. Certifying only the
first three is what left `d(x + 1)` open. -/
theorem x_plus_one_band_hyps : IntermediateBand (fun x => x + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- unbounded above on every ray
    intro K X
    refine ⟨1 + exp K + exp X, ?_, ?_, ?_⟩
    · have v : (0 : Real) + 0 + exp X ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos K)))
          (le_refl _)
      have e : (0 : Real) + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have v : (1 : Real) + 0 + 0 ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos K)))
          (le_of_lt (exp_pos X))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    · have hK : K < exp K := by
        have t1 := one_add_le_exp K
        have e : (1 : Real) + K = K + 1 := by mach_ring
        rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self K) t1
      have v : (0 : Real) + exp K + 0 ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
          (le_of_lt (exp_pos X))
      have e : (0 : Real) + exp K + 0 = exp K := by mach_ring
      rw [e] at v
      exact lt_of_lt_of_le (lt_of_lt_of_le hK v) (le_of_lt (lt_succ_self _))
  · -- below `exp x − x − C` at arbitrarily large points: `exp` outruns `2x + 1 + C`
    intro C X
    have hMp : (0 : Real) ≤ 1 + 1 :=
      le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax)
    obtain ⟨x, hxX, hx1, hlt⟩ := exp_beats_linear_past (α := 1 + 1) (β := 1 + C) hMp X
    refine ⟨x, hxX, hx1, ?_⟩
    have v := add_lt_add_left hlt (-x - C)
    have e1 : -x - C + ((1 + 1) * x + (1 + C)) = x + 1 := by mach_mpoly [x, C]
    have e2 : -x - C + exp x = exp x - x - C := by mach_mpoly [exp x, x, C]
    rw [e1, e2] at v; exact v
  · -- above the identity, trivially
    intro X
    refine ⟨1 + exp X, ?_, ?_, lt_succ_self _⟩
    · exact le_trans (self_le_exp X) (le_one_add _)
    · have v : (1 : Real) + 0 ≤ 1 + exp X := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos X))
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at v; exact v
  · -- above `C + log x` at arbitrarily large points.
    -- Substituting `x = exp w` turns the goal into `C + w < exp w + 1`, which `two_mul_add_le_exp`
    -- settles. `w := exp T + exp X` dominates `T`, `X` and `0` at once, which is what the three
    -- side goals need.
    intro C X
    obtain ⟨T, hT⟩ := two_mul_add_le_exp (C + 1 + 1)
    have hexpT : (0 : Real) < exp T := exp_pos T
    have hexpX : (0 : Real) < exp X := exp_pos X
    have hw0 : (0 : Real) ≤ exp T + exp X :=
      le_of_lt (add_pos_of_nonneg_pos (le_of_lt hexpT) hexpX)
    have hwT : T ≤ exp T + exp X := by
      have v : exp T + 0 ≤ exp T + exp X := add_le_add_wit (le_refl _) (le_of_lt hexpX)
      have e : exp T + 0 = exp T := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp T) v
    have hwX : X ≤ exp T + exp X := by
      have v : (0 : Real) + exp X ≤ exp T + exp X := add_le_add_wit (le_of_lt hexpT) (le_refl _)
      have e : (0 : Real) + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    refine ⟨exp (exp T + exp X), le_trans hwX (self_le_exp _), one_le_exp hw0, ?_⟩
    show C + log (exp (exp T + exp X)) < exp (exp T + exp X) + 1
    rw [log_exp]
    have h2 : (0 : Real) < 1 + 1 :=
      add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax
    have hpos : (0 : Real) < exp T + exp X + (1 + 1) := add_pos_of_nonneg_pos hw0 h2
    have v := add_lt_add_left hpos (C + (exp T + exp X))
    have e1 : C + (exp T + exp X) + 0 = C + (exp T + exp X) := by mach_ring
    have e2 : C + (exp T + exp X) + (exp T + exp X + (1 + 1))
        = exp T + exp X + (exp T + exp X) + (C + 1 + 1) := by
      mach_mpoly [C, exp T, exp X]
    rw [e1, e2] at v
    exact lt_of_lt_of_le (lt_of_lt_of_le v (hT (exp T + exp X) hwT))
      (le_of_lt (lt_succ_self _))

/-- **`superlinear_subexp_not_depth_le_three` cannot be lifted to depth 4 — the statement is false
there.** `f x = x + 1` satisfies all **four** band hypotheses and is computed at depth exactly 4 by
`xPlusOneTree`.

**The fourth conjunct (`Hlog`) is not optional and was missing until 2026-08-19.**
`superlinear_subexp_not_depth_le_two` takes three hypotheses; `superlinear_subexp_not_depth_le_three`
takes four, the extra one being `Hlog : C + log x < f x` infinitely often. A refutation certified
against only three therefore refutes the *depth-2-shaped* band statement at depth 4, not the depth-3
one — a strictly weaker claim, whose falsity does not by itself make the four-hypothesis version
false. Since the exclusion this is paired with is the depth-≤3 theorem, the witness has to clear all
four bars or the sharpness claim does not close. `x + 1` does clear it; the proof substitutes
`x = exp w` so that `log x` becomes `w`, and `two_mul_add_le_exp` then outruns `C + w`.

This settles what looked like an obstruction. Two apparent blockers to a depth-4 version were
identified — the bounded-left branch would need `V₃`, and the `A = var` branch would need a
classification of depth-2 trees — but neither is an obstacle to a true theorem, because there is no
true theorem to reach. The band exclusion holds at depth ≤ 3 and fails at depth 4, full stop.

`x + 1` is the natural witness: unbounded and above the identity by construction, and
sub-exponential because `exp` outruns any linear function. It slips through precisely because the
band's hypotheses constrain *growth* and `x + 1` sits at the very bottom of the band. -/
theorem band_exclusion_fails_at_depth_four :
    ∃ (f : Real → Real) (t : EMLTree),
      (∀ K X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ K < f x)
      ∧ (∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ f x < exp x - x - C)
      ∧ (∀ X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ x < f x)
      ∧ (∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ C + log x < f x)
      ∧ t.depth = 4
      ∧ ∀ x : Real, 0 < x → t.eval x = f x := by
  obtain ⟨t, hteval, htdepth⟩ := x_plus_one_in_eml
  obtain ⟨h1, h2, h3, h4⟩ := x_plus_one_band_hyps
  exact ⟨fun x => x + 1, t, h1, h2, h3, h4, htdepth, fun x _ => hteval x⟩

/-! ### The positive-translation family

`x + 1` was a specimen. This asks whether it is a stratum: is `d(x + c) = 4` for *every* `c > 0`?

The upper bound is already unrestricted — `eml_const_offset_closure` gives a depth-4 tree for every
real `c`. So the whole question is the lower bound, and that is where the sign matters: the band's
third condition is `x < f x`, which holds for `x + c` exactly when `c > 0`. The negative side is a
different problem, not a harder version of this one. -/

/-- **`x + c` lies in the intermediate band, for every `c > 0`.**

Each condition generalises the `c = 1` proof by carrying `c` where the constant `1` stood; the only
place positivity is used is `H3`, and it is used there essentially. -/
theorem x_plus_c_band (c : Real) (hc : 0 < c) : IntermediateBand (fun x => x + c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- unbounded above
    intro K X
    refine ⟨1 + exp K + exp X, ?_, ?_, ?_⟩
    · have v : (0 : Real) + 0 + exp X ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos K)))
          (le_refl _)
      have e : (0 : Real) + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have v : (1 : Real) + 0 + 0 ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos K)))
          (le_of_lt (exp_pos X))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    · have hK : K < exp K := by
        have t1 := one_add_le_exp K
        have e : (1 : Real) + K = K + 1 := by mach_ring
        rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self K) t1
      have v : (0 : Real) + exp K + 0 ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
          (le_of_lt (exp_pos X))
      have e : (0 : Real) + exp K + 0 = exp K := by mach_ring
      rw [e] at v
      have hlt : K < 1 + exp K + exp X := lt_of_lt_of_le hK v
      have w := add_lt_add_left hc (1 + exp K + exp X)
      have l : (1 + exp K + exp X : Real) + 0 = 1 + exp K + exp X := by mach_ring
      rw [l] at w
      exact lt_trans_ax hlt w
  · -- sub-exponential: `exp` outruns `2x + c + C`
    intro C X
    have hMp : (0 : Real) ≤ 1 + 1 :=
      le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax)
    obtain ⟨x, hxX, hx1, hlt⟩ := exp_beats_linear_past (α := 1 + 1) (β := c + C) hMp X
    refine ⟨x, hxX, hx1, ?_⟩
    have v := add_lt_add_left hlt (-x - C)
    have e1 : -x - C + ((1 + 1) * x + (c + C)) = x + c := by mach_mpoly [x, C, c]
    have e2 : -x - C + exp x = exp x - x - C := by mach_mpoly [exp x, x, C]
    rw [e1, e2] at v; exact v
  · -- above the identity: this is where `0 < c` is essential
    intro X
    refine ⟨1 + exp X, ?_, ?_, ?_⟩
    · exact le_trans (self_le_exp X) (le_one_add _)
    · have v : (1 : Real) + 0 ≤ 1 + exp X := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos X))
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    · have w := add_lt_add_left hc (1 + exp X)
      have l : (1 + exp X : Real) + 0 = 1 + exp X := by mach_ring
      rw [l] at w; exact w
  · -- super-logarithmic: substitute `x = exp w`
    intro C X
    obtain ⟨T, hT⟩ := two_mul_add_le_exp (C + 1 + 1)
    have hexpT : (0 : Real) < exp T := exp_pos T
    have hexpX : (0 : Real) < exp X := exp_pos X
    have hw0 : (0 : Real) ≤ exp T + exp X :=
      le_of_lt (add_pos_of_nonneg_pos (le_of_lt hexpT) hexpX)
    have hwT : T ≤ exp T + exp X := by
      have v : exp T + 0 ≤ exp T + exp X := add_le_add_wit (le_refl _) (le_of_lt hexpX)
      have e : exp T + 0 = exp T := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp T) v
    have hwX : X ≤ exp T + exp X := by
      have v : (0 : Real) + exp X ≤ exp T + exp X := add_le_add_wit (le_of_lt hexpT) (le_refl _)
      have e : (0 : Real) + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    refine ⟨exp (exp T + exp X), le_trans hwX (self_le_exp _), one_le_exp hw0, ?_⟩
    show C + log (exp (exp T + exp X)) < exp (exp T + exp X) + c
    rw [log_exp]
    have h2 : (0 : Real) < 1 + 1 :=
      add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax) zero_lt_one_ax
    have hpos : (0 : Real) < exp T + exp X + (1 + 1) := add_pos_of_nonneg_pos hw0 h2
    have v := add_lt_add_left hpos (C + (exp T + exp X))
    have e1 : C + (exp T + exp X) + 0 = C + (exp T + exp X) := by mach_ring
    have e2 : C + (exp T + exp X) + (exp T + exp X + (1 + 1))
        = exp T + exp X + (exp T + exp X) + (C + 1 + 1) := by
      mach_mpoly [C, exp T, exp X]
    rw [e1, e2] at v
    have hchain := lt_of_lt_of_le v (hT (exp T + exp X) hwT)
    have w := add_lt_add_left hc (exp (exp T + exp X))
    have l : (exp (exp T + exp X) : Real) + 0 = exp (exp T + exp X) := by mach_ring
    rw [l] at w
    exact lt_trans_ax hchain w

/-- **No tree of depth ≤ 3 computes `x + c`, for any `c > 0`.** -/
theorem x_plus_c_not_depth_le_three (c : Real) (hc : 0 < c) (t : EMLTree) (ht : t.depth ≤ 3)
    (h : ∀ x : Real, 0 < x → t.eval x = x + c) : False :=
  intermediateBand_not_depth_le_three (fun x => x + c) (x_plus_c_band c hc) t ht h

/-- **The Positive Translation Theorem: `d_(0,∞)(x + c) = 4` for every `c > 0`.**

`x + 1` was not a specimen — it is one point of a stratum. The magnitude of the translation is
irrelevant; only its sign and its non-vanishing matter, since `x + 0 = x` has depth `0`.

The upper half is `eml_const_offset_closure` at `K = 1`, which needs only `0 < 1 + c`. -/
theorem x_plus_c_depth_exact_four (c : Real) (hc : 0 < c) :
    (∀ t : EMLTree, t.depth ≤ 3 → (∀ x : Real, 0 < x → t.eval x = x + c) → False)
    ∧ (∃ t : EMLTree, t.depth = 4 ∧ ∀ x : Real, 0 < x → t.eval x = x + c) := by
  refine ⟨fun t ht h => x_plus_c_not_depth_le_three c hc t ht h, ?_⟩
  refine ⟨negOffset (Real.log (1 + c)) (negOffset (Real.log 1) EMLTree.var), ?_, ?_⟩
  · simp [negOffset_depth, EMLTree.depth]
  · intro x _
    exact eml_const_offset_closure EMLTree.var zero_lt_one_ax (add_pos zero_lt_one_ax hc) x

/-- **`d(x + 1) = 4` exactly, on `(0, ∞)`.** The lower half.

Available only because `x_plus_one_band_hyps` now certifies `Hlog` as well: the depth-≤3 band
theorem takes four hypotheses, so before that conjunct existed this instantiation could not be
formed and the exact depth of `x + 1` was open. Paired with `xPlusOneTree_depth` (depth 4) it pins
the value.

The addition-closure question is therefore settled in both directions: EML *is* closed under `+1`,
and the cost is exactly four levels, not three. -/
theorem x_plus_one_not_depth_le_three (t : EMLTree) (ht : t.depth ≤ 3)
    (h : ∀ x : Real, 0 < x → t.eval x = x + 1) : False := by
  exact intermediateBand_not_depth_le_three (fun x => x + 1) x_plus_one_band_hyps t ht h


/-! ### Eventual sign-definiteness at depth 2, unconditionally

`evSign_of_hard` reduces sign-definiteness at every depth to one proposition. At depth ≤ 2 no
import is needed: the exp gap plus the depth-1 classification settle it outright.

Besides being the first unconditional instance, this is a check on the o-minimality reading — if
every term of this grammar is `ℝ_exp`-definable then *all* of them are eventually sign-definite, so a
counterexample here would have refuted that reading. There is none. -/

/-- **Every depth-≤2 expression is eventually of constant sign.** No hypotheses. -/
theorem evSign_depth_le_two (t : EMLTree) (ht : t.depth ≤ 2) : EvSign t.eval := by
  have hlog0 : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ log x := by
    intro x hx
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hm := log_le_log zero_lt_one_ax hx
    rw [hl1] at hm; exact hm
  have hxpos : ∀ x : Real, 1 ≤ x → (0 : Real) < x := fun x hx =>
    lt_of_lt_of_le zero_lt_one_ax hx
  cases t with
  | const c =>
      rcases lt_total 0 c with hc | hc | hc
      · exact Or.inl ⟨1, le_refl 1, fun x _ => hc⟩
      · exact Or.inr ⟨1, le_refl 1, fun x _ => le_of_eq hc.symm⟩
      · exact Or.inr ⟨1, le_refl 1, fun x _ => le_of_lt hc⟩
  | var => exact Or.inl ⟨1, le_refl 1, fun x hx => lt_of_lt_of_le zero_lt_one_ax hx⟩
  | eml A B =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B hB
      rcases depth_le_one_exp_bounded_or_grows A hA with ⟨K, hK⟩ | ⟨T, hT⟩
      · -- LEFT BOUNDED: the right child decides the sign
        rcases depth_le_one_classification B hB with
            ⟨β, hb⟩ | hb | ⟨c', hc'0, hb⟩ | ⟨d, hb⟩ | hb
        · -- `B = const β`: split the bounded left child into its two forms
          rcases depth_le_one_exp_bounded_forms A hA K hK with ⟨α, ha⟩ | ⟨c, _, ha⟩
          · -- node is the constant `exp α − log β`
            rcases lt_total 0 (exp α - log β) with hs | hs | hs
            · refine Or.inl ⟨1, le_refl 1, ?_⟩
              intro x hx
              show 0 < exp (A.eval x) - log (B.eval x)
              rw [ha x (hxpos x hx), hb x (hxpos x hx)]; exact hs
            · refine Or.inr ⟨1, le_refl 1, ?_⟩
              intro x hx
              show exp (A.eval x) - log (B.eval x) ≤ 0
              rw [ha x (hxpos x hx), hb x (hxpos x hx)]; exact le_of_eq hs.symm
            · refine Or.inr ⟨1, le_refl 1, ?_⟩
              intro x hx
              show exp (A.eval x) - log (B.eval x) ≤ 0
              rw [ha x (hxpos x hx), hb x (hxpos x hx)]; exact le_of_lt hs
          · -- `A = c − log x`, so `exp (A x) → 0`; the sign follows that of `−log β`
            rcases lt_total 0 (log β) with hs | hs | hs
            · -- `log β > 0`: the node is eventually negative
              obtain ⟨X₀, hX1, hX⟩ := eventually_log_gt (c - log (log β))
              refine Or.inr ⟨X₀, hX1, ?_⟩
              intro x hx
              have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
              show exp (A.eval x) - log (B.eval x) ≤ 0
              rw [ha x (hxpos x hx1), hb x (hxpos x hx1)]
              have hlt : c - log x < log (log β) := by
                have t1 := add_lt_add_left (hX x hx) (c - (c - log (log β)))
                have e1 : c - (c - log (log β)) + (c - log (log β)) = c := by
                  mach_mpoly [c, log (log β)]
                have e2 : c - (c - log (log β)) + log x = log (log β) + log x := by
                  mach_mpoly [c, log (log β), log x]
                rw [e1, e2] at t1
                have t2 := add_lt_add_left t1 (-log x)
                have e3 : -log x + c = c - log x := by mach_ring
                have e4 : -log x + (log (log β) + log x) = log (log β) := by mach_ring
                rw [e3, e4] at t2; exact t2
              have hexp : exp (c - log x) < log β := by
                have t1 := exp_lt hlt
                rw [exp_log hs] at t1; exact t1
              have t1 := add_lt_add_left hexp (-log β)
              have e1 : -log β + exp (c - log x) = exp (c - log x) - log β := by mach_ring
              have e2 : -log β + log β = 0 := by mach_ring
              rw [e1, e2] at t1; exact le_of_lt t1
            · -- `log β = 0`: the node is `exp (A x) > 0`
              refine Or.inl ⟨1, le_refl 1, ?_⟩
              intro x hx
              show 0 < exp (A.eval x) - log (B.eval x)
              rw [hb x (hxpos x hx), ← hs]
              have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
              rw [e]; exact exp_pos _
            · -- `log β < 0`: the node exceeds `exp (A x) > 0`
              refine Or.inl ⟨1, le_refl 1, ?_⟩
              intro x hx
              show 0 < exp (A.eval x) - log (B.eval x)
              rw [hb x (hxpos x hx)]
              have hn : (0 : Real) < -log β := by
                have t1 := add_lt_add_left hs (-log β)
                have e1 : -log β + 0 = -log β := by mach_ring
                have e2 : -log β + log β = 0 := by mach_ring
                rw [e1, e2] at t1; exact t1
              have v : (0 : Real) + 0 < exp (A.eval x) + -log β :=
                lt_of_lt_of_le (add_lt_add_left hn 0)
                  (add_le_add_wit (le_of_lt (exp_pos _)) (le_refl _))
              have e1 : (0 : Real) + 0 = 0 := by mach_ring
              have e2 : exp (A.eval x) + -log β = exp (A.eval x) - log β := by mach_ring
              rw [e1, e2] at v; exact v
        · -- `B = var`: `log x` outgrows the bounded left child
          obtain ⟨X₀, hX1, hX⟩ := eventually_log_gt K
          refine Or.inr ⟨X₀, hX1, ?_⟩
          intro x hx
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          show exp (A.eval x) - log (B.eval x) ≤ 0
          rw [hb x (hxpos x hx1)]
          have t1 : exp (A.eval x) < log x := lt_of_le_of_lt (hK x hx1) (hX x hx)
          have t2 := add_lt_add_left t1 (-log x)
          have e1 : -log x + exp (A.eval x) = exp (A.eval x) - log x := by mach_ring
          have e2 : -log x + log x = 0 := by mach_ring
          rw [e1, e2] at t2; exact le_of_lt t2
        · -- `B = c' − log x`: totalised to `0`, so the node is `exp (A x) > 0`
          obtain ⟨X₀, hX1, hX⟩ := eventually_log_gt c'
          refine Or.inl ⟨X₀, hX1, ?_⟩
          intro x hx
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          show 0 < exp (A.eval x) - log (B.eval x)
          rw [hb x (hxpos x hx1)]
          have hle : c' - log x ≤ 0 := by
            have t1 := add_lt_add_left (hX x hx) (-log x)
            have e1 : -log x + c' = c' - log x := by mach_ring
            have e2 : -log x + log x = 0 := by mach_ring
            rw [e1, e2] at t1; exact le_of_lt t1
          rw [log_nonpos hle]
          have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
          rw [e]; exact exp_pos _
        · -- `B = exp x − d`
          obtain ⟨X₀, hX1, hX⟩ := eventually_log_exp_sub_gt K d
          refine Or.inr ⟨X₀, hX1, ?_⟩
          intro x hx
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          show exp (A.eval x) - log (B.eval x) ≤ 0
          rw [hb x (hxpos x hx1)]
          have t1 : exp (A.eval x) < log (exp x - d) := lt_of_le_of_lt (hK x hx1) (hX x hx)
          have t2 := add_lt_add_left t1 (-log (exp x - d))
          have e1 : -log (exp x - d) + exp (A.eval x) = exp (A.eval x) - log (exp x - d) := by
            mach_ring
          have e2 : -log (exp x - d) + log (exp x - d) = 0 := by mach_ring
          rw [e1, e2] at t2; exact le_of_lt t2
        · -- `B = exp x − log x`
          obtain ⟨X₀, hX1, hX⟩ := eventually_log_exp_sub_log_gt K
          refine Or.inr ⟨X₀, hX1, ?_⟩
          intro x hx
          have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
          show exp (A.eval x) - log (B.eval x) ≤ 0
          rw [hb x (hxpos x hx1)]
          have t1 : exp (A.eval x) < log (exp x - log x) := lt_of_le_of_lt (hK x hx1) (hX x hx)
          have t2 := add_lt_add_left t1 (-log (exp x - log x))
          have e1 : -log (exp x - log x) + exp (A.eval x)
              = exp (A.eval x) - log (exp x - log x) := by mach_ring
          have e2 : -log (exp x - log x) + log (exp x - log x) = 0 := by mach_ring
          rw [e1, e2] at t2; exact le_of_lt t2
      · -- LEFT GROWS: the node clears `x` and is positive
        obtain ⟨T₂, hT₂⟩ := two_mul_add_le_exp D
        refine Or.inl ⟨exp T + exp T₂ + 1, ?_, ?_⟩
        · have v : (0 : Real) + 0 + 1 ≤ exp T + exp T₂ + 1 :=
            add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T)) (le_of_lt (exp_pos T₂)))
              (le_refl 1)
          have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
          rw [e] at v; exact v
        · intro x hx
          have hxT : T ≤ x := by
            have v : exp T + 0 + 0 ≤ exp T + exp T₂ + 1 :=
              add_le_add_wit (add_le_add_wit (le_refl _) (le_of_lt (exp_pos T₂)))
                (le_of_lt zero_lt_one_ax)
            have e : exp T + (0 : Real) + 0 = exp T := by mach_ring
            rw [e] at v; exact le_trans (self_le_exp T) (le_trans v hx)
          have hxT₂ : T₂ ≤ x := by
            have v : (0 : Real) + exp T₂ + 0 ≤ exp T + exp T₂ + 1 :=
              add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T)) (le_refl _))
                (le_of_lt zero_lt_one_ax)
            have e : (0 : Real) + exp T₂ + 0 = exp T₂ := by mach_ring
            rw [e] at v; exact le_trans (self_le_exp T₂) (le_trans v hx)
          have hx1 : (1 : Real) ≤ x := by
            have v : (0 : Real) + 0 + 1 ≤ exp T + exp T₂ + 1 :=
              add_le_add_wit (add_le_add_wit (le_of_lt (exp_pos T)) (le_of_lt (exp_pos T₂)))
                (le_refl 1)
            have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
            rw [e] at v; exact le_trans v hx
          show 0 < exp (A.eval x) - log (B.eval x)
          have g1 : exp x ≤ exp (A.eval x) := hT x hxT
          have g2 : log (B.eval x) ≤ x + D := hD x hx1
          have g3 : x + x + D ≤ exp x := hT₂ x hxT₂
          have hlow : x ≤ exp (A.eval x) - log (B.eval x) := by
            have v := add_le_add_wit g1 (neg_le_neg_wit g2)
            have e1 : exp x + -(x + D) = exp x - (x + D) := by mach_ring
            have e2 : exp (A.eval x) + -log (B.eval x)
                = exp (A.eval x) - log (B.eval x) := by mach_ring
            rw [e1, e2] at v
            have w : x ≤ exp x - (x + D) := by
              have u := add_le_add_wit g3 (le_refl (-(x + D)))
              have e3 : x + x + D + -(x + D) = x := by mach_mpoly [x, D]
              have e4 : exp x + -(x + D) = exp x - (x + D) := by mach_ring
              rw [e3, e4] at u; exact u
            exact le_trans w v
          exact lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one_ax hx1) hlow


/-- **The value gap at depth 2.** A depth-2 `eml` node is either bounded above on a ray, or
eventually at least `exp x − x − C`. **Nothing in between** — in particular no such node is
polynomially large.

This is the value-level analogue of `depth_le_one_exp_bounded_or_grows`, which is a statement about
`exp (A x)`. Stated for `eml` nodes specifically because `var` is a genuine exception: `x` is neither
bounded above nor eventually `≥ exp x − x − C`, and it sits at depth 0.

The band exclusion at depth ≤ 2 is this dichotomy read as a refutation; stated positively it is a
structural fact about what values the grammar can take, and it composes. -/
theorem depth_two_eml_value_gap (A B : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1) :
    (∃ K X₀ : Real, 1 ≤ X₀ ∧
      ∀ x : Real, X₀ ≤ x → exp (A.eval x) - log (B.eval x) ≤ K)
    ∨ (∃ C T : Real, ∀ x : Real, T ≤ x → exp x - x - C ≤ exp (A.eval x) - log (B.eval x)) := by
  rcases depth_le_one_exp_bounded_or_grows A hA with ⟨K, hK⟩ | ⟨T, hT⟩
  · -- bounded exponential: the log floor caps the node at `K − Cl`
    obtain ⟨Cl, X₀, hX1, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
    refine Or.inl ⟨K - Cl, X₀, hX1, ?_⟩
    intro x hx
    have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
    have v := add_le_add_wit (hK x hx1) (neg_le_neg_wit (hCl x hx))
    have e1 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
    have e2 : K + -Cl = K - Cl := by mach_ring
    rw [e1, e2] at v; exact v
  · -- growing exponential: the linear log ceiling leaves `exp x − x − D`
    obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B hB
    refine Or.inr ⟨D, exp T + 1, ?_⟩
    intro x hx
    have hxT : T ≤ x := by
      have v : exp T + 0 ≤ exp T + 1 := add_le_add_wit (le_refl _) (le_of_lt zero_lt_one_ax)
      have e : exp T + (0 : Real) = exp T := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp T) (le_trans v hx)
    have hx1 : (1 : Real) ≤ x := by
      have v : (0 : Real) + 1 ≤ exp T + 1 := add_le_add_wit (le_of_lt (exp_pos T)) (le_refl 1)
      have e : (0 : Real) + 1 = 1 := by mach_ring
      rw [e] at v; exact le_trans v hx
    have v := add_le_add_wit (hT x hxT) (neg_le_neg_wit (hD x hx1))
    have e1 : exp x + -(x + D) = exp x - x - D := by mach_mpoly [exp x, x, D]
    have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
    rw [e1, e2] at v; exact v


/-- **The value gap is a depth-2 phenomenon: it fails at depth 3, and `log x` is the witness.**

`log x` is computed by `logTree var` at depth exactly 3. It is *not* bounded above, and it is *not*
eventually `≥ exp x − x − C` for any `C`. So the dichotomy of `depth_two_eml_value_gap` is sharp.

This explains the band's third hypothesis. If the value gap survived to depth 3, the depth-3 band
exclusion would follow from it in one line; it does not, and the hole that opens is exactly
`log x`-shaped — unbounded and sub-exponential but never above the identity. **(H3) exists to
exclude precisely that hole**, which is why the depth-3 exclusion needed its own apparatus rather
than a dichotomy. -/
theorem value_gap_fails_at_depth_three :
    ∃ t : EMLTree, t.depth = 3
      ∧ (¬ ∃ K X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → t.eval x ≤ K)
      ∧ (¬ ∃ C T : Real, ∀ x : Real, T ≤ x → exp x - x - C ≤ t.eval x) := by
  refine ⟨logTree EMLTree.var, by rfl, ?_, ?_⟩
  · -- `log x` is unbounded above
    rintro ⟨K, X₀, hX1, hb⟩
    obtain ⟨Y, hY1, hY⟩ := eventually_log_gt K
    have hx : X₀ + Y ≤ X₀ + Y := le_refl _
    have hxX : X₀ ≤ X₀ + Y :=
      le_add_nonneg_r' (le_trans (le_of_lt zero_lt_one_ax) hY1)
    have hxY : Y ≤ X₀ + Y := by
      have v : (0 : Real) + Y ≤ X₀ + Y :=
        add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hX1) (le_refl Y)
      have e : (0 : Real) + Y = Y := by mach_ring
      rw [e] at v; exact v
    have hval : (logTree EMLTree.var).eval (X₀ + Y) = log (X₀ + Y) := by
      rw [logTree_eval]; rfl
    have hcap := hb (X₀ + Y) hxX
    rw [hval] at hcap
    exact lt_irrefl_ax _ (lt_of_lt_of_le (hY (X₀ + Y) hxY) hcap)
  · -- `log x` never reaches `exp x − x − C`
    rintro ⟨C, T, hb⟩
    obtain ⟨T₂, hT₂⟩ := two_mul_add_le_exp (C + 1)
    have hEp : (0 : Real) < exp T := exp_pos T
    have hE2p : (0 : Real) < exp T₂ := exp_pos T₂
    refine lt_irrefl_ax (log (exp T + exp T₂ + 1)) ?_
    have hxT : T ≤ exp T + exp T₂ + 1 := by
      have v : exp T + 0 + 0 ≤ exp T + exp T₂ + 1 :=
        add_le_add_wit (add_le_add_wit (le_refl _) (le_of_lt hE2p)) (le_of_lt zero_lt_one_ax)
      have e : exp T + (0 : Real) + 0 = exp T := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp T) v
    have hxT₂ : T₂ ≤ exp T + exp T₂ + 1 := by
      have v : (0 : Real) + exp T₂ + 0 ≤ exp T + exp T₂ + 1 :=
        add_le_add_wit (add_le_add_wit (le_of_lt hEp) (le_refl _)) (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + exp T₂ + 0 = exp T₂ := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp T₂) v
    have hx1 : (1 : Real) ≤ exp T + exp T₂ + 1 := by
      have v : (0 : Real) + 0 + 1 ≤ exp T + exp T₂ + 1 :=
        add_le_add_wit (add_le_add_wit (le_of_lt hEp) (le_of_lt hE2p)) (le_refl 1)
      have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
      rw [e] at v; exact v
    have hval : (logTree EMLTree.var).eval (exp T + exp T₂ + 1)
        = log (exp T + exp T₂ + 1) := by rw [logTree_eval]; rfl
    have hlow := hb (exp T + exp T₂ + 1) hxT
    rw [hval] at hlow
    -- `log y ≤ y` and `exp y ≥ y + y + C + 1` give `log y < exp y − y − C`
    have hly : log (exp T + exp T₂ + 1) ≤ exp T + exp T₂ + 1 := log_le_self_on_ray hx1
    have hgy := hT₂ (exp T + exp T₂ + 1) hxT₂
    have hstrict : log (exp T + exp T₂ + 1)
        < exp (exp T + exp T₂ + 1) - (exp T + exp T₂ + 1) - C := by
      have v : (exp T + exp T₂ + 1) + (exp T + exp T₂ + 1) + (C + 1)
          ≤ exp (exp T + exp T₂ + 1) := hgy
      have w : log (exp T + exp T₂ + 1) + (exp T + exp T₂ + 1) + C + 1
          ≤ exp (exp T + exp T₂ + 1) := by
        have u := add_le_add_wit (add_le_add_wit (add_le_add_wit hly
          (le_refl (exp T + exp T₂ + 1))) (le_refl C)) (le_refl (1 : Real))
        have e : (exp T + exp T₂ + 1) + (exp T + exp T₂ + 1) + C + 1
            = (exp T + exp T₂ + 1) + (exp T + exp T₂ + 1) + (C + 1) := by
          mach_mpoly [exp T, exp T₂, C]
        rw [e] at u; exact le_trans u v
      have z := add_le_add_wit w (le_refl (-(exp T + exp T₂ + 1) - C))
      have e1 : log (exp T + exp T₂ + 1) + (exp T + exp T₂ + 1) + C + 1
          + (-(exp T + exp T₂ + 1) - C) = log (exp T + exp T₂ + 1) + 1 := by
        mach_mpoly [log (exp T + exp T₂ + 1), exp T, exp T₂, C]
      have e2 : exp (exp T + exp T₂ + 1) + (-(exp T + exp T₂ + 1) - C)
          = exp (exp T + exp T₂ + 1) - (exp T + exp T₂ + 1) - C := by
        mach_mpoly [exp (exp T + exp T₂ + 1), exp T, exp T₂, C]
      rw [e1, e2] at z
      exact lt_of_lt_of_le (lt_succ_self _) z
    exact lt_of_lt_of_le hstrict hlow
  
/-- **The exponential gap is also sharp at depth 2, and `log x` is again the witness.**

`exp (log x) = x`, which is neither bounded nor eventually `≥ exp x` — it is *between* the two
classes the gap says are exhaustive. Since `log x` sits at depth 3, the gap fails there.

Taken with `value_gap_fails_at_depth_three`, this says something cleaner than either alone:
**depth 3 is exactly where the grammar acquires an intermediate scale.** Both depth-2 dichotomies
assert "bounded, or exponential, nothing between", and both are broken by the *same* object for the
*same* reason. -/
theorem exp_gap_fails_at_depth_three :
    ∃ A : EMLTree, A.depth = 3
      ∧ (¬ ∃ K X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → exp (A.eval x) ≤ K)
      ∧ (¬ ∃ T : Real, ∀ x : Real, T ≤ x → exp x ≤ exp (A.eval x)) := by
  have hval : ∀ x : Real, 0 < x → exp ((logTree EMLTree.var).eval x) = x := by
    intro x hx
    rw [logTree_eval]
    show exp (log x) = x
    exact exp_log hx
  refine ⟨logTree EMLTree.var, by rfl, ?_, ?_⟩
  · -- `exp (log x) = x` is unbounded
    rintro ⟨K, X₀, hX1, hb⟩
    have hEp : (0 : Real) < exp K := exp_pos K
    have hX0n : (0 : Real) ≤ X₀ := le_trans (le_of_lt zero_lt_one_ax) hX1
    have hxX : X₀ ≤ X₀ + exp K := le_add_nonneg_r' (le_of_lt hEp)
    have hx0 : (0 : Real) < X₀ + exp K :=
      lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one_ax hX1) hxX
    have hcap := hb (X₀ + exp K) hxX
    rw [hval (X₀ + exp K) hx0] at hcap
    have hKx : K < X₀ + exp K := by
      have hK : K < exp K := by
        have t1 := one_add_le_exp K
        have e : (1 : Real) + K = K + 1 := by mach_ring
        rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self K) t1
      have v : (0 : Real) + exp K ≤ X₀ + exp K := add_le_add_wit hX0n (le_refl _)
      have e : (0 : Real) + exp K = exp K := by mach_ring
      rw [e] at v
      exact lt_of_lt_of_le hK v
    exact lt_irrefl_ax _ (lt_of_lt_of_le hKx hcap)
  · -- and never reaches `exp x`, since `exp y > y`
    rintro ⟨T, hb⟩
    have hEp : (0 : Real) < exp T := exp_pos T
    have hxT : T ≤ exp T + 1 := by
      have v : exp T + 0 ≤ exp T + 1 := add_le_add_wit (le_refl _) (le_of_lt zero_lt_one_ax)
      have e : exp T + (0 : Real) = exp T := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp T) v
    have hx0 : (0 : Real) < exp T + 1 :=
      add_pos_of_nonneg_pos (le_of_lt hEp) zero_lt_one_ax
    have hlow := hb (exp T + 1) hxT
    rw [hval (exp T + 1) hx0] at hlow
    have hgt : exp T + 1 < exp (exp T + 1) := by
      have t1 := one_add_le_exp (exp T + 1)
      have e : (1 : Real) + (exp T + 1) = exp T + 1 + 1 := by mach_ring
      rw [e] at t1
      exact lt_of_lt_of_le (lt_succ_self _) t1
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hlow)


/-! ### Depth of a semantic class, not of a function

The sharpness results are more naturally read as statements about *classes*: the least depth at which
a previously unrealisable asymptotic behaviour becomes available. The first such transition is
located exactly. -/

/-- Unbounded above, yet eventually **strictly below the identity**. `log x` is the canonical member;
`x` itself is excluded, which is what makes the class non-trivial. -/
def BelowIdentityUnbounded (f : Real → Real) : Prop :=
  (∀ K X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ K < f x)
  ∧ (∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → f x < x)

/-- **No expression of depth ≤ 2 lies in the class.** -/
theorem belowIdentityUnbounded_not_depth_le_two (f : Real → Real)
    (hf : BelowIdentityUnbounded f) (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = f x) : False := by
  obtain ⟨hunb, X₁, hX11, hbelow⟩ := hf
  cases t with
  | const c =>
      obtain ⟨x, _, hx1, hlt⟩ := hunb c 1
      have hv : c = f x := h x (lt_of_lt_of_le zero_lt_one_ax hx1)
      rw [← hv] at hlt; exact lt_irrefl_ax c hlt
  | var =>
      -- `f x = x` contradicts `f x < x`
      have hx1 : (1 : Real) ≤ X₁ := hX11
      have hv : X₁ = f X₁ := h X₁ (lt_of_lt_of_le zero_lt_one_ax hx1)
      have hlt := hbelow X₁ (le_refl X₁)
      rw [← hv] at hlt; exact lt_irrefl_ax X₁ hlt
  | eml A B =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      rcases depth_two_eml_value_gap A B hA hB with ⟨K, X₀, hX1, hcap⟩ | ⟨C, T, hfloor⟩
      · -- bounded above contradicts unboundedness
        obtain ⟨x, hxX, hx1, hlt⟩ := hunb K X₀
        have hv : exp (A.eval x) - log (B.eval x) = f x :=
          h x (lt_of_lt_of_le zero_lt_one_ax hx1)
        have hcapx := hcap x hxX
        rw [hv] at hcapx
        exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hcapx)
      · -- an exponential floor contradicts sitting below the identity
        obtain ⟨T₂, hT₂⟩ := two_mul_add_le_exp C
        obtain ⟨x, hxX, hx1, _⟩ := hunb 0 (X₁ + exp T + exp T₂)
        have hE : (0 : Real) ≤ exp T := le_of_lt (exp_pos T)
        have hE2 : (0 : Real) ≤ exp T₂ := le_of_lt (exp_pos T₂)
        have hX1n : (0 : Real) ≤ X₁ := le_trans (le_of_lt zero_lt_one_ax) hX11
        have hxX1 : X₁ ≤ x := by
          have v : X₁ + 0 + 0 ≤ X₁ + exp T + exp T₂ :=
            add_le_add_wit (add_le_add_wit (le_refl X₁) hE) hE2
          have e : X₁ + (0 : Real) + 0 = X₁ := by mach_ring
          rw [e] at v; exact le_trans v hxX
        have hxT : T ≤ x := by
          have v : (0 : Real) + exp T + 0 ≤ X₁ + exp T + exp T₂ :=
            add_le_add_wit (add_le_add_wit hX1n (le_refl _)) hE2
          have e : (0 : Real) + exp T + 0 = exp T := by mach_ring
          rw [e] at v; exact le_trans (self_le_exp T) (le_trans v hxX)
        have hxT₂ : T₂ ≤ x := by
          have v : (0 : Real) + 0 + exp T₂ ≤ X₁ + exp T + exp T₂ :=
            add_le_add_wit (add_le_add_wit hX1n hE) (le_refl _)
          have e : (0 : Real) + 0 + exp T₂ = exp T₂ := by mach_ring
          rw [e] at v; exact le_trans (self_le_exp T₂) (le_trans v hxX)
        have hv : exp (A.eval x) - log (B.eval x) = f x :=
          h x (lt_of_lt_of_le zero_lt_one_ax hx1)
        have hlow : exp x - x - C ≤ f x := by rw [← hv]; exact hfloor x hxT
        have hhigh : f x < x := hbelow x hxX1
        -- so `exp x < x + x + C`, refuted on the ray
        have hbad : exp x - x - C < x := lt_of_le_of_lt hlow hhigh
        have hgood : x + x + C ≤ exp x := hT₂ x hxT₂
        have hge : x ≤ exp x - x - C := by
          have v := add_le_add_wit (add_le_add_wit hgood (le_refl (-x))) (le_refl (-C))
          have e1 : x + x + C + -x + -C = x := by mach_mpoly [x, C]
          have e2 : exp x + -x + -C = exp x - x - C := by mach_mpoly [exp x, x, C]
          rw [e1, e2] at v; exact v
        exact lt_irrefl_ax x (lt_of_le_of_lt hge hbad)

/-- **`log x` is in the class, at depth 3.** With the previous theorem: the least depth at which
unbounded-yet-below-the-identity behaviour is realisable is exactly **3**. -/
theorem belowIdentityUnbounded_at_depth_three :
    ∃ t : EMLTree, t.depth = 3 ∧ BelowIdentityUnbounded t.eval := by
  refine ⟨logTree EMLTree.var, by rfl, ?_, ?_⟩
  · -- unbounded above. The witness uses `exp X`, not `X`: the latter may be negative.
    intro K X
    obtain ⟨Y, hY1, hY⟩ := eventually_log_gt K
    have hY0 : (0 : Real) ≤ Y := le_trans (le_of_lt zero_lt_one_ax) hY1
    have hXp : (0 : Real) < exp X := exp_pos X
    refine ⟨exp X + Y + 1, ?_, ?_, ?_⟩
    · have v : exp X + 0 + 0 ≤ exp X + Y + 1 :=
        add_le_add_wit (add_le_add_wit (le_refl _) hY0) (le_of_lt zero_lt_one_ax)
      have e : exp X + (0 : Real) + 0 = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have v : (0 : Real) + 0 + 1 ≤ exp X + Y + 1 :=
        add_le_add_wit (add_le_add_wit (le_of_lt hXp) hY0) (le_refl 1)
      have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
      rw [e] at v; exact v
    · have hval : (logTree EMLTree.var).eval (exp X + Y + 1) = log (exp X + Y + 1) := by
        rw [logTree_eval]; rfl
      rw [hval]
      refine hY (exp X + Y + 1) ?_
      have v : (0 : Real) + Y + 0 ≤ exp X + Y + 1 :=
        add_le_add_wit (add_le_add_wit (le_of_lt hXp) (le_refl Y)) (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + Y + 0 = Y := by mach_ring
      rw [e] at v; exact v
  · -- and strictly below the identity past `1`
    refine ⟨1 + 1, le_of_lt (lt_succ_self 1), ?_⟩
    intro x hx
    have hx1 : (1 : Real) < x := lt_of_lt_of_le (lt_succ_self 1) hx
    have hxpos : (0 : Real) < x := lt_trans_ax zero_lt_one_ax hx1
    have hval : (logTree EMLTree.var).eval x = log x := by rw [logTree_eval]; rfl
    rw [hval]
    have h1 : log x ≤ x := log_le_self_pos hxpos
    rcases lt_total (log x) x with hp | hp | hp
    · exact hp
    · exfalso
      have hxe : exp (log x) = x := exp_log hxpos
      rw [hp] at hxe
      have hgt : x < exp x := by
        have t1 := one_add_le_exp x
        have e : (1 : Real) + x = x + 1 := by mach_ring
        rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self x) t1
      rw [hxe] at hgt; exact lt_irrefl_ax x hgt
    · exact absurd (lt_of_lt_of_le hp h1) (lt_irrefl_ax x)

/-- **`log x` lies in the below-identity-unbounded class.**

Stated for the *function* rather than for a particular tree. `belowIdentityUnbounded_at_depth_three`
already proves the class non-empty at depth 3 by exhibiting `logTree var`, but it returns an
existential, so nothing downstream can recover which tree it was — and a consumer that wants
"`log x` specifically" cannot get there from it. This is that statement. -/
theorem log_belowIdentityUnbounded : BelowIdentityUnbounded log := by
  refine ⟨?_, ?_⟩
  · intro K X
    obtain ⟨Y, hY1, hY⟩ := eventually_log_gt K
    have hY0 : (0 : Real) ≤ Y := le_trans (le_of_lt zero_lt_one_ax) hY1
    have hXp : (0 : Real) < exp X := exp_pos X
    refine ⟨exp X + Y + 1, ?_, ?_, ?_⟩
    · have v : exp X + 0 + 0 ≤ exp X + Y + 1 :=
        add_le_add_wit (add_le_add_wit (le_refl _) hY0) (le_of_lt zero_lt_one_ax)
      have e : exp X + 0 + 0 = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have v : (0 : Real) + 0 + 1 ≤ exp X + Y + 1 :=
        add_le_add_wit (add_le_add_wit (le_of_lt hXp) hY0) (le_refl 1)
      have e : (0 : Real) + 0 + 1 = 1 := by mach_ring
      rw [e] at v; exact v
    · refine hY (exp X + Y + 1) ?_
      have v : (0 : Real) + Y + 0 ≤ exp X + Y + 1 :=
        add_le_add_wit (add_le_add_wit (le_of_lt hXp) (le_refl Y)) (le_of_lt zero_lt_one_ax)
      have e : (0 : Real) + Y + 0 = Y := by mach_ring
      rw [e] at v; exact v
  · refine ⟨1, le_refl 1, ?_⟩
    intro x hx
    exact log_lt_self (lt_of_lt_of_le zero_lt_one_ax hx)

/-- **`log x` is unreachable at depth ≤ 2** — the lower half of `d(log x) = 3`.

Registered as a named declaration because the exact depth of `log x` was being quoted publicly while
only the depth-3 *construction* had a citable name; the lower bound existed solely as an immediate
consequence of the transition machinery. A consumer must be able to cite one declaration rather than
reassemble an argument. -/
theorem log_x_not_depth_le_two (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = log x) : False :=
  belowIdentityUnbounded_not_depth_le_two log log_belowIdentityUnbounded t ht h

/-- **`d_(0,∞)(log x) = 3`, exactly — both halves, in one declaration.**

The domain is part of the claim and is carried in the statement: agreement is required on `(0, ∞)`.
An unlabelled `d(log x) = 3` is a different and weaker-provenance assertion.

Left conjunct: no tree of depth `≤ 2` agrees with `log` on `(0, ∞)`.
Right conjunct: `logTree var` has depth exactly `3` and agrees with `log` everywhere. -/
theorem log_x_depth_exact_three :
    (∀ t : EMLTree, t.depth ≤ 2 → (∀ x : Real, 0 < x → t.eval x = log x) → False)
    ∧ (∃ t : EMLTree, t.depth = 3 ∧ ∀ x : Real, 0 < x → t.eval x = log x) := by
  refine ⟨fun t ht h => log_x_not_depth_le_two t ht h, ⟨logTree EMLTree.var, by rfl, ?_⟩⟩
  intro x _
  rw [logTree_eval]; rfl

/-- **`d_(0,∞)(x + 1) = 4`, exactly — both halves, in one declaration.**

Companion to `log_x_depth_exact_three`, and the counterexample that refuted the "no standard
function lives at depth 4" claim. Domain carried in the statement for the same reason. -/
theorem x_plus_one_depth_exact_four :
    (∀ t : EMLTree, t.depth ≤ 3 → (∀ x : Real, 0 < x → t.eval x = x + 1) → False)
    ∧ (∃ t : EMLTree, t.depth = 4 ∧ ∀ x : Real, 0 < x → t.eval x = x + 1) := by
  refine ⟨fun t ht h => x_plus_one_not_depth_le_three t ht h, ?_⟩
  obtain ⟨t, hteval, htdepth⟩ := x_plus_one_in_eml
  exact ⟨t, htdepth, fun x _ => hteval x⟩

/-- **Obligation: the growing-left branch of the negative translation.**

Narrow deliberately. What is open is *not* "negative translations" — it is one branch of one case:
a depth-3 node representing `x + c` with `c < 0`, where the left child's exponential already
dominates `exp x`, so `exp (A x)` and `log (B x)` are both near `exp x` and **cancel**.

The bounded-left branch is closed (`mirrorBand_not_depth_three_bounded_left`). The split is
structural rather than an artefact of the proof: `log x` is reachable at depth 3 through *both*
branches — via `A = const 0`, and via `A = var` with `B` evaluating to `exp (exp x − log x)` — so the
super-logarithmic condition has to cut both, and only the bounded one cuts cheaply.

Stated as a Prop so the shorthand "negative translation is almost done" cannot form. It is the same
species of difficulty as `ExpExpGapBelow` and `BoundedCellApproach`, which took an arc each. -/
def NegativeTranslationGrowingLeft : Prop :=
  ∀ c : Real, c < 0 → ∀ A B : EMLTree, A.depth ≤ 2 → B.depth ≤ 2 →
    (∃ T : Real, ∀ x : Real, T ≤ x → exp x ≤ exp (A.eval x)) →
    (∀ x : Real, 0 < x → exp (A.eval x) - log (B.eval x) = x + c) → False

/-! ### The mirror band

`IntermediateBand` excludes targets that are unbounded, sub-exponential, superlinear and
super-logarithmic. Its third condition `x < f x` is what the negative translation family fails
structurally. The **mirror** replaces it by `f x < x` — below the identity rather than above — and
keeps the rest.

The class is not empty at depth 3 without the logarithmic condition: `log x` is unbounded and below
the identity and *is* depth 3 (§4). So `Hlog` is what does the separating, exactly as it did in the
positive case where its absence once broke a sharpness composition.

**Status: half proved.** The bounded-left case closes below. The growing-left case is where
`exp(A x)` and `log(B x)` are both near `exp x` and cancel, which is the same difficulty
`ExpExpGapBelow` and `BoundedCellApproach` were introduced for. It is stated as an obligation rather
than assumed. -/

/-- Unbounded above, eventually below the identity, and super-logarithmic. -/
def MirrorBand (f : Real → Real) : Prop :=
  BelowIdentityUnbounded f
  ∧ (∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ C + log x < f x)

/-- A constant at least `1` dominating a given one. `C + exp (−C) ≥ 1` because `1 − C ≤ exp (−C)`. -/
private theorem shift_nonneg (C : Real) : 1 ≤ C + exp (-C) := by
  have h := one_add_le_exp (-C)
  have e : (1 : Real) + -C = 1 - C := by mach_ring
  rw [e] at h
  have v := add_le_add_wit (le_refl C) h
  have l : C + (1 - C) = 1 := by mach_mpoly [C]
  rw [l] at v; exact v

private theorem shift_ge (C : Real) : C ≤ C + exp (-C) := by
  have v := add_le_add_wit (le_refl C) (le_of_lt (exp_pos (-C)))
  have e : C + 0 = C := by mach_ring
  rw [e] at v; exact v

/-- Where the right child is non-positive its logarithm is `0`, the node is `exp (A x) ≤ K`, and the
super-logarithmic witness gives `K + (C + exp (−C)) + 1 + log x < K`. Since `C + exp (−C) ≥ 1` and
`log x ≥ 0`, the left side exceeds `K` by at least `2`. No decay bound is needed on this branch. -/
private theorem mirror_totalised_absurd (f : Real → Real) (K C x : Real)
    (hgt : K + (C + exp (-C)) + 1 + log x < f x) (hlogx : (0 : Real) ≤ log x)
    (hshift : (1 : Real) ≤ C + exp (-C)) (hfK : f x ≤ K) : False := by
  have hlt : K + (C + exp (-C)) + 1 + log x < K := lt_of_lt_of_le hgt hfK
  have v := add_lt_add_left hlt (-K)
  have l : -K + (K + (C + exp (-C)) + 1 + log x) = C + exp (-C) + 1 + log x := by
    mach_mpoly [K, C, log x, exp (-C)]
  have r : -K + K = 0 := by mach_ring
  rw [l, r] at v
  have hpos : (0 : Real) < C + exp (-C) + 1 + log x := by
    refine lt_of_lt_of_le zero_lt_one_ax ?_
    have w := add_le_add_wit (add_le_add_wit hshift (le_refl (1 : Real))) hlogx
    have e : (1 : Real) + 1 + 0 = 1 + 1 := by mach_ring
    rw [e] at w
    refine le_trans ?_ w
    have u := add_lt_add_left zero_lt_one_ax (1 : Real)
    have l2 : (1 : Real) + 0 = 1 := by mach_ring
    rw [l2] at u; exact le_of_lt u
  exact lt_irrefl_ax _ (lt_trans_ax hpos v)

/-- **The mirror band excludes every depth-3 node whose left child has bounded exponential.**

Two sub-cases, and the totalisation splits them. Where the right child is eventually non-positive its
logarithm is identically `0`, so the node *is* `exp (A x)` and is bounded — killing unboundedness.
Where it is positive, `depth_le_two_decay_on_ray` caps `−log (B x)` at `C + log x`, so the node is at
most `K + C + log x` — killing super-logarithmicity. -/
theorem mirrorBand_not_depth_three_bounded_left (f : Real → Real) (hf : MirrorBand f)
    (A B : EMLTree) (hB : B.depth ≤ 2) (K XK : Real)
    (hK : ∀ x : Real, XK ≤ x → exp (A.eval x) ≤ K)
    (h : ∀ x : Real, 0 < x → exp (A.eval x) - log (B.eval x) = f x) : False := by
  obtain ⟨_, hlog⟩ := hf
  obtain ⟨C, X₀, hX₀, hdec⟩ := depth_le_two_decay_on_ray B hB
  -- the threshold is a sum of exponentials, so it dominates `XK` and `X₀` whatever their sign
  obtain ⟨x, hxb, hx1, hgt⟩ := hlog (K + (C + exp (-C)) + 1) (exp XK + exp X₀)
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hxK : XK ≤ x := by
    refine le_trans (self_le_exp XK) (le_trans ?_ hxb)
    have v : exp XK + 0 ≤ exp XK + exp X₀ := add_le_add_wit (le_refl _) (le_of_lt (exp_pos X₀))
    have e : exp XK + 0 = exp XK := by mach_ring
    rw [e] at v; exact v
  have hx0' : X₀ ≤ x := by
    refine le_trans (self_le_exp X₀) (le_trans ?_ hxb)
    have v : (0 : Real) + exp X₀ ≤ exp XK + exp X₀ :=
      add_le_add_wit (le_of_lt (exp_pos XK)) (le_refl _)
    have e : (0 : Real) + exp X₀ = exp X₀ := by mach_ring
    rw [e] at v; exact v
  have hval := h x hx0
  have hKx := hK x hxK
  have hlogx : (0 : Real) ≤ log x := by
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hm := log_le_log zero_lt_one_ax hx1
    rw [hl1] at hm; exact hm
  have hshift : (1 : Real) ≤ C + exp (-C) := shift_nonneg C
  rcases lt_total 0 (B.eval x) with hBpos | hBz | hBneg
  · -- right child positive: the decay bound caps the node at `K + C + log x`
    have hd := hdec x hx0' hBpos
    have cap : f x ≤ K + (C + log x) := by
      rw [← hval]
      have v := add_le_add_wit hKx hd
      have e : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
        mach_mpoly [exp (A.eval x), log (B.eval x)]
      rw [← e]; exact v
    have hlt : K + (C + exp (-C)) + 1 + log x < K + (C + log x) := lt_of_lt_of_le hgt cap
    have v := add_lt_add_left hlt (-(K + (C + log x)))
    have l : -(K + (C + log x)) + (K + (C + exp (-C)) + 1 + log x) = exp (-C) + 1 := by
      mach_mpoly [K, C, log x, exp (-C)]
    have r : -(K + (C + log x)) + (K + (C + log x)) = 0 := by mach_mpoly [K, C, log x]
    rw [l, r] at v
    exact lt_irrefl_ax _ (lt_trans_ax (add_pos (exp_pos (-C)) zero_lt_one_ax) v)
  · -- right child zero: totalisation gives `log 0 = 0`, so the node is `exp (A x) ≤ K`
    exact mirror_totalised_absurd f K C x hgt hlogx hshift
      (by rw [← hval, ← hBz, log_nonpos (le_refl 0)]
          have e : exp (A.eval x) - 0 = exp (A.eval x) := by mach_ring
          rw [e]; exact hKx)
  · -- right child negative: identically
    exact mirror_totalised_absurd f K C x hgt hlogx hshift
      (by rw [← hval, log_nonpos (le_of_lt hBneg)]
          have e : exp (A.eval x) - 0 = exp (A.eval x) := by mach_ring
          rw [e]; exact hKx)

/-! ### The negative side, and the asymmetry

For `c < 0` the band's third condition `x < f x` fails *structurally* — `x + c < x` everywhere — so
the exclusion above is unavailable, and not merely inconvenient. The grammar is not symmetric about
translation: `log` is totalised at `0` and the whole envelope theory is stated on right-hand rays.

What survives is the weaker class of §4: `x + c` is unbounded above and eventually below the
identity, which excludes depth `≤ 2` but not depth `3`. So the two sides are genuinely different at
the present state of knowledge:

```
    c > 0    d_(0,∞)(x + c)  =  4          exactly
    c = 0    d(x)            =  0          it is `var`
    c < 0    d_(0,∞)(x + c)  ∈  {3, 4}     lower bound 3, upper bound 4
```

Whether the negative gap is real or an artefact of the missing instrument is **open**, and it is the
first question this family raises that the existing machinery cannot answer. -/

/-- `x + c` is unbounded above yet eventually strictly below the identity, for `c < 0`. -/
theorem x_plus_neg_c_belowIdentity (c : Real) (hc : c < 0) :
    BelowIdentityUnbounded (fun x => x + c) := by
  refine ⟨?_, ?_⟩
  · -- unbounded above: take `x` past `K − c`, which exceeds `K` because `c < 0`
    intro K X
    refine ⟨1 + exp (K - c) + exp X, ?_, ?_, ?_⟩
    · have v : (0 : Real) + 0 + exp X ≤ 1 + exp (K - c) + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos (K - c))))
          (le_refl _)
      have e : (0 : Real) + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have v : (1 : Real) + 0 + 0 ≤ 1 + exp (K - c) + exp X :=
        add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos (K - c))))
          (le_of_lt (exp_pos X))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    · show K < 1 + exp (K - c) + exp X + c
      have hKc : K - c < exp (K - c) := by
        have t1 := one_add_le_exp (K - c)
        have e : (1 : Real) + (K - c) = (K - c) + 1 := by mach_ring
        rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self (K - c)) t1
      have v : (0 : Real) + exp (K - c) + 0 ≤ 1 + exp (K - c) + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
          (le_of_lt (exp_pos X))
      have e : (0 : Real) + exp (K - c) + 0 = exp (K - c) := by mach_ring
      rw [e] at v
      have hlt : K - c < 1 + exp (K - c) + exp X := lt_of_lt_of_le hKc v
      have w := add_lt_add_left hlt c
      have l : c + (K - c) = K := by mach_mpoly [c, K]
      have r : c + (1 + exp (K - c) + exp X) = 1 + exp (K - c) + exp X + c := by
        mach_mpoly [c, exp (K - c), exp X]
      rw [l, r] at w; exact w
  · -- eventually strictly below the identity: `x + c < x` for every `x`, since `c < 0`
    refine ⟨1, le_refl 1, ?_⟩
    intro x _
    show x + c < x
    have v := add_lt_add_left hc x
    have l : x + (0 : Real) = x := by mach_ring
    rw [l] at v; exact v

/-- **`x + c` is unreachable at depth ≤ 2 for `c < 0`.** With the depth-4 construction this pins
`d_(0,∞)(x + c) ∈ {3, 4}` — and which of the two is **open**. -/
theorem x_plus_neg_c_not_depth_le_two (c : Real) (hc : c < 0) (t : EMLTree) (ht : t.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → t.eval x = x + c) : False :=
  belowIdentityUnbounded_not_depth_le_two (fun x => x + c) (x_plus_neg_c_belowIdentity c hc) t ht h

/-- **The depth-3 band's four hypotheses for `x²`, with STRICT witnesses.**

Factored out because the band is now consumed twice — once for a tree agreeing with `x²` on `(0,∞)`
and once on `(1,∞)` — and the arithmetic is identical for both. Every witness produced here is
**strictly** greater than `1`, which is the whole point of the factoring.

**The evidence for `d(x²) ≥ 4` never used a point `x ≤ 1`.** All four of the band's hypotheses are
"infinitely often, arbitrarily far right" statements, so their witnesses can always be pushed past
any threshold; the `∀ x, 0 < x` agreement clause in the original instantiation was therefore
stronger than the proof ever needed. Recording the witnesses as strict is what makes that visible,
and it is what lets `x_sq_ray_not_depth_le_three` exist at all.

Only the sub-exponential row needed real work: `exp_beats_powNat` hands back `1 ≤ x`, so it is called
at the threshold `1 + exp X` rather than `X`, which forces `1 < x` and still clears `X` (via
`X ≤ exp X ≤ 1 + exp X`). The other three build their own witnesses and were already strict. -/
private theorem x_sq_band_hyps :
    (∀ K X : Real, ∃ x : Real, X ≤ x ∧ 1 < x ∧ K < x * x)
    ∧ (∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 < x ∧ x * x < exp x - x - C)
    ∧ (∀ X : Real, ∃ x : Real, X ≤ x ∧ 1 < x ∧ x < x * x)
    ∧ (∀ C X : Real, ∃ x : Real, X ≤ x ∧ 1 < x ∧ C + log x < x * x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- unbounded: `K < x ≤ x·x`
    intro K X
    have hKe : K < exp K := by
      have t1 := one_add_le_exp K
      have e : (1 : Real) + K = K + 1 := by mach_ring
      rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self K) t1
    have hstep1 : (1 : Real) < 1 + exp K := lt_add_of_pos_right (exp_pos K)
    have hstep2 : (1 : Real) + exp K < 1 + exp K + exp X := lt_add_of_pos_right (exp_pos X)
    have hgt : (1 : Real) < 1 + exp K + exp X := lt_trans_ax hstep1 hstep2
    have hx1 : (1 : Real) ≤ 1 + exp K + exp X := le_of_lt hgt
    refine ⟨1 + exp K + exp X, ?_, hgt, ?_⟩
    · have v : (0 : Real) + 0 + exp X ≤ 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos K)))
          (le_refl _)
      have e : (0 : Real) + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have hsq : (1 + exp K + exp X) ≤ (1 + exp K + exp X) * (1 + exp K + exp X) := by
        have u := mul_le_mul_of_nonneg_left hx1
          (le_trans (le_of_lt zero_lt_one_ax) hx1)
        have e : (1 + exp K + exp X) * (1 : Real) = 1 + exp K + exp X := by mach_ring
        rw [e] at u; exact u
      have hKx : K < 1 + exp K + exp X := by
        have v : (0 : Real) + exp K + 0 ≤ 1 + exp K + exp X :=
          add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
            (le_of_lt (exp_pos X))
        have e : (0 : Real) + exp K + 0 = exp K := by mach_ring
        rw [e] at v; exact lt_of_lt_of_le hKe v
      exact lt_of_lt_of_le hKx hsq
  · -- sub-exponential: `exp_beats_powNat` at `k = 0`, pushed past `1 + exp X` to force strictness
    intro C X
    have hone : (1 : Real) < 1 + exp X := lt_add_of_pos_right (exp_pos X)
    obtain ⟨x, hxT, _, hlt⟩ := exp_beats_powNat 0 C (1 + exp X)
    have hgt : (1 : Real) < x := lt_of_lt_of_le hone hxT
    refine ⟨x, ?_, hgt, ?_⟩
    · -- `le_add_nonneg_l'` is not in scope this early in the file; four lines beat reordering it
      have hle : exp X ≤ 1 + exp X := by
        have v : (0 : Real) + exp X ≤ 1 + exp X :=
          add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
        have e : (0 : Real) + exp X = exp X := by mach_ring
        rw [e] at v; exact v
      exact le_trans (le_trans (self_le_exp X) hle) hxT
    · have e : powNat x (0 + 2) = x * x := by
        show x * (x * 1) = x * x
        mach_ring
      rw [e] at hlt
      have v := add_lt_add_left hlt (-x - C)
      have e1 : -x - C + (x * x + x + C) = x * x := by mach_mpoly [x, C]
      have e2 : -x - C + exp x = exp x - x - C := by mach_mpoly [exp x, x, C]
      rw [e1, e2] at v; exact v
  · -- superlinear: `x < x·x` once `x > 1`
    intro X
    have hgt : (1 : Real) < 1 + 1 + exp X :=
      lt_trans_ax (lt_succ_self (1 : Real)) (lt_add_of_pos_right (exp_pos X))
    refine ⟨1 + 1 + exp X, ?_, hgt, ?_⟩
    · have v : (0 : Real) + 0 + exp X ≤ 1 + 1 + exp X :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt zero_lt_one_ax))
          (le_refl _)
      have e : (0 : Real) + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have u := mul_lt_mul_of_pos_right hgt (lt_trans_ax zero_lt_one_ax hgt)
      have e : (1 : Real) * (1 + 1 + exp X) = 1 + 1 + exp X := by mach_ring
      rw [e] at u; exact u
  · -- superlogarithmic: `C + log x ≤ C + x < x·x` once `x − 1 ≥ 1` and `x > C`
    intro C X
    have hCp : (0 : Real) < exp C := exp_pos C
    have hXp : (0 : Real) < exp X := exp_pos X
    have hgt : (1 : Real) < 1 + 1 + exp C + exp X :=
      lt_trans_ax (lt_trans_ax (lt_succ_self (1 : Real)) (lt_add_of_pos_right hCp))
        (lt_add_of_pos_right hXp)
    have hx1 : (1 : Real) ≤ 1 + 1 + exp C + exp X := le_of_lt hgt
    refine ⟨1 + 1 + exp C + exp X, ?_, hgt, ?_⟩
    · have v : (0 : Real) + 0 + 0 + exp X ≤ 1 + 1 + exp C + exp X :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
          (le_of_lt zero_lt_one_ax)) (le_of_lt hCp)) (le_refl _)
      have e : (0 : Real) + 0 + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have hx0 : (0 : Real) < 1 + 1 + exp C + exp X := lt_of_lt_of_le zero_lt_one_ax hx1
      have hx2 : (1 : Real) + 1 ≤ 1 + 1 + exp C + exp X := by
        have v : (1 : Real) + 1 + 0 + 0 ≤ 1 + 1 + exp C + exp X :=
          add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_refl 1))
            (le_of_lt hCp)) (le_of_lt hXp)
        have e : (1 : Real) + 1 + 0 + 0 = 1 + 1 := by mach_ring
        rw [e] at v; exact v
      have hCx : C < 1 + 1 + exp C + exp X := by
        have hCe : C < exp C := by
          have t1 := one_add_le_exp C
          have e : (1 : Real) + C = C + 1 := by mach_ring
          rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self C) t1
        have v : (0 : Real) + 0 + exp C + 0 ≤ 1 + 1 + exp C + exp X :=
          add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
            (le_of_lt zero_lt_one_ax)) (le_refl _)) (le_of_lt hXp)
        have e : (0 : Real) + 0 + exp C + 0 = exp C := by mach_ring
        rw [e] at v; exact lt_of_lt_of_le hCe v
      have hlogle : log (1 + 1 + exp C + exp X) ≤ 1 + 1 + exp C + exp X :=
        log_le_self_pos hx0
      -- `C + log x < x + log x ≤ x + x ≤ x·x`
      have s1 : C + log (1 + 1 + exp C + exp X)
          < (1 + 1 + exp C + exp X) + log (1 + 1 + exp C + exp X) := by
        have t1 := add_lt_add_left hCx (log (1 + 1 + exp C + exp X))
        have e1 : log (1 + 1 + exp C + exp X) + C = C + log (1 + 1 + exp C + exp X) := by
          mach_ring
        have e2 : log (1 + 1 + exp C + exp X) + (1 + 1 + exp C + exp X)
            = (1 + 1 + exp C + exp X) + log (1 + 1 + exp C + exp X) := by mach_ring
        rw [e1, e2] at t1; exact t1
      have s2 : (1 + 1 + exp C + exp X) + log (1 + 1 + exp C + exp X)
          ≤ (1 + 1 + exp C + exp X) + (1 + 1 + exp C + exp X) :=
        add_le_add_left hlogle _
      have s3 : (1 + 1 + exp C + exp X) + (1 + 1 + exp C + exp X)
          ≤ (1 + 1 + exp C + exp X) * (1 + 1 + exp C + exp X) := by
        have u := mul_le_mul_of_nonneg_left hx2 (le_of_lt hx0)
        have e : (1 + 1 + exp C + exp X) * ((1 : Real) + 1)
            = (1 + 1 + exp C + exp X) + (1 + 1 + exp C + exp X) := by mach_ring
        rw [e] at u; exact u
      exact lt_of_lt_of_le s1 (le_trans s2 s3)

/-- **`d(x²) ≥ 4` on `(0,∞)`.** The depth-3 band applied to `x²`, which requires discharging all four
of its hypotheses for that target.

Recorded explicitly because the number has been quoted from the general theorem without ever being
instantiated. `x_sq_not_depth_le_two` gave only `≥ 3`.

**Read the domain.** This is the bound for a tree agreeing with `x²` on all of `(0,∞)`. It is *not*
the lower bound that pairs with `sqTree` (depth 8), which only agrees on `(1,∞)` — see
`x_sq_ray_not_depth_le_three` for that one, and the warning on both. -/
theorem x_sq_not_depth_le_three (t : EMLTree) (ht : t.depth ≤ 3)
    (h : ∀ x : Real, 0 < x → t.eval x = x * x) : False := by
  obtain ⟨H1, H2, H3, Hlog⟩ := x_sq_band_hyps
  refine superlinear_subexp_not_depth_le_three (fun x => x * x)
    (fun K X => by obtain ⟨x, hX, hgt, hv⟩ := H1 K X; exact ⟨x, hX, le_of_lt hgt, hv⟩)
    (fun C X => by obtain ⟨x, hX, hgt, hv⟩ := H2 C X; exact ⟨x, hX, le_of_lt hgt, hv⟩)
    (fun X => by obtain ⟨x, hX, hgt, hv⟩ := H3 X; exact ⟨x, hX, le_of_lt hgt, hv⟩)
    (fun C X => by obtain ⟨x, hX, hgt, hv⟩ := Hlog C X; exact ⟨x, hX, le_of_lt hgt, hv⟩)
    t ht h

/-- **`d(x²) ≥ 4` on the ray `(1,∞)`** — the lower bound that legitimately pairs with `sqTree`.

**Why this theorem had to exist separately.** `sqTree` computes `x²` at depth 8 but only for `x > 1`
(it routes through `exp (log (log x))`, which recovers `log x` only where `log x > 0`). Quoting
`4 ≤ d(x²) ≤ 8` from `x_sq_not_depth_le_three` and `sqTree_depth` was therefore **not a bracket**: the
floor was proved for a *strictly stronger* specification than the witness meets, and a weaker
specification can only be cheaper. Nothing ruled out a depth-5 tree on `(1,∞)`.

**Why it is nonetheless cheap.** The obstruction was in the statement, not the mathematics — the band
needs only witnesses arbitrarily far to the right, and `x_sq_band_hyps` now certifies that every one
of them can be taken `> 1`.

**The trick that avoids touching the band theorem.** Instantiate it at `f := t.eval` rather than at
`fun x => x * x`. Then the agreement hypothesis is `rfl` — vacuously true on any domain — and the
entire ray restriction moves into the four witness obligations, where `h` can be applied pointwise at
witnesses already known to exceed `1`. The 190-line band theorem is reused unmodified, and its single
prior consumer is unaffected.

**Honest bracket, both domains:**
```
(0,∞):  4 ≤ d(x²) ≤ 24     (x_sq_not_depth_le_three;  mulPos var var)
(1,∞):  4 ≤ d(x²) ≤ 8      (this theorem;             sqTree)
```
The upper bounds still differ by construction quality, not by mathematics: the `(0,∞)` ceiling of 24
is the generic combinator library's, and is not claimed tight. -/
theorem x_sq_ray_not_depth_le_three (t : EMLTree) (ht : t.depth ≤ 3)
    (h : ∀ x : Real, 1 < x → t.eval x = x * x) : False := by
  obtain ⟨H1, H2, H3, Hlog⟩ := x_sq_band_hyps
  refine superlinear_subexp_not_depth_le_three t.eval
    (fun K X => by
      obtain ⟨x, hX, hgt, hv⟩ := H1 K X
      exact ⟨x, hX, le_of_lt hgt, by rw [h x hgt]; exact hv⟩)
    (fun C X => by
      obtain ⟨x, hX, hgt, hv⟩ := H2 C X
      exact ⟨x, hX, le_of_lt hgt, by rw [h x hgt]; exact hv⟩)
    (fun X => by
      obtain ⟨x, hX, hgt, hv⟩ := H3 X
      exact ⟨x, hX, le_of_lt hgt, by rw [h x hgt]; exact hv⟩)
    (fun C X => by
      obtain ⟨x, hX, hgt, hv⟩ := Hlog C X
      exact ⟨x, hX, le_of_lt hgt, by rw [h x hgt]; exact hv⟩)
    t ht (fun x _ => rfl)



/-! ### A candidate invariant beyond growth

`band_exclusion_fails_at_depth_four` refutes the depth-4 band with `x + 1`, and every asymptotic axis
in this file is blind to the difference between `x + 1` and `x²`: both are eventually positive, both
unbounded, both sub-exponential, both above the identity, and both outside the `log x`-shaped hole
that (H3) excludes.

**Excess over the identity separates them.** It is not a growth condition — it compares `f` to `x`
rather than placing `f` on a scale — and it is exactly the axis on which the two differ. -/

/-- `f x − x` is unbounded above on every ray. Strictly stronger than (H3), which asks only
`x < f x` infinitely often. -/
def UnboundedExcess (f : Real → Real) : Prop :=
  ∀ K X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ K < f x - x

/-- Unbounded excess implies (H3). -/
theorem unboundedExcess_implies_above_identity (f : Real → Real) (h : UnboundedExcess f) :
    ∀ X : Real, ∃ x : Real, X ≤ x ∧ 1 ≤ x ∧ x < f x := by
  intro X
  obtain ⟨x, hxX, hx1, hlt⟩ := h 0 X
  refine ⟨x, hxX, hx1, ?_⟩
  have v := add_lt_add_left hlt x
  have e1 : x + (0 : Real) = x := by mach_ring
  have e2 : x + (f x - x) = f x := by mach_mpoly [x, f x]
  rw [e1, e2] at v; exact v

/-- **`x + 1` does *not* have unbounded excess** — its excess is the constant `1`. So the
counterexample that refutes the depth-4 band does **not** refute the strengthened statement. -/
theorem x_add_one_not_unboundedExcess : ¬ UnboundedExcess (fun x => x + 1) := by
  intro h
  obtain ⟨x, _, _, hlt⟩ := h 1 1
  have e : x + 1 - x = (1 : Real) := by mach_mpoly [x]
  rw [e] at hlt
  exact lt_irrefl_ax 1 hlt

/-- **`x²` does have unbounded excess** — `x·x − x = x·(x−1)` grows. -/
theorem x_sq_unboundedExcess : UnboundedExcess (fun x => x * x) := by
  intro K X
  have hKp : (0 : Real) < exp K := exp_pos K
  have hXp : (0 : Real) < exp X := exp_pos X
  refine ⟨1 + 1 + exp K + exp X, ?_, ?_, ?_⟩
  · have v : (0 : Real) + 0 + 0 + exp X ≤ 1 + 1 + exp K + exp X :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt zero_lt_one_ax)) (le_of_lt hKp)) (le_refl _)
    have e : (0 : Real) + 0 + 0 + exp X = exp X := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp X) v
  · have v : (1 : Real) + 0 + 0 + 0 ≤ 1 + 1 + exp K + exp X :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1)
        (le_of_lt zero_lt_one_ax)) (le_of_lt hKp)) (le_of_lt hXp)
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  · -- `x·x − x = x·(x−1) ≥ x·1 = x > K`
    have hx1 : (1 : Real) ≤ 1 + 1 + exp K + exp X := by
      have v : (1 : Real) + 0 + 0 + 0 ≤ 1 + 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1)
          (le_of_lt zero_lt_one_ax)) (le_of_lt hKp)) (le_of_lt hXp)
      have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    have hx0 : (0 : Real) < 1 + 1 + exp K + exp X := lt_of_lt_of_le zero_lt_one_ax hx1
    have hm1 : (1 : Real) ≤ 1 + 1 + exp K + exp X - 1 := by
      have v : (1 : Real) + 1 + 0 + 0 ≤ 1 + 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_refl 1))
          (le_of_lt hKp)) (le_of_lt hXp)
      have u := add_le_add_wit v (le_refl (-1 : Real))
      have e1 : (1 : Real) + 1 + 0 + 0 + -1 = 1 := by mach_ring
      have e2 : (1 : Real) + 1 + exp K + exp X + -1 = 1 + 1 + exp K + exp X - 1 := by mach_ring
      rw [e1, e2] at u; exact u
    have hprod : (1 + 1 + exp K + exp X)
        ≤ (1 + 1 + exp K + exp X) * (1 + 1 + exp K + exp X - 1) := by
      have u := mul_le_mul_of_nonneg_left hm1 (le_of_lt hx0)
      have e : (1 + 1 + exp K + exp X) * (1 : Real) = 1 + 1 + exp K + exp X := by mach_ring
      rw [e] at u; exact u
    have hKx : K < 1 + 1 + exp K + exp X := by
      have hKe : K < exp K := by
        have t1 := one_add_le_exp K
        have e : (1 : Real) + K = K + 1 := by mach_ring
        rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self K) t1
      have v : (0 : Real) + 0 + exp K + 0 ≤ 1 + 1 + exp K + exp X :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
          (le_of_lt zero_lt_one_ax)) (le_refl _)) (le_of_lt hXp)
      have e : (0 : Real) + 0 + exp K + 0 = exp K := by mach_ring
      rw [e] at v; exact lt_of_lt_of_le hKe v
    have e : (1 + 1 + exp K + exp X) * (1 + 1 + exp K + exp X) - (1 + 1 + exp K + exp X)
        = (1 + 1 + exp K + exp X) * (1 + 1 + exp K + exp X - 1) := by
      mach_mpoly [exp K, exp X]
    show K < (1 + 1 + exp K + exp X) * (1 + 1 + exp K + exp X) - (1 + 1 + exp K + exp X)
    rw [e]
    exact lt_of_lt_of_le hKx hprod


/-! ### A function-level normal form at depth 2

`depth_le_one_classification` is stated about a *tree*. Every consumer immediately discards the tree
and works with the five closed forms of its value, and each such consumer re-derives the case split.
Naming the disjunction as a predicate on **functions** makes it composable: a depth-2 argument can
split on `Depth1Form` for each child without mentioning `EMLTree` at all.

This is the first step of an asymptotic classification by depth. It is bookkeeping, deliberately —
the content is that after it, "depth ≤ 2" is a statement about functions. -/

/-- The five closed forms available at depth ≤ 1, as a predicate on functions. -/
def Depth1Form (f : Real → Real) : Prop :=
  (∃ α : Real, ∀ x : Real, 0 < x → f x = α)
  ∨ (∀ x : Real, 0 < x → f x = x)
  ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → f x = c - log x)
  ∨ (∃ d : Real, ∀ x : Real, 0 < x → f x = exp x - d)
  ∨ (∀ x : Real, 0 < x → f x = exp x - log x)

theorem depth_le_one_form (A : EMLTree) (hA : A.depth ≤ 1) : Depth1Form A.eval :=
  depth_le_one_classification A hA

private theorem one_le_one_add_exp (a : Real) : (1 : Real) ≤ 1 + exp a := by
  have h := le_of_lt (exp_pos a)
  have v := add_le_add_left h 1
  have e : (1 : Real) + 0 = 1 := by mach_ring
  rw [e] at v; exact v

/-- Every positive constant dominates `exp (−C − x)` on `x ≥ 0`, for `C = −log g`. -/
private theorem small_exp_below {g : Real} (hg : 0 < g) :
    ∃ C : Real, ∀ x : Real, (0 : Real) ≤ x → exp (-C - x) ≤ g := by
  refine ⟨-log g, ?_⟩
  intro x hx
  have hnx : -x ≤ (0 : Real) := by
    have v := neg_le_neg_wit hx
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at v; exact v
  have hle : -(-log g) - x ≤ log g := by
    have v := add_le_add_left hnx (log g)
    have e1 : log g + -x = -(-log g) - x := by mach_ring
    have e2 : log g + (0 : Real) = log g := by mach_ring
    rw [e1, e2] at v; exact v
  have h2 := exp_monotone hle
  rw [exp_log hg] at h2
  exact h2

/-- **Approach-rate quantisation, base case: a depth-≤1 value cannot approach a constant from above
faster than exponentially.**

For every `k` there are `C` and a ray on which `k < A(x)` forces `A(x) − k ≥ exp(−C − x)`. So no
depth-≤1 expression can hug a constant from above at a super-exponential rate — the grammar has no
shape that decays that fast at this depth.

**Why it is true, form by form**, which is the content and not the bookkeeping:

* `α` — the gap `α − k` is an exact positive constant, or the hypothesis is false;
* `x`, `exp x − d`, `exp x − log x` — these diverge, so the gap exceeds `1` on a far enough ray;
* `c − log x` — this tends to `−∞`, so `k < A(x)` is **false** on a far enough ray.

The list is what makes the statement sharp: the only decaying shape available at depth ≤ 1 is
`c − log x`, and it decays *downwards* through every constant rather than approaching one from above.
Building `exp(−x)`, which would decay to `0` fast enough to break this, needs `−x` as an exponent,
and `−x` is not among the five forms.

This is the formal core of the approach-rate analysis in
`monogate-research/.../APPROACH_RATE_QUANTISATION.md`. Its use is via convexity: since
`exp u − exp v ≥ (u − v) · exp v`, a bound of this shape on the exponent is what turns a decay
obligation like `Depth3DecayHard` into a statement the classification can answer. -/
theorem depth_le_one_approach_constant (A : EMLTree) (hA : A.depth ≤ 1) (k : Real) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → k < A.eval x →
      exp (-C - x) ≤ A.eval x - k := by
  obtain ⟨C1, hC1⟩ := small_exp_below zero_lt_one_ax
  rcases depth_le_one_classification A hA with
      ⟨α, hb⟩ | hb | ⟨c, _, hb⟩ | ⟨d, hb⟩ | hb
  · -- constant `α`: an exact gap, or a false hypothesis
    rcases lt_total k α with hka | hka | hka
    · obtain ⟨C, hC⟩ := small_exp_below (sub_pos_of_lt hka)
      refine ⟨C, 1, le_refl 1, ?_⟩
      intro x hx _
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos]
      exact hC x (le_of_lt hxpos)
    · refine ⟨C1, 1, le_refl 1, ?_⟩
      intro x hx hlt
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos, hka] at hlt
      exact absurd hlt (lt_irrefl_ax α)
    · refine ⟨C1, 1, le_refl 1, ?_⟩
      intro x hx hlt
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos] at hlt
      exact absurd (lt_trans_ax hka hlt) (lt_irrefl_ax α)
  · -- the identity: the gap passes `1`
    refine ⟨C1, 1 + exp k, one_le_one_add_exp k, ?_⟩
    intro x hx _
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp k) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos]
    have hstep : (1 : Real) + k ≤ 1 + exp k := add_le_add_left (self_le_exp k) 1
    have hx2 : (1 : Real) + k ≤ x := le_trans hstep hx
    have h1 : (1 : Real) ≤ x - k := by
      have v := add_le_add_wit hx2 (le_refl (-k))
      have e1 : 1 + k + -k = (1 : Real) := by mach_mpoly [k]
      have e2 : x + -k = x - k := by mach_ring
      rw [e1, e2] at v; exact v
    exact le_trans (hC1 x (le_of_lt hxpos)) h1
  · -- `c − log x` falls below every constant: the hypothesis is eventually false
    refine ⟨C1, 1 + exp (c - k), one_le_one_add_exp (c - k), ?_⟩
    intro x hx hlt
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp (c - k)) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos] at hlt
    have hge : exp (c - k) ≤ x := by
      have h1 : exp (c - k) ≤ 1 + exp (c - k) := by
        have v := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp (c - k)))
        have e1 : (0 : Real) + exp (c - k) = exp (c - k) := by mach_ring
        rw [e1] at v; exact v
      exact le_trans h1 hx
    have hlog : c - k ≤ log x := by
      have h2 := log_le_log (exp_pos (c - k)) hge
      rw [log_exp] at h2; exact h2
    have hle : c - log x ≤ k := by
      have v := add_le_add_wit (le_refl c) (neg_le_neg_wit hlog)
      have e1 : c + -(c - k) = k := by mach_mpoly [c, k]
      have e2 : c + -log x = c - log x := by mach_ring
      rw [e1, e2] at v; exact v
    exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl_ax k)
  · -- `exp x − d` diverges
    refine ⟨C1, 1 + exp (d + k), one_le_one_add_exp (d + k), ?_⟩
    intro x hx _
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp (d + k)) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos]
    have hstep : (1 : Real) + (d + k) ≤ 1 + exp (d + k) :=
      add_le_add_left (self_le_exp (d + k)) 1
    have hx2 : (1 : Real) + (d + k) ≤ x := le_trans hstep hx
    have h3 : (1 : Real) + (d + k) ≤ exp x := le_trans hx2 (self_le_exp x)
    have h1 : (1 : Real) ≤ exp x - d - k := by
      have v := add_le_add_wit h3 (le_refl (-(d + k)))
      have e1 : 1 + (d + k) + -(d + k) = (1 : Real) := by mach_mpoly [d, k]
      have e2 : exp x + -(d + k) = exp x - d - k := by mach_mpoly [exp x, d, k]
      rw [e1, e2] at v; exact v
    exact le_trans (hC1 x (le_of_lt hxpos)) h1
  · -- `exp x − log x` diverges: `exp x ≥ x + x` beats the `log x` it subtracts
    refine ⟨C1, 1 + exp k, one_le_one_add_exp k, ?_⟩
    intro x hx _
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp k) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos]
    have hxx : x ≤ exp x - log x := by
      have v := add_le_add_wit (two_mul_le_exp (le_of_lt hxpos))
        (neg_le_neg_wit (log_le_self_on_ray hx1))
      have e1 : x + x + -x = x := by mach_mpoly [x]
      have e2 : exp x + -log x = exp x - log x := by mach_ring
      rw [e1, e2] at v; exact v
    have hstep : (1 : Real) + k ≤ 1 + exp k := add_le_add_left (self_le_exp k) 1
    have hx3 : (1 : Real) + k ≤ exp x - log x := le_trans (le_trans hstep hx) hxx
    have h1 : (1 : Real) ≤ exp x - log x - k := by
      have v := add_le_add_wit hx3 (le_refl (-k))
      have e1 : 1 + k + -k = (1 : Real) := by mach_mpoly [k]
      have e2 : exp x - log x + -k = exp x - log x - k := by mach_mpoly [exp x, log x, k]
      rw [e1, e2] at v; exact v
    exact le_trans (hC1 x (le_of_lt hxpos)) h1

/-- **Convexity of `exp`, in the form the decay obligations consume**: `exp u − exp v ≥ (u−v)·exp v`.

This is the bridge between a bound on an *exponent* and a bound on a *value*, and it is why the
approach-rate analysis transfers to `Depth3DecayHard` at all: a gap of `exp(−C−x)` in the exponent
survives exponentiation as a gap of `μ·exp(−C−x)` in the value, and the factor is absorbed into the
constant. Proved from `one_add_le_exp` and `exp_add` alone. -/
private theorem exp_sub_exp_lower (u v : Real) : (u - v) * exp v ≤ exp u - exp v := by
  have h1 : (1 : Real) + (u - v) ≤ exp (u - v) := one_add_le_exp (u - v)
  have h2 : exp v * (1 + (u - v)) ≤ exp v * exp (u - v) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos v))
  have h3 : exp v * exp (u - v) = exp u := by
    rw [← exp_add]
    have e : v + (u - v) = u := by mach_ring
    rw [e]
  rw [h3] at h2
  have e2 : exp v * (1 + (u - v)) = exp v + (u - v) * exp v := by mach_mpoly [exp v, u, v]
  rw [e2] at h2
  have v2 := add_le_add_wit h2 (le_refl (-exp v))
  have e3 : exp v + (u - v) * exp v + -exp v = (u - v) * exp v := by mach_mpoly [exp v, u, v]
  have e4 : exp u + -exp v = exp u - exp v := by mach_ring
  rw [e3, e4] at v2
  exact v2

/-- The non-positive-target half: `exp (A x)` is positive, so it clears any `μ ≤ 0` by its own
floor, with no reference to the classification. -/
private theorem exp_approach_nonpos (A : EMLTree) (hA : A.depth ≤ 1) {μ : Real} (hμ : μ ≤ 0) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → μ < exp (A.eval x) →
      exp (-C - x) ≤ exp (A.eval x) - μ := by
  obtain ⟨C, hC⟩ := depth_le_one_lower_on_ray A hA
  refine ⟨C, 1, le_refl 1, ?_⟩
  intro x hx _
  have hlogx : log x ≤ x := log_le_self_on_ray hx
  have h1 : -C - x ≤ -C - log x := by
    have v := add_le_add_left (neg_le_neg_wit hlogx) (-C)
    have e1 : -C + -x = -C - x := by mach_ring
    have e2 : -C + -log x = -C - log x := by mach_ring
    rw [e1, e2] at v; exact v
  have h3 : exp (-C - x) ≤ exp (A.eval x) := exp_monotone (le_trans h1 (hC x hx))
  have h4 : exp (A.eval x) ≤ exp (A.eval x) - μ := by
    have hnn : (0 : Real) ≤ -μ := by
      have v := neg_le_neg_wit hμ
      have e : -(0 : Real) = 0 := by mach_ring
      rw [e] at v; exact v
    have v := add_le_add_left hnn (exp (A.eval x))
    have e1 : exp (A.eval x) + (0 : Real) = exp (A.eval x) := by mach_ring
    have e2 : exp (A.eval x) + -μ = exp (A.eval x) - μ := by mach_ring
    rw [e1, e2] at v; exact v
  exact le_trans h3 h4

/-- **The same quantisation one exponential up**: `exp (A x)` cannot approach a constant `μ` from
above faster than exponentially, for `A` of depth ≤ 1.

The `μ > 0` case is where the convexity step earns its place. `μ < exp (A x)` is `log μ < A x`, so
`depth_le_one_approach_constant` gives an exponent gap `A x − log μ ≥ exp(−C−x)`; convexity turns
that into a value gap `exp (A x) − μ ≥ μ · exp(−C−x)`, and `μ · exp(−C−x) = exp(−(C − log μ) − x)`
absorbs the factor into the constant rather than losing it. For `μ ≤ 0` the classification is not
needed at all — positivity of `exp` does it.

This is the form the depth-2 statement consumes, because an `eml` node's left child enters through
`exp`, not directly. -/
theorem depth_le_one_exp_approach_constant (A : EMLTree) (hA : A.depth ≤ 1) (μ : Real) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → μ < exp (A.eval x) →
      exp (-C - x) ≤ exp (A.eval x) - μ := by
  rcases lt_total 0 μ with hμ | hμ | hμ
  · obtain ⟨C, X₀, hX₀, hC⟩ := depth_le_one_approach_constant A hA (log μ)
    refine ⟨C - log μ, X₀, hX₀, ?_⟩
    intro x hx hlt
    have hlogμ : log μ < A.eval x := by
      have h := log_lt_log hμ hlt
      rw [log_exp] at h
      exact h
    have hmul : exp (-C - x) * μ ≤ (A.eval x - log μ) * μ :=
      mul_le_mul_of_nonneg_right (hC x hx hlogμ) (le_of_lt hμ)
    have hconv : (A.eval x - log μ) * exp (log μ) ≤ exp (A.eval x) - exp (log μ) :=
      exp_sub_exp_lower (A.eval x) (log μ)
    rw [exp_log hμ] at hconv
    have hrew : exp (-(C - log μ) - x) = exp (-C - x) * μ := by
      have e : -(C - log μ) - x = -C - x + log μ := by mach_mpoly [C, x, log μ]
      rw [e, exp_add, exp_log hμ]
    rw [hrew]
    exact le_trans hmul hconv
  · exact exp_approach_nonpos A hA (by rw [← hμ]; exact le_refl 0)
  · exact exp_approach_nonpos A hA (le_of_lt hμ)

private theorem log_ge_of_exp_le {Λ y : Real} (h : exp Λ ≤ y) : Λ ≤ log y := by
  have h2 := log_le_log (exp_pos Λ) h
  rw [log_exp] at h2; exact h2

/-- If the left child is capped at `K` and the right child's log has reached `K − k`, the node has
fallen to `k`. This is the shape of every vacuous cell below. -/
private theorem sub_le_of_bounds {a b K k : Real} (hK : a ≤ K) (hbig : K - k ≤ b) : a - b ≤ k := by
  have v := add_le_add_wit hK (neg_le_neg_wit hbig)
  have e1 : a + -b = a - b := by mach_ring
  have e2 : K + -(K - k) = k := by mach_mpoly [K, k]
  rw [e1, e2] at v; exact v

private theorem self_le_exp_sub_log {x : Real} (hx : 1 ≤ x) : x ≤ exp x - log x := by
  have v := add_le_add_wit (two_mul_le_exp (le_trans (le_of_lt zero_lt_one_ax) hx))
    (neg_le_neg_wit (log_le_self_on_ray hx))
  have e1 : x + x + -x = x := by mach_mpoly [x]
  have e2 : exp x + -log x = exp x - log x := by mach_ring
  rw [e1, e2] at v; exact v

private theorem exp_le_one_add_exp (a : Real) : exp a ≤ 1 + exp a := by
  have v := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (exp a))
  have e : (0 : Real) + exp a = exp a := by mach_ring
  rw [e] at v; exact v

private theorem one_le_ray (a b : Real) : (1 : Real) ≤ 1 + exp a + exp b := by
  have h2 : (1 : Real) + exp a ≤ 1 + exp a + exp b := by
    have v := add_le_add_left (le_of_lt (exp_pos b)) (1 + exp a)
    have e : 1 + exp a + (0 : Real) = 1 + exp a := by mach_ring
    rw [e] at v; exact v
  exact le_trans (one_le_one_add_exp a) h2

private theorem fst_le_ray (a b : Real) : a ≤ 1 + exp a + exp b := by
  have h3 : (1 : Real) + exp a ≤ 1 + exp a + exp b := by
    have v := add_le_add_left (le_of_lt (exp_pos b)) (1 + exp a)
    have e : 1 + exp a + (0 : Real) = 1 + exp a := by mach_ring
    rw [e] at v; exact v
  exact le_trans (self_le_exp a) (le_trans (exp_le_one_add_exp a) h3)

private theorem one_add_snd_le_ray (a b : Real) : 1 + b ≤ 1 + exp a + exp b := by
  have h2 : (1 : Real) + exp b ≤ 1 + exp a + exp b := by
    have v := add_le_add_wit (add_le_add_left (le_of_lt (exp_pos a)) (1 : Real)) (le_refl (exp b))
    have e : (1 : Real) + 0 + exp b = 1 + exp b := by mach_ring
    rw [e] at v; exact v
  exact le_trans (add_le_add_left (self_le_exp b) 1) h2

/-- **Approach-rate quantisation at depth ≤ 2.**

Same statement as `depth_le_one_approach_constant` one level up: no depth-≤2 expression approaches a
constant from above faster than exponentially.

**The proof is not twenty-five cells.** The left child splits once, on
`depth_le_one_exp_bounded_or_grows`, and the two halves are answered by different machinery:

* *growing left child* — `exp x ≤ exp (A x)` while the right child's log is capped linearly by
  `depth_le_one_log_le_linear`, so the node exceeds `exp x − x − D ≥ x − D`, which passes `k + 1`.
  **The right child is never enumerated on this branch**;
* *bounded left child* — now the right child decides, and its five forms split three-and-two. For
  `x`, `exp x − d` and `exp x − log x` the log diverges past `K − k` and the hypothesis `k < node`
  becomes **false**: these cells are vacuous, not hard. For the two remaining forms the log is
  eventually an exact constant — `log β`, or `0` via `log_nonpos` once `c − log x` turns negative —
  so the node is `exp (A x)` against a shifted target and `depth_le_one_exp_approach_constant`
  applies.

The totalisation earns its keep in the `c − log x` cell: the log is not merely *small* there, it is
identically `0` on a ray, so the node is exactly `exp (A x)` rather than a perturbation of it. -/
theorem depth_le_two_approach_constant (t : EMLTree) (ht : t.depth ≤ 2) (k : Real) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → k < t.eval x →
      exp (-C - x) ≤ t.eval x - k := by
  cases t with
  | const c => exact depth_le_one_approach_constant (EMLTree.const c) (by simp [EMLTree.depth]) k
  | var => exact depth_le_one_approach_constant EMLTree.var (by simp [EMLTree.depth]) k
  | eml A B =>
    have hA : A.depth ≤ 1 := by
      simp only [EMLTree.depth] at ht
      have := Nat.le_max_left A.depth B.depth; omega
    have hB : B.depth ≤ 1 := by
      simp only [EMLTree.depth] at ht
      have := Nat.le_max_right A.depth B.depth; omega
    obtain ⟨C1, hC1⟩ := small_exp_below zero_lt_one_ax
    rcases depth_le_one_exp_bounded_or_grows A hA with ⟨K, hK⟩ | ⟨T, hT⟩
    · rcases depth_le_one_form B hB with ⟨β, hb⟩ | hb | ⟨c', _, hb⟩ | ⟨d, hb⟩ | hb
      · -- right child a constant: an exact shift of the target
        obtain ⟨C, X₀, hX₀, hC⟩ := depth_le_one_exp_approach_constant A hA (k + log β)
        refine ⟨C, X₀, hX₀, ?_⟩
        intro x hx hlt
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX₀ hx)
        have hlt' : k < exp (A.eval x) - log (B.eval x) := hlt
        rw [hb x hxpos] at hlt'
        have hgt : k + log β < exp (A.eval x) := by
          have v := add_lt_add_left hlt' (log β)
          have e1 : log β + k = k + log β := by mach_ring
          have e2 : log β + (exp (A.eval x) - log β) = exp (A.eval x) := by
            mach_mpoly [log β, exp (A.eval x)]
          rw [e1, e2] at v; exact v
        show exp (-C - x) ≤ exp (A.eval x) - log (B.eval x) - k
        rw [hb x hxpos]
        have e3 : exp (A.eval x) - (k + log β) = exp (A.eval x) - log β - k := by
          mach_mpoly [exp (A.eval x), k, log β]
        rw [← e3]
        exact hC x hx hgt
      · -- right child the identity: `log x` diverges, the hypothesis dies
        refine ⟨C1, 1 + exp (K - k), one_le_one_add_exp _, ?_⟩
        intro x hx hlt
        have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp _) hx
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        have hlt' : k < exp (A.eval x) - log (B.eval x) := hlt
        rw [hb x hxpos] at hlt'
        have hbig : K - k ≤ log x :=
          log_ge_of_exp_le (le_trans (exp_le_one_add_exp (K - k)) hx)
        exact absurd (lt_of_lt_of_le hlt' (sub_le_of_bounds (hK x hx1) hbig)) (lt_irrefl_ax k)
      · -- right child `c − log x`: the log is identically `0` on a ray, node is exactly `exp (A x)`
        obtain ⟨C, X₁, hX₁, hC⟩ := depth_le_one_exp_approach_constant A hA k
        refine ⟨C, X₁ + exp c', ?_, ?_⟩
        · exact le_trans hX₁ (le_add_nonneg_r' (le_of_lt (exp_pos c')))
        · intro x hx hlt
          have hX₁x : X₁ ≤ x := le_trans (le_add_nonneg_r' (le_of_lt (exp_pos c'))) hx
          have hx1 : (1 : Real) ≤ x := le_trans hX₁ hX₁x
          have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
          have hcx : exp c' ≤ x := by
            have v := add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hX₁) (le_refl (exp c'))
            have e : (0 : Real) + exp c' = exp c' := by mach_ring
            rw [e] at v; exact le_trans v hx
          have hzero : log (B.eval x) = 0 := by
            rw [hb x hxpos]
            refine log_nonpos ?_
            have hge : c' ≤ log x := log_ge_of_exp_le hcx
            have v := add_le_add_wit (le_refl c') (neg_le_neg_wit hge)
            have e1 : c' + -log x = c' - log x := by mach_ring
            have e2 : c' + -c' = (0 : Real) := by mach_mpoly [c']
            rw [e1, e2] at v; exact v
          have hlt' : k < exp (A.eval x) - log (B.eval x) := hlt
          rw [hzero] at hlt'
          have hgt : k < exp (A.eval x) := by
            have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
            rw [e] at hlt'; exact hlt'
          show exp (-C - x) ≤ exp (A.eval x) - log (B.eval x) - k
          rw [hzero]
          have e : exp (A.eval x) - (0 : Real) - k = exp (A.eval x) - k := by mach_ring
          rw [e]
          exact hC x hX₁x hgt
      · -- right child `exp x − d`: the log diverges
        refine ⟨C1, 1 + exp (K - k) + exp d, one_le_ray _ _, ?_⟩
        intro x hx hlt
        have hx1 : (1 : Real) ≤ x := le_trans (one_le_ray _ _) hx
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        have hlt' : k < exp (A.eval x) - log (B.eval x) := hlt
        rw [hb x hxpos] at hlt'
        have hreach : exp (K - k) + d ≤ x := by
          have v := add_le_add_wit (le_refl (exp (K - k))) (self_le_exp d)
          have w : exp (K - k) + exp d ≤ 1 + exp (K - k) + exp d := by
            have u := add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
              (le_refl (exp (K - k)))) (le_refl (exp d))
            have e : (0 : Real) + exp (K - k) + exp d = exp (K - k) + exp d := by mach_ring
            rw [e] at u; exact u
          exact le_trans (le_trans v w) hx
        have hbig : K - k ≤ log (exp x - d) := by
          refine log_ge_of_exp_le ?_
          have hxe : exp (K - k) + d ≤ exp x := le_trans hreach (self_le_exp x)
          have v := add_le_add_wit hxe (le_refl (-d))
          have e1 : exp (K - k) + d + -d = exp (K - k) := by mach_mpoly [exp (K - k), d]
          have e2 : exp x + -d = exp x - d := by mach_ring
          rw [e1, e2] at v; exact v
        exact absurd (lt_of_lt_of_le hlt' (sub_le_of_bounds (hK x hx1) hbig)) (lt_irrefl_ax k)
      · -- right child `exp x − log x`: the log diverges
        refine ⟨C1, 1 + exp (K - k), one_le_one_add_exp _, ?_⟩
        intro x hx hlt
        have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp _) hx
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        have hlt' : k < exp (A.eval x) - log (B.eval x) := hlt
        rw [hb x hxpos] at hlt'
        have hbig : K - k ≤ log (exp x - log x) :=
          log_ge_of_exp_le (le_trans (le_trans (exp_le_one_add_exp (K - k)) hx)
            (self_le_exp_sub_log hx1))
        exact absurd (lt_of_lt_of_le hlt' (sub_le_of_bounds (hK x hx1) hbig)) (lt_irrefl_ax k)
    · -- growing left child: the linear log ceiling cannot keep up, whatever the right child is
      obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B hB
      refine ⟨C1, 1 + exp T + exp (D + k), one_le_ray _ _, ?_⟩
      intro x hx _
      have hx1 : (1 : Real) ≤ x := le_trans (one_le_ray _ _) hx
      have hxT : T ≤ x := le_trans (fst_le_ray _ _) hx
      have hxDk : (1 : Real) + (D + k) ≤ x := le_trans (one_add_snd_le_ray _ _) hx
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hnode : exp x - (x + D) ≤ exp (A.eval x) - log (B.eval x) := by
        have v := add_le_add_wit (hT x hxT) (neg_le_neg_wit (hD x hx1))
        have e1 : exp x + -(x + D) = exp x - (x + D) := by mach_ring
        have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
        rw [e1, e2] at v; exact v
      have hxD : x - D ≤ exp x - (x + D) := by
        have v := add_le_add_wit (two_mul_le_exp (le_of_lt hxpos)) (le_refl (-(x + D)))
        have e1 : x + x + -(x + D) = x - D := by mach_mpoly [x, D]
        have e2 : exp x + -(x + D) = exp x - (x + D) := by mach_ring
        rw [e1, e2] at v; exact v
      have hone : (1 : Real) + k ≤ x - D := by
        have v := add_le_add_wit hxDk (le_refl (-D))
        have e1 : 1 + (D + k) + -D = 1 + k := by mach_mpoly [D, k]
        have e2 : x + -D = x - D := by mach_ring
        rw [e1, e2] at v; exact v
      have hfin : (1 : Real) + k ≤ exp (A.eval x) - log (B.eval x) :=
        le_trans hone (le_trans hxD hnode)
      show exp (-C1 - x) ≤ exp (A.eval x) - log (B.eval x) - k
      have hgap : (1 : Real) ≤ exp (A.eval x) - log (B.eval x) - k := by
        have v := add_le_add_wit hfin (le_refl (-k))
        have e1 : 1 + k + -k = (1 : Real) := by mach_mpoly [k]
        have e2 : exp (A.eval x) - log (B.eval x) + -k
            = exp (A.eval x) - log (B.eval x) - k := by mach_ring
        rw [e1, e2] at v; exact v
      exact le_trans (hC1 x (le_of_lt hxpos)) hgap

/-- **Normal form at depth ≤ 2.** Constant, the identity, or `exp a − log b` with both `a` and `b`
in the depth-1 form list. No tree appears in the third disjunct. -/
theorem depth_le_two_normal_form (t : EMLTree) (ht : t.depth ≤ 2) :
    (∃ c : Real, ∀ x : Real, 0 < x → t.eval x = c)
    ∨ (∀ x : Real, 0 < x → t.eval x = x)
    ∨ (∃ a b : Real → Real, Depth1Form a ∧ Depth1Form b ∧
        ∀ x : Real, 0 < x → t.eval x = exp (a x) - log (b x)) := by
  cases t with
  | const c => exact Or.inl ⟨c, fun x _ => rfl⟩
  | var => exact Or.inr (Or.inl (fun x _ => rfl))
  | eml A B =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth; omega
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      exact Or.inr (Or.inr ⟨A.eval, B.eval, depth_le_one_form A hA, depth_le_one_form B hB,
        fun x _ => rfl⟩)


/-- **Depth-≤2 lower envelope: `t(x) ≥ −C − x` on a ray.**

The depth-1 companion is `depth_le_one_lower_on_ray`, where the floor is `−C − log x`. One level of
nesting degrades it from logarithmic to **linear**, and no more than that, because an `eml` node's
value is bounded below by `−Log(B x)` alone — `exp` contributes nothing negative — and the depth-1
log ceiling is linear.

**This is what `V₃` needs, and it is why the 5 × 5 asymptotic type list is not needed for it.** The
decay bound at depth `j` comes from the lower envelope at depth `j−1`: `V₂`'s `−log t ≤ C + log x`
traces back to the depth-1 floor `−C − log x`, so the depth-2 floor `−C − x` should give
`−log t ≤ C + x` at depth 3 — logarithmic, then linear, one level apart. -/
theorem depth_le_two_lower_on_ray (t : EMLTree) (ht : t.depth ≤ 2) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → -C - x ≤ t.eval x := by
  cases t with
  | const c =>
      refine ⟨exp (-c), ?_⟩
      intro x hx
      show -exp (-c) - x ≤ c
      have h1 : -c ≤ exp (-c) := self_le_exp _
      have h2 : -exp (-c) ≤ c := by
        have v := neg_le_neg_wit h1
        have e : -(-c) = c := by mach_ring
        rw [e] at v; exact v
      have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx
      have hnx : -x ≤ 0 := by
        have v := neg_le_neg_wit hx0
        have e : -(0 : Real) = 0 := by mach_ring
        rw [e] at v; exact v
      have h3 : -exp (-c) - x ≤ -exp (-c) := by
        have v := add_le_add_left hnx (-exp (-c))
        have e1 : -exp (-c) + -x = -exp (-c) - x := by mach_ring
        have e2 : -exp (-c) + (0 : Real) = -exp (-c) := by mach_ring
        rw [e1, e2] at v; exact v
      exact le_trans h3 h2
  | var =>
      refine ⟨1, ?_⟩
      intro x hx
      show -(1 : Real) - x ≤ x
      have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx
      have h1 : (0 : Real) ≤ 1 + x :=
        le_of_lt (add_pos_of_nonneg_pos (le_of_lt zero_lt_one_ax)
          (lt_of_lt_of_le zero_lt_one_ax hx))
      have hneg : -(1 : Real) - x ≤ 0 := by
        have v := neg_le_neg_wit h1
        have e1 : -((1 : Real) + x) = -1 - x := by mach_ring
        have e2 : -(0 : Real) = 0 := by mach_ring
        rw [e1, e2] at v; exact v
      exact le_trans hneg hx0
  | eml A B =>
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth; omega
      obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B hB
      refine ⟨D, ?_⟩
      intro x hx
      show -D - x ≤ exp (A.eval x) - log (B.eval x)
      -- `exp (A x) > 0` and `log (B x) ≤ x + D`
      have v := add_le_add_wit (le_of_lt (exp_pos (A.eval x))) (neg_le_neg_wit (hD x hx))
      have e1 : (0 : Real) + -(x + D) = -D - x := by mach_mpoly [x, D]
      have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
      rw [e1, e2] at v; exact v


/-! ### `V₃`, easy branch — and why the pattern is a conjecture, not a consequence

The previous section suggested `V₁ ~ constant`, `V₂ ~ log x`, `V₃ ~ x`, each inherited from the floor
one level below. **That reasoning is valid only on the branch where the right child contributes
nothing**, and it is worth being exact about where it stops.

At depth 2, `V₂` closed because the right child ranges over *five closed forms*, and the branches
where `log (B x) > 0` were each shown vacuous on a far enough ray. At depth 3 the right child ranges
over depth-2 expressions, whose logarithm can reach `exp x + K` — so `exp (A x) − log (B x)` can in
principle be made small by **near-cancellation**, and no floor on `A` alone bounds it.

So the easy branch below is a theorem; the pattern as a whole is not. -/

/-- **`V₃` on the branch where the right child's log is non-positive.** The node is then at least
`exp (A x)`, and the depth-2 floor `A x ≥ −C − x` gives a **linear** decay bound — one level worse
than `V₂`'s logarithmic one, exactly as the floors degrade. -/
theorem depth_le_three_decay_log_nonpos (A B : EMLTree) (hA : A.depth ≤ 2) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ 0 →
      -log (exp (A.eval x) - log (B.eval x)) ≤ C + x := by
  obtain ⟨C, hC⟩ := depth_le_two_lower_on_ray A hA
  refine ⟨C, ?_⟩
  intro x hx hB
  -- the node dominates `exp (A x) ≥ exp (−C − x)`
  have hexp : exp (-C - x) ≤ exp (A.eval x) := exp_monotone (hC x hx)
  have hnn : (0 : Real) ≤ -log (B.eval x) := by
    have t := neg_le_neg_wit hB
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at t; exact t
  have hnode : exp (A.eval x) ≤ exp (A.eval x) - log (B.eval x) := by
    have v := add_le_add_left hnn (exp (A.eval x))
    have e1 : exp (A.eval x) + (0 : Real) = exp (A.eval x) := by mach_ring
    have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
    rw [e1, e2] at v; exact v
  have hlow : exp (-C - x) ≤ exp (A.eval x) - log (B.eval x) := le_trans hexp hnode
  -- take logs
  have hmono : log (exp (-C - x)) ≤ log (exp (A.eval x) - log (B.eval x)) :=
    log_le_log (exp_pos _) hlow
  rw [log_exp] at hmono
  have t := neg_le_neg_wit hmono
  have e : -(-C - x) = C + x := by mach_ring
  rw [e] at t; exact t

/-- **The witness that refutes `Depth3DecayHard`.** `eml (eml var (const 0)) var`, of depth 2,
evaluating to `exp (exp x) − log x`. The totalisation builds it: `log 0 = 0`, so `eml var (const 0)`
is exactly `exp x`, and one more node raises it to `exp (exp x)`. -/
noncomputable def dep3CounterRight : EMLTree := EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 0)) EMLTree.var

theorem dep3CounterRight_depth : dep3CounterRight.depth = 2 := rfl

theorem dep3CounterRight_eval (x : Real) :
    dep3CounterRight.eval x = exp (exp x) - log x := by
  show exp (exp x - log ((0 : Real))) - log x = exp (exp x) - log x
  rw [log_nonpos (le_refl (0 : Real))]
  have e : exp x - (0 : Real) = exp x := by mach_ring
  rw [e]

/-- **The corrected obligation.** `Depth3DecayHard` is false with the rung `C + x`; the counterexample
of §`dep3CounterRight` forces `exp x`. This is the statement that might be true.

The rung climbs one exponential per level: `V₂` is `C + log x`, and depth 3 needs `C + exp x`, not the
`C + x` that reading the progression `log x → x` off two data points suggested. -/
def Depth3DecayExp : Prop :=
  ∀ A B : EMLTree, A.depth ≤ 2 → B.depth ≤ 2 →
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (B.eval x) →
      0 < exp (A.eval x) - log (B.eval x) →
      -log (exp (A.eval x) - log (B.eval x)) ≤ C + exp x

/-- **REFUTED — this proposition is false; see below.** (It was named as the open depth-3 decay branch,
and the framing that follows is preserved because the reasoning that led here is what found the
counterexample.) At depth 3 the right child's logarithm can reach the exponential
scale, so `exp (A x) − log (B x)` may be small by cancellation rather than by `A` being small. This
is the depth-3 analogue of what the five closed forms disposed of at depth 2.

Named rather than assumed, as `SignHardCase` and `VarLeftEmlRightHard` were.

**Re-scoped 2026-08-14, and the earlier text was wrong.** This docstring used to end "and there is no
classification of depth-2 expressions to dispose of it here". There is: `depth_le_two_normal_form`,
added after this obligation was named, and never re-read against it. What the classification buys:

*The convergent regime is understood.* Where the node tends to a finite limit, convexity turns the
decay bound into a question about **approach rates** — `exp u − exp v ≥ (u − v) exp v` reduces
`−log(exp u − k) ≤ C + x` to "`u` does not approach `log k` from above faster than exponentially".
Enumerating the five forms shows a depth-≤2 value approaches a finite limit **either exactly or at
rate `Θ(1/x)`, never faster**: the only decaying shape available is `exp (c − log x) = e^c/x`, and
the totalised `Log` contributes an exact `0` rather than something tending to `0`. Both bounds are
comfortably weaker than `exp (−C − x)`. Constant-tuning moves the limit, not the rate.

*What is genuinely left* is the divergent regime: `u → ∞` with `log (B x)` tracking `exp u` from
below, both at the exponential scale by `U₂`. That is a cancellation between two exponential-scale
quantities — the same phenomenon `SignHardCase` meets one derivative up (sign there, magnitude
here); neither implies the other.

**REFUTED 2026-08-15. This proposition is FALSE as stated, and the decomposition is what found it.**
Take `A = var` and `B = dep3CounterRight`, i.e. `B x = exp (exp x) − log x`, both within the depth
bounds. Then

```
node = exp x − log (exp (exp x) − log x) = −log (1 − log x / exp (exp x)) ≈ log x · exp (−exp x)
```

which is **positive** (so the hypotheses hold: `log (B x) > 0` and `node > 0`) and
**super-exponentially small**, giving `−log node ≈ exp x − log log x`. No constant `C` satisfies
`−log node ≤ C + x`: the excess `−log node − x` is `5.8, 17.0, 50.3, 142.9, 396.8, 1089.0, 2972.2`
at `x = 2 … 8`, matching `exp x − log log x` to every digit computed.

The rung is what was wrong. `V₂` reads `C + log x`; reading the progression `log x → x` off two
levels gave `C + x`, but each level costs a whole exponential, so depth 3 needs `C + exp x`. The
corrected statement is `Depth3DecayExp` above. `depth_three_decay_growing_left` and
`depth_three_decay_const_left` are unaffected — they prove the *stronger* `C + x` bound on their own
cells, and remain true.

Worth stating plainly: the four-cell decomposition was built to locate the difficulty, and the cell
it isolated as hardest — `P = var`, the sole occupant of the single-exponential rung — is exactly
where the statement fails. **The refutation is machine-checked**: `not_depth3DecayHard`, with no
numerics in the proof — the witness (`dep3CounterRight_depth`, `dep3CounterRight_eval`) *and* the
asymptotics. The corrected statement is `Depth3DecayExp`, and all four cells are now proved (`depth3DecayExp_holds`).

See `monogate-research/exploration/eml_depth_induction_2026_08_13/APPROACH_RATE_QUANTISATION.md`. -/
def Depth3DecayHard : Prop :=
  ∀ A B : EMLTree, A.depth ≤ 2 → B.depth ≤ 2 →
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (B.eval x) →
      0 < exp (A.eval x) - log (B.eval x) →
      -log (exp (A.eval x) - log (B.eval x)) ≤ C + x




private theorem le_add_nonneg_l' {a b : Real} (ha : 0 ≤ a) : b ≤ a + b := by
  have v := add_le_add_wit ha (le_refl b)
  have e : (0 : Real) + b = b := by mach_ring
  rw [e] at v; exact v

/-- **The growing cell of the depth-3 decay decomposition: an exponential of headroom.**

If the left child `P` is a depth-≤2 expression that grows — `P x ≥ exp x − x − C`, the only
alternative to being bounded above by `depth_two_eml_value_gap` — then `exp (P x)` is *doubly*
exponential, while `depth_le_two_log_le_exp` caps `log (Q x)` at `exp x + K`, which is only *singly*
exponential. The node does not merely stay positive; it passes `1`.

**No cancellation is available in this cell, and the right child is never inspected** beyond its
depth. That is the point: this branch was being counted with the hard ones on the grounds that both
terms sit "at the exponential scale", and they do not — they are a whole exponential apart. What
remains genuinely hard is the left child being `var` (`exp x` exactly, the single-exponential rung,
which `depth_two_eml_value_gap` shows no `eml` node can occupy) or both children bounded. -/
theorem depth_three_growing_left_node_ge_one (P Q : EMLTree) (hQ : Q.depth ≤ 2) (C T : Real)
    (hP : ∀ x : Real, T ≤ x → exp x - x - C ≤ P.eval x) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 ≤ exp (P.eval x) - log (Q.eval x) := by
  obtain ⟨K, XQ, hXQ1, hQb⟩ := depth_le_two_log_le_exp Q hQ
  obtain ⟨T1, hT1⟩ := two_mul_add_le_exp C
  obtain ⟨T2, hT2⟩ := two_mul_add_le_exp (C + C + K + 1)
  have hXQ0 : (0 : Real) ≤ XQ := le_trans (le_of_lt zero_lt_one_ax) hXQ1
  have hp1 : (0 : Real) ≤ XQ + exp T := le_trans hXQ0 (le_add_nonneg_r' (le_of_lt (exp_pos T)))
  have hp2 : (0 : Real) ≤ XQ + exp T + exp T1 :=
    le_trans hp1 (le_add_nonneg_r' (le_of_lt (exp_pos T1)))
  refine ⟨XQ + exp T + exp T1 + exp T2, ?_, ?_⟩
  · exact le_trans hXQ1 (le_trans (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos T)))
      (le_add_nonneg_r' (le_of_lt (exp_pos T1)))) (le_add_nonneg_r' (le_of_lt (exp_pos T2))))
  · intro x hx
    have hXQx : XQ ≤ x := le_trans (le_trans (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos T)))
      (le_add_nonneg_r' (le_of_lt (exp_pos T1)))) (le_add_nonneg_r' (le_of_lt (exp_pos T2)))) hx
    have hTx : T ≤ x := le_trans (self_le_exp T) (le_trans (le_trans (le_add_nonneg_l' hXQ0)
      (le_add_nonneg_r' (le_of_lt (exp_pos T1)))) (le_trans (le_add_nonneg_r'
        (le_of_lt (exp_pos T2))) hx))
    have hT1x : T1 ≤ x := le_trans (self_le_exp T1) (le_trans (le_add_nonneg_l' hp1)
      (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos T2))) hx))
    have hT2x : T2 ≤ x := le_trans (self_le_exp T2) (le_trans (le_add_nonneg_l' hp2) hx)
    have hx1 : (1 : Real) ≤ x := le_trans hXQ1 hXQx
    have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
    -- the exponent is at least `x`, hence non-negative
    have hux : x ≤ exp x - x - C := by
      have v := add_le_add_wit (hT1 x hT1x) (le_refl (-x + -C))
      have e1 : x + x + C + (-x + -C) = x := by mach_mpoly [x, C]
      have e2 : exp x + (-x + -C) = exp x - x - C := by mach_mpoly [exp x, x, C]
      rw [e1, e2] at v; exact v
    have hu : exp x - x - C ≤ P.eval x := hP x hTx
    have hu0 : (0 : Real) ≤ P.eval x := le_trans hx0 (le_trans hux hu)
    -- double it: `exp u ≥ u + u`
    have hdouble : P.eval x + P.eval x ≤ exp (P.eval x) := two_mul_le_exp hu0
    have hsum : exp x - x - C + (exp x - x - C) ≤ P.eval x + P.eval x := add_le_add_wit hu hu
    have hlow : exp x - x - C + (exp x - x - C) ≤ exp (P.eval x) := le_trans hsum hdouble
    -- and the right child's log is only singly exponential
    have hnode : exp x - x - C + (exp x - x - C) - (exp x + K)
        ≤ exp (P.eval x) - log (Q.eval x) := by
      have v := add_le_add_wit hlow (neg_le_neg_wit (hQb x hXQx))
      have e1 : exp x - x - C + (exp x - x - C) + -(exp x + K)
          = exp x - x - C + (exp x - x - C) - (exp x + K) := by mach_ring
      have e2 : exp (P.eval x) + -log (Q.eval x) = exp (P.eval x) - log (Q.eval x) := by mach_ring
      rw [e1, e2] at v; exact v
    have hone : (1 : Real) ≤ exp x - x - C + (exp x - x - C) - (exp x + K) := by
      have v := add_le_add_wit (hT2 x hT2x) (le_refl (-x - x - C - C - K))
      have e1 : x + x + (C + C + K + 1) + (-x - x - C - C - K) = (1 : Real) := by
        mach_mpoly [x, C, K]
      have e2 : exp x + (-x - x - C - C - K)
          = exp x - x - C + (exp x - x - C) - (exp x + K) := by mach_mpoly [exp x, x, C, K]
      rw [e1, e2] at v; exact v
    exact le_trans hone hnode

/-- The same cell in the shape `Depth3DecayHard` wants: the node's `−log` is bounded by `C' + x`,
with `C' = 0`, because the node has already passed `1`. -/
theorem depth_three_decay_growing_left (P Q : EMLTree) (hQ : Q.depth ≤ 2) (C T : Real)
    (hP : ∀ x : Real, T ≤ x → exp x - x - C ≤ P.eval x) :
    ∃ C' X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      -log (exp (P.eval x) - log (Q.eval x)) ≤ C' + x := by
  obtain ⟨X₀, hX₀, hnode⟩ := depth_three_growing_left_node_ge_one P Q hQ C T hP
  refine ⟨0, X₀, hX₀, ?_⟩
  intro x hx
  have hlog1 : log (1 : Real) = 0 := by
    have hz : exp (0 : Real) = 1 := exp_zero
    rw [← hz, log_exp]
  have hge : (0 : Real) ≤ log (exp (P.eval x) - log (Q.eval x)) := by
    have h := log_le_log zero_lt_one_ax (hnode x hx)
    rw [hlog1] at h; exact h
  have hneg : -log (exp (P.eval x) - log (Q.eval x)) ≤ 0 := by
    have v := neg_le_neg_wit hge
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at v; exact v
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) (le_trans hX₀ hx)
  have hz : (0 : Real) ≤ 0 + x := by
    have v := add_le_add_left hx0 (0 : Real)
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at v; exact v
  exact le_trans hneg hz


/-- **Approach from below is strictly easier — and the asymmetry is structural.**

`depth_le_one_approach_constant` bounds the gap below by `exp (−C − x)`, and that is the best it can
do: the form `c − log x` contributes `exp (c − log x) = e^c/x`, so a value can sit `Θ(1/x)` above a
constant. From *below* there is no such shape, and the gap is bounded by a **positive constant**:

* `α` — an exact constant gap, or the hypothesis is false;
* `c − log x` — the gap is `k − c + log x`, which *grows*;
* `x`, `exp x − d`, `exp x − log x` — all eventually exceed `k`, so the hypothesis is **false**.

The asymmetry has one cause. The only decaying shape the grammar offers at this depth is `e^c/x`,
and it is **positive**, so it can only push a value *above* its limit, never let one creep up on a
constant from underneath. That is why this statement is stronger than its mirror rather than
symmetric with it, and it is what makes the `P = const` cell of the depth-3 decomposition tractable:
a constant gap survives multiplication by `exp (A x) ≥ exp (−C − x)` without the `x` in the exponent
doubling. -/
theorem depth_le_one_gap_below (A : EMLTree) (hA : A.depth ≤ 1) (k : Real) :
    ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → A.eval x < k → ε ≤ k - A.eval x := by
  rcases depth_le_one_classification A hA with ⟨α, hb⟩ | hb | ⟨c, _, hb⟩ | ⟨d, hb⟩ | hb
  · rcases lt_total α k with hαk | hαk | hαk
    · refine ⟨k - α, 1, sub_pos_of_lt hαk, le_refl 1, ?_⟩
      intro x hx _
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos]
      exact le_refl _
    · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
      intro x hx hlt
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos, hαk] at hlt
      exact absurd hlt (lt_irrefl_ax k)
    · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
      intro x hx hlt
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos] at hlt
      exact absurd (lt_trans_ax hlt hαk) (lt_irrefl_ax α)
  · -- the identity outruns `k`
    refine ⟨1, 1 + exp k, zero_lt_one_ax, one_le_one_add_exp k, ?_⟩
    intro x hx hlt
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans (one_le_one_add_exp k) hx)
    rw [hb x hxpos] at hlt
    have hk : k < x := by
      have h1 : k ≤ exp k := self_le_exp k
      have h2 : exp k < 1 + exp k := by
        have v := add_lt_add_left zero_lt_one_ax (exp k)
        have e1 : exp k + (0 : Real) = exp k := by mach_ring
        have e2 : exp k + 1 = 1 + exp k := by mach_ring
        rw [e1, e2] at v; exact v
      exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) hx
    exact absurd (lt_trans_ax hlt hk) (lt_irrefl_ax x)
  · -- `c − log x` falls away, so the gap grows
    refine ⟨1, 1 + exp (1 - k + c), zero_lt_one_ax, one_le_one_add_exp _, ?_⟩
    intro x hx _
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp _) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos]
    have hreach : exp (1 - k + c) ≤ x := le_trans (exp_le_one_add_exp _) hx
    have hlog : 1 - k + c ≤ log x := log_ge_of_exp_le hreach
    have v := add_le_add_wit hlog (le_refl (k - c))
    have e1 : 1 - k + c + (k - c) = (1 : Real) := by mach_mpoly [k, c]
    have e2 : log x + (k - c) = k - (c - log x) := by mach_mpoly [log x, k, c]
    rw [e1, e2] at v; exact v
  · -- `exp x − d` outruns `k`
    refine ⟨1, 1 + exp (k + d), zero_lt_one_ax, one_le_one_add_exp _, ?_⟩
    intro x hx hlt
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp _) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos] at hlt
    have hkd : k + d ≤ exp x := by
      have h1 : k + d ≤ exp (k + d) := self_le_exp (k + d)
      exact le_trans (le_trans h1 (le_trans (exp_le_one_add_exp _) hx)) (self_le_exp x)
    have hge : k ≤ exp x - d := by
      have v := add_le_add_wit hkd (le_refl (-d))
      have e1 : k + d + -d = k := by mach_mpoly [k, d]
      have e2 : exp x + -d = exp x - d := by mach_ring
      rw [e1, e2] at v; exact v
    exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl_ax k)
  · -- `exp x − log x` outruns `k`, since it dominates `x`
    refine ⟨1, 1 + exp k, zero_lt_one_ax, one_le_one_add_exp k, ?_⟩
    intro x hx hlt
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp k) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos] at hlt
    have hk : k ≤ x := le_trans (self_le_exp k) (le_trans (exp_le_one_add_exp k) hx)
    exact absurd (lt_of_le_of_lt (le_trans hk (self_le_exp_sub_log hx1)) hlt) (lt_irrefl_ax k)


/-- Convexity the other way: `exp u − exp v ≤ (u − v) · exp u`. Where `exp_sub_exp_lower` carries a
lower bound on an exponent gap up to the value, this carries a lower bound on a **value** gap back
down to the **exponent** — and it loses only a constant factor, which is what the `P = const` cell of
the depth-3 decomposition needs (`μ − log(Q x) ≥ exp(−μ) · (exp μ − Q x)`). -/
private theorem exp_sub_exp_upper (u v : Real) : exp u - exp v ≤ (u - v) * exp u := by
  have h1 : (1 : Real) + (v - u) ≤ exp (v - u) := one_add_le_exp (v - u)
  have h2 : exp u * (1 + (v - u)) ≤ exp u * exp (v - u) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos u))
  have h3 : exp u * exp (v - u) = exp v := by
    rw [← exp_add]
    have e : u + (v - u) = v := by mach_mpoly [u, v]
    rw [e]
  rw [h3] at h2
  have e2 : exp u * (1 + (v - u)) = exp u - (u - v) * exp u := by mach_mpoly [exp u, u, v]
  rw [e2] at h2
  have v2 := add_le_add_wit h2 (le_refl ((u - v) * exp u - exp v))
  have e3 : exp u - (u - v) * exp u + ((u - v) * exp u - exp v) = exp u - exp v := by
    mach_mpoly [exp u, exp v, u, v]
  have e4 : exp v + ((u - v) * exp u - exp v) = (u - v) * exp u := by
    mach_mpoly [exp u, exp v, u, v]
  rw [e3, e4] at v2
  exact v2

/-- **Value gap → exponent gap, with the conversion modulus explicit.**

`exp_sub_exp_upper` says a value gap can be carried down to the exponent; this states *at what price*.
Given any ceiling `M` on the **upper** exponent `u`, a value gap `G` below `exp u − exp v` becomes an
exponent gap of `G · exp (−M)`:

```
G ≤ exp u − exp v   ∧   u ≤ M   ⟹   G · exp (−M) ≤ u − v
```

**The modulus rides on `u`, not `v`, and that is forced.** `exp_sub_exp_upper` produces the factor
`exp u`; bounding it needs a hypothesis about the *target's* exponent. Stating the modulus on `v`
instead would require a bound on `log (Q x)` — which is the very quantity the depth-3 decay cells are
trying to bound, so the statement would be circular where it is used.

**Why `M` is a separate parameter rather than `u` itself.** The three call sites in the depth-3
decomposition differ *only* in what they can say about `u = exp (P x)`, and that difference is the
whole quantitative content of the decomposition:

| cell | `u` | admissible `M` | modulus |
| --- | --- | --- | --- |
| `P = const c` | `exp c` | `exp c` (exact) | constant |
| `P` bounded by `K` | `exp (P x)` | `K` | constant, `exp (−K)` |
| `P = var` | `exp x` | `exp x` (exact) | `exp (−exp x)` — **not** constant |

So the bounded cell survives on a weak `exp (−C − exp x)` value gap while the `var` cell needs a
**constant** one: the same reduction at two strengths, because `M` differs. A version of this lemma
that discharged the modulus — say, by fixing `M` to a constant — would prove the bounded cell and
silently lose the `var` cell. Keeping `M` free is what lets one statement serve all three without
weakening any.

Positivity of `u − v` is needed, not incidental: it is what makes `u ≤ M` monotone through the
product at the capping step.

**Public, unlike the `exp_sub_exp_*` pair it is built from.** Those are proof plumbing; this is the
interface the depth-3 decomposition actually speaks through, and the statement it makes — one
conversion, three moduli, no cell weakened — is a reuse claim, registered as such. -/
theorem exponent_gap_of_value_gap (u v M G : Real) (hu : u ≤ M) (hnode : 0 < u - v)
    (hG : G ≤ exp u - exp v) : G * exp (-M) ≤ u - v := by
  have hconv : exp u - exp v ≤ (u - v) * exp u := exp_sub_exp_upper u v
  have hcap : (u - v) * exp u ≤ (u - v) * exp M :=
    mul_le_mul_of_nonneg_left (exp_monotone hu) (le_of_lt hnode)
  have hchain : G ≤ (u - v) * exp M := le_trans hG (le_trans hconv hcap)
  have hstep := mul_le_mul_of_nonneg_right hchain (le_of_lt (exp_pos (-M)))
  have hinv : exp M * exp (-M) = 1 := by
    rw [← exp_add]
    have e : M + -M = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  have e3 : (u - v) * exp M * exp (-M) = (u - v) * (exp M * exp (-M)) := by
    mach_mpoly [u, v, exp M, exp (-M)]
  rw [e3, hinv] at hstep
  have e4 : (u - v) * (1 : Real) = u - v := by mach_ring
  rw [e4] at hstep
  exact hstep

/-- **The `exp`-level from-below gap.** `exp (A x)` cannot approach a constant `ν` from below with a
shrinking gap, for `A` of depth ≤ 1 — and as at the value level the gap is a **positive constant**.

The five forms again, and again none is tight: `exp α` is an exact constant; `exp (c − log x)` tends
to `0`, so the gap tends to `ν` (and `ν ≤ 0` makes the hypothesis false outright, since `exp` is
positive); and `exp x`, `exp (exp x − d)`, `exp (exp x − log x)` all outrun `ν`.

The `c − log x` cell is the only one needing care, and the care is choosing the target: the ray is
set so that `exp (c − log x) ≤ exp (log ν − 1)`, which is *strictly* below `ν`, so
`ν − exp (log ν − 1)` is a legitimate positive `ε`. Picking `ν/2` would have been the reflex and
would have needed division, which this base does not have. -/
theorem depth_le_one_exp_gap_below (A : EMLTree) (hA : A.depth ≤ 1) (ν : Real) :
    ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → exp (A.eval x) < ν →
      ε ≤ ν - exp (A.eval x) := by
  rcases depth_le_one_classification A hA with ⟨α, hb⟩ | hb | ⟨c, _, hb⟩ | ⟨d, hb⟩ | hb
  · rcases lt_total (exp α) ν with hαν | hαν | hαν
    · refine ⟨ν - exp α, 1, sub_pos_of_lt hαν, le_refl 1, ?_⟩
      intro x hx _
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos]
      exact le_refl _
    · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
      intro x hx hlt
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos, hαν] at hlt
      exact absurd hlt (lt_irrefl_ax ν)
    · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
      intro x hx hlt
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos] at hlt
      exact absurd (lt_trans_ax hlt hαν) (lt_irrefl_ax (exp α))
  · -- `exp x` outruns `ν`
    refine ⟨1, 1 + exp ν, zero_lt_one_ax, one_le_one_add_exp ν, ?_⟩
    intro x hx hlt
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp ν) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos] at hlt
    have hν : ν ≤ exp x :=
      le_trans (le_trans (self_le_exp ν) (le_trans (exp_le_one_add_exp ν) hx)) (self_le_exp x)
    exact absurd (lt_of_le_of_lt hν hlt) (lt_irrefl_ax ν)
  · -- `exp (c − log x)` decays to `0`
    rcases lt_total 0 ν with hν | hν | hν
    · refine ⟨ν - exp (log ν - 1), 1 + exp (c - log ν + 1), ?_, one_le_one_add_exp _, ?_⟩
      · refine sub_pos_of_lt ?_
        have hstep : log ν - 1 < log ν := by
          have v := add_lt_add_left zero_lt_one_ax (log ν - 1)
          have e1 : log ν - 1 + (0 : Real) = log ν - 1 := by mach_ring
          have e2 : log ν - 1 + 1 = log ν := by mach_ring
          rw [e1, e2] at v; exact v
        have h := exp_lt hstep
        rw [exp_log hν] at h
        exact h
      · intro x hx _
        have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp _) hx
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        rw [hb x hxpos]
        have hreach : exp (c - log ν + 1) ≤ x := le_trans (exp_le_one_add_exp _) hx
        have hlog : c - log ν + 1 ≤ log x := log_ge_of_exp_le hreach
        have hexp : c - log x ≤ log ν - 1 := by
          have v := add_le_add_wit (le_refl (c - log ν + 1 + (log ν - 1) - c))
            (neg_le_neg_wit hlog)
          have e1 : c - log ν + 1 + (log ν - 1) - c + -(c - log ν + 1) = log ν - 1 - c := by
            mach_mpoly [c, log ν]
          have e2 : c - log ν + 1 + (log ν - 1) - c + -log x = -log x := by mach_mpoly [c, log ν, log x]
          rw [e1, e2] at v
          have v2 := add_le_add_wit v (le_refl c)
          have e3 : -log x + c = c - log x := by mach_ring
          have e4 : log ν - 1 - c + c = log ν - 1 := by mach_mpoly [c, log ν]
          rw [e3, e4] at v2; exact v2
        have hmono : exp (c - log x) ≤ exp (log ν - 1) := exp_monotone hexp
        have v := add_le_add_wit (le_refl ν) (neg_le_neg_wit hmono)
        have e1 : ν + -exp (log ν - 1) = ν - exp (log ν - 1) := by mach_ring
        have e2 : ν + -exp (c - log x) = ν - exp (c - log x) := by mach_ring
        rw [e1, e2] at v; exact v
    · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
      intro x hx hlt
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos, ← hν] at hlt
      exact absurd (lt_trans_ax (exp_pos _) hlt) (lt_irrefl_ax 0)
    · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
      intro x hx hlt
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos] at hlt
      exact absurd (lt_trans_ax (lt_trans_ax (exp_pos _) hlt) hν) (lt_irrefl_ax 0)
  · -- `exp (exp x − d)` outruns `ν`
    refine ⟨1, 1 + exp d + exp ν, zero_lt_one_ax, one_le_ray d ν, ?_⟩
    intro x hx hlt
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_ray d ν) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos] at hlt
    have hdx : d ≤ x := le_trans (fst_le_ray d ν) hx
    have hνx : ν ≤ x :=
      le_trans (le_add_nonneg_l' (le_of_lt zero_lt_one_ax))
        (le_trans (one_add_snd_le_ray d ν) hx)
    have hxd : x ≤ exp x - d := by
      have v := add_le_add_wit (two_mul_le_exp (le_of_lt hxpos)) (neg_le_neg_wit hdx)
      have e1 : x + x + -x = x := by mach_mpoly [x]
      have e2 : exp x + -d = exp x - d := by mach_ring
      rw [e1, e2] at v; exact v
    have hν : ν ≤ exp (exp x - d) :=
      le_trans hνx (le_trans hxd (self_le_exp (exp x - d)))
    exact absurd (lt_of_le_of_lt hν hlt) (lt_irrefl_ax ν)
  · -- `exp (exp x − log x)` outruns `ν`
    refine ⟨1, 1 + exp ν, zero_lt_one_ax, one_le_one_add_exp ν, ?_⟩
    intro x hx hlt
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp ν) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos] at hlt
    have hνx : ν ≤ x := le_trans (self_le_exp ν) (le_trans (exp_le_one_add_exp ν) hx)
    have hν : ν ≤ exp (exp x - log x) :=
      le_trans hνx (le_trans (self_le_exp_sub_log hx1) (self_le_exp (exp x - log x)))
    exact absurd (lt_of_le_of_lt hν hlt) (lt_irrefl_ax ν)


/-- From a cap on the left child and a large enough right-child log, the gap to `k` clears `1`. -/
private theorem one_le_gap_of_bounds {a b K k : Real} (hK : a ≤ K) (hbig : 1 - k + K ≤ b) :
    1 ≤ k - (a - b) := by
  have v := add_le_add_wit (neg_le_neg_wit hK) hbig
  have e1 : -K + (1 - k + K) = 1 - k := by mach_mpoly [K, k]
  have e2 : -a + b = b - a := by mach_ring
  rw [e1, e2] at v
  have v2 := add_le_add_wit v (le_refl k)
  have e3 : 1 - k + k = (1 : Real) := by mach_mpoly [k]
  have e4 : b - a + k = k - (a - b) := by mach_mpoly [a, b, k]
  rw [e3, e4] at v2; exact v2

/-- **The from-below gap at depth ≤ 2**, with the same constant `ε` as at depth ≤ 1.

The collapse is the one used throughout: the left child splits once, and when it **grows** the right
child's linear log ceiling puts the node above `k`, so the hypothesis is false with **no enumeration
of the right child**. When it is **bounded**, the right child's five forms split three-and-two — the
three divergent logs drag the node to `−∞`, so the gap clears `1`, and the two with an eventually
exact constant log reduce to `depth_le_one_exp_gap_below` against a shifted target.

Every cell is vacuous, or clears `1`, or inherits a constant `ε`. **Nothing here is tight**, which is
the depth-2 restatement of why approach from below is the easy direction. -/
theorem depth_le_two_gap_below (t : EMLTree) (ht : t.depth ≤ 2) (k : Real) :
    ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → t.eval x < k → ε ≤ k - t.eval x := by
  cases t with
  | const c => exact depth_le_one_gap_below (EMLTree.const c) (by simp [EMLTree.depth]) k
  | var => exact depth_le_one_gap_below EMLTree.var (by simp [EMLTree.depth]) k
  | eml A B =>
    have hA : A.depth ≤ 1 := by
      simp only [EMLTree.depth] at ht
      have := Nat.le_max_left A.depth B.depth; omega
    have hB : B.depth ≤ 1 := by
      simp only [EMLTree.depth] at ht
      have := Nat.le_max_right A.depth B.depth; omega
    rcases depth_le_one_exp_bounded_or_grows A hA with ⟨K, hK⟩ | ⟨T, hT⟩
    · rcases depth_le_one_form B hB with ⟨β, hb⟩ | hb | ⟨c', _, hb⟩ | ⟨d, hb⟩ | hb
      · -- right child a constant: a shifted target for the depth-1 gap
        obtain ⟨ε, X₀, hε, hX₀, hg⟩ := depth_le_one_exp_gap_below A hA (k + log β)
        refine ⟨ε, X₀, hε, hX₀, ?_⟩
        intro x hx hlt
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX₀ hx)
        have hlt' : exp (A.eval x) - log (B.eval x) < k := hlt
        rw [hb x hxpos] at hlt'
        have hgt : exp (A.eval x) < k + log β := by
          have v := add_lt_add_left hlt' (log β)
          have e1 : log β + (exp (A.eval x) - log β) = exp (A.eval x) := by
            mach_mpoly [log β, exp (A.eval x)]
          have e2 : log β + k = k + log β := by mach_ring
          rw [e1, e2] at v; exact v
        show ε ≤ k - (exp (A.eval x) - log (B.eval x))
        rw [hb x hxpos]
        have e : k + log β - exp (A.eval x) = k - (exp (A.eval x) - log β) := by
          mach_mpoly [k, log β, exp (A.eval x)]
        rw [← e]
        exact hg x hx hgt
      · -- `log x` drags the node down
        refine ⟨1, 1 + exp (1 - k + K), zero_lt_one_ax, one_le_one_add_exp _, ?_⟩
        intro x hx _
        have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp _) hx
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        show (1 : Real) ≤ k - (exp (A.eval x) - log (B.eval x))
        rw [hb x hxpos]
        exact one_le_gap_of_bounds (hK x hx1)
          (log_ge_of_exp_le (le_trans (exp_le_one_add_exp (1 - k + K)) hx))
      · -- right child `c − log x`: the log is identically `0`, the node is `exp (A x)`
        obtain ⟨ε, X₁, hε, hX₁, hg⟩ := depth_le_one_exp_gap_below A hA k
        refine ⟨ε, X₁ + exp c', hε, le_trans hX₁ (le_add_nonneg_r' (le_of_lt (exp_pos c'))), ?_⟩
        intro x hx hlt
        have hX₁x : X₁ ≤ x := le_trans (le_add_nonneg_r' (le_of_lt (exp_pos c'))) hx
        have hx1 : (1 : Real) ≤ x := le_trans hX₁ hX₁x
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        have hcx : exp c' ≤ x := le_trans (le_add_nonneg_l' (le_trans
          (le_of_lt zero_lt_one_ax) hX₁)) hx
        have hzero : log (B.eval x) = 0 := by
          rw [hb x hxpos]
          refine log_nonpos ?_
          have hge : c' ≤ log x := log_ge_of_exp_le hcx
          have v := add_le_add_wit (le_refl c') (neg_le_neg_wit hge)
          have e1 : c' + -log x = c' - log x := by mach_ring
          have e2 : c' + -c' = (0 : Real) := by mach_mpoly [c']
          rw [e1, e2] at v; exact v
        have hlt' : exp (A.eval x) - log (B.eval x) < k := hlt
        rw [hzero] at hlt'
        have hgt : exp (A.eval x) < k := by
          have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
          rw [e] at hlt'; exact hlt'
        show ε ≤ k - (exp (A.eval x) - log (B.eval x))
        rw [hzero]
        have e : k - (exp (A.eval x) - (0 : Real)) = k - exp (A.eval x) := by mach_ring
        rw [e]
        exact hg x hX₁x hgt
      · -- right child `exp x − d`
        refine ⟨1, 1 + exp (1 - k + K) + exp d, zero_lt_one_ax, one_le_ray _ _, ?_⟩
        intro x hx _
        have hx1 : (1 : Real) ≤ x := le_trans (one_le_ray _ _) hx
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        show (1 : Real) ≤ k - (exp (A.eval x) - log (B.eval x))
        rw [hb x hxpos]
        refine one_le_gap_of_bounds (hK x hx1) (log_ge_of_exp_le ?_)
        have hreach : exp (1 - k + K) + d ≤ x := by
          have v := add_le_add_wit (le_refl (exp (1 - k + K))) (self_le_exp d)
          have w : exp (1 - k + K) + exp d ≤ 1 + exp (1 - k + K) + exp d := by
            have u := add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
              (le_refl (exp (1 - k + K)))) (le_refl (exp d))
            have e : (0 : Real) + exp (1 - k + K) + exp d = exp (1 - k + K) + exp d := by mach_ring
            rw [e] at u; exact u
          exact le_trans (le_trans v w) hx
        have hxe : exp (1 - k + K) + d ≤ exp x := le_trans hreach (self_le_exp x)
        have v := add_le_add_wit hxe (le_refl (-d))
        have e1 : exp (1 - k + K) + d + -d = exp (1 - k + K) := by
          mach_mpoly [exp (1 - k + K), d]
        have e2 : exp x + -d = exp x - d := by mach_ring
        rw [e1, e2] at v; exact v
      · -- right child `exp x − log x`
        refine ⟨1, 1 + exp (1 - k + K), zero_lt_one_ax, one_le_one_add_exp _, ?_⟩
        intro x hx _
        have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp _) hx
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
        show (1 : Real) ≤ k - (exp (A.eval x) - log (B.eval x))
        rw [hb x hxpos]
        exact one_le_gap_of_bounds (hK x hx1)
          (log_ge_of_exp_le (le_trans (le_trans (exp_le_one_add_exp (1 - k + K)) hx)
            (self_le_exp_sub_log hx1)))
    · -- growing left child: the node outruns `k`, whatever the right child is
      obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B hB
      obtain ⟨T2, hT2⟩ := two_mul_add_le_exp (D + k)
      refine ⟨1, 1 + exp T + exp T2, zero_lt_one_ax, one_le_ray T T2, ?_⟩
      intro x hx hlt
      have hx1 : (1 : Real) ≤ x := le_trans (one_le_ray T T2) hx
      have hxT : T ≤ x := le_trans (fst_le_ray T T2) hx
      have hxT2 : T2 ≤ x :=
        le_trans (le_add_nonneg_l' (le_of_lt zero_lt_one_ax)) (le_trans (one_add_snd_le_ray T T2) hx)
      have hlt' : exp (A.eval x) - log (B.eval x) < k := hlt
      have hnode : exp x - (x + D) ≤ exp (A.eval x) - log (B.eval x) := by
        have v := add_le_add_wit (hT x hxT) (neg_le_neg_wit (hD x hx1))
        have e1 : exp x + -(x + D) = exp x - (x + D) := by mach_ring
        have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by mach_ring
        rw [e1, e2] at v; exact v
      have hk : k ≤ exp x - (x + D) := by
        have v := add_le_add_wit (hT2 x hxT2) (le_refl (-x + -D))
        have e1 : x + x + (D + k) + (-x + -D) = x + k := by mach_mpoly [x, D, k]
        have e2 : exp x + (-x + -D) = exp x - (x + D) := by mach_mpoly [exp x, x, D]
        rw [e1, e2] at v
        exact le_trans (le_add_nonneg_l' (le_trans (le_of_lt zero_lt_one_ax) hx1)) v
      exact absurd (lt_of_le_of_lt (le_trans hk hnode) hlt') (lt_irrefl_ax k)


/-- **The `P = const` cell of the depth-3 decay decomposition.**

With a constant left child the node is `exp c − log (Q x)`, so the obligation asks whether
`log (Q x)` can creep up on the constant `exp c` from below faster than exponentially. It cannot, and
the reason is that **nothing here is exponentially small**:

* `depth_le_two_gap_below` says `Q x` stays a **constant** `ε` below `exp (exp c)`, because the only
  decaying shape in the grammar is positive and so cannot approach a constant from underneath;
* `exp_sub_exp_upper` carries that value gap down to the logarithm losing only a constant factor —
  `exp (exp c) − Q x ≤ (exp c − log (Q x)) · exp (exp c)` — so the node is bounded below by
  `ε · exp (−exp c)`, a positive **constant**.

A constant floor is far stronger than the `exp (−C − x)` the obligation asks for. Had the gap been
`exp (−C − x)` instead, the convexity step would have produced `exp (−C′ − 2x)` and the bound would
have degraded by a factor of `x` at every level — which is why `depth_le_one_gap_below`'s conclusion
is stated as a constant and not weakened to match its from-above mirror.

Second of the four cells. It bounds by `C + x`, which is *stronger* than the corrected rung needs, so
it transports to `Depth3DecayExp` unchanged (`depth_three_decayExp_const_left`) despite
`Depth3DecayHard` itself being false. Three of the four cells now hold; only bounded-`P` remains. -/
theorem depth_three_decay_const_left (c : Real) (Q : EMLTree) (hQ : Q.depth ≤ 2) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (Q.eval x) →
      0 < exp c - log (Q.eval x) → -log (exp c - log (Q.eval x)) ≤ C + x := by
  obtain ⟨ε, X₁, hε, hX₁, hgap⟩ := depth_le_two_gap_below Q hQ (exp (exp c))
  obtain ⟨C, hC⟩ := small_exp_below (mul_pos hε (exp_pos (-exp c)))
  refine ⟨C, X₁, hX₁, ?_⟩
  intro x hx hlogpos hnodepos
  have hx1 : (1 : Real) ≤ x := le_trans hX₁ hx
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  -- a strictly positive log forces a strictly positive argument: the totalisation gives `0` otherwise
  have hQpos : (0 : Real) < Q.eval x := by
    rcases lt_total 0 (Q.eval x) with h | h | h
    · exact h
    · have hle : Q.eval x ≤ 0 := by rw [← h]; exact le_refl 0
      have hz : log (Q.eval x) = 0 := log_nonpos hle
      rw [hz] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
    · have hz : log (Q.eval x) = 0 := log_nonpos (le_of_lt h)
      rw [hz] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
  -- the node's positivity puts `log (Q x)` below `exp c`, hence `Q x` below `exp (exp c)`
  have hlt : log (Q.eval x) < exp c := by
    have v := add_lt_add_left hnodepos (log (Q.eval x))
    have e1 : log (Q.eval x) + (0 : Real) = log (Q.eval x) := by mach_ring
    have e2 : log (Q.eval x) + (exp c - log (Q.eval x)) = exp c := by
      mach_mpoly [log (Q.eval x), exp c]
    rw [e1, e2] at v; exact v
  have hQlt : Q.eval x < exp (exp c) := by
    have h := exp_lt hlt
    rw [exp_log hQpos] at h; exact h
  -- a CONSTANT value gap, carried down to the logarithm by reverse convexity
  have hvgap : ε ≤ exp (exp c) - exp (log (Q.eval x)) := by
    rw [exp_log hQpos]; exact hgap x hx hQlt
  -- `M = u` exactly here, so the modulus `exp (−exp c)` is a constant and the conversion is tight
  have hstep : ε * exp (-exp c) ≤ exp c - log (Q.eval x) :=
    exponent_gap_of_value_gap (exp c) (log (Q.eval x)) (exp c) ε (le_refl _) hnodepos hvgap
  -- a constant floor beats `exp (−C − x)`
  have hfloor : exp (-C - x) ≤ exp c - log (Q.eval x) := le_trans (hC x hx0) hstep
  have hmono := log_le_log (exp_pos (-C - x)) hfloor
  rw [log_exp] at hmono
  have v := neg_le_neg_wit hmono
  have e : -(-C - x) = C + x := by mach_ring
  rw [e] at v; exact v



/-- **`Depth3DecayHard` is false.**

Witness `A = var`, `B = dep3CounterRight`. Writing `ε = exp (−(C+1) − x)`, the node is at most `ε` as
soon as `exp (exp x − ε) ≤ exp (exp x) − log x`, and convexity supplies

```
exp (exp x) − exp (exp x − ε) ≥ ε · exp (exp x − ε) ≥ ε · exp (exp x − 1) = exp (exp x − 1 − (C+1) − x)
```

which clears `x ≥ log x` once `exp x ≥ x + x + (C + 2)` — that is, once `two_mul_add_le_exp` fires.
So `−log node ≥ C + 1 + x`, contradicting the promised `≤ C + x`.

**Why it fails.** `exp x` and `log (B x)` sit at the *same* scale, and the totalisation is what puts
them there: `log 0 = 0` makes `eml var (const 0)` exactly `exp x`, so one further node reaches
`exp (exp x)` and its logarithm lands back on `exp x`. The two then differ by `log x · exp (−exp x)`,
and no bound of the form `C + x` can see a difference that small. The rung has to be `C + exp x`;
`Depth3DecayExp` states that. -/
theorem not_depth3DecayHard : ¬ Depth3DecayHard := by
  intro h
  obtain ⟨C, X₀, hX₀, hb⟩ :=
    h EMLTree.var dep3CounterRight (Nat.zero_le 2) (Nat.le_of_eq dep3CounterRight_depth)
  obtain ⟨T, hT⟩ := two_mul_add_le_exp (C + 1 + 1)
  have hmain : ∀ x : Real, X₀ ≤ x → T ≤ x → (1 : Real) + 1 ≤ x → -C ≤ x → False := by
    intro x hxX₀ hxT hx2 hxC
    have hx1 : (1 : Real) ≤ x := le_trans hX₀ hxX₀
    have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
    have hx0p : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    have hCx : (0 : Real) ≤ C + x := by
      have v := add_le_add_wit (le_refl C) hxC
      have e : C + -C = (0 : Real) := by mach_ring
      rw [e] at v; exact v
    have heps1 : exp (-(C + 1) - x) ≤ 1 := by
      have hneg : -(C + 1) - x ≤ 0 := by
        have v := add_le_add_wit (neg_le_neg_wit hCx) (neg_le_neg_wit (le_of_lt zero_lt_one_ax))
        have e1 : -(C + x) + -1 = -(C + 1) - x := by mach_mpoly [C, x]
        have e2 : -(0 : Real) + -0 = 0 := by mach_ring
        rw [e1, e2] at v; exact v
      have hm := exp_monotone hneg
      rw [exp_zero] at hm; exact hm
    have h1x : (1 : Real) < exp x := by
      have hlt : (1 : Real) < 1 + x := by
        have v := add_lt_add_left hx0p 1
        have e : (1 : Real) + 0 = 1 := by mach_ring
        rw [e] at v; exact v
      exact lt_of_lt_of_le hlt (one_add_le_exp x)
    have hlow : (0 : Real) < exp x - exp (-(C + 1) - x) := by
      have hone : exp (-(C + 1) - x) < exp x := lt_of_le_of_lt heps1 h1x
      have w := add_lt_add_left hone (-exp (-(C + 1) - x))
      have e1 : -exp (-(C + 1) - x) + exp (-(C + 1) - x) = (0 : Real) := by
        mach_mpoly [exp (-(C + 1) - x)]
      have e2 : -exp (-(C + 1) - x) + exp x = exp x - exp (-(C + 1) - x) := by mach_ring
      rw [e1, e2] at w; exact w
    have hBval : dep3CounterRight.eval x = exp (exp x) - log x := dep3CounterRight_eval x
    have hlogx : (0 : Real) < log x := by
      have hone1 : (1 : Real) < 1 + 1 := by
        have v := add_lt_add_left zero_lt_one_ax 1
        have e : (1 : Real) + 0 = 1 := by mach_ring
        rw [e] at v; exact v
      have h1 := log_lt_log zero_lt_one_ax (lt_of_lt_of_le hone1 hx2)
      have hl1 : log (1 : Real) = 0 := by
        have hz : exp (0 : Real) = 1 := exp_zero
        rw [← hz, log_exp]
      rw [hl1] at h1; exact h1
    have hlogle : log x ≤ x := log_le_self_on_ray hx1
    have hkey : exp (exp x - exp (-(C + 1) - x)) ≤ exp (exp x) - log x := by
      have hconv : (exp x - (exp x - exp (-(C + 1) - x))) * exp (exp x - exp (-(C + 1) - x))
          ≤ exp (exp x) - exp (exp x - exp (-(C + 1) - x)) :=
        exp_sub_exp_lower (exp x) (exp x - exp (-(C + 1) - x))
      have e0 : exp x - (exp x - exp (-(C + 1) - x)) = exp (-(C + 1) - x) := by
        mach_mpoly [exp x, exp (-(C + 1) - x)]
      rw [e0] at hconv
      have hshift : exp (exp x - 1) ≤ exp (exp x - exp (-(C + 1) - x)) := by
        refine exp_monotone ?_
        have v := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit heps1)
        have e1 : exp x + -1 = exp x - 1 := by mach_ring
        have e2 : exp x + -exp (-(C + 1) - x) = exp x - exp (-(C + 1) - x) := by mach_ring
        rw [e1, e2] at v; exact v
      have hprod : exp (exp x - 1 - (C + 1) - x)
          ≤ exp (-(C + 1) - x) * exp (exp x - exp (-(C + 1) - x)) := by
        have hm := mul_le_mul_of_nonneg_left hshift (le_of_lt (exp_pos (-(C + 1) - x)))
        have e : exp (-(C + 1) - x) * exp (exp x - 1) = exp (exp x - 1 - (C + 1) - x) := by
          rw [← exp_add]
          have e' : -(C + 1) - x + (exp x - 1) = exp x - 1 - (C + 1) - x := by
            mach_mpoly [C, x, exp x]
          rw [e']
        rw [e] at hm; exact hm
      have hbig : x ≤ exp (exp x - 1 - (C + 1) - x) := by
        refine le_trans ?_ (self_le_exp _)
        have v := add_le_add_wit (hT x hxT) (le_refl (-1 - (C + 1) - x))
        have e1 : x + x + (C + 1 + 1) + (-1 - (C + 1) - x) = x := by mach_mpoly [x, C]
        have e2 : exp x + (-1 - (C + 1) - x) = exp x - 1 - (C + 1) - x := by mach_mpoly [exp x, C, x]
        rw [e1, e2] at v; exact v
      have hchain : log x ≤ exp (exp x) - exp (exp x - exp (-(C + 1) - x)) :=
        le_trans hlogle (le_trans hbig (le_trans hprod hconv))
      have v := add_le_add_wit hchain (le_refl (exp (exp x - exp (-(C + 1) - x)) - log x))
      have e1 : log x + (exp (exp x - exp (-(C + 1) - x)) - log x)
          = exp (exp x - exp (-(C + 1) - x)) := by
        mach_mpoly [log x, exp (exp x - exp (-(C + 1) - x))]
      have e2 : exp (exp x) - exp (exp x - exp (-(C + 1) - x))
          + (exp (exp x - exp (-(C + 1) - x)) - log x) = exp (exp x) - log x := by
        mach_mpoly [exp (exp x), exp (exp x - exp (-(C + 1) - x)), log x]
      rw [e1, e2] at v; exact v
    have hBpos : (0 : Real) < dep3CounterRight.eval x := by
      rw [hBval]; exact lt_of_lt_of_le (exp_pos _) hkey
    have hloglow : exp x - exp (-(C + 1) - x) ≤ log (dep3CounterRight.eval x) := by
      rw [hBval]
      have hm := log_le_log (exp_pos (exp x - exp (-(C + 1) - x))) hkey
      rw [log_exp] at hm; exact hm
    have hnodele : exp (EMLTree.var.eval x) - log (dep3CounterRight.eval x)
        ≤ exp (-(C + 1) - x) := by
      show exp x - log (dep3CounterRight.eval x) ≤ exp (-(C + 1) - x)
      have v := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit hloglow)
      have e1 : exp x + -log (dep3CounterRight.eval x)
          = exp x - log (dep3CounterRight.eval x) := by mach_ring
      have e2 : exp x + -(exp x - exp (-(C + 1) - x)) = exp (-(C + 1) - x) := by
        mach_mpoly [exp x, exp (-(C + 1) - x)]
      rw [e1, e2] at v; exact v
    have hlogBpos : (0 : Real) < log (dep3CounterRight.eval x) := lt_of_lt_of_le hlow hloglow
    have hnodepos : (0 : Real) < exp (EMLTree.var.eval x) - log (dep3CounterRight.eval x) := by
      show (0 : Real) < exp x - log (dep3CounterRight.eval x)
      have hBlt : dep3CounterRight.eval x < exp (exp x) := by
        rw [hBval]
        have v := add_lt_add_left hlogx (exp (exp x) - log x)
        have e1 : exp (exp x) - log x + (0 : Real) = exp (exp x) - log x := by mach_ring
        have e2 : exp (exp x) - log x + log x = exp (exp x) := by
          mach_mpoly [exp (exp x), log x]
        rw [e1, e2] at v; exact v
      have hlt := log_lt_log hBpos hBlt
      rw [log_exp] at hlt
      have w := add_lt_add_left hlt (-log (dep3CounterRight.eval x))
      have e1 : -log (dep3CounterRight.eval x) + log (dep3CounterRight.eval x) = (0 : Real) := by
        mach_mpoly [log (dep3CounterRight.eval x)]
      have e2 : -log (dep3CounterRight.eval x) + exp x
          = exp x - log (dep3CounterRight.eval x) := by mach_ring
      rw [e1, e2] at w; exact w
    have hprom := hb x hxX₀ hlogBpos hnodepos
    have hmono := log_le_log hnodepos hnodele
    rw [log_exp] at hmono
    have hneg := neg_le_neg_wit hmono
    have e : -(-(C + 1) - x) = C + 1 + x := by mach_mpoly [C, x]
    rw [e] at hneg
    have hcontra : C + 1 + x ≤ C + x := le_trans hneg hprom
    have v := add_lt_add_left zero_lt_one_ax (C + x)
    have e1 : C + x + (0 : Real) = C + x := by mach_ring
    have e2 : C + x + 1 = C + 1 + x := by mach_mpoly [C, x]
    rw [e1, e2] at v
    exact absurd (lt_of_lt_of_le v hcontra) (lt_irrefl_ax (C + x))
  have hX₀0 : (0 : Real) ≤ X₀ := le_trans (le_of_lt zero_lt_one_ax) hX₀
  have hp1 : (0 : Real) ≤ X₀ + exp T := le_trans hX₀0 (le_add_nonneg_r' (le_of_lt (exp_pos T)))
  have hp2 : (0 : Real) ≤ X₀ + exp T + exp (1 + 1) :=
    le_trans hp1 (le_add_nonneg_r' (le_of_lt (exp_pos (1 + 1))))
  refine hmain (X₀ + exp T + exp (1 + 1) + exp (-C)) ?_ ?_ ?_ ?_
  · exact le_trans (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos T)))
      (le_add_nonneg_r' (le_of_lt (exp_pos (1 + 1))))) (le_add_nonneg_r' (le_of_lt (exp_pos (-C))))
  · exact le_trans (self_le_exp T) (le_trans (le_add_nonneg_l' hX₀0)
      (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos (1 + 1))))
        (le_add_nonneg_r' (le_of_lt (exp_pos (-C))))))
  · exact le_trans (self_le_exp (1 + 1)) (le_trans (le_add_nonneg_l' hp1)
      (le_add_nonneg_r' (le_of_lt (exp_pos (-C)))))
  · exact le_trans (self_le_exp (-C)) (le_add_nonneg_l' hp2)


/-- Weakening the rung. `x ≤ exp x`, so every `C + x` bound is a `C + exp x` bound. -/
private theorem rung_weaken {y C x : Real} (h : y ≤ C + x) : y ≤ C + exp x :=
  le_trans h (add_le_add_left (self_le_exp x) C)

/-- **The growing cell, transported to the corrected rung.** -/
theorem depth_three_decayExp_growing_left (P Q : EMLTree) (hQ : Q.depth ≤ 2) (C T : Real)
    (hP : ∀ x : Real, T ≤ x → exp x - x - C ≤ P.eval x) :
    ∃ C' X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      -log (exp (P.eval x) - log (Q.eval x)) ≤ C' + exp x := by
  obtain ⟨C', X₀, hX₀, h⟩ := depth_three_decay_growing_left P Q hQ C T hP
  exact ⟨C', X₀, hX₀, fun x hx => rung_weaken (h x hx)⟩

/-- **The `const` cell, transported to the corrected rung.**

Two of `Depth3DecayExp`'s four cells therefore hold already, and hold for a reason worth stating: the
cells discharged against the *false* `Depth3DecayHard` were proved with the **stronger** `C + x`
bound, so refuting the conjunction cost nothing on those cells. A refutation invalidates a
conjecture, not the lemmas proved on the way to it — and turning that remark into these two
corollaries is what keeps it from being a remark. -/
theorem depth_three_decayExp_const_left (c : Real) (Q : EMLTree) (hQ : Q.depth ≤ 2) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (Q.eval x) →
      0 < exp c - log (Q.eval x) → -log (exp c - log (Q.eval x)) ≤ C + exp x := by
  obtain ⟨C, X₀, hX₀, h⟩ := depth_three_decay_const_left c Q hQ
  exact ⟨C, X₀, hX₀, fun x hx h1 h2 => rung_weaken (h x hx h1 h2)⟩


/-- **What the `P = var` cell reduces to.** A depth-≤2 value cannot approach `exp (exp x)` from below
with a shrinking gap.

Unlike `depth_le_two_gap_below`, the target here **moves with `x`**, which is why that theorem does
not apply and this is a separate statement. The enumeration behind it is routine and the collapse is
sharp: writing `Q = exp a − Log b`, only `a = exp x − d` with `d = 0` is delicate. `d > 0` scales `Q`
down by `exp (−d)` and opens a gap of order `exp (exp x)`; `d < 0` pushes `Q` *above* `exp (exp x)`,
making the hypothesis false; `a = exp x − log x` divides by `x` and again opens an enormous gap; and
every other form of `a` leaves `Q` far below. At `d = 0` the gap is exactly `Log (b x)`, and that cell is
now closed by `depth_le_one_log_gap_pos`.

**Assembly route, worked out but not written.** Three of the five `A`-forms (`α`, `x`, `c − log x`)
give `exp (A x)` bounded by a constant or by `exp x`, and `exp (exp x) ≥ exp x ≥ x + x` leaves room to
spare against the constant floor `Cl ≤ log (B x)` from `depth_le_one_log_lower_at_infinity`. The two
`exp x − …` forms need `exp_sub_exp_lower` and a division-free trick:

* `a = exp x − d`, `d > 0`: the gap is at least `d · exp (exp x − d) + Cl`, and **`d = exp (log d)`**
  turns the product into `exp (log d + exp x − d)`, which `self_le_exp` then bounds below by
  `log d + exp x − d`. Linear in the end, so the ray is explicit. Writing `d` as `exp (log d)` is what
  removes the need to divide by `d`, which this base cannot do.
* `a = exp x − d`, `d < 0`: **vacuous**, and the same trick shows it. `exp (exp x − d) − exp (exp x)`
  is at least `(−d) · exp (exp x) = exp (log (−d) + exp x)`, which outruns the linear ceiling
  `log (B x) ≤ x + D`, so the hypothesis `Q x < exp (exp x)` fails on a ray.
* `a = exp x − log x`: the gap is at least `log x · exp (exp x − log x) + Cl`, and past `x ≥ e` the
  factor `log x ≥ 1` makes it at least `exp (exp x − log x) + Cl ≥ x + Cl`.

Estimated ~400 lines, mostly ray plumbing. The mathematics is in `depth_le_one_log_gap_pos` and the
two convexity applications; everything else is arithmetic. -/
def ExpExpGapBelow : Prop :=
  ∀ Q : EMLTree, Q.depth ≤ 2 → ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧
    ∀ x : Real, X₀ ≤ x → Q.eval x < exp (exp x) → ε ≤ exp (exp x) - Q.eval x

/-- **The `P = var` cell follows from it.** The reduction is the content; the enumeration is grinding.

`node = exp x − log (Q x)` is positive exactly when `Q x < exp (exp x)`, and reverse convexity turns a
gap at the *value* level into a gap at the *exponent* level losing only the factor `exp (exp x)`:

```
exp (exp x) − Q x ≤ (exp x − log (Q x)) · exp (exp x)
```

so a constant floor `ε` on the value gap gives `node ≥ ε · exp (−exp x)`, which is exactly
`exp (−C − exp x)` for `C = −log ε`. **The corrected rung is what makes this work**: the same argument
against `C + x` would need `ε · exp (−exp x) ≥ exp (−C − x)`, which is false. The rung and the
`exp (exp x)` target are the same phenomenon seen from two sides. -/
theorem depth_three_decayExp_var_left_of_gap (h : ExpExpGapBelow) (Q : EMLTree) (hQ : Q.depth ≤ 2) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (Q.eval x) →
      0 < exp x - log (Q.eval x) → -log (exp x - log (Q.eval x)) ≤ C + exp x := by
  obtain ⟨ε, X₁, hε, hX₁, hgap⟩ := h Q hQ
  refine ⟨-log ε, X₁, hX₁, ?_⟩
  intro x hx hlogpos hnodepos
  have hQpos : (0 : Real) < Q.eval x := by
    rcases lt_total 0 (Q.eval x) with hq | hq | hq
    · exact hq
    · have hle : Q.eval x ≤ 0 := by rw [← hq]; exact le_refl 0
      rw [log_nonpos hle] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
    · rw [log_nonpos (le_of_lt hq)] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
  have hlt : log (Q.eval x) < exp x := by
    have v := add_lt_add_left hnodepos (log (Q.eval x))
    have e1 : log (Q.eval x) + (0 : Real) = log (Q.eval x) := by mach_ring
    have e2 : log (Q.eval x) + (exp x - log (Q.eval x)) = exp x := by
      mach_mpoly [log (Q.eval x), exp x]
    rw [e1, e2] at v; exact v
  have hQlt : Q.eval x < exp (exp x) := by
    have hh := exp_lt hlt
    rw [exp_log hQpos] at hh; exact hh
  have hvgap : ε ≤ exp (exp x) - exp (log (Q.eval x)) := by
    rw [exp_log hQpos]; exact hgap x hx hQlt
  -- `M = u = exp x`: the modulus is `exp (−exp x)`, NOT a constant — which is why this cell needs a
  -- constant `ε` where the bounded cell survives on a decaying gap
  have hstep : ε * exp (-exp x) ≤ exp x - log (Q.eval x) :=
    exponent_gap_of_value_gap (exp x) (log (Q.eval x)) (exp x) ε (le_refl _) hnodepos hvgap
  have hrew : exp (-(-log ε) - exp x) = ε * exp (-exp x) := by
    have e : -(-log ε) - exp x = log ε + -exp x := by mach_mpoly [log ε, exp x]
    rw [e, exp_add, exp_log hε]
  have hfloor : exp (-(-log ε) - exp x) ≤ exp x - log (Q.eval x) := by
    rw [hrew]; exact hstep
  have hmono := log_le_log (exp_pos (-(-log ε) - exp x)) hfloor
  rw [log_exp] at hmono
  have v := neg_le_neg_wit hmono
  have e : -(-(-log ε) - exp x) = -log ε + exp x := by mach_mpoly [log ε, exp x]
  rw [e] at v; exact v


/-- **What the bounded cell reduces to.** A value-level approach statement, with the target
`exp (exp (P x))` now determined by the *other* tree.

**Carries the boundedness hypothesis, deliberately.** An earlier draft quantified over all `P`, which
made the obligation strictly stronger than its only consumer needs — and a stronger obligation is
harder to discharge for no benefit. `depth_three_decayExp_bounded_left_of_gap` already holds the cap,
so passing it through costs nothing and narrows what has to be proved to the bounded regime, which is
the only one where the statement is delicate. (For a growing `P` the target is *triply* exponential
against a `Q` that `U₂` caps at *doubly* exponential; for `P = var` it is `ExpExpGapBelow`, already a
theorem.)

**This does not unify with `ExpExpGapBelow`, and the reason is quantitative.** Both cells convert a
value gap into an exponent gap by reverse convexity, and the conversion costs a factor
`exp (−exp (P x))`. When `P` is bounded that factor is a **constant**, so a value gap as weak as
`exp (−C − exp x)` suffices — which is what this Prop asks. When `P = var` the factor is
`exp (−exp x)`, and the same weak gap would give `exp (−C − 2·exp x)`, missing the rung; that cell
needs a **constant** value gap, which is why `ExpExpGapBelow` demands one. Same reduction, two
strengths, because the conversion factor is not the same. -/
def BoundedCellApproach : Prop :=
  ∀ P Q : EMLTree, P.depth ≤ 2 → Q.depth ≤ 2 →
    ∀ K XK : Real, (∀ x : Real, XK ≤ x → exp (P.eval x) ≤ K) →
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → Q.eval x < exp (exp (P.eval x)) →
      exp (-C - exp x) ≤ exp (exp (P.eval x)) - Q.eval x

/-- **The bounded cell follows from it**, completing the decomposition of `Depth3DecayExp`: two cells
proved outright, two reduced to named value-level statements. -/
theorem depth_three_decayExp_bounded_left_of_gap (h : BoundedCellApproach)
    (P Q : EMLTree) (hP : P.depth ≤ 2) (hQ : Q.depth ≤ 2) (K XK : Real)
    (hK : ∀ x : Real, XK ≤ x → exp (P.eval x) ≤ K) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (Q.eval x) →
      0 < exp (P.eval x) - log (Q.eval x) →
      -log (exp (P.eval x) - log (Q.eval x)) ≤ C + exp x := by
  obtain ⟨C₁, X₁, hX₁, hgap⟩ := h P Q hP hQ K XK hK
  refine ⟨C₁ + K, X₁ + exp XK, le_trans hX₁ (le_add_nonneg_r' (le_of_lt (exp_pos XK))), ?_⟩
  intro x hx hlogpos hnodepos
  have hX₁x : X₁ ≤ x := le_trans (le_add_nonneg_r' (le_of_lt (exp_pos XK))) hx
  have hXKx : XK ≤ x :=
    le_trans (self_le_exp XK) (le_trans (le_add_nonneg_l' (le_trans (le_of_lt zero_lt_one_ax) hX₁)) hx)
  have hQpos : (0 : Real) < Q.eval x := by
    rcases lt_total 0 (Q.eval x) with hq | hq | hq
    · exact hq
    · have hle : Q.eval x ≤ 0 := by rw [← hq]; exact le_refl 0
      rw [log_nonpos hle] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
    · rw [log_nonpos (le_of_lt hq)] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
  have hlt : log (Q.eval x) < exp (P.eval x) := by
    have v := add_lt_add_left hnodepos (log (Q.eval x))
    have e1 : log (Q.eval x) + (0 : Real) = log (Q.eval x) := by mach_ring
    have e2 : log (Q.eval x) + (exp (P.eval x) - log (Q.eval x)) = exp (P.eval x) := by
      mach_mpoly [log (Q.eval x), exp (P.eval x)]
    rw [e1, e2] at v; exact v
  have hQlt : Q.eval x < exp (exp (P.eval x)) := by
    have hh := exp_lt hlt
    rw [exp_log hQpos] at hh; exact hh
  have hvgap : exp (-C₁ - exp x) ≤ exp (exp (P.eval x)) - exp (log (Q.eval x)) := by
    rw [exp_log hQpos]; exact hgap x hX₁x hQlt
  -- `M = K` is the whole point of this cell: the cap on `exp (P x)` makes the modulus the CONSTANT
  -- `exp (−K)`, which is why a decaying `exp (−C₁ − exp x)` value gap suffices here and not at `var`
  have hstep : exp (-C₁ - exp x) * exp (-K) ≤ exp (P.eval x) - log (Q.eval x) :=
    exponent_gap_of_value_gap (exp (P.eval x)) (log (Q.eval x)) K (exp (-C₁ - exp x))
      (hK x hXKx) hnodepos hvgap
  have e5 : exp (-C₁ - exp x) * exp (-K) = exp (-(C₁ + K) - exp x) := by
    rw [← exp_add]
    have e : -C₁ - exp x + -K = -(C₁ + K) - exp x := by mach_mpoly [C₁, exp x, K]
    rw [e]
  rw [e5] at hstep
  have hmono := log_le_log (exp_pos (-(C₁ + K) - exp x)) hstep
  rw [log_exp] at hmono
  have v := neg_le_neg_wit hmono
  have e6 : -(-(C₁ + K) - exp x) = C₁ + K + exp x := by mach_mpoly [C₁, K, exp x]
  rw [e6] at v
  exact v

/-- **What is left of `BoundedCellApproach` once `P`'s normal form is consumed.**

`BoundedCellApproach` quantifies over every depth-≤2 `P` subject to a cap. `depth_le_two_normal_form`
splits that into three shapes, and **two of the three are not hard**:

| `P` | why | cost |
| --- | --- | --- |
| `const c` | the target `exp (exp c)` stops moving — it is a **constant**, so `depth_le_two_gap_below` applies verbatim | free |
| `var` | `exp (P x) = exp x` is unbounded, so the cap is **contradicted**; the cell is vacuous | free |
| `eml A B` | the target genuinely moves, bounded | **this obligation** |

So the residue is narrower than the parent in the way that matters: the target is still a moving one,
but `P` is now pinned to a *single* syntactic shape, `exp (a x) − log (b x)` with `a` and `b` among the
five `Depth1Form`s, rather than ranging over all of depth ≤ 2.

**Where the remaining difficulty is concentrated — and the pruning is a lemma, not an enumeration.**
`depth_le_two_bounded_left_exp_bounded` shows the cap forces `exp (A x)` **bounded on `[1,∞)`**, with
no case analysis on `A`'s shape at all: `depth_le_one_exp_bounded_or_grows` says `exp (A x)` is either
bounded or eventually `≥ exp x` with **nothing between**, and the growing branch dies against
`depth_le_one_log_le_linear`'s ceiling `log (B x) ≤ x + C`. So the three divergent `Depth1Form`s are
excluded *wholesale* rather than one at a time — the same collapse `depth_le_two_approach_constant`
saw, where a classification describes values but a proof branches on behaviour, and behaviour is
coarser.

**Stated over the children `A B` rather than over `Depth1Form` functions**, which is what lets it
consume those tree-level lemmas directly. The earlier function-shaped draft could not: every depth-≤1
tool in this file takes an `EMLTree`, so a normal-form statement would have needed each one
re-proved at the function level for no gain. The reduction from `BoundedCellApproach` then becomes
the restriction itself, with no threshold plumbing.

**What remains after the pruning:** the target `exp (exp (A x) − log (B x))` is bounded in
`(1, exp K]` but still *moves*, and `Q` must be shown unable to approach it super-exponentially fast.

**Not machine-checked, and stated here so it is not mistaken for a result:** the *reason* to expect
this to hold is that the obligation only has to beat `exp (−exp x)`, while every quantity at depth ≤ 2
moves at most polynomially — the approach-rate quantisation says convergence here is exact or
`Θ(1/x)`. `probe_bounded.py` found no counterexample across 50 754 live cells with margins of
`−log(gap) − exp x` at −10.9, −139, −2972, −162746 for `x` = 3, 5, 8, 12. **A probe cannot prove
absence** — and this one samples only bounded `P`, with a window-based boundedness filter. -/
def BoundedEmlCellApproach : Prop :=
  ∀ A B Q : EMLTree, A.depth ≤ 1 → B.depth ≤ 1 → Q.depth ≤ 2 →
    ∀ K XK : Real, (∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K) →
      ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
        Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
          exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x

/-- **`BoundedCellApproach` reduces to the `eml` shape alone.** The `const` and `var` shapes of `P`
are discharged here — the first because its target stops moving, the second because the cap is false
— so the last open cell of `Depth3DecayExp` is now `BoundedEmlCellApproach`.

**The `const` branch is where the modulus argument pays off again.** With `P = const c` the target is
the constant `exp (exp c)`, and `depth_le_two_gap_below` supplies a **constant** floor `ε` — vastly
stronger than the `exp (−C − exp x)` the obligation asks for. `small_exp_below` converts, and the
conversion is not tight at any point: `exp (−C − exp x) ≤ exp (−C − x) ≤ ε` uses only `x ≤ exp x`. -/
theorem boundedCellApproach_of_eml (h : BoundedEmlCellApproach) : BoundedCellApproach := by
  intro P Q hP hQ K XK hK
  cases P with
  | const c =>
    -- the target is the CONSTANT `exp (exp c)`, so the parent's own depth-2 tool closes it
    obtain ⟨ε, X₁, hε, hX₁, hgap⟩ := depth_le_two_gap_below Q hQ (exp (exp c))
    obtain ⟨C, hC⟩ := small_exp_below hε
    refine ⟨C, X₁, hX₁, ?_⟩
    intro x hx hlt
    have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX₁ hx)
    have hvgap : ε ≤ exp (exp c) - Q.eval x := hgap x hx hlt
    have hne : -(exp x) ≤ -x := neg_le_neg_wit (self_le_exp x)
    have v := add_le_add_left hne (-C)
    have e1 : -C + -(exp x) = -C - exp x := by mach_ring
    have e2 : -C + -x = -C - x := by mach_ring
    rw [e1, e2] at v
    exact le_trans (le_trans (exp_monotone v) (hC x (le_of_lt hx0))) hvgap
  | var =>
    -- `exp x ≤ K` on a ray is false, so the cell is vacuous
    exfalso
    have hwXK : XK ≤ 1 + exp XK + exp K := by
      have v : (0 : Real) + exp XK + 0 ≤ 1 + exp XK + exp K :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
          (le_of_lt (exp_pos K))
      have e : (0 : Real) + exp XK + 0 = exp XK := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp XK) v
    have hwK : K < 1 + exp XK + exp K := by
      have hKe : K < exp K := by
        have t1 := one_add_le_exp K
        have e : (1 : Real) + K = K + 1 := by mach_ring
        rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self K) t1
      have v : (0 : Real) + 0 + exp K ≤ 1 + exp XK + exp K :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XK)))
          (le_refl _)
      have e : (0 : Real) + 0 + exp K = exp K := by mach_ring
      rw [e] at v; exact lt_of_lt_of_le hKe v
    exact lt_irrefl_ax K
      (lt_of_lt_of_le (lt_of_lt_of_le hwK (self_le_exp _)) (hK _ hwXK))
  | eml A B =>
    -- the residue. Stated over the CHILDREN rather than a normal form, so it can consume the
    -- tree-level depth-1 lemmas directly; the reduction is then the restriction itself.
    have hA : A.depth ≤ 1 := by
      simp only [EMLTree.depth] at hP
      have := Nat.le_max_left A.depth B.depth; omega
    have hB : B.depth ≤ 1 := by
      simp only [EMLTree.depth] at hP
      have := Nat.le_max_right A.depth B.depth; omega
    exact h A B Q hA hB hQ K XK hK

/-- **The small-right branch of the bounded cell, unconditionally.** When the approaching tree sits
at or below `1`, the gap to `exp (exp (P x))` is bounded below by `exp (−C − exp x)` outright.

Three inequalities, no case analysis and **no cap** — this holds for every `A`:

```
exp (−K − exp x) ≤ exp (P x)          `log (B x) ≤ exp x + K`, and `exp (A x) > 0`
exp (P x)        ≤ exp (exp (P x)) − 1 `one_add_le_exp` at `exp (P x)`
exp (exp (P x)) − 1 ≤ exp (exp (P x)) − Q x   the hypothesis `Q x ≤ 1`
```

**Why the first step is the whole content.** `exp (A x)` is dropped to `0`, so the only thing keeping
`exp (P x)` above the rung is the *ceiling on the right child's logarithm* — and
`depth_le_two_log_le_exp` caps that at `exp x + K`, exactly the scale the rung is written in. This is
the `C + exp x` rung being the right one again, seen from a third side: `V₂` sets how far
`−log (B x)` can drag the node down, and the rung was corrected to `exp x` precisely to cover it. -/
theorem expexp_gap_of_right_le_one (A B Q : EMLTree) (hB : B.depth ≤ 1) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → Q.eval x ≤ 1 →
      exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  obtain ⟨K', X₁, hX₁, hlog⟩ := depth_le_two_log_le_exp B (by omega)
  refine ⟨K', X₁, hX₁, ?_⟩
  intro x hx hQ1
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  -- 1. the node cannot be dragged below `−K' − exp x`: only `−log (B x)` pushes down, and `V₂` caps it
  have hstep : -K' - exp x ≤ (EMLTree.eml A B).eval x := by
    rw [hval]
    have h1 : log (B.eval x) ≤ exp x + K' := hlog x hx
    have hneg : -(exp x + K') ≤ -log (B.eval x) := neg_le_neg_wit h1
    have hup : -log (B.eval x) ≤ exp (A.eval x) - log (B.eval x) := by
      have v := add_le_add_wit (le_of_lt (exp_pos (A.eval x))) (le_refl (-log (B.eval x)))
      have e1 : (0 : Real) + -log (B.eval x) = -log (B.eval x) := by mach_ring
      have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
        mach_mpoly [exp (A.eval x), log (B.eval x)]
      rw [e1, e2] at v; exact v
    have e3 : -K' - exp x = -(exp x + K') := by mach_mpoly [exp x, K']
    rw [e3]
    exact le_trans hneg hup
  have hu : exp (-K' - exp x) ≤ exp ((EMLTree.eml A B).eval x) := exp_monotone hstep
  -- 2. `1 + u ≤ exp u`, i.e. the target clears `1` by at least the node itself
  have hT : exp ((EMLTree.eml A B).eval x)
      ≤ exp (exp ((EMLTree.eml A B).eval x)) - 1 := by
    have h := one_add_le_exp (exp ((EMLTree.eml A B).eval x))
    have v := add_le_add_wit h (le_refl (-1 : Real))
    have e1 : (1 : Real) + exp ((EMLTree.eml A B).eval x) + -1
        = exp ((EMLTree.eml A B).eval x) := by
      mach_mpoly [exp ((EMLTree.eml A B).eval x)]
    have e2 : exp (exp ((EMLTree.eml A B).eval x)) + (-1 : Real)
        = exp (exp ((EMLTree.eml A B).eval x)) - 1 := by
      mach_ring
    rw [e1, e2] at v; exact v
  -- 3. `Q x ≤ 1` turns the `−1` into `−Q x`
  have hQ : exp (exp ((EMLTree.eml A B).eval x)) - 1
      ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
    have hneg : -(1 : Real) ≤ -Q.eval x := neg_le_neg_wit hQ1
    have v := add_le_add_left hneg (exp (exp ((EMLTree.eml A B).eval x)))
    have e1 : exp (exp ((EMLTree.eml A B).eval x)) + -(1 : Real)
        = exp (exp ((EMLTree.eml A B).eval x)) - 1 := by mach_ring
    have e2 : exp (exp ((EMLTree.eml A B).eval x)) + -Q.eval x
        = exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
      mach_mpoly [exp (exp ((EMLTree.eml A B).eval x)), Q.eval x]
    rw [e1, e2] at v; exact v
  exact le_trans hu (le_trans hT hQ)

/-- **The bounded cell, discharged wherever its target is constant.**

Reached by trying to *falsify* `BoundedEmlCellApproachLarge` rather than prove it — the family has
form, since `Depth3DecayHard` in this same file was a false conjecture. The cheapest corner to break
is a constant target: take `A` and `B` constant, so `exp (exp (eml A B))` is a fixed `V > 1`, and ask
whether some depth-≤2 `Q` can crawl up to `V` faster than `exp (−C − exp x)`.

It cannot, and `depth_le_two_gap_below` already says so: below any **constant** `k`, a depth-≤2 tree
sits below it by a *uniform* `ε`. A uniform constant beats `exp (−C − exp x)` for free, because
`exp_surj` names a `C` with `exp (−C) = ε` and `exp (−exp x) ≤ 1` does the rest. So the corner is
evidence *for* the conjecture, not against it.

**What this localises.** The obligation's difficulty is not that the target is bounded — it is that
the target MOVES. `1 < T ≤ exp K` follows from `u ≤ K` and `u > 0`, so `T` lives in a fixed band; but
`depth_le_two_gap_below` needs a constant `k`, and no uniform `ε` survives `k` sliding toward `Q x`.
Everything else in the bounded cell is already available.

Stated on the target rather than on `A` and `B` because that is the honest hypothesis: constant
children are merely the easiest way to satisfy it. -/
theorem boundedEmlCellApproachLarge_const_target
    (A B Q : EMLTree) (hQ : Q.depth ≤ 2) (V : Real)
    (hT : ∀ x : Real, 1 ≤ x → exp (exp ((EMLTree.eml A B).eval x)) = V) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  obtain ⟨ε, X₁, hε, hX₁, hgap⟩ := depth_le_two_gap_below Q hQ V
  obtain ⟨y, hy⟩ := exp_surj ε hε
  refine ⟨-y, X₁, hX₁, ?_⟩
  intro x hx _ hlt
  have hx1 : (1 : Real) ≤ x := le_trans hX₁ hx
  rw [hT x hx1] at hlt ⊢
  refine le_trans ?_ (hgap x hx hlt)
  have e : -(-y) - exp x = y + -(exp x) := by mach_ring
  rw [e, exp_add, hy]
  have hnp : -(exp x) ≤ 0 := by
    have v := neg_le_neg_wit (le_of_lt (exp_pos x))
    have z : -(0 : Real) = 0 := by mach_ring
    rw [z] at v; exact v
  have hle := mul_le_mul_of_nonneg_left (exp_le_one_of_nonpos hnp) (le_of_lt hε)
  have one : ε * (1 : Real) = ε := by mach_ring
  rw [one] at hle; exact hle

/-- The constant-target hypothesis is inhabited: constant children give one. Recorded so the lemma
above is not a statement about the empty set. -/
theorem const_target_of_const_children (α b : Real) (x : Real) :
    exp (exp ((EMLTree.eml (EMLTree.const α) (EMLTree.const b)).eval x))
      = exp (exp (exp α - log b)) := rfl

/-- **The cap already names `A`'s shape, before any analysis of the gap.**

`BoundedEmlCellApproachLarge`'s hypothesis is a cap on `exp (eml A B)`, and a cap on an exponential
is a cap on its argument for free: `self_le_exp` gives `(eml A B) x ≤ exp ((eml A B) x) ≤ K`, with no
`log` and no positivity side-condition. That is exactly the input
`depth_le_two_bounded_left_exp_bounded` consumes, so the obligation's own hypothesis forces
`exp (A x)` bounded, and `depth_le_one_exp_bounded_forms` then leaves **two** shapes for `A` where the
statement admits five.

**Why this is worth recording separately.** The obligation is stated for arbitrary depth-≤1 `A`, and
the circularity noted below is a fact about the *conversion* route — reverse convexity against
`exponent_gap_of_value_gap` — not about the obligation. Those two theorems are inverses, so no
further conversion helps; but a conversion is not the only move available, and the hypothesis had
never been mined for structure. `A` constant and `A = c − log x` are different enough functions that
the surviving cases can be attacked separately rather than uniformly.

Not itself progress on the bound. It is the narrowing that says which two problems the bound is. -/
theorem boundedEmlCell_left_forms (A B : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (K XK : Real) (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K) :
    (∃ α : Real, ∀ x : Real, 0 < x → A.eval x = α)
    ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → A.eval x = c - log x) := by
  have hbnd : ∀ x : Real, XK ≤ x → 1 ≤ x → exp (A.eval x) - log (B.eval x) ≤ K := by
    intro x hx _
    have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
    have h2 := le_trans (self_le_exp ((EMLTree.eml A B).eval x)) (hK x hx)
    rw [hval] at h2; exact h2
  obtain ⟨Kb, hKb⟩ := depth_le_two_bounded_left_exp_bounded A B hA hB K XK hbnd
  exact depth_le_one_exp_bounded_forms A hA Kb hKb

/-- **A cap on a ray already thins the admissible targets to two kinds.**

The filter-before-enumeration step for `BoundedEmlCellApproachLarge`'s `1 < Q x` branch. `Q` there is
squeezed into `(1, exp K]` — below the target and above `1` — and a compact window is a strong
hypothesis, not a weak one. Applied *before* any classification it removes most of the grammar:

* `var` cannot stay under a cap at all. Witness `1 + exp XM + exp M`, which clears `XM` and `1` and
  strictly exceeds `M` by `self_le_exp` on each summand — the file's usual division-free maximum.
* `eml P R` inherits `depth_le_two_bounded_left_exp_bounded` directly, because `(eml P R).eval` *is*
  `exp (P x) − log (R x)`, so the cap is already that theorem's hypothesis. Its left child is then
  constant or `c − log x`.
* `const` is the remaining case and is already constant.

So an admissible target is a constant tree, or an `eml` node whose left child is one of **two**
shapes — the same pair `boundedEmlCell_left_forms` extracts for `A`, reached by the same route from
the other side. The pair analysis the bounded cell needs is therefore finite in both coordinates.

**Deliberately says nothing about `R`.** Bounding `log (R x)` needs the lower bound `1 < Q x` as well
as the cap, and that is a separate step with a separate hypothesis; folding it in here would produce
a lemma that cannot be reused by a caller holding only a cap. -/
theorem bounded_ray_depth_two_left_forms (Q : EMLTree) (hQ : Q.depth ≤ 2) (M XM : Real)
    (hcap : ∀ x : Real, XM ≤ x → 1 ≤ x → Q.eval x ≤ M) :
    (∃ v : Real, ∀ x : Real, 0 < x → Q.eval x = v)
    ∨ (∃ P R : EMLTree, Q = EMLTree.eml P R ∧ P.depth ≤ 1 ∧ R.depth ≤ 1 ∧
        ((∃ α : Real, ∀ x : Real, 0 < x → P.eval x = α)
          ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → P.eval x = c - log x))) := by
  cases Q with
  | const c => exact Or.inl ⟨c, fun _ _ => rfl⟩
  | var =>
    exfalso
    -- `1 + exp XM + exp M` clears `XM` and `1`, and strictly beats `M`.
    have hXM : XM ≤ 1 + exp XM + exp M := by
      have v : (0 : Real) + exp XM + 0 ≤ 1 + exp XM + exp M :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
          (le_of_lt (exp_pos M))
      have e : (0 : Real) + exp XM + 0 = exp XM := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp XM) v
    have hone : (1 : Real) ≤ 1 + exp XM + exp M := by
      have v : (1 : Real) + 0 + 0 ≤ 1 + exp XM + exp M :=
        add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XM)))
          (le_of_lt (exp_pos M))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    have hgt : M < 1 + exp XM + exp M := by
      have v : (0 : Real) + 0 + exp M < 1 + exp XM + exp M := by
        have w := add_lt_add_left (add_lt_add_left (exp_pos XM) (1 : Real)) (exp M)
        have l : exp M + (1 + 0) = 0 + 0 + exp M + 1 := by mach_ring
        have r : exp M + (1 + exp XM) = 1 + exp XM + exp M := by mach_ring
        rw [l, r] at w
        have w2 := add_lt_add_left zero_lt_one_ax (0 + 0 + exp M)
        have l2 : (0 : Real) + 0 + exp M + 0 = 0 + 0 + exp M := by mach_ring
        rw [l2] at w2
        exact lt_trans_ax w2 w
      have e : (0 : Real) + 0 + exp M = exp M := by mach_ring
      rw [e] at v; exact lt_of_le_of_lt (self_le_exp M) v
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt (hcap _ hXM hone))
  | eml P R =>
    have hP : P.depth ≤ 1 := by
      simp only [EMLTree.depth] at hQ
      have := Nat.le_max_left P.depth R.depth; omega
    have hR : R.depth ≤ 1 := by
      simp only [EMLTree.depth] at hQ
      have := Nat.le_max_right P.depth R.depth; omega
    obtain ⟨Kb, hKb⟩ := depth_le_two_bounded_left_exp_bounded P R hP hR M XM hcap
    exact Or.inr ⟨P, R, rfl, hP, hR, depth_le_one_exp_bounded_forms P hP Kb hKb⟩

/-- **Both children, from the two hypotheses the bounded cell already carries.**

`bounded_ray_depth_two_left_forms` uses only the cap and so says nothing about `R`. The `1 < Q x`
branch of `BoundedEmlCellApproachLarge` carries a *lower* bound too, and that is exactly what the
right child needs: from `1 < exp (P x) − log (R x)` comes `log (R x) < exp (P x) − 1 ≤ Kb − 1`, an
upper bound on a logarithm on a ray, which is `depth_le_one_log_bounded_forms_from`'s hypothesis.

**Consequence — the remaining cell is a finite pair analysis.** An admissible `Q` is a constant tree,
or `eml P R` with *each* child in the same two-element family `{const, c − log x}`. Together with
`boundedEmlCell_left_forms` doing the same for `A`, the open branch ranges over

    {2 shapes for A} × ({constant} ∪ {2 shapes for P} × {2 shapes for R})

and nothing else. That is a search, not an asymptotic argument, and it is the reason to enumerate
before conjecturing a general moving-target gap principle.

**No counterexample is claimed or refuted here.** This bounds the space a counterexample could live
in; it does not say the space is empty. The `c − log x` right child in particular is *not* discarded
on the grounds that it goes negative far out on the ray — `log` of a nonpositive argument is whatever
this base makes it, and an elimination that leaned on informal analysis there would be exactly the
kind of step this corpus does not accept. -/
theorem bounded_ray_depth_two_both_forms (Q : EMLTree) (hQ : Q.depth ≤ 2) (M XM : Real)
    (hcap : ∀ x : Real, XM ≤ x → 1 ≤ x → Q.eval x ≤ M)
    (hlo : ∀ x : Real, XM ≤ x → 1 ≤ x → 1 < Q.eval x) :
    (∃ v : Real, ∀ x : Real, 0 < x → Q.eval x = v)
    ∨ (∃ P R : EMLTree, Q = EMLTree.eml P R
        ∧ ((∃ α : Real, ∀ x : Real, 0 < x → P.eval x = α)
            ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → P.eval x = c - log x))
        ∧ ((∃ β : Real, ∀ x : Real, 0 < x → R.eval x = β)
            ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → R.eval x = c - log x))) := by
  rcases bounded_ray_depth_two_left_forms Q hQ M XM hcap with hconst | ⟨P, R, rfl, hP, hR, hPform⟩
  · exact Or.inl hconst
  obtain ⟨Kb, hKb⟩ := depth_le_two_bounded_left_exp_bounded P R hP hR M XM hcap
  refine Or.inr ⟨P, R, rfl, hPform, ?_⟩
  refine depth_le_one_log_bounded_forms_from R hR XM (Kb - 1) ?_
  intro x hxS hx1
  -- `1 < exp (P x) − log (R x)` gives `log (R x) < exp (P x) − 1`
  have hgt : (1 : Real) < exp (P.eval x) - log (R.eval x) := hlo x hxS hx1
  have hstep := add_lt_add_left hgt (log (R.eval x))
  have hl : log (R.eval x) + 1 = 1 + log (R.eval x) := by mach_ring
  have hr : log (R.eval x) + (exp (P.eval x) - log (R.eval x)) = exp (P.eval x) := by
    mach_mpoly [exp (P.eval x), log (R.eval x)]
  rw [hl, hr] at hstep
  -- and `exp (P x) ≤ Kb` caps it
  have hcapx : (1 : Real) + log (R.eval x) ≤ Kb := le_of_lt (lt_of_lt_of_le hstep (hKb x hx1))
  have hsub := add_le_add_wit hcapx (le_refl (-(1 : Real)))
  have hl2 : (1 : Real) + log (R.eval x) + -1 = log (R.eval x) := by
    mach_mpoly [log (R.eval x)]
  have hr2 : Kb + -(1 : Real) = Kb - 1 := by mach_mpoly [Kb]
  rw [hl2, hr2] at hsub; exact hsub

/-- **The target never gets doubly-exponentially close to `1`.** The scale fact behind the whole
bounded cell, and the reason a counterexample search over the surviving shapes finds nothing.

`depth_le_one_log_le_linear` caps a depth-≤1 logarithm at `x + C`. With `exp (A x) > 0` that gives
`(eml A B) x ≥ −x − C`, so `u = exp ((eml A B) x) ≥ exp (−x − C)`, and `1 + u ≤ exp u` finishes:

    exp (exp ((eml A B) x)) − 1  ≥  exp (−x − C)

**Why this settles the falsification question rather than merely decorating it.** The obligation asks
for a floor of `exp (−C − exp x)` — *doubly* exponentially small. Every scale this grammar can build
is at worst *singly* exponential, and this lemma is where that ceiling comes from: `log (B x)` cannot
grow faster than linearly, so the node cannot fall faster than `−x`, so the target cannot approach
its limit faster than `e^{−x}`. A gap that decays like `e^{−kx}` for any `k` still clears
`exp (−C − exp x)` with room to spare.

**No `A` hypothesis.** Only positivity of `exp (A x)` is used, so this holds for every depth of `A` —
the constraint that matters is entirely on the right child. Stated that way because the caller in the
bounded cell has `A` restricted to two shapes and does not need to spend them here. -/
theorem target_above_one_singly_exponential (A B : EMLTree) (hB : B.depth ≤ 1) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x →
      exp (-x - C) ≤ exp (exp ((EMLTree.eml A B).eval x)) - 1 := by
  obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B hB
  refine ⟨C, ?_⟩
  intro x hx1
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  have hE : -x - C ≤ (EMLTree.eml A B).eval x := by
    rw [hval]
    have v := add_le_add_wit (le_of_lt (exp_pos (A.eval x))) (neg_le_neg_wit (hC x hx1))
    have l : (0 : Real) + -(x + C) = -x - C := by mach_mpoly [x, C]
    have r : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
      mach_mpoly [exp (A.eval x), log (B.eval x)]
    rw [l, r] at v; exact v
  have hu : exp (-x - C) ≤ exp ((EMLTree.eml A B).eval x) := exp_monotone hE
  have hT := one_add_le_exp (exp ((EMLTree.eml A B).eval x))
  have hstep := add_le_add_wit hu (le_refl (0 : Real))
  have hchain : 1 + exp (-x - C) ≤ exp (exp ((EMLTree.eml A B).eval x)) :=
    le_trans (add_le_add_wit (le_refl (1 : Real)) hu) hT
  have hsub := add_le_add_wit hchain (le_refl (-(1 : Real)))
  have l2 : (1 : Real) + exp (-x - C) + -1 = exp (-x - C) := by mach_mpoly [exp (-x - C)]
  have r2 : exp (exp ((EMLTree.eml A B).eval x)) + -(1 : Real)
      = exp (exp ((EMLTree.eml A B).eval x)) - 1 := by
    mach_mpoly [exp (exp ((EMLTree.eml A B).eval x))]
  rw [l2, r2] at hsub; exact hsub

/-- `x² ≤ exp (exp x)` on `[1,∞)`. Two applications of `self_le_exp` and one of `two_mul_le_exp`. -/
theorem sq_le_exp_exp {x : Real} (hx : 1 ≤ x) : x * x ≤ exp (exp x) := by
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx
  have h1 : x * x ≤ exp x * x := mul_le_mul_of_nonneg_right (self_le_exp x) hx0
  have h2 : exp x * x ≤ exp x * exp x :=
    mul_le_mul_of_nonneg_left (self_le_exp x) (le_of_lt (exp_pos x))
  have h3 : exp x * exp x = exp (x + x) := (exp_add x x).symm
  rw [h3] at h2
  exact le_trans (le_trans h1 h2) (exp_monotone (two_mul_le_exp hx0))

/-- **Any inverse-square floor beats the doubly exponential one, and `C` is free to choose.**

The obligation's floor `exp (−C − exp x)` is existentially quantified in `C`, so a caller that has
established *any* separation of order `1/x²` can pick `C` and be done. This is the step that makes
the whole bounded-cell analysis collapse: the census showed the surviving gaps are `Θ(1/x)`
generically and `Θ(1/x²)` on the cancellation locus, and both are astronomically larger than what is
being asked for — at `x = 1000` the floor is around `10^(−4.3 × 10^433)`.

Division-free by construction: stated as `floor · x² ≤ β` rather than `floor ≤ β/x²`, so it needs no
reciprocal lemmas and composes by `mul_le_mul_of_nonneg_*` at the call site. `exp_surj` names the `C`
with `exp (−C) = β`; the rest is `x² ≤ exp (exp x)` against `exp (−exp x)`. -/
theorem double_exp_floor_dominated (β : Real) (hβ : 0 < β) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → exp (-C - exp x) * (x * x) ≤ β := by
  obtain ⟨y, hy⟩ := exp_surj β hβ
  refine ⟨-y, ?_⟩
  intro x hx
  have e : -(-y) - exp x = y + -(exp x) := by mach_ring
  rw [e, exp_add, hy]
  have hmul : exp (-(exp x)) * (x * x) ≤ exp (-(exp x)) * exp (exp x) :=
    mul_le_mul_of_nonneg_left (sq_le_exp_exp hx) (le_of_lt (exp_pos (-(exp x))))
  have hone : exp (-(exp x)) * exp (exp x) = 1 := by
    rw [← exp_add]
    have z : -(exp x) + exp x = 0 := by mach_ring
    rw [z, exp_zero]
  rw [hone] at hmul
  have hassoc : β * exp (-(exp x)) * (x * x) = β * (exp (-(exp x)) * (x * x)) := by
    mach_ring
  rw [hassoc]
  have hstep := mul_le_mul_of_nonneg_left hmul (le_of_lt hβ)
  have hb : β * (1 : Real) = β := by mach_ring
  rw [hb] at hstep; exact hstep

/-- **The one surviving moving target, in closed form: `L + a·(1/x)` with `a > 0`.**

After `bounded_ray_depth_two_both_forms` and `log_nonpos`, exactly one nonconstant `Q` shape reaches
the bounded cell: left child `c − log x`, right child a positive constant. `exp_c_sub_log_eq` turns
it into `exp c · (1/x) + (−log β)` — a positive multiple of `1/x` above a constant floor.

**This is what replaces the asymptotic expansion.** The census measured `Θ(1/x)` separation
generically and `Θ(1/x²)` on the cancellation locus; those were reconnaissance. With the closed form
in hand the comparison against a target becomes an inequality between explicit terms, and
`double_exp_floor_dominated` converts any inverse-square separation into the obligation's floor. No
Taylor theorem and no `o(·)` notation enters the Lean argument at any point.

The other three `P`/`R` combinations do not survive: `R = c − log x` totalizes to `log (R x) = 0` by
`log_nonpos`, leaving `Q = exp (P x)`, which is either constant or `e^{c_P}/x → 0` and so violates
`1 < Q x`. -/
theorem moving_Q_eventual_form (P R : EMLTree) (c β : Real)
    (hP : ∀ x : Real, 0 < x → P.eval x = c - log x)
    (hR : ∀ x : Real, 0 < x → R.eval x = β) :
    ∀ x : Real, 0 < x →
      (EMLTree.eml P R).eval x = -(log β) + exp c * (1 / x) := by
  intro x hx
  have hval : (EMLTree.eml P R).eval x = exp (P.eval x) - log (R.eval x) := rfl
  rw [hval, hP x hx, hR x hx, exp_c_sub_log_eq c hx]
  mach_mpoly [exp c, (1 / x : Real), log β]

/-- The coefficient of `1/x` in `moving_Q_eventual_form` is strictly positive, so the surviving
target descends to its floor rather than rising to it. Recorded separately because the sign is what
makes the comparison a *separation* rather than a collision. -/
theorem moving_Q_coefficient_pos (c : Real) : 0 < exp c := exp_pos c

/-- **A constant barrier between the two is enough; the target may move freely above it.**

`boundedEmlCellApproachLarge_const_target` asked for a *constant* target. Its proof never used that:
what it consumed was a fixed `k` with `Q x < k ≤ T x`. Stating the weaker hypothesis turns a corner
case into the generic tool, and the target becomes an arbitrary function — no depth bound, no
tree — because nothing about it is inspected beyond the barrier.

**How the moving case reaches it.** When the target and `Q` converge to *different* limits, any `k`
strictly between them is such a barrier eventually, so the whole different-limits regime collapses to
this lemma and yields a **uniform** `ε`, far more than the obligation asks. Only equal limits need
first- and second-order work, which is where the cancellation locus lives.

`depth_le_two_gap_below` supplies the uniform `ε` below `k`; `exp_surj` converts it to the floor by
naming `C` with `exp (−C) = ε`; `exp (−exp x) ≤ 1` does the rest. Thresholds merge as
`1 + exp X₁ + exp X₂` — the division-free maximum. -/
theorem gap_below_constant_barrier (Q : EMLTree) (hQ : Q.depth ≤ 2) (f : Real → Real)
    (k X₁ : Real) (hbar : ∀ x : Real, X₁ ≤ x → k ≤ f x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → Q.eval x < k →
      exp (-C - exp x) ≤ f x - Q.eval x := by
  obtain ⟨ε, X₂, hε, hX₂, hgap⟩ := depth_le_two_gap_below Q hQ k
  obtain ⟨y, hy⟩ := exp_surj ε hε
  refine ⟨-y, 1 + exp X₁ + exp X₂, ?_, ?_⟩
  · have v : (1 : Real) + 0 + 0 ≤ 1 + exp X₁ + exp X₂ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos X₁)))
        (le_of_lt (exp_pos X₂))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx hlt
  have hX₁x : X₁ ≤ x := by
    have v : (0 : Real) + exp X₁ + 0 ≤ 1 + exp X₁ + exp X₂ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos X₂))
    have e : (0 : Real) + exp X₁ + 0 = exp X₁ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp X₁) (le_trans v hx)
  have hX₂x : X₂ ≤ x := by
    have v : (0 : Real) + 0 + exp X₂ ≤ 1 + exp X₁ + exp X₂ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos X₁)))
        (le_refl _)
    have e : (0 : Real) + 0 + exp X₂ = exp X₂ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp X₂) (le_trans v hx)
  -- ε below the barrier, and the barrier below the target
  have hεk : ε ≤ k - Q.eval x := hgap x hX₂x hlt
  have hkf : k - Q.eval x ≤ f x - Q.eval x := by
    have v := add_le_add_wit (hbar x hX₁x) (le_refl (-(Q.eval x)))
    have l : k + -(Q.eval x) = k - Q.eval x := by mach_mpoly [k, Q.eval x]
    have r : f x + -(Q.eval x) = f x - Q.eval x := by mach_mpoly [f x, Q.eval x]
    rw [l, r] at v; exact v
  refine le_trans ?_ (le_trans hεk hkf)
  have e : -(-y) - exp x = y + -(exp x) := by mach_ring
  rw [e, exp_add, hy]
  have hnp : -(exp x) ≤ 0 := by
    have v := neg_le_neg_wit (le_of_lt (exp_pos x))
    have z : -(0 : Real) = 0 := by mach_ring
    rw [z] at v; exact v
  have hle := mul_le_mul_of_nonneg_left (exp_le_one_of_nonpos hnp) (le_of_lt hε)
  have one : ε * (1 : Real) = ε := by mach_ring
  rw [one] at hle; exact hle

/-- The constant-target cell is the barrier lemma at `k := V`. Recorded as a check that the
generalisation is faithful rather than merely wider. -/
example (A B Q : EMLTree) (hQ : Q.depth ≤ 2) (V : Real)
    (hT : ∀ x : Real, 1 ≤ x → exp (exp ((EMLTree.eml A B).eval x)) = V) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → Q.eval x < V →
      exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x :=
  gap_below_constant_barrier Q hQ (fun x => exp (exp ((EMLTree.eml A B).eval x))) V 1
    (fun x hx => le_of_eq (hT x hx).symm)

/-- **`exp` outruns a line of ANY slope, on a whole ray.**

`exp_beats_linear` and `exp_beats_linear_past` produce a *point* where `exp` is ahead. A point
suffices to contradict a universally quantified hypothesis, which is what they are used for
throughout this file. It is **not** enough to show a region is eventually empty, and that is what a
vacuity argument needs.

The shift supplies the missing form. `two_mul_le_exp` gives slope `2` from `0`, and
`exp x = exp (x − S) · exp S` promotes it to slope `exp S` past `2S`:

    x ≤ 2(x − S) ≤ exp (x − S)   ⟹   x · exp S ≤ exp x     for x ≥ S + S

Taking `S := exp m` makes `exp S ≥ m` by two applications of `self_le_exp`, so any slope is reached
with no case split on the sign of `m` and no maximum. -/
theorem exp_ge_mul_shift {S x : Real} (hS : 0 ≤ S) (hx : S + S ≤ x) : x * exp S ≤ exp x := by
  have hSS : S ≤ S + S := by
    have v := add_le_add_wit (le_refl S) hS
    have e : S + (0 : Real) = S := by mach_ring
    rw [e] at v; exact v
  have hxS : (0 : Real) ≤ x - S := by
    have v := add_le_add_wit (le_trans hSS hx) (le_refl (-S))
    have l : S + -S = 0 := by mach_ring
    have r : x + -S = x - S := by mach_mpoly [x, S]
    rw [l, r] at v; exact v
  have hlin : x ≤ (x - S) + (x - S) := by
    have v := add_le_add_wit hx (le_refl (x - S - S))
    have l : S + S + (x - S - S) = x := by mach_mpoly [x, S]
    have r : x + (x - S - S) = (x - S) + (x - S) := by mach_mpoly [x, S]
    rw [l, r] at v; exact v
  have hmul := mul_le_mul_of_nonneg_right (le_trans hlin (two_mul_le_exp hxS))
    (le_of_lt (exp_pos S))
  have hsplit : exp (x - S) * exp S = exp x := by
    rw [← exp_add]
    have e : x - S + S = x := by mach_mpoly [x, S]
    rw [e]
  rw [hsplit] at hmul; exact hmul

/-- The ∀-form this file did not have: past a threshold, `exp` dominates `m · x` for every slope. -/
theorem exp_beats_linear_eventually (m : Real) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → m * x ≤ exp x := by
  have hS : (0 : Real) ≤ exp m := le_of_lt (exp_pos m)
  refine ⟨1 + exp m + exp m, ?_, ?_⟩
  · have v : (1 : Real) + 0 + 0 ≤ 1 + exp m + exp m :=
      add_le_add_wit (add_le_add_wit (le_refl 1) hS) hS
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx
  have hshift : exp m + exp m ≤ x := by
    have v : (0 : Real) + exp m + exp m ≤ 1 + exp m + exp m :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)) (le_refl _)
    have e : (0 : Real) + exp m + exp m = exp m + exp m := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hx0 : (0 : Real) ≤ x := by
    have v := add_le_add_wit hS hS
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at v; exact le_trans v hshift
  have hm : m ≤ exp (exp m) := le_trans (self_le_exp m) (self_le_exp (exp m))
  have h1 := mul_le_mul_of_nonneg_right hm hx0
  have hcomm : exp (exp m) * x = x * exp (exp m) := by mach_ring
  rw [hcomm] at h1
  exact le_trans h1 (exp_ge_mul_shift hS hshift)

/-! ## ▸ The linear LOWER bound on a depth-≤1 logarithm

`depth_le_one_log_le_linear` caps `log (B x)` at `x + C`. The `T → 1` regime needs the opposite
direction for the two `exp`-shaped forms, and `depth_le_one_log_lower_at_infinity` supplies only a
**constant** floor. These three close that gap.

The whole argument rests on `exp 1 ≥ 2`, which is `one_add_le_exp 1`. -/

/-- `exp (x−1) ≤ exp x − exp (x−1)`: one step back costs at least half, because `exp 1 ≥ 2`. -/
theorem exp_pred_le_exp_sub_exp_pred (x : Real) : exp (x - 1) ≤ exp x - exp (x - 1) := by
  have he : exp x = exp (x - 1) * exp 1 := by
    rw [← exp_add]
    have e : x - 1 + 1 = x := by mach_ring
    rw [e]
  have hge : (1 : Real) ≤ exp 1 - 1 := by
    have v := add_le_add_wit (one_add_le_exp 1) (le_refl (-(1 : Real)))
    have l : (1 : Real) + 1 + -1 = 1 := by mach_ring
    have r : exp 1 + -(1 : Real) = exp 1 - 1 := by mach_mpoly [exp 1]
    rw [l, r] at v; exact v
  have hmul := mul_le_mul_of_nonneg_left hge (le_of_lt (exp_pos (x - 1)))
  have l2 : exp (x - 1) * (1 : Real) = exp (x - 1) := by mach_ring
  have r2 : exp (x - 1) * (exp 1 - 1) = exp (x - 1) * exp 1 - exp (x - 1) := by
    mach_mpoly [exp (x - 1), exp 1]
  rw [l2, r2, ← he] at hmul; exact hmul

/-- Monotonicity of the totalized `log`, in the only direction needed here. -/
theorem log_ge_sub_one_of_exp_pred_le {x z : Real} (h : exp (x - 1) ≤ z) : x - 1 ≤ log z := by
  rcases (le_iff_lt_or_eq (exp (x - 1)) z).mp h with hlt | heq
  · have hv := log_lt_log (exp_pos (x - 1)) hlt
    rw [log_exp] at hv; exact le_of_lt hv
  · rw [← heq, log_exp]; exact le_refl _

/-- **`log (exp x − d) ≥ x − 1`, past `d + 1`.** The subtracted constant is absorbed by one step
back: `exp x − exp (x−1) ≥ exp (x−1) ≥ x − 1 ≥ d`. -/
theorem log_exp_sub_const_ge_linear (d : Real) {x : Real} (hx : d + 1 ≤ x) :
    x - 1 ≤ log (exp x - d) := by
  refine log_ge_sub_one_of_exp_pred_le ?_
  have hd : d ≤ x - 1 := by
    have v := add_le_add_wit hx (le_refl (-(1 : Real)))
    have l : d + 1 + -1 = d := by mach_ring
    have r : x + -(1 : Real) = x - 1 := by mach_mpoly [x]
    rw [l, r] at v; exact v
  have hchain : d ≤ exp x - exp (x - 1) :=
    le_trans hd (le_trans (self_le_exp (x - 1)) (exp_pred_le_exp_sub_exp_pred x))
  have v := add_le_add_wit hchain (le_refl (exp (x - 1) - exp x))
  have l : d + (exp (x - 1) - exp x) = exp (x - 1) - (exp x - d) := by
    mach_mpoly [d, exp x, exp (x - 1)]
  have r : exp x - exp (x - 1) + (exp (x - 1) - exp x) = 0 := by
    mach_mpoly [exp x, exp (x - 1)]
  rw [l, r] at v
  have w := add_le_add_wit v (le_refl (exp x - d))
  have l2 : exp (x - 1) - (exp x - d) + (exp x - d) = exp (x - 1) := by
    mach_mpoly [exp x, exp (x - 1), d]
  have r2 : (0 : Real) + (exp x - d) = exp x - d := by mach_ring
  rw [l2, r2] at w; exact w

/-- **`log (exp x − log x) ≥ x − 1` on `[1,∞)`.** Same step, with `log x ≤ x − 1` doing the
absorbing instead of a constant. -/
theorem log_exp_sub_log_ge_linear {x : Real} (hx : 1 ≤ x) : x - 1 ≤ log (exp x - log x) := by
  refine log_ge_sub_one_of_exp_pred_le ?_
  have hchain : log x ≤ exp x - exp (x - 1) :=
    le_trans (log_le_sub_one_of_one_le hx)
      (le_trans (self_le_exp (x - 1)) (exp_pred_le_exp_sub_exp_pred x))
  have v := add_le_add_wit hchain (le_refl (exp (x - 1) - exp x))
  have l : log x + (exp (x - 1) - exp x) = exp (x - 1) - (exp x - log x) := by
    mach_mpoly [log x, exp x, exp (x - 1)]
  have r : exp x - exp (x - 1) + (exp (x - 1) - exp x) = 0 := by
    mach_mpoly [exp x, exp (x - 1)]
  rw [l, r] at v
  have w := add_le_add_wit v (le_refl (exp x - log x))
  have l2 : exp (x - 1) - (exp x - log x) + (exp x - log x) = exp (x - 1) := by
    mach_mpoly [exp x, exp (x - 1), log x]
  have r2 : (0 : Real) + (exp x - log x) = exp x - log x := by mach_ring
  rw [l2, r2] at w; exact w

/-- **With the right child `exp`-shaped, the target falls to `1` at a singly exponential rate.**

The mirror of `target_above_one_singly_exponential`, and the second half of the scale sandwich. That
lemma used `depth_le_one_log_le_linear` to keep the target *above* `1 + e^{−x−C}`; this one uses the
new linear *lower* bound on `log (B x)` to keep it *below* `1 + D·e^{−x}`.

    log (B x) ≥ x − 1   ⟹   (eml A B) x ≤ (Kb + 1) − x
                        ⟹   u = exp ((eml A B) x) ≤ e^{Kb+1}·e^{−x}
                        ⟹   T − 1 = exp u − exp 0 ≤ u·exp u ≤ D·e^{−x}

`exp_sub_exp_upper` at `v = 0` is what converts the exponent bound into a value bound, and it costs
only the factor `exp u`, which is bounded because `u` is.

**Why this matters.** The surviving moving `Q` sits at `L + a·(1/x)` with `a > 0`, so `Q − 1 ≥ a/x`
whenever `L ≥ 1`. A target that is within `D·e^{−x}` of `1` cannot stay above it, since `e^{−x}`
loses to `a/x`. That is the whole `T → 1` regime, and it is vacuous rather than hard.

**Stated on a ray `X ≥ 1`, not from `1`.** Both hypotheses arrive from tree classifications that
only hold eventually — `log_exp_sub_const_ge_linear` needs `d + 1 ≤ x`, and the router's node
enumeration hands back its log bound past an existential `XV`, never past `1`. Taking `X = 1`
recovers the original statement, and `1 ≤ X` is all the proof ever wanted from `1 ≤ x`. -/
theorem target_below_one_singly_exponential (A B : EMLTree) (Kb X : Real) (hX : 1 ≤ X)
    (hA : ∀ x : Real, X ≤ x → exp (A.eval x) ≤ Kb)
    (hB : ∀ x : Real, X ≤ x → x - 1 ≤ log (B.eval x)) :
    ∃ D : Real, 0 < D ∧ ∀ x : Real, X ≤ x →
      exp (exp ((EMLTree.eml A B).eval x)) - 1 ≤ D * exp (-x) := by
  refine ⟨exp (Kb + 1) * exp (exp (Kb + 1)), mul_pos (exp_pos _) (exp_pos _), ?_⟩
  intro x hxX
  have hx1 : (1 : Real) ≤ x := le_trans hX hxX
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  -- 1. the node is below `(Kb + 1) − x`
  have hnode : (EMLTree.eml A B).eval x ≤ Kb + 1 - x := by
    rw [hval]
    have v := add_le_add_wit (hA x hxX) (neg_le_neg_wit (hB x hxX))
    have l : Kb + -(x - 1) = Kb + 1 - x := by mach_mpoly [Kb, x]
    have r : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
      mach_mpoly [exp (A.eval x), log (B.eval x)]
    rw [l, r] at v; exact v
  -- 2. so `u` is below `e^{Kb+1}·e^{−x}`
  have hsplit : exp (Kb + 1 - x) = exp (Kb + 1) * exp (-x) := by
    rw [← exp_add]
    have e : Kb + 1 + -x = Kb + 1 - x := by mach_mpoly [Kb, x]
    rw [e]
  have hu : exp ((EMLTree.eml A B).eval x) ≤ exp (Kb + 1) * exp (-x) := by
    rw [← hsplit]; exact exp_monotone hnode
  -- 3. and `u` is bounded, so `exp u` is
  have hxpos : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hnegx : exp (-x) ≤ 1 := by
    refine exp_le_one_of_nonpos ?_
    have v := neg_le_neg_wit hxpos
    have z : -(0 : Real) = 0 := by mach_ring
    rw [z] at v; exact v
  have hub : exp ((EMLTree.eml A B).eval x) ≤ exp (Kb + 1) := by
    refine le_trans hu ?_
    have v := mul_le_mul_of_nonneg_left hnegx (le_of_lt (exp_pos (Kb + 1)))
    have e : exp (Kb + 1) * (1 : Real) = exp (Kb + 1) := by mach_ring
    rw [e] at v; exact v
  -- 4. `exp u − 1 ≤ u · exp u`
  have hgap : exp (exp ((EMLTree.eml A B).eval x)) - 1
      ≤ exp ((EMLTree.eml A B).eval x) * exp (exp ((EMLTree.eml A B).eval x)) := by
    have h := exp_sub_exp_upper (exp ((EMLTree.eml A B).eval x)) 0
    rw [exp_zero] at h
    have e : exp ((EMLTree.eml A B).eval x) - 0 = exp ((EMLTree.eml A B).eval x) := by
      mach_mpoly [exp ((EMLTree.eml A B).eval x)]
    rw [e] at h; exact h
  -- 5. bound each factor
  have hfac : exp ((EMLTree.eml A B).eval x) * exp (exp ((EMLTree.eml A B).eval x))
      ≤ (exp (Kb + 1) * exp (-x)) * exp (exp (Kb + 1)) := by
    refine le_trans (mul_le_mul_of_nonneg_right hu (le_of_lt (exp_pos _))) ?_
    exact mul_le_mul_of_nonneg_left (exp_monotone hub)
      (le_of_lt (mul_pos (exp_pos (Kb + 1)) (exp_pos (-x))))
  refine le_trans hgap (le_trans hfac (le_of_eq ?_))
  mach_mpoly [exp (Kb + 1), exp (-x), exp (exp (Kb + 1))]

/-- `x·e^{−x} ≤ η` past a threshold, for every `η > 0`. Immediate from
`exp_beats_linear_eventually` at slope `1/η`: that gives `x ≤ η·e^x`, and multiplying by `e^{−x}`
finishes. -/
theorem x_mul_exp_neg_eventually_small (η : Real) (hη : 0 < η) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → x * exp (-x) ≤ η := by
  obtain ⟨X₀, hX₀, h⟩ := exp_beats_linear_eventually (1 / η)
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx
  have h2 := mul_le_mul_of_nonneg_left (h x hx) (le_of_lt hη)
  have hinv : η * (1 / η) = 1 := mul_inv η (ne_of_gt hη)
  have l : η * (1 / η * x) = η * (1 / η) * x := by mach_ring
  rw [l, hinv] at h2
  have l2 : (1 : Real) * x = x := by mach_ring
  rw [l2] at h2
  have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt (exp_pos (-x)))
  have hee : exp x * exp (-x) = 1 := by
    rw [← exp_add]
    have z : x + -x = 0 := by mach_ring
    rw [z, exp_zero]
  have r : η * exp x * exp (-x) = η * (exp x * exp (-x)) := by mach_ring
  rw [r, hee] at h3
  have r2 : η * (1 : Real) = η := by mach_ring
  rw [r2] at h3; exact h3

/-- **The falling target's headroom loses to the moving target's excess.**

`D·e^{−x} ≤ a·(1/x)` eventually, for any `a, D > 0`. This is the arithmetic core of the `T → 1`
regime: `target_below_one_singly_exponential` puts the target within `D·e^{−x}` of `1`, while
`moving_Q_eventual_form` keeps `Q` at least `a·(1/x)` above `1` whenever its limit is `≥ 1`. Since
`e^{−x}` loses to `1/x`, the cell's hypothesis `Q x < T x` cannot hold far out, and the whole regime
is vacuous rather than difficult.

Non-strict suffices: `Q < T` yields `a/x < D·e^{−x}`, and `D·e^{−x} ≤ a/x` closes it. -/
theorem exp_neg_le_inv_of_pos (a D : Real) (ha : 0 < a) (hD : 0 < D) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → D * exp (-x) ≤ a * (1 / x) := by
  obtain ⟨X₀, hX₀, h⟩ := x_mul_exp_neg_eventually_small (a * (1 / D)) (mul_pos ha (one_div_pos_of_pos hD))
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx
  have hx1 : (1 : Real) ≤ x := le_trans hX₀ hx
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  -- D·x·e^{−x} ≤ D·(a/D) = a
  have h2 := mul_le_mul_of_nonneg_left (h x hx) (le_of_lt hD)
  have hinvD : D * (1 / D) = 1 := mul_inv D (ne_of_gt hD)
  have r : D * (a * (1 / D)) = a * (D * (1 / D)) := by mach_ring
  rw [r, hinvD] at h2
  have r2 : a * (1 : Real) = a := by mach_ring
  rw [r2] at h2
  -- multiply by 1/x
  have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt (one_div_pos_of_pos hxpos))
  have hinvx : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
  have l : D * (x * exp (-x)) * (1 / x) = D * exp (-x) * (x * (1 / x)) := by mach_ring
  rw [l, hinvx] at h3
  have l2 : D * exp (-x) * (1 : Real) = D * exp (-x) := by mach_ring
  rw [l2] at h3; exact h3

/-! ## ▸ Second-order convexity, for the cancellation locus

`exp_sub_exp_lower` is first order: `(u − v)·exp v ≤ exp u − exp v`. On the locus where the first
order terms cancel exactly, that bound gives `0` and says nothing. The census measured `Θ(1/x²)`
separation there, so a quadratic term is the missing analytic ingredient.

MachLib's `exp` is axiomatised without a series — `one_add_le_exp` is all the convexity there is. The
half-angle identity supplies the rest: `exp (z+z) = exp z · exp z ≥ (1+z)²`, which is a second-order
bound with coefficient `1` on `z²` rather than the series' `1/2`, and that is fine for a *lower*
bound. Parameterising by `z` with `y = z + z` keeps it division-free. -/

/-- `exp (z+z) ≥ 1 + (z+z) + z²` for `z ≥ 0`. The half-angle square of `one_add_le_exp`. -/
theorem exp_two_ge_quadratic {z : Real} (hz : 0 ≤ z) :
    1 + (z + z) + z * z ≤ exp (z + z) := by
  have h1 : (1 : Real) + z ≤ exp z := one_add_le_exp z
  have hnn : (0 : Real) ≤ 1 + z := by
    have v := add_le_add_wit (le_of_lt zero_lt_one_ax) hz
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at v; exact v
  have h2 : (1 + z) * (1 + z) ≤ exp z * (1 + z) := mul_le_mul_of_nonneg_right h1 hnn
  have h3 : exp z * (1 + z) ≤ exp z * exp z :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos z))
  have h4 : exp z * exp z = exp (z + z) := (exp_add z z).symm
  have h5 : (1 + z) * (1 + z) = 1 + (z + z) + z * z := by mach_ring
  rw [h4] at h3; rw [h5] at h2
  exact le_trans h2 h3

/-- **The second-order companion to `exp_sub_exp_lower`.**

    exp v · ((z+z) + z²)  ≤  exp (v + (z+z)) − exp v

Where the first-order term is cancelled by a competitor, this leaves `exp v · z²` — a positive
`Θ(1/x²)` separation when `z = Θ(1/x)`, which `double_exp_floor_dominated` then converts to the
obligation's floor. That is the intended route through the cancellation locus. -/
theorem exp_sub_exp_lower_quadratic (v : Real) {z : Real} (hz : 0 ≤ z) :
    exp v * ((z + z) + z * z) ≤ exp (v + (z + z)) - exp v := by
  have h2 := mul_le_mul_of_nonneg_left (exp_two_ge_quadratic hz) (le_of_lt (exp_pos v))
  have hsplit : exp v * exp (z + z) = exp (v + (z + z)) := (exp_add v (z + z)).symm
  rw [hsplit] at h2
  have hexp : exp v * (1 + (z + z) + z * z) = exp v + exp v * ((z + z) + z * z) := by
    mach_mpoly [exp v, z]
  rw [hexp] at h2
  have w := add_le_add_wit h2 (le_refl (-(exp v)))
  have l : exp v + exp v * ((z + z) + z * z) + -(exp v) = exp v * ((z + z) + z * z) := by
    mach_mpoly [exp v, z]
  have r : exp (v + (z + z)) + -(exp v) = exp (v + (z + z)) - exp v := by
    mach_mpoly [exp (v + (z + z)), exp v]
  rw [l, r] at w; exact w

/-- **The cancellation locus, in its purest form: when the linear term is exactly consumed, the
quadratic term is what is left over.**

    a ≤ exp v · (z+z)   ⟹   exp v · z²  ≤  exp (v + (z+z)) − exp v − a

Read `exp (v + (z+z)) − exp v` as the target's rise above its limit, and `a` as the competitor's. The
hypothesis says the target's *linear* term covers the competitor — including the boundary case where
it covers it **exactly**, which is the locus the census found. On that boundary the first-order
comparison returns `0` and says nothing; this returns `exp v · z²`, strictly positive.

With `z = Θ(1/x)` that is a `Θ(1/x²)` separation, and `double_exp_floor_dominated` carries it the
rest of the way to `exp (−C − exp x)`. **This is the branch the whole census was hunting, and it is
an inequality between four explicit terms — no expansion, no `o(·)`, no Taylor theorem.**

Division-free by keeping the half-increment `z` as the parameter rather than the increment `2z`; a
caller holding `d` supplies `z := d·(1/2)` at the call site, where the reciprocal is harmless. -/
theorem quadratic_separation_of_linear_dominance (v a : Real) {z : Real} (hz : 0 ≤ z)
    (hdom : a ≤ exp v * (z + z)) :
    exp v * (z * z) ≤ exp (v + (z + z)) - exp v - a := by
  have hq := exp_sub_exp_lower_quadratic v hz
  -- split the quadratic form's left side into linear + square
  have hsplit : exp v * ((z + z) + z * z) = exp v * (z + z) + exp v * (z * z) := by
    mach_mpoly [exp v, z]
  rw [hsplit] at hq
  -- the linear part alone already covers `a`
  have hcover : a + exp v * (z * z) ≤ exp v * (z + z) + exp v * (z * z) :=
    add_le_add_wit hdom (le_refl _)
  have hchain := le_trans hcover hq
  -- move `a` across
  have w := add_le_add_wit hchain (le_refl (-a))
  have l : a + exp v * (z * z) + -a = exp v * (z * z) := by mach_mpoly [exp v, z, a]
  have r : exp (v + (z + z)) - exp v + -a = exp (v + (z + z)) - exp v - a := by
    mach_mpoly [exp (v + (z + z)), exp v, a]
  rw [l, r] at w; exact w

/-- **The target's rise, through BOTH exponentials, with the quadratic term surviving.**

The instantiation step. `moving_Q_eventual_form` puts the node at `E = E∞ + κ·w` with `w = 1/x`;
the target is `exp (exp E)`, so the linear term has to be pushed through *two* exponentials, not one.
Writing `v := exp E∞`:

    T = exp (v · exp (κ·w))        L_T = exp v

`one_add_le_exp` at `κw` gives `v·exp(κw) − v ≥ v·κ·w`, so the increment on the outer exponential is
at least `v·κ·w`. Feeding half of that to `exp_sub_exp_lower_quadratic` and letting `exp_monotone`
absorb the slack — the true increment is only ever *larger* — yields

    exp v · z²  ≤  T − L_T − a       where  z = (v·κ·w)/2

whenever `a ≤ exp v · (v·κ·w)`, which is the dominance condition and is **independent of `x`**: it
reads `a_Q ≤ exp v · v · κ` once the common factor `w` is cancelled.

**The equality case is included**, which is the whole point. `z² = Θ(w²) = Θ(1/x²)`, matching what
the census measured on the locus, and `double_exp_floor_dominated` takes it from there.

The increment need not equal `z+z`: `exp_sub_exp_lower_quadratic` is applied at the *smaller*
increment and `exp_monotone` lifts it, so no exact halving of an opaque quantity is required and the
only reciprocal is `1/(1+1)` on a constant. -/
theorem target_rise_quadratic (v κ w a : Real) (hv : 0 < v) (hκ : 0 < κ) (hw : 0 < w)
    (hdom : a ≤ exp v * (v * κ * w)) :
    exp v * ((v * κ * w * (1 / (1 + 1))) * (v * κ * w * (1 / (1 + 1))))
      ≤ exp (v * exp (κ * w)) - exp v - a := by
  have h2pos : (0 : Real) < 1 + 1 := by
    have u := add_lt_add_left zero_lt_one_ax 1
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at u; exact lt_trans_ax zero_lt_one_ax u
  have hhalf : (1 + 1 : Real) * (1 / (1 + 1)) = 1 := mul_inv _ (ne_of_gt h2pos)
  have hkw : (0 : Real) ≤ v * κ * w :=
    le_of_lt (mul_pos (mul_pos hv hκ) hw)
  have hz0 : (0 : Real) ≤ v * κ * w * (1 / (1 + 1)) :=
    le_of_lt (mul_pos (mul_pos (mul_pos hv hκ) hw) (one_div_pos_of_pos h2pos))
  -- the two halves rebuild the whole
  have hzz : v * κ * w * (1 / (1 + 1)) + v * κ * w * (1 / (1 + 1)) = v * κ * w := by
    have e : v * κ * w * (1 / (1 + 1)) + v * κ * w * (1 / (1 + 1))
        = v * κ * w * ((1 + 1) * (1 / (1 + 1))) := by mach_ring
    rw [e, hhalf]
    mach_ring
  have hcond : a ≤ exp v * (v * κ * w * (1 / (1 + 1)) + v * κ * w * (1 / (1 + 1))) := by
    rw [hzz]; exact hdom
  have hq := quadratic_separation_of_linear_dominance v a hz0 hcond
  rw [hzz] at hq
  -- the true increment is at least `v·κ·w`, so `exp_monotone` lifts the bound
  have hinc : v + v * κ * w ≤ v * exp (κ * w) := by
    have h1 := mul_le_mul_of_nonneg_left (one_add_le_exp (κ * w)) (le_of_lt hv)
    have e : v * (1 + κ * w) = v + v * κ * w := by mach_mpoly [v, κ, w]
    rw [e] at h1; exact h1
  have hmono : exp (v + v * κ * w) ≤ exp (v * exp (κ * w)) := exp_monotone hinc
  refine le_trans hq ?_
  have step := add_le_add_wit hmono (le_refl (-(exp v) + -a))
  have l : exp (v + v * κ * w) + (-(exp v) + -a) = exp (v + v * κ * w) - exp v - a := by
    mach_mpoly [exp (v + v * κ * w), exp v, a]
  have r : exp (v * exp (κ * w)) + (-(exp v) + -a) = exp (v * exp (κ * w)) - exp v - a := by
    mach_mpoly [exp (v * exp (κ * w)), exp v, a]
  rw [l, r] at step; exact step

/-- **The target's rise, bounded ABOVE, through both exponentials.**

The mirror of `target_rise_quadratic`, and the input the sub-dominant sub-case needs. Two
applications of `exp_sub_exp_upper`, one per exponential:

    exp (κw) − 1                 ≤ κw · exp (κw)               (inner, at v = 0)
    exp (v·exp (κw)) − exp v     ≤ (v·exp (κw) − v) · exp (v·exp (κw))   (outer)

Composing them puts the rise below `v·κ·w · exp (κw) · exp (v·exp (κw))`, whose leading factor is
`w` and whose remaining factors fall to `exp v` as `w → 0`. Against `Q`'s rise of exactly `a·w`, a
coefficient `a` strictly above `v·κ·exp v` therefore forces `Q > T` — the cell's own hypothesis
fails and that sub-case is empty.

**Both bounds are now in hand and they bracket the same quantity**, which is what makes the
equal-limits regime a decidable dichotomy rather than an open question:

| | |
| --- | --- |
| `a ≤ exp v · v · κ` | `target_rise_quadratic` — `Θ(1/x²)` separation, equality included |
| `a > exp v · v · κ` | this bound — `Q > T`, the sub-case is vacuous |

What is *not* yet built is the second row's final step: choosing an explicit `w₀` at which the
falling factors are close enough to `exp v` for `a` to win. That is a quantitative continuity
argument — `exp (κw) ≤ 1 + κw·e` and its outer analogue — and it is arithmetic grinding rather than
a missing idea. Named here rather than sketched in a comment somewhere else. -/
theorem target_rise_upper (v κ w : Real) (hv : 0 < v) :
    exp (v * exp (κ * w)) - exp v
      ≤ v * (κ * w * exp (κ * w)) * exp (v * exp (κ * w)) := by
  -- inner: `exp (κw) − 1 ≤ κw · exp (κw)`
  have hin : exp (κ * w) - 1 ≤ κ * w * exp (κ * w) := by
    have h := exp_sub_exp_upper (κ * w) 0
    rw [exp_zero] at h
    have e : κ * w - 0 = κ * w := by mach_mpoly [κ, w]
    rw [e] at h; exact h
  -- scale it by `v`
  have hscaled : v * exp (κ * w) - v ≤ v * (κ * w * exp (κ * w)) := by
    have h := mul_le_mul_of_nonneg_left hin (le_of_lt hv)
    have e : v * (exp (κ * w) - 1) = v * exp (κ * w) - v := by
      mach_mpoly [v, exp (κ * w)]
    rw [e] at h; exact h
  -- outer
  have hout := exp_sub_exp_upper (v * exp (κ * w)) v
  refine le_trans hout ?_
  exact mul_le_mul_of_nonneg_right hscaled (le_of_lt (exp_pos (v * exp (κ * w))))

/-! ## ▸ Quantitative continuity at `0`, for the sub-dominant sub-case

The remaining sub-case needs an explicit `w₀` at which the falling factors of `target_rise_upper` are
close enough to their limits. In a base with no limit notion that is not a topological argument but
an inequality with a rate, and `exp_sub_exp_upper` already supplies one. -/

/-- **`exp y ≤ 1 + y·e` on `[0,1]`.** The linear-with-explicit-constant form of continuity at `0`.

`exp_sub_exp_upper` at `(y, 0)` gives `exp y − 1 ≤ y·exp y`, and on `[0,1]` the trailing `exp y` is
at most `exp 1`. That is the whole proof, and it is the only continuity this development needs — the
constant `e` is explicit, so every downstream threshold is computable rather than merely existent. -/
theorem exp_le_one_add_scaled {y : Real} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    exp y ≤ 1 + y * exp 1 := by
  have h := exp_sub_exp_upper y 0
  rw [exp_zero] at h
  have e : y - 0 = y := by mach_mpoly [y]
  rw [e] at h
  have hcap : y * exp y ≤ y * exp 1 := mul_le_mul_of_nonneg_left (exp_monotone hy1) hy0
  have hchain := le_trans h hcap
  have w := add_le_add_wit hchain (le_refl (1 : Real))
  have l : exp y - 1 + 1 = exp y := by mach_mpoly [exp y]
  have r : y * exp 1 + 1 = 1 + y * exp 1 := by mach_mpoly [y, exp 1]
  rw [l, r] at w; exact w

/-- **The outer exponent, bounded linearly in `w`.**

`target_rise_upper`'s bound is `v·κ·w · exp (κw) · exp (v·exp (κw))`, whose two trailing factors are
`exp` of `κw` and of `v·exp (κw)`. This bounds the second one's argument:

    κw + v·exp (κw)  ≤  v + κw·(1 + v·e)        for 0 ≤ κw ≤ 1

so the whole exponent sits within `κw·(1 + v·e)` of its limiting value `v`. Choosing `w` small enough
to make that slack as small as required is then arithmetic on explicit constants — which is exactly
what the sub-dominant sub-case needs, and what a limit-free base has to supply in place of a
continuity appeal. -/
theorem outer_exponent_linear_bound (v κ w : Real) (hv : 0 ≤ v)
    (h0 : 0 ≤ κ * w) (h1 : κ * w ≤ 1) :
    κ * w + v * exp (κ * w) ≤ v + κ * w * (1 + v * exp 1) := by
  have hin := exp_le_one_add_scaled h0 h1
  have hscaled : v * exp (κ * w) ≤ v * (1 + κ * w * exp 1) :=
    mul_le_mul_of_nonneg_left hin hv
  have hsum := add_le_add_wit (le_refl (κ * w)) hscaled
  have r : κ * w + v * (1 + κ * w * exp 1) = v + κ * w * (1 + v * exp 1) := by
    mach_mpoly [v, κ, w, exp 1]
  rw [r] at hsum; exact hsum

/-- **The target's rise, as an explicit multiple of `w`.**

`target_rise_upper` bounds the rise by `v·κ·w · exp (κw) · exp (v·exp (κw))`, whose two trailing
factors both depend on `w`. Merging them with `exp_add` and applying `outer_exponent_linear_bound`
collapses the whole thing to a **coefficient times `w`**:

    T − L_T  ≤  v·κ·exp (v + κw·(1 + v·e)) · w

The coefficient falls to `v·κ·exp v` as `w → 0`, and `Q`'s rise is exactly `a·w`. So `a > v·κ·exp v`
makes `Q` win once the slack `κw·(1 + v·e)` is small enough — and *how* small is now a question about
explicit constants, with no limit or continuity appeal left in it.

That is the last structural step of the sub-dominant sub-case. What remains after it is choosing the
threshold: `exp_le_one_add_scaled` turns `exp (v + σ) ≤ exp v·(1 + σ·e)` into a linear condition on
`σ = κw·(1 + v·e)`, and the required `w₀` is then a reciprocal of a compound of `a`, `v`, `κ` and `e`.
Arithmetic, and not yet written. -/
theorem target_rise_upper_linearised (v κ w : Real) (hv : 0 < v) (hκ : 0 < κ) (hw : 0 < w)
    (h1 : κ * w ≤ 1) :
    v * (κ * w * exp (κ * w)) * exp (v * exp (κ * w))
      ≤ v * κ * exp (v + κ * w * (1 + v * exp 1)) * w := by
  have h0 : (0 : Real) ≤ κ * w := le_of_lt (mul_pos hκ hw)
  have hmerge : exp (κ * w) * exp (v * exp (κ * w)) = exp (κ * w + v * exp (κ * w)) :=
    (exp_add _ _).symm
  have hmono : exp (κ * w + v * exp (κ * w))
      ≤ exp (v + κ * w * (1 + v * exp 1)) :=
    exp_monotone (outer_exponent_linear_bound v κ w (le_of_lt hv) h0 h1)
  have e1 : v * (κ * w * exp (κ * w)) * exp (v * exp (κ * w))
      = v * κ * w * (exp (κ * w) * exp (v * exp (κ * w))) := by mach_ring
  rw [e1, hmerge]
  have hnn : (0 : Real) ≤ v * κ * w := le_of_lt (mul_pos (mul_pos hv hκ) hw)
  have hstep := mul_le_mul_of_nonneg_left hmono hnn
  refine le_trans hstep (le_of_eq ?_)
  mach_ring

/-- **One reciprocal that undercuts two positive bounds at once — the division-free `min`.**

This file takes maxima with `exp C₁ + exp C₂`, because sums of positive terms dominate each summand
and no `max` exists in the base. Minima are the harder direction, and they are needed as soon as a
threshold must satisfy *several* smallness conditions — here `σ ≤ 1` for
`exp_le_one_add_scaled` and `σ < S` for the coefficient comparison.

    D := A + A·(1/S) + 1      ⟹      A·(1/D) < 1   and   A·(1/D) < S

`A < D` gives the first because `D − A = A·(1/S) + 1 > 0`. The second is `A < S·D`, which expands to
`S·A + A + S` once `S·(1/S) = 1` is used — so `S·D − A = S·A + S > 0`. Both then follow by
multiplying through by `1/D`.

Reusable well beyond this cell: any construction needing a positive quantity below finitely many
positive bounds can extend the pattern one summand at a time. -/
theorem shrink_below_two_bounds (A S : Real) (hA : 0 < A) (hS : 0 < S) :
    0 < A + A * (1 / S) + 1
    ∧ A * (1 / (A + A * (1 / S) + 1)) < 1
    ∧ A * (1 / (A + A * (1 / S) + 1)) < S := by
  have hinvS : (0 : Real) < 1 / S := one_div_pos_of_pos hS
  have hAS : (0 : Real) < A * (1 / S) := mul_pos hA hinvS
  have hD : (0 : Real) < A + A * (1 / S) + 1 := by
    have v := add_lt_add_left (add_lt_add_left hAS A) (1 : Real)
    have l : (1 : Real) + (A + 0) = A + 1 := by mach_ring
    have r : (1 : Real) + (A + A * (1 / S)) = A + A * (1 / S) + 1 := by
      mach_mpoly [A, (1 / S : Real)]
    rw [l, r] at v
    have w := add_lt_add_left hA (1 : Real)
    have l2 : (1 : Real) + 0 = 1 := by mach_ring
    have r2 : (1 : Real) + A = A + 1 := by mach_ring
    rw [l2, r2] at w
    exact lt_trans_ax (lt_trans_ax zero_lt_one_ax w) v
  have hinvD : (0 : Real) < 1 / (A + A * (1 / S) + 1) := one_div_pos_of_pos hD
  have hDinv : (A + A * (1 / S) + 1) * (1 / (A + A * (1 / S) + 1)) = 1 :=
    mul_inv _ (ne_of_gt hD)
  refine ⟨hD, ?_, ?_⟩
  · -- A < D, then scale by 1/D
    have hlt : A < A + A * (1 / S) + 1 := by
      have v := add_lt_add_left (add_lt_add_left hAS A) (1 : Real)
      have l : (1 : Real) + (A + 0) = A + 1 := by mach_ring
      have r : (1 : Real) + (A + A * (1 / S)) = A + A * (1 / S) + 1 := by
        mach_mpoly [A, (1 / S : Real)]
      rw [l, r] at v
      have w := add_lt_add_left zero_lt_one_ax A
      have l2 : A + (0 : Real) = A := by mach_ring
      rw [l2] at w
      exact lt_trans_ax w v
    have hscaled := mul_lt_mul_of_pos_right hlt hinvD
    rw [hDinv] at hscaled; exact hscaled
  · -- A < S·D, then scale by 1/D
    have hSinv : S * (1 / S) = 1 := mul_inv S (ne_of_gt hS)
    have hexp : S * (A + A * (1 / S) + 1) = S * A + A * (S * (1 / S)) + S := by
      mach_mpoly [A, S, (1 / S : Real)]
    have hlt : A < S * (A + A * (1 / S) + 1) := by
      rw [hexp, hSinv]
      have e : A * (1 : Real) = A := by mach_ring
      rw [e]
      have v := add_lt_add_left hS (S * A + A)
      have l : S * A + A + (0 : Real) = S * A + A := by mach_ring
      rw [l] at v
      have w := add_lt_add_left (mul_pos hS hA) A
      have l2 : A + (0 : Real) = A := by mach_ring
      have r2 : A + S * A = S * A + A := by mach_ring
      rw [l2, r2] at w
      exact lt_trans_ax w v
    have hscaled := mul_lt_mul_of_pos_right hlt hinvD
    have e2 : S * (A + A * (1 / S) + 1) * (1 / (A + A * (1 / S) + 1))
        = S * ((A + A * (1 / S) + 1) * (1 / (A + A * (1 / S) + 1))) := by mach_ring
    rw [e2, hDinv] at hscaled
    have e3 : S * (1 : Real) = S := by mach_ring
    rw [e3] at hscaled; exact hscaled

/-- **The sub-dominant sub-case, analytically: `Q` overtakes the target.**

Takes the two smallness conditions as *hypotheses* rather than constructing a threshold, which keeps
the analysis separate from the reciprocal arithmetic that supplies it (`shrink_below_two_bounds`).
Writing `σ := κw·(1 + v·e)` and `P := v·κ·exp v`:

    σ ≤ 1                    so `exp_le_one_add_scaled` applies to `σ`
    (P·e)·σ < a − P          so the linear slack cannot close the gap

`target_rise_upper_linearised` bounds the target's rise by `v·κ·exp (v+σ)·w`, and `exp (v+σ)` is
`exp v · exp σ ≤ exp v·(1 + σ·e)`. The coefficient is then `P + (P·e)·σ`, which the second hypothesis
puts strictly below `a`. Multiplying by `w > 0` gives `T − L_T < a·w = Q − L_T`, so **`Q` is above the
target** and the cell's hypothesis `Q x < T x` is false.

That is the complement of `target_rise_quadratic`'s dominance condition, so the equal-limits regime is
now covered on both sides: dominance yields a `Θ(1/x²)` separation, sub-dominance yields an empty
region. -/
theorem subdominant_step (v κ a w : Real) (hv : 0 < v) (hκ : 0 < κ) (hw : 0 < w)
    (hσ1 : κ * w * (1 + v * exp 1) ≤ 1)
    (hσS : v * κ * exp v * exp 1 * (κ * w * (1 + v * exp 1)) < a - v * κ * exp v) :
    v * (κ * w * exp (κ * w)) * exp (v * exp (κ * w)) < a * w := by
  have hE1 : (0 : Real) < exp 1 := exp_pos 1
  have hkw : (0 : Real) < κ * w := mul_pos hκ hw
  have hone_v : (1 : Real) ≤ 1 + v * exp 1 := by
    have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (mul_pos hv hE1))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at u; exact u
  have hσ0 : (0 : Real) ≤ κ * w * (1 + v * exp 1) :=
    le_of_lt (mul_pos hkw (lt_of_lt_of_le zero_lt_one_ax hone_v))
  -- `κw ≤ σ ≤ 1`
  have hkw1 : κ * w ≤ 1 := by
    have u := mul_le_mul_of_nonneg_left hone_v (le_of_lt hkw)
    have e : κ * w * (1 : Real) = κ * w := by mach_ring
    rw [e] at u; exact le_trans u hσ1
  -- the linearised upper bound
  have hup := target_rise_upper_linearised v κ w hv hκ hw hkw1
  -- `exp (v + σ) ≤ exp v * (1 + σ * e)`
  have hexp : exp (v + κ * w * (1 + v * exp 1))
      ≤ exp v * (1 + κ * w * (1 + v * exp 1) * exp 1) := by
    have hsplit : exp (v + κ * w * (1 + v * exp 1)) = exp v * exp (κ * w * (1 + v * exp 1)) :=
      exp_add _ _
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (exp_le_one_add_scaled hσ0 hσ1) (le_of_lt (exp_pos v))
  -- coefficient bound
  have hcoef : v * κ * exp (v + κ * w * (1 + v * exp 1))
      ≤ v * κ * exp v + v * κ * exp v * exp 1 * (κ * w * (1 + v * exp 1)) := by
    have h := mul_le_mul_of_nonneg_left hexp (le_of_lt (mul_pos hv hκ))
    have e : v * κ * (exp v * (1 + κ * w * (1 + v * exp 1) * exp 1))
        = v * κ * exp v + v * κ * exp v * exp 1 * (κ * w * (1 + v * exp 1)) := by
      mach_mpoly [v, κ, w, exp v, exp 1]
    have e2 : v * κ * exp (v + κ * w * (1 + v * exp 1))
        = v * κ * exp (v + κ * w * (1 + v * exp 1)) := rfl
    rw [e] at h; exact h
  -- strictly below `a`
  have hlt : v * κ * exp (v + κ * w * (1 + v * exp 1)) < a := by
    refine lt_of_le_of_lt hcoef ?_
    have u := add_lt_add_left hσS (v * κ * exp v)
    have r : v * κ * exp v + (a - v * κ * exp v) = a := by
      mach_mpoly [a, v, κ, exp v]
    rw [r] at u; exact u
  -- scale by `w`
  have hscaled := mul_lt_mul_of_pos_right hlt hw
  exact lt_of_le_of_lt hup hscaled

/-- **The sub-dominant sub-case, with its threshold supplied.**

`subdominant_step` needs `σ ≤ 1` and `(P·e)·σ < a − P` with `σ = κw·(1 + v·e)`. Both are smallness
conditions on the same quantity, so `shrink_below_two_bounds` supplies them together:
`A·(1/D)` sits below `1` and below `S := (a − P)·(1/(P·e))` at once, and `σ = A·w` reaches exactly
that value at `w = 1/D`.

The cancellation `(P·e)·S = a − P` is the only place a reciprocal is undone, and it is undone against
the constant it was built from.

**With this the equal-limits regime is closed.** Dominance gives a `Θ(1/x²)` separation including the
cancellation locus; sub-dominance gives an empty region. -/
theorem subdominant_coefficient_vacuous (v κ a : Real) (hv : 0 < v) (hκ : 0 < κ)
    (hsub : v * κ * exp v < a) :
    ∃ w₀ : Real, 0 < w₀ ∧ ∀ w : Real, 0 < w → w ≤ w₀ →
      v * (κ * w * exp (κ * w)) * exp (v * exp (κ * w)) < a * w := by
  have hE1 : (0 : Real) < exp 1 := exp_pos 1
  have hP : (0 : Real) < v * κ * exp v := mul_pos (mul_pos hv hκ) (exp_pos v)
  have hPE : (0 : Real) < v * κ * exp v * exp 1 := mul_pos hP hE1
  have hd : (0 : Real) < a - v * κ * exp v := by
    have u := add_lt_add_left hsub (-(v * κ * exp v))
    have l : -(v * κ * exp v) + v * κ * exp v = 0 := by mach_ring
    have r : -(v * κ * exp v) + a = a - v * κ * exp v := by mach_mpoly [a, v, κ, exp v]
    rw [l, r] at u; exact u
  have hS : (0 : Real) < (a - v * κ * exp v) * (1 / (v * κ * exp v * exp 1)) := mul_pos hd (one_div_pos_of_pos hPE)
  have hA : (0 : Real) < κ * (1 + v * exp 1) := by
    refine mul_pos hκ ?_
    have u := add_lt_add_left (mul_pos hv hE1) (1 : Real)
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact lt_trans_ax zero_lt_one_ax u
  obtain ⟨hD, hlt1, hltS⟩ := shrink_below_two_bounds (κ * (1 + v * exp 1)) ((a - v * κ * exp v) * (1 / (v * κ * exp v * exp 1))) hA hS
  refine ⟨1 / (κ * (1 + v * exp 1) + κ * (1 + v * exp 1) * (1 / ((a - v * κ * exp v) * (1 / (v * κ * exp v * exp 1)))) + 1), one_div_pos_of_pos hD, ?_⟩
  intro w hw hwle
  have hsig : κ * w * (1 + v * exp 1) ≤ κ * (1 + v * exp 1) * (1 / (κ * (1 + v * exp 1) + κ * (1 + v * exp 1) * (1 / ((a - v * κ * exp v) * (1 / (v * κ * exp v * exp 1)))) + 1)) := by
    have h := mul_le_mul_of_nonneg_left hwle (le_of_lt hA)
    have e : κ * (1 + v * exp 1) * w = κ * w * (1 + v * exp 1) := by mach_ring
    rw [e] at h; exact h
  refine subdominant_step v κ a w hv hκ hw (le_of_lt (lt_of_le_of_lt hsig hlt1)) ?_
  have hstrict : κ * w * (1 + v * exp 1) < (a - v * κ * exp v) * (1 / (v * κ * exp v * exp 1)) := lt_of_le_of_lt hsig hltS
  have h2 := mul_lt_mul_of_pos_right hstrict hPE
  have el : κ * w * (1 + v * exp 1) * (v * κ * exp v * exp 1) = v * κ * exp v * exp 1 * (κ * w * (1 + v * exp 1)) := by mach_ring
  have er : (a - v * κ * exp v) * (1 / (v * κ * exp v * exp 1)) * (v * κ * exp v * exp 1) = a - v * κ * exp v := by
    have e : (a - v * κ * exp v) * (1 / (v * κ * exp v * exp 1)) * (v * κ * exp v * exp 1) = (a - v * κ * exp v) * ((v * κ * exp v * exp 1) * (1 / (v * κ * exp v * exp 1))) := by mach_ring
    rw [e, mul_inv _ (ne_of_gt hPE)]
    mach_ring
  rw [el, er] at h2
  exact h2

/-! ## ▸ Wiring the pieces to the obligation

The analysis is complete on every branch; what remains is case-splitting the actual trees and reading
the constants off. Two facts do most of the bookkeeping.

**The interface mismatch is real and worth naming.** `bounded_ray_depth_two_both_forms` filters `Q` to
five shapes, but it wants `1 < Q x ≤ M` on a *ray*, and the obligation supplies those two facts only
*guarded*, inside `∀ x, X₀ ≤ x → 1 < Q x → Q x < T x → …`. A hypothesis available at each point of a
set is not a hypothesis available on a ray, and the filter cannot be applied to the obligation as
stated. The split therefore has to be unconditional — `depth_le_two_normal_form` — with the guarded
facts used pointwise inside each case. That is a larger case space than the filtered five, and it is
exactly the kind of mismatch a finite assembly exposes. -/

/-- **The cap bounds the target itself, on the whole ray.** `exp (eml A B) ≤ K` gives
`exp (exp (eml A B)) ≤ exp K` by monotonicity — the only consequence of the cap that survives
unguarded, and the one every vacuity argument below runs on. -/
theorem target_le_exp_cap (A B : EMLTree) (K XK : Real)
    (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K) :
    ∀ x : Real, XK ≤ x → exp (exp ((EMLTree.eml A B).eval x)) ≤ exp K :=
  fun x hx => exp_monotone (hK x hx)

/-- **Every `Q` that outgrows the cap makes the cell vacuous.**

`Q x < T x ≤ exp K` is impossible once `Q x ≥ exp K`, so the guarded hypotheses are contradictory and
the conclusion holds for want of a case. This retires `Q = var` and every other shape whose value
rises past a constant — which, on the depth-≤2 grammar, is most of them.

Stated on `Q`'s eventual size rather than on its shape, so one application covers all of them. -/
theorem boundedEmlCell_vacuous_of_large_Q (A B Q : EMLTree) (K XK X₁ : Real)
    (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K)
    (hbig : ∀ x : Real, X₁ ≤ x → exp K ≤ Q.eval x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  refine ⟨0, 1 + exp XK + exp X₁, ?_, ?_⟩
  · have v : (1 : Real) + 0 + 0 ≤ 1 + exp XK + exp X₁ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XK)))
        (le_of_lt (exp_pos X₁))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx _ hlt
  exfalso
  have hXKx : XK ≤ x := by
    have v : (0 : Real) + exp XK + 0 ≤ 1 + exp XK + exp X₁ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos X₁))
    have e : (0 : Real) + exp XK + 0 = exp XK := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XK) (le_trans v hx)
  have hX₁x : X₁ ≤ x := by
    have v : (0 : Real) + 0 + exp X₁ ≤ 1 + exp XK + exp X₁ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XK)))
        (le_refl _)
    have e : (0 : Real) + 0 + exp X₁ = exp X₁ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp X₁) (le_trans v hx)
  -- `Q x < T x ≤ exp K ≤ Q x`
  exact lt_irrefl_ax _
    (lt_of_lt_of_le hlt (le_trans (target_le_exp_cap A B K XK hK x hXKx) (hbig x hX₁x)))

/-- **First casualty of the unconditional split: `Q = var`.**

`var.eval x = x`, which passes `exp K` at `x = exp K` and never returns, so
`boundedEmlCell_vacuous_of_large_Q` applies with `X₁ := exp K` and the whole shape is retired in one
line. The same argument disposes of `exp x − d` and `exp x − log x` in either child position; only
shapes that stay bounded reach the analytic branches. -/
theorem boundedEmlCell_var_Q (A B : EMLTree) (K XK : Real)
    (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < EMLTree.var.eval x →
      EMLTree.var.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - EMLTree.var.eval x :=
  boundedEmlCell_vacuous_of_large_Q A B EMLTree.var K XK (exp K) hK (fun _ hx => hx)

/-- **A growing left child makes `Q` outrun the cap, so three of its five shapes die at once.**

`depth_le_one_exp_bounded_or_grows` is a dichotomy with nothing in between: `exp (P x)` is bounded, or
it eventually dominates `exp x`. In the growing branch `depth_le_one_log_le_linear` caps the right
child at `x + C`, so

    Q x = exp (P x) − log (R x)  ≥  exp x − x − C  ≥  x − C

using `two_mul_le_exp`, and that passes `exp K` at `x = exp K + C`. `boundedEmlCell_vacuous_of_large_Q`
then applies.

**This is the unconditional replacement for the filter's left-child step.**
`bounded_ray_depth_two_both_forms` reached the same two surviving shapes from a ray-wide cap on `Q`,
which the obligation does not supply; this reaches them from the dichotomy instead, which needs no
hypothesis about `Q` at all. Three of `P`'s five forms — `var`, `exp x − d`, `exp x − log x` — are
retired here, leaving `const` and `c − log x`. -/
theorem boundedEmlCell_vacuous_of_growing_left (A B P R : EMLTree) (hR : R.depth ≤ 1)
    (K XK T : Real)
    (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K)
    (hgrow : ∀ x : Real, T ≤ x → exp x ≤ exp (P.eval x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < (EMLTree.eml P R).eval x →
      (EMLTree.eml P R).eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - (EMLTree.eml P R).eval x := by
  obtain ⟨CR, hCR⟩ := depth_le_one_log_le_linear R hR
  refine boundedEmlCell_vacuous_of_large_Q A B (EMLTree.eml P R) K XK
    (1 + exp T + exp (exp K + CR)) hK ?_
  intro x hx
  -- unpack the merged threshold
  have hone : (1 : Real) ≤ x := by
    have v : (1 : Real) + 0 + 0 ≤ 1 + exp T + exp (exp K + CR) :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos T)))
        (le_of_lt (exp_pos (exp K + CR)))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hTx : T ≤ x := by
    have v : (0 : Real) + exp T + 0 ≤ 1 + exp T + exp (exp K + CR) :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos (exp K + CR)))
    have e : (0 : Real) + exp T + 0 = exp T := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp T) (le_trans v hx)
  have hKC : exp K + CR ≤ x := by
    have v : (0 : Real) + 0 + exp (exp K + CR) ≤ 1 + exp T + exp (exp K + CR) :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos T)))
        (le_refl _)
    have e : (0 : Real) + 0 + exp (exp K + CR) = exp (exp K + CR) := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp (exp K + CR)) (le_trans v hx)
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hone
  -- `Q x ≥ exp x − (x + CR)`
  have hval : (EMLTree.eml P R).eval x = exp (P.eval x) - log (R.eval x) := rfl
  have hlow : exp x - (x + CR) ≤ (EMLTree.eml P R).eval x := by
    rw [hval]
    have v := add_le_add_wit (hgrow x hTx) (neg_le_neg_wit (hCR x hone))
    have l : exp x + -(x + CR) = exp x - (x + CR) := by mach_mpoly [x, CR]
    have r : exp (P.eval x) + -log (R.eval x) = exp (P.eval x) - log (R.eval x) := by
      mach_mpoly [exp (P.eval x), log (R.eval x)]
    rw [l, r] at v; exact v
  -- `exp x − (x + CR) ≥ x − CR ≥ exp K`
  have hlin : exp K ≤ exp x - (x + CR) := by
    have hxx := two_mul_le_exp hx0
    have v := add_le_add_wit hxx (le_refl (-(x + CR)))
    have l : x + x + -(x + CR) = x - CR := by mach_mpoly [x, CR]
    have r : exp x + -(x + CR) = exp x - (x + CR) := by mach_mpoly [x, CR]
    rw [l, r] at v
    refine le_trans ?_ v
    have w := add_le_add_wit hKC (le_refl (-CR))
    have l2 : exp K + CR + -CR = exp K := by mach_mpoly [exp K, CR]
    have r2 : x + -CR = x - CR := by mach_mpoly [x, CR]
    rw [l2, r2] at w; exact w
  exact le_trans hlin hlow

/-- **The case-split entry point: either the cell is already proved, or `P` is one of two shapes.**

Feeds `depth_le_one_exp_bounded_or_grows` straight into the two preceding lemmas. The growing branch
discharges the obligation outright by vacuity; the bounded branch hands back exactly the hypothesis
`depth_le_one_exp_bounded_forms` consumes, so a caller continues with `P` constant or `c − log x` and
never sees the other three forms.

**This is the unconditional analogue of `boundedEmlCell_left_forms`**, which did the same job for `A`
using the cap. Here there is no hypothesis about `Q` to lean on, so the dichotomy does the work
instead — and the outcome is the same two shapes, reached from the other side. -/
theorem boundedEmlCell_left_dichotomy (A B P R : EMLTree) (hP : P.depth ≤ 1) (hR : R.depth ≤ 1)
    (K XK : Real)
    (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K) :
    (∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < (EMLTree.eml P R).eval x →
        (EMLTree.eml P R).eval x < exp (exp ((EMLTree.eml A B).eval x)) →
          exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - (EMLTree.eml P R).eval x)
    ∨ (∃ Kb : Real, ∀ x : Real, 1 ≤ x → exp (P.eval x) ≤ Kb) := by
  rcases depth_le_one_exp_bounded_or_grows P hP with hb | ⟨T, hT⟩
  · exact Or.inr hb
  · exact Or.inl (boundedEmlCell_vacuous_of_growing_left A B P R hR K XK T hK hT)

/-- Continuing the split: in the bounded branch `P` is constant or `c − log x`, and nothing else. -/
theorem boundedEmlCell_left_two_shapes (P : EMLTree) (hP : P.depth ≤ 1) (Kb : Real)
    (hb : ∀ x : Real, 1 ≤ x → exp (P.eval x) ≤ Kb) :
    (∃ α : Real, ∀ x : Real, 0 < x → P.eval x = α)
    ∨ (∃ c : Real, 0 < c ∧ ∀ x : Real, 0 < x → P.eval x = c - log x) :=
  depth_le_one_exp_bounded_forms P hP Kb hb

/-- **The other vacuity: `Q` falls below `1`.**

The left child was retired by `Q` outrunning the cap. The right child cannot be: making `log (R x)`
large drives `Q = exp (P x) − log (R x)` *down*, not up, so it fails the obligation's OTHER guard,
`1 < Q x`. Two different mechanisms, and the expectation that the two sides would be symmetric was
wrong — `depth_le_one_log_bounded_or_unbounded`'s second branch is **cofinal** (`∀ Λ, ∃ x`), not
eventual, precisely because the log side has three growth classes rather than two. The file's own
docstring says so; the dichotomy cannot drive a vacuity argument on a ray, and this lemma takes the
eventual hypothesis directly instead. -/
theorem boundedEmlCell_vacuous_of_small_Q (A B Q : EMLTree) (X₁ : Real)
    (hsmall : ∀ x : Real, X₁ ≤ x → Q.eval x ≤ 1) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  refine ⟨0, 1 + exp X₁, ?_, ?_⟩
  · have v : (1 : Real) + 0 ≤ 1 + exp X₁ :=
      add_le_add_wit (le_refl 1) (le_of_lt (exp_pos X₁))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx hgt _
  exfalso
  have hX₁x : X₁ ≤ x := by
    have v : (0 : Real) + exp X₁ ≤ 1 + exp X₁ :=
      add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
    have e : (0 : Real) + exp X₁ = exp X₁ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp X₁) (le_trans v hx)
  exact lt_irrefl_ax _ (lt_of_lt_of_le hgt (hsmall x hX₁x))

/-- **A right child whose logarithm outgrows the left child's cap retires the shape.**

`exp (P x) ≤ Kb` and `log (R x) ≥ Kb − 1` give `Q x ≤ 1` directly, so
`boundedEmlCell_vacuous_of_small_Q` applies. Every `R` whose logarithm rises without bound is covered,
and this development already proves the three cases that matter:
`log_exp_sub_const_ge_linear` and `log_exp_sub_log_ge_linear` give `log (R x) ≥ x − 1` for the two
`exp`-shaped forms, and `log_ge_sub_one_of_exp_pred_le` gives it for `var` at `x ≥ exp (Kb − 1)`.
So `R` is left with `const` and `c − log x`, matching the left child. -/
theorem boundedEmlCell_vacuous_of_large_log_right (A B P R : EMLTree) (Kb XP XR : Real)
    (hP : ∀ x : Real, XP ≤ x → exp (P.eval x) ≤ Kb)
    (hR : ∀ x : Real, XR ≤ x → Kb - 1 ≤ log (R.eval x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < (EMLTree.eml P R).eval x →
      (EMLTree.eml P R).eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - (EMLTree.eml P R).eval x := by
  refine boundedEmlCell_vacuous_of_small_Q A B (EMLTree.eml P R) (1 + exp XP + exp XR) ?_
  intro x hx
  have hXPx : XP ≤ x := by
    have v : (0 : Real) + exp XP + 0 ≤ 1 + exp XP + exp XR :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XR))
    have e : (0 : Real) + exp XP + 0 = exp XP := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XP) (le_trans v hx)
  have hXRx : XR ≤ x := by
    have v : (0 : Real) + 0 + exp XR ≤ 1 + exp XP + exp XR :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XP)))
        (le_refl _)
    have e : (0 : Real) + 0 + exp XR = exp XR := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XR) (le_trans v hx)
  have hval : (EMLTree.eml P R).eval x = exp (P.eval x) - log (R.eval x) := rfl
  rw [hval]
  have v := add_le_add_wit (hP x hXPx) (neg_le_neg_wit (hR x hXRx))
  have l : exp (P.eval x) + -log (R.eval x) = exp (P.eval x) - log (R.eval x) := by
    mach_mpoly [exp (P.eval x), log (R.eval x)]
  have r : Kb + -(Kb - 1) = 1 := by mach_mpoly [Kb]
  rw [l, r] at v; exact v

/-- **`Q = const c`, discharged through the node rather than the target.**

A constant `Q` is not the easy case it looks like: the target may fall toward `c`, so no barrier
separates them and `gap_below_constant_barrier` does not apply.

The route goes one level down. `c = exp (exp k)` with `k := log (log c)`, so `c < T x` says exactly
`k < (eml A B) x` — a depth-≤2 tree exceeding a constant, which is
`depth_le_two_approach_constant`'s hypothesis. It answers with a **singly** exponential floor
`exp (−C₁ − x)` on `(eml A B) x − k`, and two applications of `exp_sub_exp_lower` lift that through
the two exponentials at a cost of the positive constant `exp k · exp (exp k) = log c · c`.

The obligation asks only for `exp (−C − exp x)`, and `x ≤ exp x` makes that no larger than
`exp (−C − x)`, so the singly exponential floor clears the doubly exponential ask with room to
spare — the same scale gap `target_above_one_singly_exponential` identified, used here to close a
branch rather than to explain one.

`1 < c` has to be decided before `C` and `X₀` can be chosen, since `k` is undefined otherwise; the
`lt_total` split handles that, and the branches where `c ≤ 1` are vacuous against the guard. -/
theorem boundedEmlCell_const_Q (A B : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1) (c : Real) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < c →
      c < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - c := by
  have hAB : (EMLTree.eml A B).depth ≤ 2 := by
    simp only [EMLTree.depth]
    have := Nat.max_le.mpr (And.intro hA hB); omega
  rcases lt_total 1 c with hc | hc | hc
  · -- the real case: `c > 1`, so `k := log (log c)` exists
    have hcpos : (0 : Real) < c := lt_trans_ax zero_lt_one_ax hc
    have hlogc : (0 : Real) < log c := by
      have h := log_lt_log zero_lt_one_ax hc
      rw [log_one] at h; exact h
    have hek : exp (log (log c)) = log c := exp_log hlogc
    have heek : exp (exp (log (log c))) = c := by rw [hek, exp_log hcpos]
    obtain ⟨C₁, X₁, hX₁, happ⟩ := depth_le_two_approach_constant (EMLTree.eml A B) hAB (log (log c))
    have hD : (0 : Real) < exp (-C₁) * (log c * c) :=
      mul_pos (exp_pos _) (mul_pos hlogc hcpos)
    obtain ⟨y, hy⟩ := exp_surj _ hD
    refine ⟨-y, X₁, hX₁, ?_⟩
    intro x hx _ hlt
    -- `k < node x`, by trichotomy against the guard
    have hkE : log (log c) < (EMLTree.eml A B).eval x := by
      rcases lt_total (log (log c)) ((EMLTree.eml A B).eval x) with h | h | h
      · exact h
      · exfalso; rw [← h, heek] at hlt; exact lt_irrefl_ax _ hlt
      · exfalso
        have hstep := exp_monotone (le_of_lt (exp_lt h))
        rw [heek] at hstep
        exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hstep)
    have hgap := happ x hx hkE
    -- lift through both exponentials
    have hlow1 : ((EMLTree.eml A B).eval x - log (log c)) * exp (log (log c))
        ≤ exp ((EMLTree.eml A B).eval x) - exp (log (log c)) :=
      exp_sub_exp_lower _ _
    have hlow2 : (exp ((EMLTree.eml A B).eval x) - exp (log (log c))) * exp (exp (log (log c)))
        ≤ exp (exp ((EMLTree.eml A B).eval x)) - exp (exp (log (log c))) :=
      exp_sub_exp_lower _ _
    rw [heek] at hlow2
    -- chain the two lower bounds
    have hchain : (exp (-C₁ - x) * log c) * c
        ≤ exp (exp ((EMLTree.eml A B).eval x)) - c := by
      refine le_trans ?_ hlow2
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hcpos)
      refine le_trans ?_ hlow1
      rw [hek]
      exact mul_le_mul_of_nonneg_right hgap (le_of_lt hlogc)
    refine le_trans ?_ hchain
    -- `exp (-C - exp x) ≤ exp (-C₁ - x) * (log c * c)` by the choice of `C`
    have hxe : -(exp x) ≤ -x := neg_le_neg_wit (self_le_exp x)
    have hstep : exp (-(-y) - exp x) ≤ exp (-(-y) - x) := by
      refine exp_monotone ?_
      have v := add_le_add_wit (le_refl (-(-y))) hxe
      have l : -(-y) + -(exp x) = -(-y) - exp x := by mach_mpoly [y, exp x]
      have r : -(-y) + -x = -(-y) - x := by mach_mpoly [y, x]
      rw [l, r] at v; exact v
    refine le_trans hstep (le_of_eq ?_)
    have esplit : -(-y) - x = y + -x := by mach_ring
    rw [esplit, exp_add, hy]
    have e1 : exp (-C₁) * (log c * c) * exp (-x) = exp (-C₁) * exp (-x) * log c * c := by
      mach_ring
    rw [e1, ← exp_add]
    have e2 : -C₁ + -x = -C₁ - x := by mach_mpoly [C₁, x]
    rw [e2]
  · exact ⟨0, 1, le_refl _, fun _ _ h1 _ => absurd hc (ne_of_lt h1)⟩
  · exact ⟨0, 1, le_refl _, fun _ _ h1 _ => absurd (lt_trans_ax h1 hc) (lt_irrefl_ax 1)⟩

/-- **`log (c − log x) = 0` past `exp c`.** The totalized log collapsing the `c − log x` shape, as a
theorem rather than the informal "the argument goes negative". `log_nonpos` is a CHOICE this base
makes, so the collapse changes the function rather than merely simplifying it, and the threshold is
explicit. -/
theorem log_c_sub_log_eventually_zero (c : Real) :
    ∀ x : Real, exp c ≤ x → log (c - log x) = 0 := by
  intro x hx
  refine log_nonpos ?_
  have hcl : c ≤ log x := by
    have h := log_ge_sub_one_of_exp_pred_le (x := c + 1) (z := x) ?_
    · have e : c + 1 - 1 = c := by mach_ring
      rw [e] at h; exact h
    · have e : c + 1 - 1 = c := by mach_ring
      rw [e]; exact hx
  have v := add_le_add_wit hcl (le_refl (-(log x)))
  have l : c + -(log x) = c - log x := by mach_mpoly [c, log x]
  have r : log x + -(log x) = 0 := by mach_ring
  rw [l, r] at v; exact v

/-- **An eventually-constant `Q` inherits `boundedEmlCell_const_Q`.**

Two of the four surviving `P`/`R` combinations land here: `P` constant makes `exp (P x)` constant, and
either `R` constant or — by `log_c_sub_log_eventually_zero` — `R = c − log x` makes `log (R x)`
constant too. The value is then fixed on a ray even though the tree is not a `const` node. -/
theorem boundedEmlCell_eventually_const_Q (A B Q : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (c XC : Real) (hconst : ∀ x : Real, XC ≤ x → Q.eval x = c) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  obtain ⟨C, X₀, hX₀, h⟩ := boundedEmlCell_const_Q A B hA hB c
  refine ⟨C, X₀ + exp XC, ?_, ?_⟩
  · have v : X₀ + 0 ≤ X₀ + exp XC := add_le_add_wit (le_refl _) (le_of_lt (exp_pos XC))
    have e : X₀ + (0 : Real) = X₀ := by mach_ring
    rw [e] at v; exact le_trans hX₀ v
  intro x hx hgt hlt
  have hX₀x : X₀ ≤ x := by
    have v : X₀ + 0 ≤ X₀ + exp XC := add_le_add_wit (le_refl _) (le_of_lt (exp_pos XC))
    have e : X₀ + (0 : Real) = X₀ := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hXCx : XC ≤ x := by
    have v : (0 : Real) + exp XC ≤ X₀ + exp XC :=
      add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hX₀) (le_refl _)
    have e : (0 : Real) + exp XC = exp XC := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XC) (le_trans v hx)
  rw [hconst x hXCx] at hgt hlt ⊢
  exact h x hX₀x hgt hlt

/-! ## ▸ The four surviving `P`/`R` combinations

`P` and `R` each survive as `const` or `c − log x`. Three of the four pairings collapse; only
`P = c − log x` with `R` constant leaves a genuinely moving target. -/

/-- `P` and `R` both constant: `Q` is constant. -/
theorem boundedEmlCell_constP_constR (A B P R : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (α β : Real) (hP : ∀ x : Real, 0 < x → P.eval x = α) (hR : ∀ x : Real, 0 < x → R.eval x = β) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < (EMLTree.eml P R).eval x →
      (EMLTree.eml P R).eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - (EMLTree.eml P R).eval x := by
  refine boundedEmlCell_eventually_const_Q A B (EMLTree.eml P R) hA hB (exp α - log β) 1 ?_
  intro x hx
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
  have hval : (EMLTree.eml P R).eval x = exp (P.eval x) - log (R.eval x) := rfl
  rw [hval, hP x hx0, hR x hx0]

/-- `P` constant, `R = c − log x`: the totalized log zeroes the right child, so `Q` is eventually the
constant `exp α`. -/
theorem boundedEmlCell_constP_logR (A B P R : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (α cR : Real) (hP : ∀ x : Real, 0 < x → P.eval x = α)
    (hR : ∀ x : Real, 0 < x → R.eval x = cR - log x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < (EMLTree.eml P R).eval x →
      (EMLTree.eml P R).eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - (EMLTree.eml P R).eval x := by
  refine boundedEmlCell_eventually_const_Q A B (EMLTree.eml P R) hA hB (exp α) (1 + exp cR) ?_
  intro x hx
  have hone : (1 : Real) ≤ x := by
    have v : (1 : Real) + 0 ≤ 1 + exp cR := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos cR))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hcR : exp cR ≤ x := by
    have v : (0 : Real) + exp cR ≤ 1 + exp cR :=
      add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
    have e : (0 : Real) + exp cR = exp cR := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hval : (EMLTree.eml P R).eval x = exp (P.eval x) - log (R.eval x) := rfl
  rw [hval, hP x hx0, hR x hx0, log_c_sub_log_eventually_zero cR x hcR]
  mach_mpoly [exp α]

/-- Both children `c − log x`: the right child zeroes and the left decays, so `Q → 0` and falls below
the guard `1 < Q x`. Vacuous. -/
theorem boundedEmlCell_logP_logR (A B P R : EMLTree) (cP cR : Real)
    (hP : ∀ x : Real, 0 < x → P.eval x = cP - log x)
    (hR : ∀ x : Real, 0 < x → R.eval x = cR - log x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < (EMLTree.eml P R).eval x →
      (EMLTree.eml P R).eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - (EMLTree.eml P R).eval x := by
  refine boundedEmlCell_vacuous_of_small_Q A B (EMLTree.eml P R) (1 + exp cR + exp cP) ?_
  intro x hx
  have hone : (1 : Real) ≤ x := by
    have v : (1 : Real) + 0 + 0 ≤ 1 + exp cR + exp cP :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos cR))) (le_of_lt (exp_pos cP))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hcR : exp cR ≤ x := by
    have v : (0 : Real) + exp cR + 0 ≤ 1 + exp cR + exp cP :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)) (le_of_lt (exp_pos cP))
    have e : (0 : Real) + exp cR + 0 = exp cR := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hcP : exp cP ≤ x := by
    have v : (0 : Real) + 0 + exp cP ≤ 1 + exp cR + exp cP :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos cR))) (le_refl _)
    have e : (0 : Real) + 0 + exp cP = exp cP := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hval : (EMLTree.eml P R).eval x = exp (P.eval x) - log (R.eval x) := rfl
  rw [hval, hP x hx0, hR x hx0, log_c_sub_log_eventually_zero cR x hcR, exp_c_sub_log_eq cP hx0]
  -- `exp cP * (1/x) − 0 ≤ 1`
  have hinv : x * (1 / x) = 1 := mul_inv x (ne_of_gt hx0)
  have hstep := mul_le_mul_of_nonneg_right hcP (le_of_lt (one_div_pos_of_pos hx0))
  rw [hinv] at hstep
  have e : exp cP * (1 / x) - 0 = exp cP * (1 / x) := by mach_mpoly [exp cP, (1 / x : Real)]
  rw [e]; exact hstep

/-! ## ▸ Splitting on the TARGET

The `Q` side is exhausted: every shape is discharged or vacuous except `P = c − log x` with `R`
constant. What decides that last one is the target, so the split moves to `A` and `B`. -/

/-- **An eventually-constant target discharges the cell for EVERY `Q` at once.**

`boundedEmlCellApproachLarge_const_target` wanted the target constant from `1` onward.
`gap_below_constant_barrier` takes its barrier on a **ray**, which is the weaker hypothesis the tree
cases actually produce — `log (c − log x)` only zeroes past `exp c`, so nothing is constant from `1`.

Since the barrier is the target's own value, `Q x < T x` *is* `Q x < k`, and the lemma applies with
no further work. -/
theorem boundedEmlCell_eventually_const_target (A B Q : EMLTree) (hQ : Q.depth ≤ 2) (V XV : Real)
    (hT : ∀ x : Real, XV ≤ x → exp (exp ((EMLTree.eml A B).eval x)) = V) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  obtain ⟨C, X₀, hX₀, h⟩ :=
    gap_below_constant_barrier Q hQ (fun x => exp (exp ((EMLTree.eml A B).eval x))) V XV
      (fun x hx => le_of_eq (hT x hx).symm)
  refine ⟨C, X₀ + exp XV, ?_, ?_⟩
  · have v : X₀ + 0 ≤ X₀ + exp XV := add_le_add_wit (le_refl _) (le_of_lt (exp_pos XV))
    have e : X₀ + (0 : Real) = X₀ := by mach_ring
    rw [e] at v; exact le_trans hX₀ v
  intro x hx _ hlt
  have hX₀x : X₀ ≤ x := by
    have v : X₀ + 0 ≤ X₀ + exp XV := add_le_add_wit (le_refl _) (le_of_lt (exp_pos XV))
    have e : X₀ + (0 : Real) = X₀ := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hXVx : XV ≤ x := by
    have v : (0 : Real) + exp XV ≤ X₀ + exp XV :=
      add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hX₀) (le_refl _)
    have e : (0 : Real) + exp XV = exp XV := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XV) (le_trans v hx)
  exact h x hX₀x (by rw [← hT x hXVx]; exact hlt)

/-- `A` and `B` both constant: the target is constant, so every `Q` is covered. -/
theorem boundedEmlCell_constA_constB (A B Q : EMLTree) (hQ : Q.depth ≤ 2) (α β : Real)
    (hA : ∀ x : Real, 0 < x → A.eval x = α) (hB : ∀ x : Real, 0 < x → B.eval x = β) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  refine boundedEmlCell_eventually_const_target A B Q hQ (exp (exp (exp α - log β))) 1 ?_
  intro x hx
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  rw [hval, hA x hx0, hB x hx0]

/-- `A` constant, `B = c − log x`: the totalized log zeroes `B`'s logarithm past `exp c`, so the
target is eventually the constant `exp (exp (exp α))`. -/
theorem boundedEmlCell_constA_logB (A B Q : EMLTree) (hQ : Q.depth ≤ 2) (α cB : Real)
    (hA : ∀ x : Real, 0 < x → A.eval x = α)
    (hB : ∀ x : Real, 0 < x → B.eval x = cB - log x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  refine boundedEmlCell_eventually_const_target A B Q hQ (exp (exp (exp α))) (1 + exp cB) ?_
  intro x hx
  have hone : (1 : Real) ≤ x := by
    have v : (1 : Real) + 0 ≤ 1 + exp cB := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos cB))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hcB : exp cB ≤ x := by
    have v : (0 : Real) + exp cB ≤ 1 + exp cB :=
      add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
    have e : (0 : Real) + exp cB = exp cB := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  rw [hval, hA x hx0, hB x hx0, log_c_sub_log_eventually_zero cB x hcB]
  have e : exp α - (0 : Real) = exp α := by mach_mpoly [exp α]
  rw [e]

/-- **A target falling to `1` at `e^{−x}` cannot stay above a `Q` that sits `a/x` above `1`.**

The `T → 1` regime, wired up. `target_below_one_singly_exponential` supplies the hypothesis `hT` for
either `exp`-shaped `B`; `moving_Q_eventual_form` supplies `hQ` for the one surviving moving `Q` shape
whenever its limit is at least `1`. `exp_neg_le_inv_of_pos` then closes it:

    T x − 1  ≤  D·e^{−x}  ≤  a·(1/x)  ≤  Q x − 1

so `T x ≤ Q x`, contradicting the guard `Q x < T x`. The region is empty.

`e^{−x}` losing to `1/x` is the entire content — a singly exponential approach cannot outrun a
polynomial one — and it retires every combination with an `exp`-shaped right child in the node. -/
theorem boundedEmlCell_vacuous_of_fast_target (A B Q : EMLTree) (D a XD Xa : Real)
    (hDpos : 0 < D) (hapos : 0 < a)
    (hT : ∀ x : Real, XD ≤ x → exp (exp ((EMLTree.eml A B).eval x)) - 1 ≤ D * exp (-x))
    (hQlow : ∀ x : Real, Xa ≤ x → 1 + a * (1 / x) ≤ Q.eval x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  obtain ⟨XE, hXE, hE⟩ := exp_neg_le_inv_of_pos a D hapos hDpos
  refine ⟨0, 1 + exp XD + exp Xa + exp XE, ?_, ?_⟩
  · have v : (1 : Real) + 0 + 0 + 0 ≤ 1 + exp XD + exp Xa + exp XE :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XD)))
        (le_of_lt (exp_pos Xa))) (le_of_lt (exp_pos XE))
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx _ hlt
  exfalso
  have grab : ∀ Y : Real, exp Y ≤ 1 + exp XD + exp Xa + exp XE → Y ≤ x := by
    intro Y hY; exact le_trans (self_le_exp Y) (le_trans hY hx)
  have hXDx : XD ≤ x := by
    refine grab XD ?_
    have v : (0 : Real) + exp XD + 0 + 0 ≤ 1 + exp XD + exp Xa + exp XE :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos Xa))) (le_of_lt (exp_pos XE))
    have e : (0 : Real) + exp XD + 0 + 0 = exp XD := by mach_ring
    rw [e] at v; exact v
  have hXax : Xa ≤ x := by
    refine grab Xa ?_
    have v : (0 : Real) + 0 + exp Xa + 0 ≤ 1 + exp XD + exp Xa + exp XE :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XD))) (le_refl _)) (le_of_lt (exp_pos XE))
    have e : (0 : Real) + 0 + exp Xa + 0 = exp Xa := by mach_ring
    rw [e] at v; exact v
  have hXEx : XE ≤ x := by
    refine grab XE ?_
    have v : (0 : Real) + 0 + 0 + exp XE ≤ 1 + exp XD + exp Xa + exp XE :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XD))) (le_of_lt (exp_pos Xa))) (le_refl _)
    have e : (0 : Real) + 0 + 0 + exp XE = exp XE := by mach_ring
    rw [e] at v; exact v
  -- `T ≤ 1 + D e^{-x} ≤ 1 + a/x ≤ Q`
  have hchain : exp (exp ((EMLTree.eml A B).eval x)) ≤ Q.eval x := by
    refine le_trans ?_ (hQlow x hXax)
    have h1 := hT x hXDx
    have v := add_le_add_wit (le_trans h1 (hE x hXEx)) (le_refl (1 : Real))
    have l : exp (exp ((EMLTree.eml A B).eval x)) - 1 + 1
        = exp (exp ((EMLTree.eml A B).eval x)) := by
      mach_mpoly [exp (exp ((EMLTree.eml A B).eval x))]
    have r : a * (1 / x) + 1 = 1 + a * (1 / x) := by mach_mpoly [a, (1 / x : Real)]
    rw [l, r] at v; exact v
  exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hchain)

/-! ## ▸ Reading `v` and `κ` off the node

`target_rise_quadratic` and `subdominant_coefficient_vacuous` speak about `exp (v · exp (κ·w))`.
These put the surviving node forms into that shape, which is the last translation the assembly
needs. -/

/-- **`A = c − log x`, `B` constant: the node is exactly `v · exp (κ·w)`.**

    exp ((eml A B) x)  =  exp (−log β) · exp (exp c · (1/x))

so `v := exp (−log β)` and `κ := exp c`, both positive. This is the one node form that lands on
`target_rise_quadratic`'s shape with no slack at all: `exp_c_sub_log_eq` turns the left child into
`exp c · (1/x)`, and `exp_add` splits off the constant right child.

`κ = exp c > 0` is what makes the target *rise* toward its limit rather than fall to it, which is the
orientation both analytic lemmas assume. -/
theorem node_form_logA_constB (A B : EMLTree) (cA β : Real)
    (hA : ∀ x : Real, 0 < x → A.eval x = cA - log x)
    (hB : ∀ x : Real, 0 < x → B.eval x = β) :
    ∀ x : Real, 0 < x →
      exp ((EMLTree.eml A B).eval x) = exp (-(log β)) * exp (exp cA * (1 / x)) := by
  intro x hx
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  rw [hval, hA x hx, hB x hx, exp_c_sub_log_eq cA hx, ← exp_add]
  have e : -(log β) + exp cA * (1 / x) = exp cA * (1 / x) - log β := by
    mach_mpoly [exp cA, (1 / x : Real), log β]
  rw [e]

/-- **`A = c − log x`, `B = c' − log x`: the same shape with `v = 1`.**

The totalized log zeroes the right child past `exp c'`, leaving
`exp ((eml A B) x) = exp (exp c · (1/x))`, which is `v · exp (κ·w)` at `v = 1`. -/
theorem node_form_logA_logB (A B : EMLTree) (cA cB : Real)
    (hA : ∀ x : Real, 0 < x → A.eval x = cA - log x)
    (hB : ∀ x : Real, 0 < x → B.eval x = cB - log x) :
    ∀ x : Real, exp cB ≤ x → 0 < x →
      exp ((EMLTree.eml A B).eval x) = 1 * exp (exp cA * (1 / x)) := by
  intro x hcB hx
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  rw [hval, hA x hx, hB x hx, log_c_sub_log_eventually_zero cB x hcB,
    exp_c_sub_log_eq cA hx]
  have e : exp cA * (1 / x) - 0 = exp cA * (1 / x) := by
    mach_mpoly [exp cA, (1 / x : Real)]
  rw [e]
  have e2 : (1 : Real) * exp (exp cA * (1 / x)) = exp (exp cA * (1 / x)) := by mach_ring
  rw [e2]

/-- **`A` constant, `B = var`: a different shape — the node DECAYS to `0`.**

    exp ((eml A B) x)  =  exp (exp α) · (1/x)

Linear in `w`, not `v·exp (κ·w)`, so `target_rise_quadratic` does not apply and the target falls to
`1` rather than rising to a limit above it. Recorded explicitly because the two forms look alike and
are not: here `v` would have to be `0`, which the analytic lemmas exclude by hypothesis. -/
theorem node_form_constA_varB (A B : EMLTree) (α : Real)
    (hA : ∀ x : Real, 0 < x → A.eval x = α)
    (hB : ∀ x : Real, 0 < x → B.eval x = x) :
    ∀ x : Real, 0 < x → exp ((EMLTree.eml A B).eval x) = exp (exp α) * (1 / x) := by
  intro x hx
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  rw [hval, hA x hx, hB x hx]
  exact exp_c_sub_log_eq (exp α) hx

/-! ## ▸ The limit-`1` comparison, for a decaying node

`node_form_constA_varB` gives a node linear in `w`, so the target is `exp (M·w)` falling to `1` rather
than `exp (v·exp (κ·w))` rising to `exp v`. The dominance / sub-dominance split is the same, but with
no `v` to carry — which makes both halves shorter than their rising counterparts. -/

/-- **Limit-`1` dominance: the quadratic term survives when `M` covers `a`.**

    a ≤ M   ⟹   (M·w/2)²  ≤  exp (M·w) − 1 − a·w

`exp_two_ge_quadratic` at `z := M·w/2` gives `exp (M·w) ≥ 1 + M·w + z²`, and `a·w ≤ M·w` leaves `z²`.
Equality `a = M` is included, which is the limit-`1` cancellation locus. -/
theorem limit_one_quadratic_separation (M a w : Real) (hM : 0 < M) (hw : 0 < w) (hdom : a ≤ M) :
    (M * w * (1 / (1 + 1))) * (M * w * (1 / (1 + 1))) ≤ exp (M * w) - 1 - a * w := by
  have h2pos : (0 : Real) < 1 + 1 := by
    have u := add_lt_add_left zero_lt_one_ax 1
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at u; exact lt_trans_ax zero_lt_one_ax u
  have hhalf : (1 + 1 : Real) * (1 / (1 + 1)) = 1 := mul_inv _ (ne_of_gt h2pos)
  have hz0 : (0 : Real) ≤ M * w * (1 / (1 + 1)) :=
    le_of_lt (mul_pos (mul_pos hM hw) (one_div_pos_of_pos h2pos))
  have hzz : M * w * (1 / (1 + 1)) + M * w * (1 / (1 + 1)) = M * w := by
    have e : M * w * (1 / (1 + 1)) + M * w * (1 / (1 + 1))
        = M * w * ((1 + 1) * (1 / (1 + 1))) := by mach_ring
    rw [e, hhalf]; mach_ring
  have hq := exp_two_ge_quadratic hz0
  rw [hzz] at hq
  -- `z² ≤ exp (M w) − 1 − M w`
  have hstep := add_le_add_wit hq (le_refl (-(1 : Real) + -(M * w)))
  have l : 1 + M * w + M * w * (1 / (1 + 1)) * (M * w * (1 / (1 + 1))) + (-(1 : Real) + -(M * w))
      = M * w * (1 / (1 + 1)) * (M * w * (1 / (1 + 1))) := by
    mach_mpoly [M, w, (1 / (1 + 1) : Real)]
  have r : exp (M * w) + (-(1 : Real) + -(M * w)) = exp (M * w) - 1 - M * w := by
    mach_mpoly [exp (M * w), M, w]
  rw [l, r] at hstep
  refine le_trans hstep ?_
  -- `a w ≤ M w` weakens the subtraction
  have haw : a * w ≤ M * w := mul_le_mul_of_nonneg_right hdom (le_of_lt hw)
  have v := add_le_add_wit (le_refl (exp (M * w) - 1)) (neg_le_neg_wit haw)
  have l2 : exp (M * w) - 1 + -(M * w) = exp (M * w) - 1 - M * w := by
    mach_mpoly [exp (M * w), M, w]
  have r2 : exp (M * w) - 1 + -(a * w) = exp (M * w) - 1 - a * w := by
    mach_mpoly [exp (M * w), a, w]
  rw [l2, r2] at v; exact v

/-- **Limit-`1` sub-dominance: `Q` overtakes a target that falls too slowly.**

    M·(1 + M·w·e) < a   ⟹   exp (M·w) − 1  <  a·w

`exp_sub_exp_upper` at `(M·w, 0)` bounds the rise by `M·w·exp (M·w)`, and `exp_le_one_add_scaled`
caps the trailing factor at `1 + M·w·e` on `M·w ≤ 1`. The hypothesis is then exactly what makes the
coefficient lose to `a`, and it is satisfiable for any `a > M` by taking `w` small — the same
explicit-rate continuity as the rising case. -/
theorem limit_one_subdominant (M a w : Real) (hM : 0 < M) (hw : 0 < w)
    (hMw : M * w ≤ 1) (hsub : M * (1 + M * w * exp 1) < a) :
    exp (M * w) - 1 < a * w := by
  have hMw0 : (0 : Real) ≤ M * w := le_of_lt (mul_pos hM hw)
  -- `exp (Mw) − 1 ≤ Mw · exp (Mw)`
  have hup : exp (M * w) - 1 ≤ M * w * exp (M * w) := by
    have h := exp_sub_exp_upper (M * w) 0
    rw [exp_zero] at h
    have e : M * w - 0 = M * w := by mach_mpoly [M, w]
    rw [e] at h; exact h
  -- cap the trailing factor
  have hcap : M * w * exp (M * w) ≤ M * w * (1 + M * w * exp 1) :=
    mul_le_mul_of_nonneg_left (exp_le_one_add_scaled hMw0 hMw) hMw0
  refine lt_of_le_of_lt (le_trans hup hcap) ?_
  have hstrict := mul_lt_mul_of_pos_right hsub hw
  have l : M * (1 + M * w * exp 1) * w = M * w * (1 + M * w * exp 1) := by mach_ring
  rw [l] at hstrict; exact hstrict

/-- **The floor, in the shape the comparisons actually produce.**

`double_exp_floor_dominated` is multiplicative — `floor · x² ≤ β` — because that form needed no
reciprocals to prove. The separation lemmas deliver `β · (1/x)·(1/x)`, so this converts once, here,
rather than at every call site. Multiplying by `(1/x)·(1/x)` and cancelling `x·(1/x) = 1` twice does
it, and `1/(x·x)` never has to be mentioned. -/
theorem floor_le_inv_sq (β : Real) (hβ : 0 < β) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → exp (-C - exp x) ≤ β * ((1 / x) * (1 / x)) := by
  obtain ⟨C, hC⟩ := double_exp_floor_dominated β hβ
  refine ⟨C, ?_⟩
  intro x hx
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
  have hinv : x * (1 / x) = 1 := mul_inv x (ne_of_gt hxpos)
  have hinvpos : (0 : Real) < (1 / x) * (1 / x) :=
    mul_pos (one_div_pos_of_pos hxpos) (one_div_pos_of_pos hxpos)
  have h := mul_le_mul_of_nonneg_right (hC x hx) (le_of_lt hinvpos)
  have l : exp (-C - exp x) * (x * x) * ((1 / x) * (1 / x))
      = exp (-C - exp x) * ((x * (1 / x)) * (x * (1 / x))) := by mach_ring
  rw [l, hinv] at h
  have e : exp (-C - exp x) * ((1 : Real) * 1) = exp (-C - exp x) := by mach_ring
  rw [e] at h; exact h

/-- **A decaying target with the dominant coefficient: the cell holds with a `Θ(1/x²)` margin.**

The first branch of this assembly to produce a *bound* rather than a vacuity. `T = exp (M·w)` falls to
`1`; `Q = 1 + a·w` rises from it; `a ≤ M` means the target's linear term covers `Q`'s, so
`limit_one_quadratic_separation` leaves `(M·w/2)²`, and `floor_le_inv_sq` converts that to the
obligation's floor.

**`a = M` is inside the hypothesis**, so the limit-`1` cancellation locus is discharged here rather
than left as a boundary case. -/
theorem cell_of_decaying_target_dominant (A B Q : EMLTree) (M a XT XQ : Real)
    (hM : 0 < M) (ha : 0 < a) (hdom : a ≤ M)
    (hT : ∀ x : Real, XT ≤ x → exp (exp ((EMLTree.eml A B).eval x)) = exp (M * (1 / x)))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = 1 + a * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hβ : (0 : Real) < (M * (1 / (1 + 1))) * (M * (1 / (1 + 1))) := by
    have h2pos : (0 : Real) < 1 + 1 := by
      have u := add_lt_add_left zero_lt_one_ax 1
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at u; exact lt_trans_ax zero_lt_one_ax u
    exact mul_pos (mul_pos hM (one_div_pos_of_pos h2pos))
      (mul_pos hM (one_div_pos_of_pos h2pos))
  obtain ⟨C, hC⟩ := floor_le_inv_sq _ hβ
  refine ⟨C, 1 + exp XT + exp XQ, ?_, ?_⟩
  · have v : (1 : Real) + 0 + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx _ _
  have hone : (1 : Real) ≤ x := by
    have v : (1 : Real) + 0 + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hXTx : XT ≤ x := by
    have v : (0 : Real) + exp XT + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))
    have e : (0 : Real) + exp XT + 0 = exp XT := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XT) (le_trans v hx)
  have hXQx : XQ ≤ x := by
    have v : (0 : Real) + 0 + exp XQ ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XT)))
        (le_refl _)
    have e : (0 : Real) + 0 + exp XQ = exp XQ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XQ) (le_trans v hx)
  rw [hT x hXTx, hQ x hXQx]
  have hsep := limit_one_quadratic_separation M a (1 / x) hM (one_div_pos_of_pos hxpos) hdom
  have heq : (M * (1 / (1 + 1))) * (M * (1 / (1 + 1))) * ((1 / x) * (1 / x))
      = (M * (1 / x) * (1 / (1 + 1))) * (M * (1 / x) * (1 / (1 + 1))) := by mach_ring
  have hgoal : exp (M * (1 / x)) - 1 - a * (1 / x)
      = exp (M * (1 / x)) - (1 + a * (1 / x)) := by
    mach_mpoly [exp (M * (1 / x)), a, (1 / x : Real)]
  rw [← hgoal]
  refine le_trans (hC x hone) ?_
  rw [heq]
  exact hsep

/-- **A decaying target with the sub-dominant coefficient: the region is empty.**

Companion to `cell_of_decaying_target_dominant`. With `M < a` the target's linear term cannot cover
`Q`'s, `limit_one_subdominant` gives `T − 1 < a·w = Q − 1`, and the guard `Q x < T x` fails.

The threshold comes from `shrink_below_two_bounds` at `A := M` and
`S := (a − M)·(1/(M·e))`: it delivers one `w` below both `1/M` — so `M·w ≤ 1` for
`exp_le_one_add_scaled` — and below `S`, which is exactly `M·(1 + M·w·e) < a`. `one_div_antitone`
carries the bound from `x ≥ D` to `w ≤ 1/D`.

Together with the dominant case this closes the decaying-target regime: `a ≤ M` bounded,
`a > M` empty, and the two are complements. -/
theorem cell_of_decaying_target_subdominant (A B Q : EMLTree) (M a XT XQ : Real)
    (hM : 0 < M) (hlt : M < a)
    (hT : ∀ x : Real, XT ≤ x → exp (exp ((EMLTree.eml A B).eval x)) = exp (M * (1 / x)))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = 1 + a * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hE1 : (0 : Real) < exp 1 := exp_pos 1
  have hdiff : (0 : Real) < a - M := by
    have u := add_lt_add_left hlt (-M)
    have l : -M + M = 0 := by mach_ring
    have r : -M + a = a - M := by mach_mpoly [a, M]
    rw [l, r] at u; exact u
  have hS : (0 : Real) < (a - M) * (1 / (M * exp 1)) :=
    mul_pos hdiff (one_div_pos_of_pos (mul_pos hM hE1))
  obtain ⟨hD, hlt1, hltS⟩ := shrink_below_two_bounds M ((a - M) * (1 / (M * exp 1))) hM hS
  refine ⟨0, 1 + exp XT + exp XQ + (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1), ?_, ?_⟩
  · have v : (1 : Real) + 0 + 0 + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))) (le_of_lt hD)
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx _ hguard
  exfalso
  have grab : ∀ Y : Real, Y ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1)
      → Y ≤ x := fun Y hY => le_trans hY hx
  have hXTx : XT ≤ x := by
    refine grab XT (le_trans (self_le_exp XT) ?_)
    have v : (0 : Real) + exp XT + 0 + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))) (le_of_lt hD)
    have e : (0 : Real) + exp XT + 0 + 0 = exp XT := by mach_ring
    rw [e] at v; exact v
  have hXQx : XQ ≤ x := by
    refine grab XQ (le_trans (self_le_exp XQ) ?_)
    have v : (0 : Real) + 0 + exp XQ + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_refl _)) (le_of_lt hD)
    have e : (0 : Real) + 0 + exp XQ + 0 = exp XQ := by mach_ring
    rw [e] at v; exact v
  have hDx : M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1 ≤ x := by
    refine grab _ ?_
    have v : (0 : Real) + 0 + 0 + (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1)
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_of_lt (exp_pos XQ))) (le_refl _)
    have e : (0 : Real) + 0 + 0 + (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1)
        = M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1 := by mach_ring
    rw [e] at v; exact v
  have hxpos : (0 : Real) < x := lt_of_lt_of_le hD hDx
  have hwle : 1 / x ≤ 1 / (M + M * (1 / ((a - M) * (1 / (M * exp 1)))) + 1) :=
    one_div_antitone hD hDx
  have hwpos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  -- `M·w ≤ 1`
  have hMw : M * (1 / x) ≤ 1 :=
    le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwle (le_of_lt hM)) hlt1)
  -- `M·(1 + M·w·e) < a`
  have hMwS : M * (1 / x) < (a - M) * (1 / (M * exp 1)) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwle (le_of_lt hM)) hltS
  have hcancel := mul_lt_mul_of_pos_right hMwS (mul_pos hM hE1)
  have lr : (a - M) * (1 / (M * exp 1)) * (M * exp 1) = a - M := by
    have e : (a - M) * (1 / (M * exp 1)) * (M * exp 1)
        = (a - M) * ((M * exp 1) * (1 / (M * exp 1))) := by mach_ring
    rw [e, mul_inv _ (ne_of_gt (mul_pos hM hE1))]; mach_ring
  rw [lr] at hcancel
  have hsubh : M * (1 + M * (1 / x) * exp 1) < a := by
    have u := add_lt_add_left hcancel M
    have l : M + M * (1 / x) * (M * exp 1) = M * (1 + M * (1 / x) * exp 1) := by
      mach_mpoly [M, (1 / x : Real), exp 1]
    have r : M + (a - M) = a := by mach_mpoly [a, M]
    rw [l, r] at u; exact u
  have hfinal := limit_one_subdominant M a (1 / x) hM hwpos hMw hsubh
  rw [hT x hXTx, hQ x hXQx] at hguard
  have hcontra : exp (M * (1 / x)) < 1 + a * (1 / x) := by
    have u := add_lt_add_left hfinal (1 : Real)
    have l : (1 : Real) + (exp (M * (1 / x)) - 1) = exp (M * (1 / x)) := by
      mach_mpoly [exp (M * (1 / x))]
    rw [l] at u; exact u
  exact lt_irrefl_ax _ (lt_trans_ax hguard hcontra)

/-- **A rising target with the dominant coefficient: bounded, with a `Θ(1/x²)` margin.**

The `v`-carrying counterpart of `cell_of_decaying_target_dominant`. `node_form_logA_constB` puts the
node at `v·exp (κ·w)`, so the target rises to `exp v`; `Q` rises to the same limit at rate `aQ·w`.
The dominance condition is **independent of `x`** — the common `w` cancels — leaving
`aQ ≤ exp v · v · κ`, and `target_rise_quadratic` then yields `exp v · z²` with `z = v·κ·w/2`.

Equality is inside the hypothesis, so the rising cancellation locus is discharged here. -/
theorem cell_of_rising_target_dominant (A B Q : EMLTree) (v κ aQ XT XQ : Real)
    (hv : 0 < v) (hκ : 0 < κ) (hdom : aQ ≤ exp v * (v * κ))
    (hT : ∀ x : Real, XT ≤ x →
      exp (exp ((EMLTree.eml A B).eval x)) = exp (v * exp (κ * (1 / x))))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = exp v + aQ * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have h2pos : (0 : Real) < 1 + 1 := by
    have u := add_lt_add_left zero_lt_one_ax 1
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at u; exact lt_trans_ax zero_lt_one_ax u
  have hhpos : (0 : Real) < 1 / (1 + 1) := one_div_pos_of_pos h2pos
  have hβ : (0 : Real) < exp v * ((v * κ * (1 / (1 + 1))) * (v * κ * (1 / (1 + 1)))) :=
    mul_pos (exp_pos v)
      (mul_pos (mul_pos (mul_pos hv hκ) hhpos) (mul_pos (mul_pos hv hκ) hhpos))
  obtain ⟨C, hC⟩ := floor_le_inv_sq _ hβ
  refine ⟨C, 1 + exp XT + exp XQ, ?_, ?_⟩
  · have v0 : (1 : Real) + 0 + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact v0
  intro x hx _ _
  have hone : (1 : Real) ≤ x := by
    have v0 : (1 : Real) + 0 + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact le_trans v0 hx
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hwpos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hXTx : XT ≤ x := by
    have v0 : (0 : Real) + exp XT + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))
    have e : (0 : Real) + exp XT + 0 = exp XT := by mach_ring
    rw [e] at v0; exact le_trans (self_le_exp XT) (le_trans v0 hx)
  have hXQx : XQ ≤ x := by
    have v0 : (0 : Real) + 0 + exp XQ ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XT)))
        (le_refl _)
    have e : (0 : Real) + 0 + exp XQ = exp XQ := by mach_ring
    rw [e] at v0; exact le_trans (self_le_exp XQ) (le_trans v0 hx)
  -- the dominance condition, scaled by `w`
  have hdomw : aQ * (1 / x) ≤ exp v * (v * κ * (1 / x)) := by
    have h := mul_le_mul_of_nonneg_right hdom (le_of_lt hwpos)
    have e : exp v * (v * κ) * (1 / x) = exp v * (v * κ * (1 / x)) := by mach_ring
    rw [e] at h; exact h
  have hsep := target_rise_quadratic v κ (1 / x) (aQ * (1 / x)) hv hκ hwpos hdomw
  rw [hT x hXTx, hQ x hXQx]
  have hgoal : exp (v * exp (κ * (1 / x))) - exp v - aQ * (1 / x)
      = exp (v * exp (κ * (1 / x))) - (exp v + aQ * (1 / x)) := by
    mach_mpoly [exp (v * exp (κ * (1 / x))), exp v, aQ, (1 / x : Real)]
  rw [← hgoal]
  refine le_trans (hC x hone) ?_
  have heq : exp v * ((v * κ * (1 / (1 + 1))) * (v * κ * (1 / (1 + 1)))) * ((1 / x) * (1 / x))
      = exp v * ((v * κ * (1 / x) * (1 / (1 + 1))) * (v * κ * (1 / x) * (1 / (1 + 1)))) := by
    mach_ring
  rw [heq]; exact hsep

/-- **A rising target with the sub-dominant coefficient: the region is empty.**

`subdominant_coefficient_vacuous` already carries its own threshold, so this only has to convert it
from a bound on `w` to a bound on `x` — `one_div_antitone` and `one_div_one_div_pos`, both of which
this file already had. `target_rise_upper` then puts the target's rise under that bound, `Q` overtakes
it, and the guard fails.

With the dominant case this closes the rising regime, as its decaying twin was closed one commit
ago. -/
theorem cell_of_rising_target_subdominant (A B Q : EMLTree) (v κ aQ XT XQ : Real)
    (hv : 0 < v) (hκ : 0 < κ) (hsub : v * κ * exp v < aQ)
    (hT : ∀ x : Real, XT ≤ x →
      exp (exp ((EMLTree.eml A B).eval x)) = exp (v * exp (κ * (1 / x))))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = exp v + aQ * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  obtain ⟨w₀, hw₀, hvac⟩ := subdominant_coefficient_vacuous v κ aQ hv hκ hsub
  refine ⟨0, 1 + exp XT + exp XQ + 1 / w₀, ?_, ?_⟩
  · have v0 : (1 : Real) + 0 + 0 + 0 ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))) (le_of_lt (one_div_pos_of_pos hw₀))
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact v0
  intro x hx _ hguard
  exfalso
  have grab : ∀ Y : Real, Y ≤ 1 + exp XT + exp XQ + 1 / w₀ → Y ≤ x := fun Y hY => le_trans hY hx
  have hone : (1 : Real) ≤ x := by
    refine grab 1 ?_
    have v0 : (1 : Real) + 0 + 0 + 0 ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))) (le_of_lt (one_div_pos_of_pos hw₀))
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact v0
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hwpos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hXTx : XT ≤ x := by
    refine grab XT (le_trans (self_le_exp XT) ?_)
    have v0 : (0 : Real) + exp XT + 0 + 0 ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))) (le_of_lt (one_div_pos_of_pos hw₀))
    have e : (0 : Real) + exp XT + 0 + 0 = exp XT := by mach_ring
    rw [e] at v0; exact v0
  have hXQx : XQ ≤ x := by
    refine grab XQ (le_trans (self_le_exp XQ) ?_)
    have v0 : (0 : Real) + 0 + exp XQ + 0 ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_refl _)) (le_of_lt (one_div_pos_of_pos hw₀))
    have e : (0 : Real) + 0 + exp XQ + 0 = exp XQ := by mach_ring
    rw [e] at v0; exact v0
  -- `w = 1/x ≤ w₀`
  have hinvx : 1 / w₀ ≤ x := by
    refine grab _ ?_
    have v0 : (0 : Real) + 0 + 0 + 1 / w₀ ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_of_lt (exp_pos XQ))) (le_refl _)
    have e : (0 : Real) + 0 + 0 + 1 / w₀ = 1 / w₀ := by mach_ring
    rw [e] at v0; exact v0
  have hwle : 1 / x ≤ w₀ := by
    have h := one_div_antitone (one_div_pos_of_pos hw₀) hinvx
    rw [one_div_one_div_pos hw₀] at h; exact h
  -- the target's rise is under `aQ·w`
  have hupper := target_rise_upper v κ (1 / x) hv
  have hstrict := hvac (1 / x) hwpos hwle
  rw [hT x hXTx, hQ x hXQx] at hguard
  have hcontra : exp (v * exp (κ * (1 / x))) < exp v + aQ * (1 / x) := by
    have h := lt_of_le_of_lt hupper hstrict
    have u := add_lt_add_left h (exp v)
    have l : exp v + (exp (v * exp (κ * (1 / x))) - exp v) = exp (v * exp (κ * (1 / x))) := by
      mach_mpoly [exp (v * exp (κ * (1 / x))), exp v]
    rw [l] at u; exact u
  exact lt_irrefl_ax _ (lt_trans_ax hguard hcontra)

/-- **The right-child dichotomy: either the cell is already proved, or `R` is one of two shapes.**

Mirror of `boundedEmlCell_left_dichotomy`, and the step that finishes the `Q` side. Three of `R`'s
five forms send `log (R x)` past `Kb − 1`, which drives `Q = exp (P x) − log (R x)` below the guard
`1 < Q x` and empties the region:

* `var` — `log x ≥ Kb − 1` past `exp (Kb − 1)`, by `log_ge_sub_one_of_exp_pred_le`.
* `exp x − d` — `log (R x) ≥ x − 1` by `log_exp_sub_const_ge_linear`, past `d + 1`.
* `exp x − log x` — likewise by `log_exp_sub_log_ge_linear`.

The surviving two are `const` and `c − log x`, matching the left child. Note the mechanism differs
from the left dichotomy's: there `Q` grew past the cap, here it falls below `1`. Same conclusion, two
guards. -/
theorem boundedEmlCell_right_dichotomy (A B P R : EMLTree) (hR : R.depth ≤ 1) (Kb XP : Real)
    (hP : ∀ x : Real, XP ≤ x → exp (P.eval x) ≤ Kb) :
    (∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < (EMLTree.eml P R).eval x →
        (EMLTree.eml P R).eval x < exp (exp ((EMLTree.eml A B).eval x)) →
          exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - (EMLTree.eml P R).eval x)
    ∨ (∃ β : Real, ∀ x : Real, 0 < x → R.eval x = β)
    ∨ (∃ cR : Real, 0 < cR ∧ ∀ x : Real, 0 < x → R.eval x = cR - log x) := by
  rcases depth_le_one_classification R hR with
      ⟨β, hb⟩ | hb | ⟨cR, hcR0, hb⟩ | ⟨d, hb⟩ | hb
  · exact Or.inr (Or.inl ⟨β, hb⟩)
  · -- `R = var`
    refine Or.inl (boundedEmlCell_vacuous_of_large_log_right A B P R Kb XP (exp (Kb - 1)) hP ?_)
    intro x hx
    have hx0 : (0 : Real) < x := lt_of_lt_of_le (exp_pos (Kb - 1)) hx
    rw [hb x hx0]
    have h := log_ge_sub_one_of_exp_pred_le (x := Kb) (z := x) hx
    exact h
  · exact Or.inr (Or.inr ⟨cR, hcR0, hb⟩)
  · -- `R = exp x − d`
    refine Or.inl (boundedEmlCell_vacuous_of_large_log_right A B P R Kb XP
      (1 + exp (d + 1) + exp Kb) hP ?_)
    intro x hx
    have hd1 : d + 1 ≤ x := by
      have v : (0 : Real) + exp (d + 1) + 0 ≤ 1 + exp (d + 1) + exp Kb :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
          (le_of_lt (exp_pos Kb))
      have e : (0 : Real) + exp (d + 1) + 0 = exp (d + 1) := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp (d + 1)) (le_trans v hx)
    have hKb : Kb ≤ x := by
      have v : (0 : Real) + 0 + exp Kb ≤ 1 + exp (d + 1) + exp Kb :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos (d + 1))))
          (le_refl _)
      have e : (0 : Real) + 0 + exp Kb = exp Kb := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp Kb) (le_trans v hx)
    have hone : (1 : Real) ≤ x := by
      have v : (1 : Real) + 0 + 0 ≤ 1 + exp (d + 1) + exp Kb :=
        add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos (d + 1))))
          (le_of_lt (exp_pos Kb))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact le_trans v hx
    have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
    rw [hb x hx0]
    refine le_trans ?_ (log_exp_sub_const_ge_linear d hd1)
    have v := add_le_add_wit hKb (le_refl (-(1 : Real)))
    have l : Kb + -(1 : Real) = Kb - 1 := by mach_mpoly [Kb]
    have r : x + -(1 : Real) = x - 1 := by mach_mpoly [x]
    rw [l, r] at v; exact v
  · -- `R = exp x − log x`
    refine Or.inl (boundedEmlCell_vacuous_of_large_log_right A B P R Kb XP
      (1 + exp Kb) hP ?_)
    intro x hx
    have hone : (1 : Real) ≤ x := by
      have v : (1 : Real) + 0 ≤ 1 + exp Kb := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos Kb))
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at v; exact le_trans v hx
    have hKb : Kb ≤ x := by
      have v : (0 : Real) + exp Kb ≤ 1 + exp Kb :=
        add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
      have e : (0 : Real) + exp Kb = exp Kb := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp Kb) (le_trans v hx)
    have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
    rw [hb x hx0]
    refine le_trans ?_ (log_exp_sub_log_ge_linear hone)
    have v := add_le_add_wit hKb (le_refl (-(1 : Real)))
    have l : Kb + -(1 : Real) = Kb - 1 := by mach_mpoly [Kb]
    have r : x + -(1 : Real) = x - 1 := by mach_mpoly [x]
    rw [l, r] at v; exact v

/-- **Separated limits: a constant between them closes the cell, with a UNIFORM gap.**

The generic branch, and much the cheapest. When the target and `Q` tend to different limits, any `k`
strictly between them eventually satisfies both `k ≤ T x` and `Q x < k`, and
`gap_below_constant_barrier` returns a **uniform** `ε` — far more than the obligation's
`exp (−C − exp x)`.

Neither limit appears in the statement. All that is needed is a constant the two are eventually on
opposite sides of, which is a weaker and much easier thing to supply than a limit computation. Only
when no such constant exists — the limits coincide — is the first/second-order comparison required,
which is exactly where the census located the cancellation locus. -/
theorem cell_of_separated_limits (A B Q : EMLTree) (hQ : Q.depth ≤ 2) (k XT XQ : Real)
    (hT : ∀ x : Real, XT ≤ x → k ≤ exp (exp ((EMLTree.eml A B).eval x)))
    (hQlt : ∀ x : Real, XQ ≤ x → Q.eval x < k) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  obtain ⟨C, X₀, hX₀, h⟩ :=
    gap_below_constant_barrier Q hQ (fun x => exp (exp ((EMLTree.eml A B).eval x))) k XT hT
  refine ⟨C, X₀ + exp XQ, ?_, ?_⟩
  · have v : X₀ + 0 ≤ X₀ + exp XQ := add_le_add_wit (le_refl _) (le_of_lt (exp_pos XQ))
    have e : X₀ + (0 : Real) = X₀ := by mach_ring
    rw [e] at v; exact le_trans hX₀ v
  intro x hx _ _
  have hX₀x : X₀ ≤ x := by
    have v : X₀ + 0 ≤ X₀ + exp XQ := add_le_add_wit (le_refl _) (le_of_lt (exp_pos XQ))
    have e : X₀ + (0 : Real) = X₀ := by mach_ring
    rw [e] at v; exact le_trans v hx
  have hXQx : XQ ≤ x := by
    have v : (0 : Real) + exp XQ ≤ X₀ + exp XQ :=
      add_le_add_wit (le_trans (le_of_lt zero_lt_one_ax) hX₀) (le_refl _)
    have e : (0 : Real) + exp XQ = exp XQ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XQ) (le_trans v hx)
  exact h x hX₀x (hQlt x hXQx)

/-- **The other side of separation: `Q` above the target is empty.**

If `Q` eventually sits at or above the target, the guard `Q x < T x` fails and there is nothing to
prove. Stated as its own lemma because the two separated-limit orientations need different
treatments — one produces a bound, the other a vacuity — and reading which is which off a limit
comparison is where an assembly quietly goes wrong. -/
theorem cell_of_Q_above_target (A B Q : EMLTree) (X₁ : Real)
    (habove : ∀ x : Real, X₁ ≤ x → exp (exp ((EMLTree.eml A B).eval x)) ≤ Q.eval x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  refine ⟨0, 1 + exp X₁, ?_, ?_⟩
  · have v : (1 : Real) + 0 ≤ 1 + exp X₁ :=
      add_le_add_wit (le_refl 1) (le_of_lt (exp_pos X₁))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx _ hguard
  exfalso
  have hX₁x : X₁ ≤ x := by
    have v : (0 : Real) + exp X₁ ≤ 1 + exp X₁ :=
      add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
    have e : (0 : Real) + exp X₁ = exp X₁ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp X₁) (le_trans v hx)
  exact lt_irrefl_ax _ (lt_of_lt_of_le hguard (habove x hX₁x))

/-- **Rising target, `Q` below its limit: the barrier is the target's own limit.**

The limit comparison the router needs, in the generic orientation. A rising target never falls below
`exp v`, so `k := exp v` is a barrier for free — no `k` has to be found strictly between the two
limits, which is the step that would otherwise need both of them computed.

`Q` clears it because `LQ < exp v` and `Q` descends to `LQ`: the threshold is
`1 + aQ·(1/(exp v − LQ))`, and `cell_of_separated_limits` then returns a **uniform** gap. -/
theorem cell_of_rising_target_lower_Q (A B Q : EMLTree) (hQd : Q.depth ≤ 2)
    (v κ LQ aQ XT XQ : Real) (hv : 0 < v) (hκ : 0 < κ) (haQ : 0 < aQ)
    (hsep : LQ < exp v)
    (hT : ∀ x : Real, XT ≤ x →
      exp (exp ((EMLTree.eml A B).eval x)) = exp (v * exp (κ * (1 / x))))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = LQ + aQ * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hδ : (0 : Real) < exp v - LQ := by
    have u := add_lt_add_left hsep (-LQ)
    have l : -LQ + LQ = 0 := by mach_ring
    have r : -LQ + exp v = exp v - LQ := by mach_mpoly [exp v, LQ]
    rw [l, r] at u; exact u
  refine cell_of_separated_limits A B Q hQd (exp v) (1 + exp XT) (1 + exp XQ + aQ * (1 / (exp v - LQ))) ?_ ?_
  · -- the rising target never dips below `exp v`
    intro x hx
    have hone : (1 : Real) ≤ x := by
      have v0 : (1 : Real) + 0 ≤ 1 + exp XT := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT))
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at v0; exact le_trans v0 hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
    have hXTx : XT ≤ x := by
      have v0 : (0 : Real) + exp XT ≤ 1 + exp XT :=
        add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
      have e : (0 : Real) + exp XT = exp XT := by mach_ring
      rw [e] at v0; exact le_trans (self_le_exp XT) (le_trans v0 hx)
    rw [hT x hXTx]
    refine exp_monotone ?_
    -- `v ≤ v * exp (κ w)` since `exp (κ w) ≥ 1`
    have hkw : (0 : Real) ≤ κ * (1 / x) := le_of_lt (mul_pos hκ (one_div_pos_of_pos hxpos))
    have hge1 : (1 : Real) ≤ exp (κ * (1 / x)) := by
      have h := exp_monotone hkw
      rw [exp_zero] at h; exact h
    have h := mul_le_mul_of_nonneg_left hge1 (le_of_lt hv)
    have e : v * (1 : Real) = v := by mach_ring
    rw [e] at h; exact h
  · -- `Q` descends below `exp v`
    intro x hx
    have hone : (1 : Real) ≤ x := by
      have v0 : (1 : Real) + 0 + 0 ≤ 1 + exp XQ + aQ * (1 / (exp v - LQ)) :=
        add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XQ)))
          (le_of_lt (mul_pos haQ (one_div_pos_of_pos hδ)))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v0; exact le_trans v0 hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
    have hXQx : XQ ≤ x := by
      have v0 : (0 : Real) + exp XQ + 0 ≤ 1 + exp XQ + aQ * (1 / (exp v - LQ)) :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
          (le_of_lt (mul_pos haQ (one_div_pos_of_pos hδ)))
      have e : (0 : Real) + exp XQ + 0 = exp XQ := by mach_ring
      rw [e] at v0; exact le_trans (self_le_exp XQ) (le_trans v0 hx)
    have hthr : aQ * (1 / (exp v - LQ)) < x := by
      have v0 : (0 : Real) + 0 + aQ * (1 / (exp v - LQ)) ≤ 1 + exp XQ + aQ * (1 / (exp v - LQ)) :=
        add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XQ)))
          (le_refl _)
      have e : (0 : Real) + 0 + aQ * (1 / (exp v - LQ)) = aQ * (1 / (exp v - LQ)) := by mach_ring
      rw [e] at v0
      have hstrict : aQ * (1 / (exp v - LQ)) < 1 + exp XQ + aQ * (1 / (exp v - LQ)) := by
        have w := add_lt_add_left (add_lt_add_left (exp_pos XQ) (1 : Real)) (aQ * (1 / (exp v - LQ)))
        have l : aQ * (1 / (exp v - LQ)) + (1 + 0) = aQ * (1 / (exp v - LQ)) + 1 := by mach_ring
        have r : aQ * (1 / (exp v - LQ)) + (1 + exp XQ)
            = 1 + exp XQ + aQ * (1 / (exp v - LQ)) := by
          mach_mpoly [aQ, (1 / (exp v - LQ) : Real), exp XQ]
        rw [l, r] at w
        refine lt_trans_ax ?_ w
        have u := add_lt_add_left zero_lt_one_ax (aQ * (1 / (exp v - LQ)))
        have l2 : aQ * (1 / (exp v - LQ)) + (0 : Real) = aQ * (1 / (exp v - LQ)) := by mach_ring
        rw [l2] at u; exact u
      exact lt_of_lt_of_le hstrict hx
    -- `aQ < δ x`, hence `aQ (1/x) < δ`
    have hδx : aQ < (exp v - LQ) * x := by
      have h := mul_lt_mul_of_pos_right hthr hδ
      have l : aQ * (1 / (exp v - LQ)) * (exp v - LQ)
          = aQ * ((exp v - LQ) * (1 / (exp v - LQ))) := by mach_ring
      rw [l, mul_inv _ (ne_of_gt hδ)] at h
      have e : aQ * (1 : Real) = aQ := by mach_ring
      rw [e] at h
      have r : x * (exp v - LQ) = (exp v - LQ) * x := by mach_ring
      rw [r] at h; exact h
    have hscaled := mul_lt_mul_of_pos_right hδx (one_div_pos_of_pos hxpos)
    have l2 : (exp v - LQ) * x * (1 / x) = (exp v - LQ) * (x * (1 / x)) := by mach_ring
    rw [l2, mul_inv x (ne_of_gt hxpos)] at hscaled
    have e2 : (exp v - LQ) * (1 : Real) = exp v - LQ := by mach_ring
    rw [e2] at hscaled
    rw [hQ x hXQx]
    have u := add_lt_add_left hscaled LQ
    have r : LQ + (exp v - LQ) = exp v := by mach_mpoly [exp v, LQ]
    rw [r] at u; exact u

/-- **Rising target, `Q` above its limit: the region is empty.**

The third orientation, and the only one that genuinely needs the target's approach RATE rather than
just its monotonicity. `Q ≥ LQ > exp v` while the target descends to `exp v`, so the guard fails once
the target is within `LQ − exp v` of its limit.

`target_rise_upper_linearised` bounds the rise by `v·κ·exp (v + κw(1+v·e))·w`, and on `κw ≤ 1` the
exponential factor is capped by the constant `E' := exp (v + (1 + v·e))`. What is left is
`v·κ·E'·w < δ`, and `shrink_below_two_bounds` at `A := κ`, `S := δ·(1/(v·E'))` delivers a single `w`
satisfying both that and `κw ≤ 1` — the same device as the sub-dominant thresholds, third use. -/
theorem cell_of_rising_target_upper_Q (A B Q : EMLTree) (v κ LQ aQ XT XQ : Real)
    (hv : 0 < v) (hκ : 0 < κ) (haQ : 0 < aQ) (hsep : exp v < LQ)
    (hT : ∀ x : Real, XT ≤ x →
      exp (exp ((EMLTree.eml A B).eval x)) = exp (v * exp (κ * (1 / x))))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = LQ + aQ * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hE1 : (0 : Real) < exp 1 := exp_pos 1
  have hδ : (0 : Real) < LQ - exp v := by
    have u := add_lt_add_left hsep (-(exp v))
    have l : -(exp v) + exp v = 0 := by mach_ring
    have r : -(exp v) + LQ = LQ - exp v := by mach_mpoly [LQ, exp v]
    rw [l, r] at u; exact u
  have hEp : (0 : Real) < exp (v + (1 + v * exp 1)) := exp_pos _
  have hS : (0 : Real) < (LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))) :=
    mul_pos hδ (one_div_pos_of_pos (mul_pos hv hEp))
  obtain ⟨hD, hlt1, hltS⟩ :=
    shrink_below_two_bounds κ ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1))))) hκ hS
  refine cell_of_Q_above_target A B Q
    (1 + exp XT + exp XQ + (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1)) ?_
  intro x hx
  have grab : ∀ Y : Real,
      Y ≤ 1 + exp XT + exp XQ + (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1)
      → Y ≤ x := fun Y hY => le_trans hY hx
  have hone : (1 : Real) ≤ x := by
    refine grab 1 ?_
    have v0 : (1 : Real) + 0 + 0 + 0
        ≤ 1 + exp XT + exp XQ + (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))) (le_of_lt hD)
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact v0
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hwpos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hXTx : XT ≤ x := by
    refine grab XT (le_trans (self_le_exp XT) ?_)
    have v0 : (0 : Real) + exp XT + 0 + 0
        ≤ 1 + exp XT + exp XQ + (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))) (le_of_lt hD)
    have e : (0 : Real) + exp XT + 0 + 0 = exp XT := by mach_ring
    rw [e] at v0; exact v0
  have hXQx : XQ ≤ x := by
    refine grab XQ (le_trans (self_le_exp XQ) ?_)
    have v0 : (0 : Real) + 0 + exp XQ + 0
        ≤ 1 + exp XT + exp XQ + (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_refl _)) (le_of_lt hD)
    have e : (0 : Real) + 0 + exp XQ + 0 = exp XQ := by mach_ring
    rw [e] at v0; exact v0
  have hDx : κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1 ≤ x := by
    refine grab _ ?_
    have v0 : (0 : Real) + 0 + 0 + (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1)
        ≤ 1 + exp XT + exp XQ + (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_of_lt (exp_pos XQ))) (le_refl _)
    have e : (0 : Real) + 0 + 0 + (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1)
        = κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1 := by mach_ring
    rw [e] at v0; exact v0
  have hwle : 1 / x ≤ 1 / (κ + κ * (1 / ((LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))))) + 1) :=
    one_div_antitone hD hDx
  have hκw1 : κ * (1 / x) ≤ 1 :=
    le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwle (le_of_lt hκ)) hlt1)
  have hκwS : κ * (1 / x) < (LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwle (le_of_lt hκ)) hltS
  -- the target's rise is under `δ`
  have hrise : exp (v * exp (κ * (1 / x))) - exp v
      ≤ v * κ * exp (v + κ * (1 / x) * (1 + v * exp 1)) * (1 / x) :=
    le_trans (target_rise_upper v κ (1 / x) hv)
      (target_rise_upper_linearised v κ (1 / x) hv hκ hwpos hκw1)
  have hcap : exp (v + κ * (1 / x) * (1 + v * exp 1)) ≤ exp (v + (1 + v * exp 1)) := by
    refine exp_monotone ?_
    have hfac : (0 : Real) ≤ 1 + v * exp 1 := by
      have u := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (mul_pos hv hE1))
      have e : (0 : Real) + 0 = 0 := by mach_ring
      rw [e] at u; exact u
    have h := mul_le_mul_of_nonneg_right hκw1 hfac
    have e : (1 : Real) * (1 + v * exp 1) = 1 + v * exp 1 := by mach_ring
    rw [e] at h
    exact add_le_add_wit (le_refl v) h
  have hbound : exp (v * exp (κ * (1 / x))) - exp v
      ≤ v * exp (v + (1 + v * exp 1)) * (κ * (1 / x)) := by
    refine le_trans hrise ?_
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap (le_of_lt (mul_pos hv hκ))) (le_of_lt hwpos)
    have l : v * κ * exp (v + κ * (1 / x) * (1 + v * exp 1)) * (1 / x)
        = v * κ * exp (v + κ * (1 / x) * (1 + v * exp 1)) * (1 / x) := rfl
    have r : v * κ * exp (v + (1 + v * exp 1)) * (1 / x)
        = v * exp (v + (1 + v * exp 1)) * (κ * (1 / x)) := by mach_ring
    rw [r] at h; exact h
  -- `v·E'·(κw) < δ`
  have hfinal : v * exp (v + (1 + v * exp 1)) * (κ * (1 / x)) < LQ - exp v := by
    have h := mul_lt_mul_of_pos_right hκwS (mul_pos hv hEp)
    have l : κ * (1 / x) * (v * exp (v + (1 + v * exp 1)))
        = v * exp (v + (1 + v * exp 1)) * (κ * (1 / x)) := by mach_ring
    have r : (LQ - exp v) * (1 / (v * exp (v + (1 + v * exp 1)))) * (v * exp (v + (1 + v * exp 1)))
        = (LQ - exp v) * ((v * exp (v + (1 + v * exp 1))) * (1 / (v * exp (v + (1 + v * exp 1))))) := by
      mach_ring
    rw [l, r, mul_inv _ (ne_of_gt (mul_pos hv hEp))] at h
    have e : (LQ - exp v) * (1 : Real) = LQ - exp v := by mach_ring
    rw [e] at h; exact h
  -- so `T < LQ ≤ Q`
  rw [hT x hXTx, hQ x hXQx]
  have hTlt : exp (v * exp (κ * (1 / x))) < LQ := by
    have h := lt_of_le_of_lt hbound hfinal
    have u := add_lt_add_left h (exp v)
    have l : exp v + (exp (v * exp (κ * (1 / x))) - exp v) = exp (v * exp (κ * (1 / x))) := by
      mach_mpoly [exp (v * exp (κ * (1 / x))), exp v]
    have r : exp v + (LQ - exp v) = LQ := by mach_mpoly [LQ, exp v]
    rw [l, r] at u; exact u
  have hQge : LQ ≤ LQ + aQ * (1 / x) := by
    have u := add_le_add_wit (le_refl LQ) (le_of_lt (mul_pos haQ hwpos))
    have e : LQ + (0 : Real) = LQ := by mach_ring
    rw [e] at u; exact u
  exact le_trans (le_of_lt hTlt) hQge

/-- **`Q` below `1`: empty, and the target is irrelevant.**

The cheapest branch in the whole assembly. `Q → LQ < 1` from above, so `Q x ≤ 1` past
`1 + aQ·(1/(1 − LQ))` and the guard `1 < Q x` fails. **No hypothesis about the target appears** —
whatever it does, this region is empty, so this one lemma serves the decaying trichotomy and any
other. -/
theorem cell_of_Q_below_one (A B Q : EMLTree) (LQ aQ XQ : Real)
    (haQ : 0 < aQ) (hLQ : LQ < 1)
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = LQ + aQ * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hδ : (0 : Real) < 1 - LQ := by
    have u := add_lt_add_left hLQ (-LQ)
    have l : -LQ + LQ = 0 := by mach_ring
    have r : -LQ + 1 = 1 - LQ := by mach_mpoly [LQ]
    rw [l, r] at u; exact u
  refine boundedEmlCell_vacuous_of_small_Q A B Q (1 + exp XQ + aQ * (1 / (1 - LQ))) ?_
  intro x hx
  have hone : (1 : Real) ≤ x := by
    have v0 : (1 : Real) + 0 + 0 ≤ 1 + exp XQ + aQ * (1 / (1 - LQ)) :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XQ)))
        (le_of_lt (mul_pos haQ (one_div_pos_of_pos hδ)))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact le_trans v0 hx
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hXQx : XQ ≤ x := by
    have v0 : (0 : Real) + exp XQ + 0 ≤ 1 + exp XQ + aQ * (1 / (1 - LQ)) :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (mul_pos haQ (one_div_pos_of_pos hδ)))
    have e : (0 : Real) + exp XQ + 0 = exp XQ := by mach_ring
    rw [e] at v0; exact le_trans (self_le_exp XQ) (le_trans v0 hx)
  have hthr : aQ * (1 / (1 - LQ)) ≤ x := by
    have v0 : (0 : Real) + 0 + aQ * (1 / (1 - LQ)) ≤ 1 + exp XQ + aQ * (1 / (1 - LQ)) :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XQ)))
        (le_refl _)
    have e : (0 : Real) + 0 + aQ * (1 / (1 - LQ)) = aQ * (1 / (1 - LQ)) := by mach_ring
    rw [e] at v0; exact le_trans v0 hx
  -- `aQ ≤ δ x`, hence `aQ (1/x) ≤ δ`
  have hδx : aQ ≤ (1 - LQ) * x := by
    have h := mul_le_mul_of_nonneg_right hthr (le_of_lt hδ)
    have l : aQ * (1 / (1 - LQ)) * (1 - LQ) = aQ * ((1 - LQ) * (1 / (1 - LQ))) := by mach_ring
    rw [l, mul_inv _ (ne_of_gt hδ)] at h
    have e : aQ * (1 : Real) = aQ := by mach_ring
    rw [e] at h
    have r : x * (1 - LQ) = (1 - LQ) * x := by mach_ring
    rw [r] at h; exact h
  have hscaled := mul_le_mul_of_nonneg_right hδx (le_of_lt (one_div_pos_of_pos hxpos))
  have l2 : (1 - LQ) * x * (1 / x) = (1 - LQ) * (x * (1 / x)) := by mach_ring
  rw [l2, mul_inv x (ne_of_gt hxpos)] at hscaled
  have e2 : (1 - LQ) * (1 : Real) = 1 - LQ := by mach_ring
  rw [e2] at hscaled
  rw [hQ x hXQx]
  have u := add_le_add_wit (le_refl LQ) hscaled
  have r : LQ + (1 - LQ) = 1 := by mach_mpoly [LQ]
  rw [r] at u; exact u

/-- **Decaying target, `Q` above `1`: the region is empty.**

Mirror of `cell_of_rising_target_upper_Q`, one level simpler because the limit is the constant `1`
rather than `exp v`. `exp_le_one_add_scaled` caps `T ≤ 1 + M·w·e` on `M·w ≤ 1`, and
`shrink_below_two_bounds` at `A := M`, `S := (LQ − 1)·(1/e)` gives one `w` with `M·w ≤ 1` and
`M·w·e < LQ − 1`, so `T < LQ ≤ Q`. Fourth use of that device. -/
theorem cell_of_decaying_target_upper_Q (A B Q : EMLTree) (M LQ aQ XT XQ : Real)
    (hM : 0 < M) (haQ : 0 < aQ) (hsep : 1 < LQ)
    (hT : ∀ x : Real, XT ≤ x → exp (exp ((EMLTree.eml A B).eval x)) = exp (M * (1 / x)))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = LQ + aQ * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hE1 : (0 : Real) < exp 1 := exp_pos 1
  have hδ : (0 : Real) < LQ - 1 := by
    have u := add_lt_add_left hsep (-(1 : Real))
    have l : -(1 : Real) + 1 = 0 := by mach_ring
    have r : -(1 : Real) + LQ = LQ - 1 := by mach_mpoly [LQ]
    rw [l, r] at u; exact u
  have hS : (0 : Real) < (LQ - 1) * (1 / exp 1) := mul_pos hδ (one_div_pos_of_pos hE1)
  obtain ⟨hD, hlt1, hltS⟩ := shrink_below_two_bounds M ((LQ - 1) * (1 / exp 1)) hM hS
  refine cell_of_Q_above_target A B Q
    (1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1)) ?_
  intro x hx
  have grab : ∀ Y : Real,
      Y ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) → Y ≤ x :=
    fun Y hY => le_trans hY hx
  have hone : (1 : Real) ≤ x := by
    refine grab 1 ?_
    have v0 : (1 : Real) + 0 + 0 + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))) (le_of_lt hD)
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact v0
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hwpos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hXTx : XT ≤ x := by
    refine grab XT (le_trans (self_le_exp XT) ?_)
    have v0 : (0 : Real) + exp XT + 0 + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))) (le_of_lt hD)
    have e : (0 : Real) + exp XT + 0 + 0 = exp XT := by mach_ring
    rw [e] at v0; exact v0
  have hXQx : XQ ≤ x := by
    refine grab XQ (le_trans (self_le_exp XQ) ?_)
    have v0 : (0 : Real) + 0 + exp XQ + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_refl _)) (le_of_lt hD)
    have e : (0 : Real) + 0 + exp XQ + 0 = exp XQ := by mach_ring
    rw [e] at v0; exact v0
  have hDx : M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1 ≤ x := by
    refine grab _ ?_
    have v0 : (0 : Real) + 0 + 0 + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1)
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_of_lt (exp_pos XQ))) (le_refl _)
    have e : (0 : Real) + 0 + 0 + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1)
        = M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1 := by mach_ring
    rw [e] at v0; exact v0
  have hwle : 1 / x ≤ 1 / (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) := one_div_antitone hD hDx
  have hMw1 : M * (1 / x) ≤ 1 :=
    le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwle (le_of_lt hM)) hlt1)
  have hMwS : M * (1 / x) < (LQ - 1) * (1 / exp 1) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwle (le_of_lt hM)) hltS
  have hMwe : M * (1 / x) * exp 1 < LQ - 1 := by
    have h := mul_lt_mul_of_pos_right hMwS hE1
    have r : (LQ - 1) * (1 / exp 1) * exp 1 = (LQ - 1) * (exp 1 * (1 / exp 1)) := by mach_ring
    rw [r, mul_inv _ (ne_of_gt hE1)] at h
    have e : (LQ - 1) * (1 : Real) = LQ - 1 := by mach_ring
    rw [e] at h; exact h
  rw [hT x hXTx, hQ x hXQx]
  have hMw0 : (0 : Real) ≤ M * (1 / x) := le_of_lt (mul_pos hM hwpos)
  have hTle : exp (M * (1 / x)) ≤ 1 + M * (1 / x) * exp 1 := exp_le_one_add_scaled hMw0 hMw1
  have hlt : exp (M * (1 / x)) < LQ := by
    refine lt_of_le_of_lt hTle ?_
    have u := add_lt_add_left hMwe (1 : Real)
    have r : (1 : Real) + (LQ - 1) = LQ := by mach_mpoly [LQ]
    rw [r] at u; exact u
  have hQge : LQ ≤ LQ + aQ * (1 / x) := by
    have u := add_le_add_wit (le_refl LQ) (le_of_lt (mul_pos haQ hwpos))
    have e : LQ + (0 : Real) = LQ := by mach_ring
    rw [e] at u; exact u
  exact le_trans (le_of_lt hlt) hQge

/-- **A FIFTH node shape, found while enumerating the router's cases.**

    A = c − log x,  B = var   ⟹   exp ((eml A B) x) = exp (exp c · (1/x)) · (1/x)

Neither `v·exp (κ·w)` (rising, `node_form_logA_constB`) nor `M·w` (decaying,
`node_form_constA_varB`), but `exp (κ·w)·w` — a decaying shape with an exponential factor on it.

**This was not in the four-case enumeration the previous commits worked from.** The left child
contributes `exp c · (1/x)` and the right contributes `− log x`, and `exp_c_sub_log_eq` applies a
*second* time with `c := exp c · (1/x)` — the same lemma used twice on one node, which is why the
shape did not appear when the two children were considered separately.

Not new mathematics: it is sandwiched between `w` and `exp κ · w` on `w ≤ 1`
(`node_logA_varB_bounds`), so the decaying analysis covers it once those lemmas take an inequality
where they currently take an equality. But it is a case, and it was missing. -/
theorem node_form_logA_varB (A B : EMLTree) (cA : Real)
    (hA : ∀ x : Real, 0 < x → A.eval x = cA - log x)
    (hB : ∀ x : Real, 0 < x → B.eval x = x) :
    ∀ x : Real, 0 < x →
      exp ((EMLTree.eml A B).eval x) = exp (exp cA * (1 / x)) * (1 / x) := by
  intro x hx
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  rw [hval, hA x hx, hB x hx, exp_c_sub_log_eq cA hx]
  exact exp_c_sub_log_eq (exp cA * (1 / x)) hx

/-- The fifth shape is sandwiched between the two known decaying ones on `w ≤ 1`. -/
theorem node_logA_varB_bounds (κ w : Real) (hκ : 0 < κ) (hw : 0 < w) (hw1 : w ≤ 1) :
    w ≤ exp (κ * w) * w ∧ exp (κ * w) * w ≤ exp κ * w := by
  constructor
  · have hge1 : (1 : Real) ≤ exp (κ * w) := by
      have h := exp_monotone (le_of_lt (mul_pos hκ hw))
      rw [exp_zero] at h; exact h
    have h := mul_le_mul_of_nonneg_right hge1 (le_of_lt hw)
    have e : (1 : Real) * w = w := by mach_ring
    rw [e] at h; exact h
  · have hle : κ * w ≤ κ := by
      have h := mul_le_mul_of_nonneg_left hw1 (le_of_lt hκ)
      have e : κ * (1 : Real) = κ := by mach_ring
      rw [e] at h; exact h
    exact mul_le_mul_of_nonneg_right (exp_monotone hle) (le_of_lt hw)

/-! ## ▸ The decaying lemmas, with the target only BOUNDED

The fifth node shape `exp (κ·w)·w` is sandwiched between `w` and `exp κ · w`, never equal to either,
so the decaying pair has to accept an inequality where it currently demands an equality. Each side
needs the bound that points the right way: the dominant case wants the target from **below** (a
bigger target only widens the margin), the vacuity case wants it from **above**. -/

/-- Dominant case with the target bounded below. `exp (M·w) ≤ T` suffices — the separation is proved
against `exp (M·w)` and a larger target only helps. -/
theorem cell_of_decaying_target_dominant_ge (A B Q : EMLTree) (M a XT XQ : Real)
    (hM : 0 < M) (hdom : a ≤ M)
    (hT : ∀ x : Real, XT ≤ x → exp (M * (1 / x)) ≤ exp (exp ((EMLTree.eml A B).eval x)))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = 1 + a * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have h2pos : (0 : Real) < 1 + 1 := by
    have u := add_lt_add_left zero_lt_one_ax 1
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at u; exact lt_trans_ax zero_lt_one_ax u
  have hβ : (0 : Real) < (M * (1 / (1 + 1))) * (M * (1 / (1 + 1))) :=
    mul_pos (mul_pos hM (one_div_pos_of_pos h2pos)) (mul_pos hM (one_div_pos_of_pos h2pos))
  obtain ⟨C, hC⟩ := floor_le_inv_sq _ hβ
  refine ⟨C, 1 + exp XT + exp XQ, ?_, ?_⟩
  · have v0 : (1 : Real) + 0 + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact v0
  intro x hx _ _
  have hone : (1 : Real) ≤ x := by
    have v0 : (1 : Real) + 0 + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact le_trans v0 hx
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hwpos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hXTx : XT ≤ x := by
    have v0 : (0 : Real) + exp XT + 0 ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))
    have e : (0 : Real) + exp XT + 0 = exp XT := by mach_ring
    rw [e] at v0; exact le_trans (self_le_exp XT) (le_trans v0 hx)
  have hXQx : XQ ≤ x := by
    have v0 : (0 : Real) + 0 + exp XQ ≤ 1 + exp XT + exp XQ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XT)))
        (le_refl _)
    have e : (0 : Real) + 0 + exp XQ = exp XQ := by mach_ring
    rw [e] at v0; exact le_trans (self_le_exp XQ) (le_trans v0 hx)
  rw [hQ x hXQx]
  have hsep := limit_one_quadratic_separation M a (1 / x) hM hwpos hdom
  have heq : (M * (1 / (1 + 1))) * (M * (1 / (1 + 1))) * ((1 / x) * (1 / x))
      = (M * (1 / x) * (1 / (1 + 1))) * (M * (1 / x) * (1 / (1 + 1))) := by mach_ring
  -- the target only grows the margin
  have hwiden : exp (M * (1 / x)) - 1 - a * (1 / x)
      ≤ exp (exp ((EMLTree.eml A B).eval x)) - (1 + a * (1 / x)) := by
    have v0 := add_le_add_wit (hT x hXTx) (le_refl (-(1 : Real) + -(a * (1 / x))))
    have l : exp (M * (1 / x)) + (-(1 : Real) + -(a * (1 / x)))
        = exp (M * (1 / x)) - 1 - a * (1 / x) := by
      mach_mpoly [exp (M * (1 / x)), a, (1 / x : Real)]
    have r : exp (exp ((EMLTree.eml A B).eval x)) + (-(1 : Real) + -(a * (1 / x)))
        = exp (exp ((EMLTree.eml A B).eval x)) - (1 + a * (1 / x)) := by
      mach_mpoly [exp (exp ((EMLTree.eml A B).eval x)), a, (1 / x : Real)]
    rw [l, r] at v0; exact v0
  refine le_trans (hC x hone) (le_trans (le_of_eq heq) (le_trans hsep hwiden))

/-- Vacuity case with the target bounded above. `T ≤ exp (M·w)` suffices — a smaller target only
loses to `Q` sooner. -/
theorem cell_of_decaying_target_upper_Q_le (A B Q : EMLTree) (M LQ aQ XT XQ : Real)
    (hM : 0 < M) (haQ : 0 < aQ) (hsep : 1 < LQ)
    (hT : ∀ x : Real, XT ≤ x → exp (exp ((EMLTree.eml A B).eval x)) ≤ exp (M * (1 / x)))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = LQ + aQ * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hE1 : (0 : Real) < exp 1 := exp_pos 1
  have hδ : (0 : Real) < LQ - 1 := by
    have u := add_lt_add_left hsep (-(1 : Real))
    have l : -(1 : Real) + 1 = 0 := by mach_ring
    have r : -(1 : Real) + LQ = LQ - 1 := by mach_mpoly [LQ]
    rw [l, r] at u; exact u
  have hS : (0 : Real) < (LQ - 1) * (1 / exp 1) := mul_pos hδ (one_div_pos_of_pos hE1)
  obtain ⟨hD, hlt1, hltS⟩ := shrink_below_two_bounds M ((LQ - 1) * (1 / exp 1)) hM hS
  refine cell_of_Q_above_target A B Q
    (1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1)) ?_
  intro x hx
  have grab : ∀ Y : Real,
      Y ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) → Y ≤ x :=
    fun Y hY => le_trans hY hx
  have hone : (1 : Real) ≤ x := by
    refine grab 1 ?_
    have v0 : (1 : Real) + 0 + 0 + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))) (le_of_lt hD)
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact v0
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hwpos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hXTx : XT ≤ x := by
    refine grab XT (le_trans (self_le_exp XT) ?_)
    have v0 : (0 : Real) + exp XT + 0 + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))) (le_of_lt hD)
    have e : (0 : Real) + exp XT + 0 + 0 = exp XT := by mach_ring
    rw [e] at v0; exact v0
  have hXQx : XQ ≤ x := by
    refine grab XQ (le_trans (self_le_exp XQ) ?_)
    have v0 : (0 : Real) + 0 + exp XQ + 0
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_refl _)) (le_of_lt hD)
    have e : (0 : Real) + 0 + exp XQ + 0 = exp XQ := by mach_ring
    rw [e] at v0; exact v0
  have hDx : M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1 ≤ x := by
    refine grab _ ?_
    have v0 : (0 : Real) + 0 + 0 + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1)
        ≤ 1 + exp XT + exp XQ + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_of_lt (exp_pos XQ))) (le_refl _)
    have e : (0 : Real) + 0 + 0 + (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1)
        = M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1 := by mach_ring
    rw [e] at v0; exact v0
  have hwle : 1 / x ≤ 1 / (M + M * (1 / ((LQ - 1) * (1 / exp 1))) + 1) := one_div_antitone hD hDx
  have hMw1 : M * (1 / x) ≤ 1 :=
    le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwle (le_of_lt hM)) hlt1)
  have hMwS : M * (1 / x) < (LQ - 1) * (1 / exp 1) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwle (le_of_lt hM)) hltS
  have hMwe : M * (1 / x) * exp 1 < LQ - 1 := by
    have h := mul_lt_mul_of_pos_right hMwS hE1
    have r : (LQ - 1) * (1 / exp 1) * exp 1 = (LQ - 1) * (exp 1 * (1 / exp 1)) := by mach_ring
    rw [r, mul_inv _ (ne_of_gt hE1)] at h
    have e : (LQ - 1) * (1 : Real) = LQ - 1 := by mach_ring
    rw [e] at h; exact h
  rw [hQ x hXQx]
  have hMw0 : (0 : Real) ≤ M * (1 / x) := le_of_lt (mul_pos hM hwpos)
  have hTle : exp (exp ((EMLTree.eml A B).eval x)) ≤ 1 + M * (1 / x) * exp 1 :=
    le_trans (hT x hXTx) (exp_le_one_add_scaled hMw0 hMw1)
  have hlt : exp (exp ((EMLTree.eml A B).eval x)) < LQ := by
    refine lt_of_le_of_lt hTle ?_
    have u := add_lt_add_left hMwe (1 : Real)
    have r : (1 : Real) + (LQ - 1) = LQ := by mach_mpoly [LQ]
    rw [r] at u; exact u
  have hQge : LQ ≤ LQ + aQ * (1 / x) := by
    have u := add_le_add_wit (le_refl LQ) (le_of_lt (mul_pos haQ hwpos))
    have e : LQ + (0 : Real) = LQ := by mach_ring
    rw [e] at u; exact u
  exact le_trans (le_of_lt hlt) hQge

/-- **The node enumeration, DERIVED rather than asserted.**

Every previous list of node shapes in this development was written by hand, and one of them was
wrong — `exp (κ·w)·w` went missing for four commits because it only appears when
`exp_c_sub_log_eq` fires twice on the same node, which considering the children separately never
produces.

This derives the list instead. `boundedEmlCell_left_forms` gives `A` two shapes from the cap,
`depth_le_one_classification` gives `B` five, and the ten combinations are discharged one at a time.
**A sixth shape cannot hide here**: it would have to surface as an unhandled case, and Lean would
refuse the proof.

The five outcomes:

| | node |
| --- | --- |
| eventually constant | `A` const with `B` const or `c − log x` |
| rising `v·exp (κw)` | `A = c − log x` with `B` const or `c − log x` |
| decaying `M·w` | `A` const, `B = var` |
| decaying `exp (κw)·w` | `A = c − log x`, `B = var` — the one that was missing |
| `log (B x) ≥ x − 1` | `B` either `exp`-shaped, against either `A` |

The last is a bound rather than a form, and deliberately so: those targets fall to `1` at `e^{−x}`
and the vacuity argument needs the bound, not the shape. -/
theorem node_form_classification (A B : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (K XK : Real) (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K) :
    (∃ V XV : Real, ∀ x : Real, XV ≤ x → exp ((EMLTree.eml A B).eval x) = V)
    ∨ (∃ v κ XV : Real, 0 < v ∧ 0 < κ ∧ ∀ x : Real, XV ≤ x →
        exp ((EMLTree.eml A B).eval x) = v * exp (κ * (1 / x)))
    ∨ (∃ M XV : Real, 0 < M ∧ ∀ x : Real, XV ≤ x →
        exp ((EMLTree.eml A B).eval x) = M * (1 / x))
    ∨ (∃ κ XV : Real, 0 < κ ∧ ∀ x : Real, XV ≤ x →
        exp ((EMLTree.eml A B).eval x) = exp (κ * (1 / x)) * (1 / x))
    ∨ (∃ XV : Real, ∀ x : Real, XV ≤ x → x - 1 ≤ log (B.eval x)) := by
  have hval : ∀ x : Real, (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) :=
    fun _ => rfl
  -- helper: past `1 + exp t` we clear both `1` and `t`
  have clear1 : ∀ t x : Real, 1 + exp t ≤ x → (1 : Real) ≤ x ∧ exp t ≤ x := by
    intro t x hx
    constructor
    · have v0 : (1 : Real) + 0 ≤ 1 + exp t := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos t))
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at v0; exact le_trans v0 hx
    · have v0 : (0 : Real) + exp t ≤ 1 + exp t :=
        add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
      have e : (0 : Real) + exp t = exp t := by mach_ring
      rw [e] at v0; exact le_trans v0 hx
  rcases boundedEmlCell_left_forms A B hA hB K XK hK with ⟨α, hα⟩ | ⟨cA, _, hcA⟩
  · -- `A` constant
    rcases depth_le_one_classification B hB with
        ⟨β, hβ⟩ | hβ | ⟨cB, _, hβ⟩ | ⟨d, hβ⟩ | hβ
    · -- `B` constant: node constant
      refine Or.inl ⟨exp (exp α - log β), 1, ?_⟩
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hval x, hα x hx0, hβ x hx0]
    · -- `B = var`: node is `M·w`
      refine Or.inr (Or.inr (Or.inl ⟨exp (exp α), 1, exp_pos _, ?_⟩))
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hval x, hα x hx0, hβ x hx0]
      exact exp_c_sub_log_eq (exp α) hx0
    · -- `B = c − log x`: totalized log zeroes it, node constant
      refine Or.inl ⟨exp (exp α), 1 + exp cB, ?_⟩
      intro x hx
      obtain ⟨h1, hcBx⟩ := clear1 cB x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax h1
      rw [hval x, hα x hx0, hβ x hx0, log_c_sub_log_eventually_zero cB x hcBx]
      have e : exp α - (0 : Real) = exp α := by mach_mpoly [exp α]
      rw [e]
    · -- `B = exp x − d`: the log bound
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨1 + exp (d + 1), ?_⟩)))
      intro x hx
      obtain ⟨h1, hdx⟩ := clear1 (d + 1) x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax h1
      rw [hβ x hx0]
      exact log_exp_sub_const_ge_linear d (le_trans (self_le_exp (d + 1)) hdx)
    · -- `B = exp x − log x`: the log bound
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨1, ?_⟩)))
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hβ x hx0]
      exact log_exp_sub_log_ge_linear hx
  · -- `A = c − log x`
    rcases depth_le_one_classification B hB with
        ⟨β, hβ⟩ | hβ | ⟨cB, _, hβ⟩ | ⟨d, hβ⟩ | hβ
    · -- `B` constant: rising
      refine Or.inr (Or.inl ⟨exp (-(log β)), exp cA, 1, exp_pos _, exp_pos _, ?_⟩)
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      exact node_form_logA_constB A B cA β hcA hβ x hx0
    · -- `B = var`: the fifth shape
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨exp cA, 1, exp_pos _, ?_⟩)))
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      exact node_form_logA_varB A B cA hcA hβ x hx0
    · -- `B = c − log x`: rising with `v = 1`
      refine Or.inr (Or.inl ⟨1, exp cA, 1 + exp cB, zero_lt_one_ax, exp_pos _, ?_⟩)
      intro x hx
      obtain ⟨h1, hcBx⟩ := clear1 cB x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax h1
      exact node_form_logA_logB A B cA cB hcA hβ x hcBx hx0
    · -- `B = exp x − d`: the log bound
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨1 + exp (d + 1), ?_⟩)))
      intro x hx
      obtain ⟨h1, hdx⟩ := clear1 (d + 1) x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax h1
      rw [hβ x hx0]
      exact log_exp_sub_const_ge_linear d (le_trans (self_le_exp (d + 1)) hdx)
    · -- `B = exp x − log x`: the log bound
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨1, ?_⟩)))
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hβ x hx0]
      exact log_exp_sub_log_ge_linear hx

/-- **The fifth shape's sandwich is too LOOSE, and this is the tight upper half.**

    exp (κ·w)·w  ≤  (1 + κ·w·e)·w        for κ·w ≤ 1

`node_logA_varB_bounds` brackets the fifth node shape between `w` and `exp κ · w`. That is enough to
route its `LQ ≠ 1` branches, and **not** enough for `LQ = 1`.

There the comparison is against `Q`'s coefficient `aQ`, and the two decaying lemmas want
`aQ ≤ M` (dominant, `M := 1` from the lower bracket) or `M < aQ` (vacuity, `M := exp κ` from the
upper). Between them sits `1 < aQ ≤ exp κ`, which **neither** covers — a real gap, not a routing
choice.

The bracket is the wrong shape for that question. `exp (κ·w) → 1` as `w → 0`, so the node's true
coefficient is `1`, not something in `[1, exp κ]`; the constant upper bracket throws away exactly the
convergence the comparison needs. `exp_le_one_add_scaled` keeps it: the coefficient is `1 + κ·w·e`,
which tends to `1`, so any `aQ > 1` eventually wins and the gap closes.

Recorded as its own lemma because the loose bracket was mine, was used twice before this was noticed,
and reads as sufficient until the equal-limits case asks it a question it cannot answer. -/
theorem node_logA_varB_tight (κ w : Real) (hw : 0 < w) (hκw : κ * w ≤ 1) (hκw0 : 0 ≤ κ * w) :
    exp (κ * w) * w ≤ (1 + κ * w * exp 1) * w :=
  mul_le_mul_of_nonneg_right (exp_le_one_add_scaled hκw0 hκw) (le_of_lt hw)

/-- **The rise bound, made MONOTONE in a surrogate.**

    0 ≤ u ≤ U ≤ 1   ⟹   exp u − 1  ≤  U·(1 + U·e)

`exp_sub_exp_upper` and `exp_le_one_add_scaled` bound `exp u − 1` by `u·(1 + u·e)`, which is exact but
useless when `u` is only known through a bound. The fifth node shape is exactly that situation:
`u = exp (κw)·w` has no closed form the comparison lemmas accept, and only
`u ≤ (1 + κ·w·e)·w` is available.

Since `u ↦ u·(1 + u·e)` is increasing on `u ≥ 0`, the surrogate can be substituted wholesale. That is
what lets `node_logA_varB_tight`'s bound be used where the shape itself cannot.

Stated separately rather than inlined because the substitution is the whole content: every previous
decaying lemma took the target's form, and this is the first that takes only a bound on it. -/
theorem exp_sub_one_le_of_le {u U : Real} (hu0 : 0 ≤ u) (huU : u ≤ U) (hU1 : U ≤ 1) :
    exp u - 1 ≤ U * (1 + U * exp 1) := by
  have hu1 : u ≤ 1 := le_trans huU hU1
  have hU0 : (0 : Real) ≤ U := le_trans hu0 huU
  -- `exp u − 1 ≤ u · exp u`
  have h1 : exp u - 1 ≤ u * exp u := by
    have h := exp_sub_exp_upper u 0
    rw [exp_zero] at h
    have e : u - 0 = u := by mach_mpoly [u]
    rw [e] at h; exact h
  -- `exp u ≤ 1 + u·e`
  have h2 : u * exp u ≤ u * (1 + u * exp 1) :=
    mul_le_mul_of_nonneg_left (exp_le_one_add_scaled hu0 hu1) hu0
  -- monotone in the surrogate: both factors grow with `u`
  have h3 : u * (1 + u * exp 1) ≤ U * (1 + U * exp 1) := by
    have hfac : 1 + u * exp 1 ≤ 1 + U * exp 1 :=
      add_le_add_wit (le_refl 1) (mul_le_mul_of_nonneg_right huU (le_of_lt (exp_pos 1)))
    have hstep1 : u * (1 + u * exp 1) ≤ u * (1 + U * exp 1) :=
      mul_le_mul_of_nonneg_left hfac hu0
    have hnn : (0 : Real) ≤ 1 + U * exp 1 := by
      have v := add_le_add_wit (le_of_lt zero_lt_one_ax) (mul_le_mul_of_nonneg_right hU0
        (le_of_lt (exp_pos 1)))
      have l : (0 : Real) + 0 * exp 1 = 0 := by mach_ring
      rw [l] at v; exact v
    exact le_trans hstep1 (mul_le_mul_of_nonneg_right huU hnn)
  exact le_trans h1 (le_trans h2 h3)

/-- **The fifth shape's coefficient, linearised in one small parameter.**

    0 ≤ g ≤ ε,  0 ≤ h ≤ ε,  ε ≤ 1   ⟹   (1+g)·(1 + (1+g)·h)  ≤  1 + 5ε

The coefficient `cell_of_decaying_target_subdominant` needs to beat, for the fifth node shape, is
`(1 + κwe)·(1 + (1 + κwe)·we)` — a product of two nested affine factors in `w`. Expanded it is
`1 + 2ε + 2ε² + ε³`, and on `ε ≤ 1` every higher power collapses into `ε`, leaving a **linear**
bound.

That is the whole reason the threshold is reachable: `aQ > 1` gives `aQ − 1 > 0`, and a linear bound
in `ε` can be pushed under it by shrinking `ε`, where a bound with `ε²` and `ε³` left in it would
need a root. Two applications of `shrink_below_two_bounds` then suffice — one to choose `ε` under
both `1` and `(aQ−1)/5`, one to choose `w` under `ε` for both `κe` and `e`. -/
theorem fifth_shape_coefficient_bound {g h ε : Real} (hg0 : 0 ≤ g) (hh0 : 0 ≤ h)
    (hg : g ≤ ε) (hh : h ≤ ε) (hε1 : ε ≤ 1) :
    (1 + g) * (1 + (1 + g) * h) ≤ 1 + (1 + 1 + 1 + 1 + 1) * ε := by
  have hε0 : (0 : Real) ≤ ε := le_trans hg0 hg
  have h1g : (0 : Real) ≤ 1 + g := by
    have v := add_le_add_wit (le_of_lt zero_lt_one_ax) hg0
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at v; exact v
  have h1e : (0 : Real) ≤ 1 + ε := by
    have v := add_le_add_wit (le_of_lt zero_lt_one_ax) hε0
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at v; exact v
  -- widen `g` and `h` to `ε` in both factors
  have hfac1 : 1 + g ≤ 1 + ε := add_le_add_wit (le_refl 1) hg
  have hprod : (1 + g) * h ≤ (1 + ε) * ε :=
    le_trans (mul_le_mul_of_nonneg_left hh h1g) (mul_le_mul_of_nonneg_right hfac1 hε0)
  have hfac2 : 1 + (1 + g) * h ≤ 1 + (1 + ε) * ε := add_le_add_wit (le_refl 1) hprod
  have hinner : (0 : Real) ≤ 1 + (1 + g) * h := by
    have v := add_le_add_wit (le_of_lt zero_lt_one_ax) (mul_le_mul_of_nonneg_left hh0 h1g)
    have e : (0 : Real) + (1 + g) * 0 = 0 := by mach_ring
    rw [e] at v; exact v
  have hwide : (1 + g) * (1 + (1 + g) * h) ≤ (1 + ε) * (1 + (1 + ε) * ε) :=
    le_trans (mul_le_mul_of_nonneg_left hfac2 h1g)
      (mul_le_mul_of_nonneg_right hfac1 (le_trans hinner hfac2))
  refine le_trans hwide ?_
  -- `(1+ε)(1+(1+ε)ε) = 1 + 2ε + 2ε² + ε³`, and every higher power collapses on `ε ≤ 1`
  have hsq : ε * ε ≤ ε := by
    have v := mul_le_mul_of_nonneg_left hε1 hε0
    have e : ε * (1 : Real) = ε := by mach_ring
    rw [e] at v; exact v
  have hcube : ε * ε * ε ≤ ε := by
    have v := mul_le_mul_of_nonneg_right hsq hε0
    refine le_trans v ?_
    exact hsq
  have hexpand : (1 + ε) * (1 + (1 + ε) * ε)
      = 1 + ε + ε + (ε * ε + ε * ε) + ε * ε * ε := by mach_ring
  rw [hexpand]
  have hgoal : 1 + ε + ε + (ε * ε + ε * ε) + ε * ε * ε
      ≤ 1 + ε + ε + (ε + ε) + ε :=
    add_le_add_wit (add_le_add_wit (le_refl (1 + ε + ε)) (add_le_add_wit hsq hsq)) hcube
  refine le_trans hgoal (le_of_eq ?_)
  mach_ring

/-! ## ▸ The two nested thresholds for the fifth shape

`fifth_shape_coefficient_bound` reduces the fifth shape's vacuity condition to `1 + 5ε ≤ aQ` plus
three smallness conditions on `w`. These pick `ε` and then `w`, each by one call to
`shrink_below_two_bounds`. Kept as separate lemmas because the composite threshold term is large
enough that inlining it makes the surrounding proof unreadable — and unreadable is where a wrong
direction hides. -/

/-- Pick `ε` under both `1` and `(aQ − 1)/5`, for `aQ > 1`. -/
theorem small_eps_for (aQ : Real) (haQ : 1 < aQ) :
    ∃ ε : Real, 0 < ε ∧ ε ≤ 1 ∧ (1 + 1 + 1 + 1 + 1) * ε < aQ - 1 := by
  have h5 : (0 : Real) < (1 + 1 + 1 + 1 + 1 : Real) := by
    have v : (1 : Real) + 0 + 0 + 0 + 0 ≤ 1 + 1 + 1 + 1 + 1 :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1)
        (le_of_lt zero_lt_one_ax)) (le_of_lt zero_lt_one_ax)) (le_of_lt zero_lt_one_ax))
        (le_of_lt zero_lt_one_ax)
    have e : (1 : Real) + 0 + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact lt_of_lt_of_le zero_lt_one_ax v
  have hd : (0 : Real) < aQ - 1 := by
    have u := add_lt_add_left haQ (-(1 : Real))
    have l : -(1 : Real) + 1 = 0 := by mach_ring
    have r : -(1 : Real) + aQ = aQ - 1 := by mach_mpoly [aQ]
    rw [l, r] at u; exact u
  obtain ⟨hD, hlt1, hltS⟩ := shrink_below_two_bounds (1 + 1 + 1 + 1 + 1 : Real) (aQ - 1) h5 hd
  refine ⟨1 / ((1 + 1 + 1 + 1 + 1 : Real)
      + (1 + 1 + 1 + 1 + 1 : Real) * (1 / (aQ - 1)) + 1), one_div_pos_of_pos hD, ?_, hltS⟩
  -- `ε ≤ 5ε < 1`
  have hεpos : (0 : Real) < 1 / ((1 + 1 + 1 + 1 + 1 : Real)
      + (1 + 1 + 1 + 1 + 1 : Real) * (1 / (aQ - 1)) + 1) := one_div_pos_of_pos hD
  have hle5 : (1 : Real) ≤ (1 + 1 + 1 + 1 + 1 : Real) := by
    have v : (1 : Real) + 0 + 0 + 0 + 0 ≤ 1 + 1 + 1 + 1 + 1 :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1)
        (le_of_lt zero_lt_one_ax)) (le_of_lt zero_lt_one_ax)) (le_of_lt zero_lt_one_ax))
        (le_of_lt zero_lt_one_ax)
    have e : (1 : Real) + 0 + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  have hstep := mul_le_mul_of_nonneg_right hle5 (le_of_lt hεpos)
  have e1 : (1 : Real) * (1 / ((1 + 1 + 1 + 1 + 1 : Real)
      + (1 + 1 + 1 + 1 + 1 : Real) * (1 / (aQ - 1)) + 1))
      = 1 / ((1 + 1 + 1 + 1 + 1 : Real)
        + (1 + 1 + 1 + 1 + 1 : Real) * (1 / (aQ - 1)) + 1) := by mach_ring
  rw [e1] at hstep
  exact le_of_lt (lt_of_le_of_lt hstep hlt1)

/-- Pick `w` under `ε` for both `κ·e` and `e`, and under `1/2`, in one shrink. -/
theorem small_w_for (κ ε : Real) (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ w₀ : Real, 0 < w₀ ∧ ∀ w : Real, 0 < w → w ≤ w₀ →
      κ * w * exp 1 ≤ ε ∧ w * exp 1 ≤ ε ∧ (1 + 1) * w ≤ 1 := by
  have hE1 : (0 : Real) < exp 1 := exp_pos 1
  have htwo : (0 : Real) < (1 : Real) + 1 := by
    have v : (1 : Real) + 0 ≤ 1 + 1 := add_le_add_wit (le_refl 1) (le_of_lt zero_lt_one_ax)
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at v; exact lt_of_lt_of_le zero_lt_one_ax v
  have hA : (0 : Real) < κ * exp 1 + exp 1 + (1 + 1) := by
    have v : (0 : Real) + 0 + (1 + 1) ≤ κ * exp 1 + exp 1 + (1 + 1) :=
      add_le_add_wit (add_le_add_wit (le_of_lt (mul_pos hκ hE1)) (le_of_lt hE1)) (le_refl _)
    have e : (0 : Real) + 0 + (1 + 1) = 1 + 1 := by mach_ring
    rw [e] at v; exact lt_of_lt_of_le htwo v
  obtain ⟨hD, hlt1, hltS⟩ :=
    shrink_below_two_bounds (κ * exp 1 + exp 1 + (1 + 1)) ε hA hε
  refine ⟨1 / (κ * exp 1 + exp 1 + (1 + 1)
      + (κ * exp 1 + exp 1 + (1 + 1)) * (1 / ε) + 1), one_div_pos_of_pos hD, ?_⟩
  intro w hw hwle
  have hAw : (κ * exp 1 + exp 1 + (1 + 1)) * w
      ≤ (κ * exp 1 + exp 1 + (1 + 1)) * (1 / (κ * exp 1 + exp 1 + (1 + 1)
        + (κ * exp 1 + exp 1 + (1 + 1)) * (1 / ε) + 1)) :=
    mul_le_mul_of_nonneg_left hwle (le_of_lt hA)
  have hlt1' : (κ * exp 1 + exp 1 + (1 + 1)) * w ≤ 1 := le_of_lt (lt_of_le_of_lt hAw hlt1)
  have hltS' : (κ * exp 1 + exp 1 + (1 + 1)) * w ≤ ε := le_of_lt (lt_of_le_of_lt hAw hltS)
  -- each summand is dominated by the whole
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ hltS'
    have v : κ * exp 1 * w + 0 + 0 ≤ κ * exp 1 * w + exp 1 * w + (1 + 1) * w :=
      add_le_add_wit (add_le_add_wit (le_refl _) (le_of_lt (mul_pos hE1 hw)))
        (le_of_lt (mul_pos htwo hw))
    have l : κ * exp 1 * w + 0 + 0 = κ * w * exp 1 := by mach_ring
    have r : κ * exp 1 * w + exp 1 * w + (1 + 1) * w
        = (κ * exp 1 + exp 1 + (1 + 1)) * w := by mach_ring
    rw [l, r] at v; exact v
  · refine le_trans ?_ hltS'
    have v : (0 : Real) + exp 1 * w + 0 ≤ κ * exp 1 * w + exp 1 * w + (1 + 1) * w :=
      add_le_add_wit (add_le_add_wit (le_of_lt (mul_pos (mul_pos hκ hE1) hw)) (le_refl _))
        (le_of_lt (mul_pos htwo hw))
    have l : (0 : Real) + exp 1 * w + 0 = w * exp 1 := by mach_ring
    have r : κ * exp 1 * w + exp 1 * w + (1 + 1) * w
        = (κ * exp 1 + exp 1 + (1 + 1)) * w := by mach_ring
    rw [l, r] at v; exact v
  · refine le_trans ?_ hlt1'
    have v : (0 : Real) + 0 + (1 + 1) * w ≤ κ * exp 1 * w + exp 1 * w + (1 + 1) * w :=
      add_le_add_wit (add_le_add_wit (le_of_lt (mul_pos (mul_pos hκ hE1) hw))
        (le_of_lt (mul_pos hE1 hw))) (le_refl _)
    have l : (0 : Real) + 0 + (1 + 1) * w = (1 + 1) * w := by mach_ring
    have r : κ * exp 1 * w + exp 1 * w + (1 + 1) * w
        = (κ * exp 1 + exp 1 + (1 + 1)) * w := by mach_ring
    rw [l, r] at v; exact v

/-- **The fifth shape's `LQ = 1`, `aQ > 1` branch — the hole the router found, now closed.**

Assembles the six pieces built for it. `small_eps_for` and `small_w_for` supply the nested
thresholds; `node_logA_varB_tight` replaces the node by `U := (1 + κwe)·w`;
`exp_sub_one_le_of_le` accepts that surrogate in place of the shape, which is the only decaying
lemma that can, because `exp (κw)·w` has no closed form the others take;
`fifth_shape_coefficient_bound` flattens the resulting nested product to `1 + 5ε`; and `small_eps_for`
had already put that under `aQ`. So `T ≤ 1 + aQ·w = Q` and the guard fails.

`κ·w ≤ 1` costs nothing: `exp 1 ≥ 2 > 1`, so `κw ≤ κ·w·e ≤ ε ≤ 1` falls out of a threshold that was
needed anyway. -/
theorem cell_of_fifth_shape_subdominant (A B Q : EMLTree) (κ aQ XT XQ : Real)
    (hκ : 0 < κ) (haQ : 1 < aQ)
    (hT : ∀ x : Real, XT ≤ x →
      exp ((EMLTree.eml A B).eval x) = exp (κ * (1 / x)) * (1 / x))
    (hQ : ∀ x : Real, XQ ≤ x → Q.eval x = 1 + aQ * (1 / x)) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hE1 : (0 : Real) < exp 1 := exp_pos 1
  have hE1ge : (1 : Real) ≤ exp 1 := by
    refine le_trans ?_ (one_add_le_exp 1)
    have v := add_le_add_wit (le_refl (1 : Real)) (le_of_lt zero_lt_one_ax)
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  obtain ⟨ε, hε0, hε1, h5ε⟩ := small_eps_for aQ haQ
  obtain ⟨w₀, hw₀, hw⟩ := small_w_for κ ε hκ hε0
  refine cell_of_Q_above_target A B Q (1 + exp XT + exp XQ + 1 / w₀) ?_
  intro x hx
  have grab : ∀ Y : Real, Y ≤ 1 + exp XT + exp XQ + 1 / w₀ → Y ≤ x := fun Y hY => le_trans hY hx
  have hone : (1 : Real) ≤ x := by
    refine grab 1 ?_
    have v0 : (1 : Real) + 0 + 0 + 0 ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XT)))
        (le_of_lt (exp_pos XQ))) (le_of_lt (one_div_pos_of_pos hw₀))
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at v0; exact v0
  have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hone
  have hwpos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
  have hXTx : XT ≤ x := by
    refine grab XT (le_trans (self_le_exp XT) ?_)
    have v0 : (0 : Real) + exp XT + 0 + 0 ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos XQ))) (le_of_lt (one_div_pos_of_pos hw₀))
    have e : (0 : Real) + exp XT + 0 + 0 = exp XT := by mach_ring
    rw [e] at v0; exact v0
  have hXQx : XQ ≤ x := by
    refine grab XQ (le_trans (self_le_exp XQ) ?_)
    have v0 : (0 : Real) + 0 + exp XQ + 0 ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_refl _)) (le_of_lt (one_div_pos_of_pos hw₀))
    have e : (0 : Real) + 0 + exp XQ + 0 = exp XQ := by mach_ring
    rw [e] at v0; exact v0
  have hinvx : 1 / w₀ ≤ x := by
    refine grab _ ?_
    have v0 : (0 : Real) + 0 + 0 + 1 / w₀ ≤ 1 + exp XT + exp XQ + 1 / w₀ :=
      add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
        (le_of_lt (exp_pos XT))) (le_of_lt (exp_pos XQ))) (le_refl _)
    have e : (0 : Real) + 0 + 0 + 1 / w₀ = 1 / w₀ := by mach_ring
    rw [e] at v0; exact v0
  have hwle : 1 / x ≤ w₀ := by
    have h := one_div_antitone (one_div_pos_of_pos hw₀) hinvx
    rw [one_div_one_div_pos hw₀] at h; exact h
  obtain ⟨hg, hh, htwo⟩ := hw (1 / x) hwpos hwle
  have hκw0 : (0 : Real) ≤ κ * (1 / x) := le_of_lt (mul_pos hκ hwpos)
  have hg0 : (0 : Real) ≤ κ * (1 / x) * exp 1 := le_of_lt (mul_pos (mul_pos hκ hwpos) hE1)
  have hh0 : (0 : Real) ≤ 1 / x * exp 1 := le_of_lt (mul_pos hwpos hE1)
  -- `κ w ≤ 1` free from `exp 1 ≥ 1`
  have hκw1 : κ * (1 / x) ≤ 1 := by
    refine le_trans (le_trans ?_ hg) hε1
    have v := mul_le_mul_of_nonneg_left hE1ge hκw0
    have e : κ * (1 / x) * (1 : Real) = κ * (1 / x) := by mach_ring
    rw [e] at v; exact v
  have hU1 : (1 + κ * (1 / x) * exp 1) * (1 / x) ≤ 1 := by
    refine le_trans ?_ htwo
    have hfac : 1 + κ * (1 / x) * exp 1 ≤ 1 + 1 := add_le_add_wit (le_refl 1) (le_trans hg hε1)
    exact mul_le_mul_of_nonneg_right hfac (le_of_lt hwpos)
  have hu0 : (0 : Real) ≤ exp (κ * (1 / x)) * (1 / x) :=
    le_of_lt (mul_pos (exp_pos _) hwpos)
  have hrise := exp_sub_one_le_of_le hu0 (node_logA_varB_tight κ (1 / x) hwpos hκw1 hκw0) hU1
  have hcoef := fifth_shape_coefficient_bound hg0 hh0 hg hh hε1
  -- `U(1+Ue) = w · [(1+g)(1+(1+g)h)] ≤ w · (1+5ε) ≤ w · aQ`
  have hfold : (1 + κ * (1 / x) * exp 1) * (1 / x)
        * (1 + (1 + κ * (1 / x) * exp 1) * (1 / x) * exp 1)
      = 1 / x * ((1 + κ * (1 / x) * exp 1)
        * (1 + (1 + κ * (1 / x) * exp 1) * (1 / x * exp 1))) := by mach_ring
  have haQge : 1 + (1 + 1 + 1 + 1 + 1) * ε ≤ aQ := by
    have u := add_lt_add_left h5ε (1 : Real)
    have r : (1 : Real) + (aQ - 1) = aQ := by mach_mpoly [aQ]
    rw [r] at u; exact le_of_lt u
  have hchain : (1 + κ * (1 / x) * exp 1) * (1 / x)
        * (1 + (1 + κ * (1 / x) * exp 1) * (1 / x) * exp 1)
      ≤ aQ * (1 / x) := by
    rw [hfold]
    refine le_trans (mul_le_mul_of_nonneg_left (le_trans hcoef haQge) (le_of_lt hwpos))
      (le_of_eq ?_)
    mach_ring
  rw [hT x hXTx, hQ x hXQx]
  have hfinal := le_trans hrise hchain
  have u := add_le_add_wit hfinal (le_refl (1 : Real))
  have l : exp (exp (κ * (1 / x)) * (1 / x)) - 1 + 1
      = exp (exp (κ * (1 / x)) * (1 / x)) := by
    mach_mpoly [exp (exp (κ * (1 / x)) * (1 / x))]
  have r : aQ * (1 / x) + 1 = 1 + aQ * (1 / x) := by mach_mpoly [aQ, (1 / x : Real)]
  rw [l, r] at u; exact u

/-- **What is left of the bounded cell after the small-right branch is discharged.** Identical to
`BoundedEmlCellApproach` except for the added hypothesis `1 < Q x`.

**Why the split is at `1` and not somewhere else.** Below `1` the target's own distance to `1` carries
the whole bound (`expexp_gap_of_right_le_one`), with no reference to `Q`'s structure at all. Above
`1`, `log (Q x)` becomes a genuine quantity and the natural route is reverse convexity —
`T − Q ≥ (u − v)·exp v` with `u = exp (P x)`, `v = log (Q x)` — which is where the difficulty
concentrates.

**And that route is CIRCULAR, which is the useful thing to know about this obligation.** Since
`exp v = Q x > 1`, it gives `T − Q ≥ u − v = exp (P x) − log (Q x)`: the value of the depth-3 node
`eml P Q`, with the *same* bounded `P`. Bounding it below by `exp (−C − exp x)` is precisely
`Depth3DecayExp`'s bounded cell — the statement this whole chain reduces *from*. So the remaining
difficulty cannot be discharged by moving between the value level and the exponent level in either
direction; `exponent_gap_of_value_gap` and reverse convexity are exact inverses here, and a new
ingredient is needed rather than a further conversion.

Recorded so the next session does not spend its first hour rediscovering that the obvious move closes
a loop. -/
def BoundedEmlCellApproachLarge : Prop :=
  ∀ A B Q : EMLTree, A.depth ≤ 1 → B.depth ≤ 1 → Q.depth ≤ 2 →
    ∀ K XK : Real, (∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K) →
      ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
        Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
          exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x

/-- **The small-right branch is discharged, so only `1 < Q x` remains.**

Merging two `(C, X₀)` pairs needs a constant dominating both and a ray past both. Neither `max` nor
division exists in this base, so `exp C₁ + exp C₂` and `1 + exp X₁ + exp X₂` do the work —
`self_le_exp` on each summand clears the corresponding bound, and the `1` supplies `1 ≤ X₀`. -/
theorem boundedEmlCellApproach_of_large (h : BoundedEmlCellApproachLarge) :
    BoundedEmlCellApproach := by
  intro A B Q hA hB hQ K XK hK
  obtain ⟨C₂, X₂, hX₂, hlarge⟩ := h A B Q hA hB hQ K XK hK
  obtain ⟨C₁, X₁, hX₁, hsmall⟩ := expexp_gap_of_right_le_one A B Q hB
  refine ⟨exp C₁ + exp C₂, 1 + exp X₁ + exp X₂, ?_, ?_⟩
  · have v : (1 : Real) + 0 + 0 ≤ 1 + exp X₁ + exp X₂ :=
      add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos X₁)))
        (le_of_lt (exp_pos X₂))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  intro x hx hlt
  have hX₁x : X₁ ≤ x := by
    have v : (0 : Real) + exp X₁ + 0 ≤ 1 + exp X₁ + exp X₂ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
        (le_of_lt (exp_pos X₂))
    have e : (0 : Real) + exp X₁ + 0 = exp X₁ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp X₁) (le_trans v hx)
  have hX₂x : X₂ ≤ x := by
    have v : (0 : Real) + 0 + exp X₂ ≤ 1 + exp X₁ + exp X₂ :=
      add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos X₁)))
        (le_refl _)
    have e : (0 : Real) + 0 + exp X₂ = exp X₂ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp X₂) (le_trans v hx)
  -- the merged constant dominates each branch's own
  have hC₁ : C₁ ≤ exp C₁ + exp C₂ := by
    have v : exp C₁ + 0 ≤ exp C₁ + exp C₂ :=
      add_le_add_wit (le_refl _) (le_of_lt (exp_pos C₂))
    have e : exp C₁ + (0 : Real) = exp C₁ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp C₁) v
  have hC₂ : C₂ ≤ exp C₁ + exp C₂ := by
    have v : (0 : Real) + exp C₂ ≤ exp C₁ + exp C₂ :=
      add_le_add_wit (le_of_lt (exp_pos C₁)) (le_refl _)
    have e : (0 : Real) + exp C₂ = exp C₂ := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp C₂) v
  have hmono : ∀ D : Real, D ≤ exp C₁ + exp C₂ →
      exp (-(exp C₁ + exp C₂) - exp x) ≤ exp (-D - exp x) := by
    intro D hD
    refine exp_monotone ?_
    have hneg : -(exp C₁ + exp C₂) ≤ -D := neg_le_neg_wit hD
    have v := add_le_add_wit hneg (le_refl (-exp x))
    have e1 : -(exp C₁ + exp C₂) + -exp x = -(exp C₁ + exp C₂) - exp x := by mach_ring
    have e2 : -D + -exp x = -D - exp x := by mach_ring
    rw [e1, e2] at v; exact v
  rcases lt_total 1 (Q.eval x) with hq | hq | hq
  · exact le_trans (hmono C₂ hC₂) (hlarge x hX₂x hq hlt)
  · exact le_trans (hmono C₁ hC₁) (hsmall x hX₁x (by rw [← hq]; exact le_refl 1))
  · exact le_trans (hmono C₁ hC₁) (hsmall x hX₁x (le_of_lt hq))

/-- **The log-bound target: `T → 1` at `e^{−x}`, which any moving `Q` outruns.**

The fifth outcome of `node_form_classification` is a *bound*, not a form — `log (B x) ≥ x − 1` —
because both `exp`-shaped right children land here and their shapes differ. That is enough:
`target_below_one_singly_exponential` turns it into `T − 1 ≤ D·e^{−x}`, and a `Q` sitting at
`L + a·(1/x)` with `L ≥ 1` is at least `a/x` above `1`. A singly exponential approach loses to a
polynomial one, so `Q` overtakes `T` and the region is empty.

The cap is consumed twice over: `boundedEmlCell_left_forms` reads `A`'s two shapes off it, and both
have a bounded exponential — `exp α` exactly, and `exp (cA − log x) ≤ exp cA` for `x ≥ 1` because
`log x ≥ 0`. Neither needs the division form, which is why `log_nonneg` appears here and
`exp_c_sub_log_eq` does not. -/
theorem cell_of_log_bound_target (A B Q : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (K XK : Real) (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K)
    (XV : Real) (hV : ∀ x : Real, XV ≤ x → x - 1 ≤ log (B.eval x))
    (LQ aQ XQ : Real) (haQ : 0 < aQ)
    (hQf : ∀ x : Real, XQ ≤ x → Q.eval x = LQ + aQ * (1 / x))
    (hLQ : (1 : Real) ≤ LQ) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  have hX1 : (1 : Real) ≤ 1 + exp XV := by
    have v : (1 : Real) + 0 ≤ 1 + exp XV := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XV))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at v; exact v
  have hXV : ∀ x : Real, 1 + exp XV ≤ x → XV ≤ x := by
    intro x hx
    have v : (0 : Real) + exp XV ≤ 1 + exp XV :=
      add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
    have e : (0 : Real) + exp XV = exp XV := by mach_ring
    rw [e] at v; exact le_trans (self_le_exp XV) (le_trans v hx)
  -- the cap names `A`, and both surviving shapes have a bounded exponential
  have hAb : ∃ Kb : Real, ∀ x : Real, (1 : Real) ≤ x → exp (A.eval x) ≤ Kb := by
    rcases boundedEmlCell_left_forms A B hA hB K XK hK with ⟨α, hα⟩ | ⟨cA, _, hcA⟩
    · refine ⟨exp α, ?_⟩
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hα x hx0]; exact le_refl _
    · refine ⟨exp cA, ?_⟩
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hcA x hx0]
      refine exp_monotone ?_
      have hlog : (0 : Real) ≤ log x := log_nonneg hx
      have v := add_le_add_wit (le_refl cA) (neg_le_neg_wit hlog)
      have l : cA + -log x = cA - log x := by mach_mpoly [cA, log x]
      have r : cA + -(0 : Real) = cA := by mach_ring
      rw [l, r] at v; exact v
  obtain ⟨Kb, hKb⟩ := hAb
  obtain ⟨D, hDpos, hT⟩ :=
    target_below_one_singly_exponential A B Kb (1 + exp XV) hX1
      (fun x hx => hKb x (le_trans hX1 hx))
      (fun x hx => hV x (hXV x hx))
  refine boundedEmlCell_vacuous_of_fast_target A B Q D aQ (1 + exp XV) XQ hDpos haQ hT ?_
  intro x hx
  rw [hQf x hx]
  exact add_le_add_wit hLQ (le_refl _)

/-- **The inner dispatch: one moving `Q` against all five node shapes.**

`Q` has been reduced to `L + a·(1/x)` with `a > 0` — the single surviving shape of the four `P`/`R`
combinations — and the node to one of the five forms `node_form_classification` derives. This routes
the pair to the comparison layer, and it is the step that decides which comparison is even the right
one: a **limit** comparison where the limits separate, a **coefficient** comparison where they
coincide.

| node | branch on | discharged by |
| --- | --- | --- |
| constant | — | `boundedEmlCell_eventually_const_target` |
| `v·exp (κw)` | `L` vs `exp v` | `cell_of_rising_target_{lower_Q, dominant, subdominant, upper_Q}` |
| `M·w` | `L` vs `1`, then `a` vs `M` | `cell_of_{Q_below_one, decaying_target_*}` |
| `exp (κw)·w` | `L` vs `1`, then `a` vs `1` | the bracketed decaying pair, plus `cell_of_fifth_shape_subdominant` |
| `log (B x) ≥ x − 1` | `L` vs `1` | `cell_of_log_bound_target` |

**Only the fifth shape needs both brackets.** `node_logA_varB_bounds` puts it between `w` and
`exp κ · w`, so the lower bracket (`M = 1`) feeds the `_ge` form and the upper (`M = exp κ`) the
`_le` form. Its `L = 1` row is the one a bracket cannot decide — a constant upper bracket discards
the very convergence the equal-limits comparison rests on — and that row is why
`cell_of_fifth_shape_subdominant` exists and takes the node's exact form instead.

Two arrangements of one product are not one term: `cell_of_rising_target_dominant` asks for
`aQ ≤ exp v * (v * κ)` and `cell_of_rising_target_subdominant` for `v * κ * exp v < aQ`, so the
trichotomy needs a `mach_ring` step between its second and third branches. Cosmetic, but it is the
sort of gap a hand-written dispatch papers over by choosing whichever lemma looks applicable. -/
theorem cell_of_moving_Q (A B Q : EMLTree) (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (hQ2 : Q.depth ≤ 2) (LQ aQ XQ K XK : Real) (haQ : 0 < aQ)
    (hQf : ∀ x : Real, XQ ≤ x → Q.eval x = LQ + aQ * (1 / x))
    (hK : ∀ x : Real, XK ≤ x → exp ((EMLTree.eml A B).eval x) ≤ K) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 1 < Q.eval x →
      Q.eval x < exp (exp ((EMLTree.eml A B).eval x)) →
        exp (-C - exp x) ≤ exp (exp ((EMLTree.eml A B).eval x)) - Q.eval x := by
  rcases node_form_classification A B hA hB K XK hK with
      ⟨V, XV, hV⟩ | ⟨v, κ, XV, hv, hκ, hV⟩ | ⟨M, XV, hM, hV⟩ | ⟨κ, XV, hκ, hV⟩ | ⟨XV, hV⟩
  · -- (1) eventually-constant target
    exact boundedEmlCell_eventually_const_target A B Q hQ2 (exp V) XV
      (fun x hx => by rw [hV x hx])
  · -- (2) rising target `v·exp (κw)`
    rcases lt_total LQ (exp v) with hs | hs | hs
    · exact cell_of_rising_target_lower_Q A B Q hQ2 v κ LQ aQ XV XQ hv hκ haQ hs
        (fun x hx => by rw [hV x hx]) hQf
    · rcases lt_total aQ (exp v * (v * κ)) with hd | hd | hd
      · exact cell_of_rising_target_dominant A B Q v κ aQ XV XQ hv hκ (le_of_lt hd)
          (fun x hx => by rw [hV x hx]) (fun x hx => by rw [hQf x hx, hs])
      · exact cell_of_rising_target_dominant A B Q v κ aQ XV XQ hv hκ (le_of_eq hd)
          (fun x hx => by rw [hV x hx]) (fun x hx => by rw [hQf x hx, hs])
      · refine cell_of_rising_target_subdominant A B Q v κ aQ XV XQ hv hκ ?_
          (fun x hx => by rw [hV x hx]) (fun x hx => by rw [hQf x hx, hs])
        have e : exp v * (v * κ) = v * κ * exp v := by mach_ring
        rw [← e]; exact hd
    · exact cell_of_rising_target_upper_Q A B Q v κ LQ aQ XV XQ hv hκ haQ hs
        (fun x hx => by rw [hV x hx]) hQf
  · -- (3) decaying target `M·w`
    rcases lt_total LQ 1 with hs | hs | hs
    · exact cell_of_Q_below_one A B Q LQ aQ XQ haQ hs hQf
    · rcases lt_total aQ M with hd | hd | hd
      · exact cell_of_decaying_target_dominant A B Q M aQ XV XQ hM haQ (le_of_lt hd)
          (fun x hx => by rw [hV x hx]) (fun x hx => by rw [hQf x hx, hs])
      · exact cell_of_decaying_target_dominant A B Q M aQ XV XQ hM haQ (le_of_eq hd)
          (fun x hx => by rw [hV x hx]) (fun x hx => by rw [hQf x hx, hs])
      · exact cell_of_decaying_target_subdominant A B Q M aQ XV XQ hM hd
          (fun x hx => by rw [hV x hx]) (fun x hx => by rw [hQf x hx, hs])
    · exact cell_of_decaying_target_upper_Q A B Q M LQ aQ XV XQ hM haQ hs
        (fun x hx => by rw [hV x hx]) hQf
  · -- (4) the fifth shape `exp (κw)·w`
    have clear : ∀ x : Real, 1 + exp XV ≤ x → (1 : Real) ≤ x ∧ XV ≤ x := by
      intro x hx
      constructor
      · have v0 : (1 : Real) + 0 ≤ 1 + exp XV := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos XV))
        have e : (1 : Real) + 0 = 1 := by mach_ring
        rw [e] at v0; exact le_trans v0 hx
      · have v0 : (0 : Real) + exp XV ≤ 1 + exp XV :=
          add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
        have e : (0 : Real) + exp XV = exp XV := by mach_ring
        rw [e] at v0; exact le_trans (self_le_exp XV) (le_trans v0 hx)
    have hwle : ∀ x : Real, (1 : Real) ≤ x → 1 / x ≤ 1 := by
      intro x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      have hinv : x * (1 / x) = 1 := mul_inv x (ne_of_gt hx0)
      have h := mul_le_mul_of_nonneg_right hx (le_of_lt (one_div_pos_of_pos hx0))
      rw [hinv] at h
      have e : (1 : Real) * (1 / x) = 1 / x := by mach_ring
      rw [e] at h; exact h
    rcases lt_total LQ 1 with hs | hs | hs
    · exact cell_of_Q_below_one A B Q LQ aQ XQ haQ hs hQf
    · rcases lt_total aQ 1 with hd | hd | hd
      · refine cell_of_decaying_target_dominant_ge A B Q 1 aQ (1 + exp XV) XQ zero_lt_one_ax
          (le_of_lt hd) ?_ (fun x hx => by rw [hQf x hx, hs])
        intro x hx
        obtain ⟨h1, hXVx⟩ := clear x hx
        have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax h1
        have hbnd := node_logA_varB_bounds κ (1 / x) hκ (one_div_pos_of_pos hx0) (hwle x h1)
        rw [hV x hXVx]
        refine exp_monotone ?_
        have e : (1 : Real) * (1 / x) = 1 / x := by mach_ring
        rw [e]; exact hbnd.1
      · refine cell_of_decaying_target_dominant_ge A B Q 1 aQ (1 + exp XV) XQ zero_lt_one_ax
          (le_of_eq hd) ?_ (fun x hx => by rw [hQf x hx, hs])
        intro x hx
        obtain ⟨h1, hXVx⟩ := clear x hx
        have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax h1
        have hbnd := node_logA_varB_bounds κ (1 / x) hκ (one_div_pos_of_pos hx0) (hwle x h1)
        rw [hV x hXVx]
        refine exp_monotone ?_
        have e : (1 : Real) * (1 / x) = 1 / x := by mach_ring
        rw [e]; exact hbnd.1
      · exact cell_of_fifth_shape_subdominant A B Q κ aQ XV XQ hκ hd hV
          (fun x hx => by rw [hQf x hx, hs])
    · refine cell_of_decaying_target_upper_Q_le A B Q (exp κ) LQ aQ (1 + exp XV) XQ
        (exp_pos κ) haQ hs ?_ hQf
      intro x hx
      obtain ⟨h1, hXVx⟩ := clear x hx
      have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax h1
      have hbnd := node_logA_varB_bounds κ (1 / x) hκ (one_div_pos_of_pos hx0) (hwle x h1)
      rw [hV x hXVx]
      exact exp_monotone hbnd.2
  · -- (5) the log-bound target
    rcases lt_total LQ 1 with hs | hs | hs
    · exact cell_of_Q_below_one A B Q LQ aQ XQ haQ hs hQf
    · exact cell_of_log_bound_target A B Q hA hB K XK hK XV hV LQ aQ XQ haQ hQf (le_of_eq hs.symm)
    · exact cell_of_log_bound_target A B Q hA hB K XK hK XV hV LQ aQ XQ haQ hQf (le_of_lt hs)

/-- **`BoundedEmlCellApproachLarge` holds — the router, and the obligation closes.**

The outer dispatch. `Q` is split on its structure first, because three of its four surviving shapes
close outright and only one reaches the node at all:

* `const c` — `boundedEmlCell_eventually_const_Q`.
* `var` — `Q x = x` outruns the cap: `exp (exp (node x)) ≤ exp K ≤ x` past `exp (exp K)`, so
  `cell_of_Q_above_target` empties the region. The one branch where `Q` fails the *upper* guard
  rather than the lower one.
* `eml P R` — the left dichotomy bounds `exp (P x)`, the right dichotomy then leaves `P` and `R` each
  `const` or `c − log x`. Three of those four pairings are already lemmas; the fourth,
  `P = cP − log x` with `R` constant, is the moving `Q` that `cell_of_moving_Q` takes on.

**What writing it actually bought.** Twice now the router has been the thing that found the defect
rather than the thing that consumed the pieces: enumerating its cases exposed a missing fifth node
shape, and writing its inner dispatch exposed a bracket too loose to decide that shape's `L = 1` row.
Both were invisible from the comparison layer, which looked complete because nothing had yet queried
the part that was not. An assembly that type-checks is a stronger statement about a case analysis
than any prose claim that the analysis is exhaustive — Lean refuses the proof if a case is missing,
and it refused twice. -/
theorem boundedEmlCellApproachLarge_holds : BoundedEmlCellApproachLarge := by
  intro A B Q hA hB hQ2 K XK hK
  cases Q with
  | const c =>
      exact boundedEmlCell_eventually_const_Q A B (EMLTree.const c) hA hB c 1 (fun x _ => rfl)
  | var =>
      refine cell_of_Q_above_target A B EMLTree.var (1 + exp XK + exp (exp K)) ?_
      intro x hx
      have hXKx : XK ≤ x := by
        have v : (0 : Real) + exp XK + 0 ≤ 1 + exp XK + exp (exp K) :=
          add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _))
            (le_of_lt (exp_pos (exp K)))
        have e : (0 : Real) + exp XK + 0 = exp XK := by mach_ring
        rw [e] at v; exact le_trans (self_le_exp XK) (le_trans v hx)
      have hEK : exp (exp K) ≤ x := by
        have v : (0 : Real) + 0 + exp (exp K) ≤ 1 + exp XK + exp (exp K) :=
          add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax) (le_of_lt (exp_pos XK)))
            (le_refl _)
        have e : (0 : Real) + 0 + exp (exp K) = exp (exp K) := by mach_ring
        rw [e] at v; exact le_trans v hx
      show exp (exp ((EMLTree.eml A B).eval x)) ≤ x
      exact le_trans (exp_monotone (hK x hXKx)) (le_trans (self_le_exp (exp K)) hEK)
  | eml P R =>
      have hP : P.depth ≤ 1 := by
        simp only [EMLTree.depth] at hQ2
        have := Nat.le_max_left P.depth R.depth; omega
      have hR : R.depth ≤ 1 := by
        simp only [EMLTree.depth] at hQ2
        have := Nat.le_max_right P.depth R.depth; omega
      rcases boundedEmlCell_left_dichotomy A B P R hP hR K XK hK with hdone | ⟨Kb, hb⟩
      · exact hdone
      rcases boundedEmlCell_right_dichotomy A B P R hR Kb 1 hb with
          hdone | ⟨β, hβ⟩ | ⟨cR, _, hβ⟩
      · exact hdone
      · rcases boundedEmlCell_left_two_shapes P hP Kb hb with ⟨α, hα⟩ | ⟨cP, _, hα⟩
        · exact boundedEmlCell_constP_constR A B P R hA hB α β hα hβ
        · refine cell_of_moving_Q A B (EMLTree.eml P R) hA hB hQ2 (-(log β)) (exp cP) 1 K XK
            (exp_pos cP) ?_ hK
          intro x hx
          exact moving_Q_eventual_form P R cP β hα hβ x (lt_of_lt_of_le zero_lt_one_ax hx)
      · rcases boundedEmlCell_left_two_shapes P hP Kb hb with ⟨α, hα⟩ | ⟨cP, _, hα⟩
        · exact boundedEmlCell_constP_logR A B P R hA hB α cR hα hβ
        · exact boundedEmlCell_logP_logR A B P R cP cR hα hβ

/-- **`BoundedEmlCellApproach` holds**, by the small-right merge. -/
theorem boundedEmlCellApproach_holds : BoundedEmlCellApproach :=
  boundedEmlCellApproach_of_large boundedEmlCellApproachLarge_holds

/-- **`BoundedCellApproach` holds** — the reduction chain collapses to theorems.

`boundedCellApproach_of_eml` moved a general depth-≤2 `P` to the `eml A B` case; that reduction was
recorded as *reduced* rather than *discharged* precisely because its target was still open. It is not
any more, and the ledger rows change with it: three obligations that were bookkeeping become
theorems, and nothing in the chain still rests on an assumption. -/
theorem boundedCellApproach_holds : BoundedCellApproach :=
  boundedCellApproach_of_eml boundedEmlCellApproach_holds


/-- **A positive depth-≤1 logarithm is bounded below by a positive constant.**

The grammar cannot produce arbitrarily small *positive* logarithms at this depth. Of the five forms:
`log β` is an exact constant, and if it is not positive the hypothesis is false; `log x` and the two
`exp x − …` forms diverge; and `c − log x` goes non-positive, so `Log` totalises to `0` and the
hypothesis fails again.

**This is the delicate cell of `ExpExpGapBelow`.** There, the right child of a depth-2 tree whose left
child is exactly `exp x` contributes a gap of precisely `Log (B x)`, so the whole question of whether
`exp (exp x)` can be approached from below with a shrinking gap comes down to this lemma — a positive
constant floor, not a decaying one. The same asymmetry as `depth_le_one_gap_below`, and the same
cause: nothing in the grammar decays to `0` from above at this depth except by way of a shape that
crosses into the totalised branch. -/
theorem depth_le_one_log_gap_pos (B : EMLTree) (hB : B.depth ≤ 1) :
    ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧
      ∀ x : Real, X₀ ≤ x → 0 < log (B.eval x) → ε ≤ log (B.eval x) := by
  rcases depth_le_one_classification B hB with ⟨β, hb⟩ | hb | ⟨c, _, hb⟩ | ⟨d, hb⟩ | hb
  · rcases lt_total 0 (log β) with hβ | hβ | hβ
    · refine ⟨log β, 1, hβ, le_refl 1, ?_⟩
      intro x hx _
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos]
      exact le_refl _
    · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
      intro x hx hpos
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos, ← hβ] at hpos
      exact absurd hpos (lt_irrefl_ax 0)
    · refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
      intro x hx hpos
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
      rw [hb x hxpos] at hpos
      exact absurd (lt_trans_ax hpos hβ) (lt_irrefl_ax 0)
  · -- `log x` diverges
    refine ⟨1, 1 + exp 1, zero_lt_one_ax, one_le_one_add_exp 1, ?_⟩
    intro x hx _
    have hxpos : (0 : Real) < x :=
      lt_of_lt_of_le zero_lt_one_ax (le_trans (one_le_one_add_exp 1) hx)
    rw [hb x hxpos]
    exact log_ge_of_exp_le (le_trans (exp_le_one_add_exp 1) hx)
  · -- `c − log x` totalises to `0`, so the hypothesis fails
    refine ⟨1, 1 + exp c, zero_lt_one_ax, one_le_one_add_exp c, ?_⟩
    intro x hx hpos
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp c) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos] at hpos
    have hge : c ≤ log x := log_ge_of_exp_le (le_trans (exp_le_one_add_exp c) hx)
    have hle : c - log x ≤ 0 := by
      have v := add_le_add_wit (le_refl c) (neg_le_neg_wit hge)
      have e1 : c + -log x = c - log x := by mach_ring
      have e2 : c + -c = (0 : Real) := by mach_mpoly [c]
      rw [e1, e2] at v; exact v
    rw [log_nonpos hle] at hpos
    exact absurd hpos (lt_irrefl_ax 0)
  · -- `exp x − d` diverges
    refine ⟨1, 1 + exp 1 + exp d, zero_lt_one_ax, one_le_ray 1 d, ?_⟩
    intro x hx _
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_ray 1 d) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos]
    refine log_ge_of_exp_le ?_
    have hreach : exp 1 + d ≤ x := by
      have v := add_le_add_wit (le_refl (exp 1)) (self_le_exp d)
      have w : exp 1 + exp d ≤ 1 + exp 1 + exp d := by
        have u := add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
          (le_refl (exp 1))) (le_refl (exp d))
        have e : (0 : Real) + exp 1 + exp d = exp 1 + exp d := by mach_ring
        rw [e] at u; exact u
      exact le_trans (le_trans v w) hx
    have hxe : exp 1 + d ≤ exp x := le_trans hreach (self_le_exp x)
    have v := add_le_add_wit hxe (le_refl (-d))
    have e1 : exp 1 + d + -d = exp 1 := by mach_mpoly [exp 1, d]
    have e2 : exp x + -d = exp x - d := by mach_ring
    rw [e1, e2] at v; exact v
  · -- `exp x − log x` diverges, since it dominates `x`
    refine ⟨1, 1 + exp 1, zero_lt_one_ax, one_le_one_add_exp 1, ?_⟩
    intro x hx _
    have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp 1) hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
    rw [hb x hxpos]
    exact log_ge_of_exp_le (le_trans (le_trans (exp_le_one_add_exp 1) hx)
      (self_le_exp_sub_log hx1))


/-- **The `d < 0` branch of `ExpExpGapBelow` is vacuous, not hard.**

If the left child is `exp x − d` with `d < 0` then the depth-2 tree's value already *exceeds*
`exp (exp x)`, so it cannot approach it from below at all and the hypothesis of `ExpExpGapBelow` is
false on a ray.

The proof is where the division-free move earns its place. Convexity gives
`exp (exp x − d) − exp (exp x) ≥ (−d) · exp (exp x)`, and this base cannot divide by `−d` to make that
usable. Writing **`−d = exp (log (−d))`** turns the product into `exp (log (−d) + exp x)`, which
`self_le_exp` bounds below by `log (−d) + exp x` — *linear*, so it can be compared directly against
the linear ceiling `log (B x) ≤ x + D` and the ray comes out explicitly as `x ≥ D − log (−d)`.

A doubly exponential quantity is thereby handled without ever bounding it above: the only fact used is
that it dominates its own logarithm. -/
theorem exp_shift_neg_exceeds (B : EMLTree) (hB : B.depth ≤ 1) {d : Real} (hd : d < 0) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      exp (exp x) ≤ exp (exp x - d) - log (B.eval x) := by
  obtain ⟨D, hD⟩ := depth_le_one_log_le_linear B hB
  have hdpos : (0 : Real) < -d := by
    have v := add_lt_add_left hd (-d)
    have e1 : -d + d = (0 : Real) := by mach_mpoly [d]
    have e2 : -d + (0 : Real) = -d := by mach_ring
    rw [e1, e2] at v; exact v
  refine ⟨1 + exp (D - log (-d)), one_le_one_add_exp _, ?_⟩
  intro x hx
  have hx1 : (1 : Real) ≤ x := le_trans (one_le_one_add_exp _) hx
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hreach : D - log (-d) ≤ x :=
    le_trans (self_le_exp _) (le_trans (exp_le_one_add_exp _) hx)
  have hconv : (exp x - d - exp x) * exp (exp x) ≤ exp (exp x - d) - exp (exp x) :=
    exp_sub_exp_lower (exp x - d) (exp x)
  have e0 : exp x - d - exp x = -d := by mach_mpoly [exp x, d]
  rw [e0] at hconv
  -- the division-free step: `−d = exp (log (−d))`, so the product is itself an exponential
  have hprod : exp (log (-d) + exp x) = -d * exp (exp x) := by
    rw [exp_add, exp_log hdpos]
  have hlin : log (-d) + exp x ≤ -d * exp (exp x) := by
    rw [← hprod]; exact self_le_exp _
  have h1 : log (-d) + (x + x) ≤ log (-d) + exp x :=
    add_le_add_left (two_mul_le_exp hx0) (log (-d))
  have h2 : x + D ≤ log (-d) + (x + x) := by
    have v := add_le_add_wit hreach (le_refl (x + log (-d)))
    have e1 : D - log (-d) + (x + log (-d)) = x + D := by mach_mpoly [D, x, log (-d)]
    have e2 : x + (x + log (-d)) = log (-d) + (x + x) := by mach_mpoly [x, log (-d)]
    rw [e1, e2] at v; exact v
  have hbig : x + D ≤ -d * exp (exp x) := le_trans h2 (le_trans h1 hlin)
  have hfinal : log (B.eval x) ≤ exp (exp x - d) - exp (exp x) :=
    le_trans (hD x hx1) (le_trans hbig hconv)
  have v := add_le_add_wit hfinal (le_refl (exp (exp x) - log (B.eval x)))
  have e1 : log (B.eval x) + (exp (exp x) - log (B.eval x)) = exp (exp x) := by
    mach_mpoly [log (B.eval x), exp (exp x)]
  have e2 : exp (exp x - d) - exp (exp x) + (exp (exp x) - log (B.eval x))
      = exp (exp x - d) - log (B.eval x) := by
    mach_mpoly [exp (exp x - d), exp (exp x), log (B.eval x)]
  rw [e1, e2] at v; exact v


/-- **The `d > 0` branch of `ExpExpGapBelow`, by the same route.** Here the gap is genuinely large
rather than the hypothesis being false, and it clears `1` unconditionally.

`exp (exp x) − exp (exp x − d) ≥ d · exp (exp x − d)` by convexity, and `d = exp (log d)` turns that
product into `exp (log d + (exp x − d))`, which `self_le_exp` flattens to `log d + exp x − d`. With
`exp x ≥ x + x` and the constant floor `Cl ≤ log (B x)`, the whole gap is linear in `x` from below,
so the ray is explicit. Same three moves as `exp_shift_neg_exceeds`, used to prove a bound rather
than a vacuity. -/
theorem exp_shift_pos_gap (B : EMLTree) (hB : B.depth ≤ 1) {d : Real} (hd : 0 < d) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      1 ≤ exp (exp x) - (exp (exp x - d) - log (B.eval x)) := by
  obtain ⟨Cl, XC, hXC, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
  have hXC0 : (0 : Real) ≤ XC := le_trans (le_of_lt zero_lt_one_ax) hXC
  refine ⟨XC + exp (1 + d - log d - Cl),
    le_trans hXC (le_add_nonneg_r' (le_of_lt (exp_pos _))), ?_⟩
  intro x hx
  have hXCx : XC ≤ x := le_trans (le_add_nonneg_r' (le_of_lt (exp_pos _))) hx
  have hx1 : (1 : Real) ≤ x := le_trans hXC hXCx
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hreach : 1 + d - log d - Cl ≤ x :=
    le_trans (self_le_exp _) (le_trans (le_add_nonneg_l' hXC0) hx)
  -- convexity, then `d = exp (log d)` to flatten the product
  have hconv : (exp x - (exp x - d)) * exp (exp x - d) ≤ exp (exp x) - exp (exp x - d) :=
    exp_sub_exp_lower (exp x) (exp x - d)
  have e0 : exp x - (exp x - d) = d := by mach_mpoly [exp x, d]
  rw [e0] at hconv
  have hprod : exp (log d + (exp x - d)) = d * exp (exp x - d) := by
    rw [exp_add, exp_log hd]
  have hlin : log d + (exp x - d) ≤ d * exp (exp x - d) := by
    rw [← hprod]; exact self_le_exp _
  have h1 : log d + (exp x - d) ≤ exp (exp x) - exp (exp x - d) := le_trans hlin hconv
  -- `exp x ≥ x + x` makes the lower bound linear
  have h2 : log d + (x + x - d) ≤ log d + (exp x - d) := by
    refine add_le_add_left ?_ (log d)
    have v := add_le_add_wit (two_mul_le_exp hx0) (le_refl (-d))
    have e1 : x + x + -d = x + x - d := by mach_mpoly [x, d]
    have e2 : exp x + -d = exp x - d := by mach_ring
    rw [e1, e2] at v; exact v
  have h3 : log d + (x + x - d) ≤ exp (exp x) - exp (exp x - d) := le_trans h2 h1
  have h4 : log d + (x + x - d) + Cl
      ≤ exp (exp x) - exp (exp x - d) + log (B.eval x) := add_le_add_wit h3 (hCl x hXCx)
  have h5 : (1 : Real) ≤ log d + (x + x - d) + Cl := by
    have hxx : x ≤ x + x := le_add_nonneg_l' hx0
    have hstep : 1 + d - log d - Cl ≤ x + x := le_trans hreach hxx
    have v := add_le_add_wit hstep (le_refl (log d - d + Cl))
    have e1 : 1 + d - log d - Cl + (log d - d + Cl) = (1 : Real) := by mach_mpoly [d, log d, Cl]
    have e2 : x + x + (log d - d + Cl) = log d + (x + x - d) + Cl := by
      mach_mpoly [x, d, log d, Cl]
    rw [e1, e2] at v; exact v
  have h6 : (1 : Real) ≤ exp (exp x) - exp (exp x - d) + log (B.eval x) := le_trans h5 h4
  have e3 : exp (exp x) - exp (exp x - d) + log (B.eval x)
      = exp (exp x) - (exp (exp x - d) - log (B.eval x)) := by
    mach_mpoly [exp (exp x), exp (exp x - d), log (B.eval x)]
  rw [e3] at h6
  exact h6


/-- **The bounded-left-child branches of `ExpExpGapBelow`, in one lemma.** If `exp (A x)` is capped by
a constant then the gap to `exp (exp x)` clears `1`, because `exp (exp x) ≥ exp x ≥ x` grows past any
constant while `log (B x)` has a constant floor.

Covers the `A = α` and `A = c − log x` forms at once — the two whose exponential is bounded — and
never inspects `B` beyond its depth. -/
theorem expexp_gap_of_bounded (A B : EMLTree) (hB : B.depth ≤ 1) {M XM : Real}
    (hM : ∀ x : Real, XM ≤ x → exp (A.eval x) ≤ M) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      1 ≤ exp (exp x) - (exp (A.eval x) - log (B.eval x)) := by
  obtain ⟨Cl, XC, hXC, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
  have hXC0 : (0 : Real) ≤ XC := le_trans (le_of_lt zero_lt_one_ax) hXC
  have hp1 : (0 : Real) ≤ XC + exp XM := le_trans hXC0 (le_add_nonneg_r' (le_of_lt (exp_pos XM)))
  refine ⟨XC + exp XM + exp (1 + M - Cl),
    le_trans hXC (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos XM)))
      (le_add_nonneg_r' (le_of_lt (exp_pos _)))), ?_⟩
  intro x hx
  have hXCx : XC ≤ x :=
    le_trans (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos XM)))
      (le_add_nonneg_r' (le_of_lt (exp_pos _)))) hx
  have hXMx : XM ≤ x :=
    le_trans (self_le_exp XM) (le_trans (le_add_nonneg_l' hXC0)
      (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos _))) hx))
  have hreach : 1 + M - Cl ≤ x := le_trans (self_le_exp _) (le_trans (le_add_nonneg_l' hp1) hx)
  have hx1 : (1 : Real) ≤ x := le_trans hXC hXCx
  -- `exp (exp x) ≥ exp x ≥ x`
  have hee : x ≤ exp (exp x) := le_trans (self_le_exp x) (self_le_exp (exp x))
  have hbig : 1 + M - Cl ≤ exp (exp x) := le_trans hreach hee
  -- assemble
  have hstep : 1 + M - Cl - M + Cl ≤ exp (exp x) - exp (A.eval x) + log (B.eval x) := by
    have v := add_le_add_wit (add_le_add_wit hbig (neg_le_neg_wit (hM x hXMx))) (hCl x hXCx)
    have e1 : 1 + M - Cl + -M + Cl = 1 + M - Cl - M + Cl := by mach_mpoly [M, Cl]
    have e2 : exp (exp x) + -exp (A.eval x) + log (B.eval x)
        = exp (exp x) - exp (A.eval x) + log (B.eval x) := by mach_ring
    rw [e1, e2] at v; exact v
  have e3 : 1 + M - Cl - M + Cl = (1 : Real) := by mach_mpoly [M, Cl]
  rw [e3] at hstep
  have e4 : exp (exp x) - exp (A.eval x) + log (B.eval x)
      = exp (exp x) - (exp (A.eval x) - log (B.eval x)) := by
    mach_mpoly [exp (exp x), exp (A.eval x), log (B.eval x)]
  rw [e4] at hstep
  exact hstep


/-- **`ExpExpGapBelow` holds.** The obligation the `P = var` cell of `Depth3DecayExp` reduces to.

Assembly only: every branch is a lemma proved above. `const` and `var` clear `1` because
`exp (exp x) ≥ exp x ≥ x + x`; `A = α` and `A = c − log x` go through `expexp_gap_of_bounded`;
`A = x` and `A = exp x − log x` are one convexity step each against the constant floor
`Cl ≤ log (B x)`; and the three `A = exp x − d` sub-cases are `exp_shift_pos_gap`,
`depth_le_one_log_gap_pos` and `exp_shift_neg_exceeds` respectively.

The `d = 0` sub-case is the one that matters: there the gap is *exactly* `Log (B x)`, and it is
positive precisely because the hypothesis says the tree is below `exp (exp x)`. That is the same
construction that refuted `Depth3DecayHard`, now bounded rather than unbounded, because the question
changed from "how small can the node be" to "how small can this gap be". -/
theorem expExpGapBelow_holds : ExpExpGapBelow := by
  intro Q hQ
  cases Q with
  | const c =>
    refine ⟨1, 1 + exp (c + 1), zero_lt_one_ax, one_le_one_add_exp _, ?_⟩
    intro x hx _
    have hreach : c + 1 ≤ x := le_trans (self_le_exp _) (le_trans (exp_le_one_add_exp _) hx)
    have hee : x ≤ exp (exp x) := le_trans (self_le_exp x) (self_le_exp (exp x))
    show (1 : Real) ≤ exp (exp x) - c
    have v := add_le_add_wit (le_trans hreach hee) (le_refl (-c))
    have e1 : c + 1 + -c = (1 : Real) := by mach_mpoly [c]
    have e2 : exp (exp x) + -c = exp (exp x) - c := by mach_ring
    rw [e1, e2] at v; exact v
  | var =>
    refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x hx _
    have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx
    show (1 : Real) ≤ exp (exp x) - x
    have h3 : x + x ≤ exp (exp x) := le_trans (two_mul_le_exp hx0) (self_le_exp (exp x))
    have v := add_le_add_wit h3 (le_refl (-x))
    have e1 : x + x + -x = x := by mach_mpoly [x]
    have e2 : exp (exp x) + -x = exp (exp x) - x := by mach_ring
    rw [e1, e2] at v
    exact le_trans hx v
  | eml A B =>
    have hA : A.depth ≤ 1 := by
      simp only [EMLTree.depth] at hQ
      have := Nat.le_max_left A.depth B.depth; omega
    have hB : B.depth ≤ 1 := by
      simp only [EMLTree.depth] at hQ
      have := Nat.le_max_right A.depth B.depth; omega
    rcases depth_le_one_classification A hA with ⟨α, ha⟩ | ha | ⟨c, _, ha⟩ | ⟨d, ha⟩ | ha
    · obtain ⟨X₀, hX₀, hg⟩ := expexp_gap_of_bounded A B hB (M := exp α) (XM := 1)
        (fun x hx => by rw [ha x (lt_of_lt_of_le zero_lt_one_ax hx)]; exact le_refl _)
      exact ⟨1, X₀, zero_lt_one_ax, hX₀, fun x hx _ => hg x hx⟩
    · obtain ⟨Cl, XC, hXC, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
      have hXC0 : (0 : Real) ≤ XC := le_trans (le_of_lt zero_lt_one_ax) hXC
      refine ⟨1, XC + exp (1 - Cl), zero_lt_one_ax,
        le_trans hXC (le_add_nonneg_r' (le_of_lt (exp_pos _))), ?_⟩
      intro x hx _
      have hXCx : XC ≤ x := le_trans (le_add_nonneg_r' (le_of_lt (exp_pos _))) hx
      have hx1 : (1 : Real) ≤ x := le_trans hXC hXCx
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have hreach : 1 - Cl ≤ x := le_trans (self_le_exp _) (le_trans (le_add_nonneg_l' hXC0) hx)
      show (1 : Real) ≤ exp (exp x) - (exp (A.eval x) - log (B.eval x))
      rw [ha x hxpos]
      have h1 : x ≤ exp (exp x) - exp x := by
        have v := add_le_add_wit (two_mul_le_exp (le_of_lt (exp_pos x))) (le_refl (-exp x))
        have e1 : exp x + exp x + -exp x = exp x := by mach_mpoly [exp x]
        have e2 : exp (exp x) + -exp x = exp (exp x) - exp x := by mach_ring
        rw [e1, e2] at v; exact le_trans (self_le_exp x) v
      have h2 : x + Cl ≤ exp (exp x) - exp x + log (B.eval x) :=
        add_le_add_wit h1 (hCl x hXCx)
      have h3 : (1 : Real) ≤ x + Cl := by
        have v := add_le_add_wit hreach (le_refl Cl)
        have e1 : 1 - Cl + Cl = (1 : Real) := by mach_mpoly [Cl]
        rw [e1] at v; exact v
      have e4 : exp (exp x) - exp x + log (B.eval x)
          = exp (exp x) - (exp x - log (B.eval x)) := by
        mach_mpoly [exp (exp x), exp x, log (B.eval x)]
      rw [e4] at h2
      exact le_trans h3 h2
    · obtain ⟨X₀, hX₀, hg⟩ := expexp_gap_of_bounded A B hB (M := exp c) (XM := 1)
        (fun x hx => by
          have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
          rw [ha x hxpos]
          refine exp_monotone ?_
          have hl1 : log (1 : Real) = 0 := by
            have hz : exp (0 : Real) = 1 := exp_zero
            rw [← hz, log_exp]
          have hlx : (0 : Real) ≤ log x := by
            have hm := log_le_log zero_lt_one_ax hx
            rw [hl1] at hm; exact hm
          have v := add_le_add_wit (le_refl c) (neg_le_neg_wit hlx)
          have e1 : c + -log x = c - log x := by mach_ring
          have e2 : c + -(0 : Real) = c := by mach_ring
          rw [e1, e2] at v; exact v)
      exact ⟨1, X₀, zero_lt_one_ax, hX₀, fun x hx _ => hg x hx⟩
    · rcases lt_total 0 d with hd | hd | hd
      · obtain ⟨X₀, hX₀, hg⟩ := exp_shift_pos_gap B hB hd
        refine ⟨1, X₀, zero_lt_one_ax, hX₀, ?_⟩
        intro x hx _
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX₀ hx)
        show (1 : Real) ≤ exp (exp x) - (exp (A.eval x) - log (B.eval x))
        rw [ha x hxpos]
        exact hg x hx
      · obtain ⟨ε, X₁, hε, hX₁, hg⟩ := depth_le_one_log_gap_pos B hB
        refine ⟨ε, X₁, hε, hX₁, ?_⟩
        intro x hx hlt
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX₁ hx)
        have e0 : exp x - (0 : Real) = exp x := by mach_ring
        have hlt' : exp (A.eval x) - log (B.eval x) < exp (exp x) := hlt
        rw [ha x hxpos, ← hd, e0] at hlt'
        have hpos : (0 : Real) < log (B.eval x) := by
          have v := add_lt_add_left hlt' (log (B.eval x) - exp (exp x))
          have e1 : log (B.eval x) - exp (exp x) + (exp (exp x) - log (B.eval x)) = (0 : Real) := by
            mach_mpoly [log (B.eval x), exp (exp x)]
          have e2 : log (B.eval x) - exp (exp x) + exp (exp x) = log (B.eval x) := by
            mach_mpoly [log (B.eval x), exp (exp x)]
          rw [e1, e2] at v; exact v
        show ε ≤ exp (exp x) - (exp (A.eval x) - log (B.eval x))
        rw [ha x hxpos, ← hd, e0]
        have e1 : exp (exp x) - (exp (exp x) - log (B.eval x)) = log (B.eval x) := by
          mach_mpoly [exp (exp x), log (B.eval x)]
        rw [e1]
        exact hg x hx hpos
      · obtain ⟨X₀, hX₀, hge⟩ := exp_shift_neg_exceeds B hB hd
        refine ⟨1, X₀, zero_lt_one_ax, hX₀, ?_⟩
        intro x hx hlt
        have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX₀ hx)
        have hlt' : exp (A.eval x) - log (B.eval x) < exp (exp x) := hlt
        rw [ha x hxpos] at hlt'
        exact absurd (lt_of_le_of_lt (hge x hx) hlt') (lt_irrefl_ax (exp (exp x)))
    · obtain ⟨Cl, XC, hXC, hCl⟩ := depth_le_one_log_lower_at_infinity B hB
      have hXC0 : (0 : Real) ≤ XC := le_trans (le_of_lt zero_lt_one_ax) hXC
      have hp1 : (0 : Real) ≤ XC + exp 1 := le_trans hXC0 (le_add_nonneg_r' (le_of_lt (exp_pos 1)))
      refine ⟨1, XC + exp 1 + exp (1 - Cl), zero_lt_one_ax,
        le_trans hXC (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos 1)))
          (le_add_nonneg_r' (le_of_lt (exp_pos _)))), ?_⟩
      intro x hx _
      have hXCx : XC ≤ x := le_trans (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos 1)))
        (le_add_nonneg_r' (le_of_lt (exp_pos _)))) hx
      have hx1 : (1 : Real) ≤ x := le_trans hXC hXCx
      have hxpos : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
      have he1x : exp 1 ≤ x := le_trans (le_add_nonneg_l' hXC0)
        (le_trans (le_add_nonneg_r' (le_of_lt (exp_pos _))) hx)
      have hreach : 1 - Cl ≤ x := le_trans (self_le_exp _) (le_trans (le_add_nonneg_l' hp1) hx)
      show (1 : Real) ≤ exp (exp x) - (exp (A.eval x) - log (B.eval x))
      rw [ha x hxpos]
      have hconv : (exp x - (exp x - log x)) * exp (exp x - log x)
          ≤ exp (exp x) - exp (exp x - log x) := exp_sub_exp_lower (exp x) (exp x - log x)
      have e0 : exp x - (exp x - log x) = log x := by mach_mpoly [exp x, log x]
      rw [e0] at hconv
      have hlogx : (1 : Real) ≤ log x := log_ge_of_exp_le he1x
      have hexp_ge : x ≤ exp (exp x - log x) :=
        le_trans (self_le_exp_sub_log hx1) (self_le_exp _)
      have hmul : exp (exp x - log x) ≤ log x * exp (exp x - log x) := by
        have v := mul_le_mul_of_nonneg_right hlogx (le_of_lt (exp_pos (exp x - log x)))
        have e : (1 : Real) * exp (exp x - log x) = exp (exp x - log x) := by mach_ring
        rw [e] at v; exact v
      have h1 : x ≤ exp (exp x) - exp (exp x - log x) :=
        le_trans hexp_ge (le_trans hmul hconv)
      have h2 : x + Cl ≤ exp (exp x) - exp (exp x - log x) + log (B.eval x) :=
        add_le_add_wit h1 (hCl x hXCx)
      have h3 : (1 : Real) ≤ x + Cl := by
        have v := add_le_add_wit hreach (le_refl Cl)
        have e1 : 1 - Cl + Cl = (1 : Real) := by mach_mpoly [Cl]
        rw [e1] at v; exact v
      have e4 : exp (exp x) - exp (exp x - log x) + log (B.eval x)
          = exp (exp x) - (exp (exp x - log x) - log (B.eval x)) := by
        mach_mpoly [exp (exp x), exp (exp x - log x), log (B.eval x)]
      rw [e4] at h2
      exact le_trans h3 h2


/-- **The `P = var` cell of `Depth3DecayExp`, unconditionally.** `ExpExpGapBelow` is now a theorem, so
the reduction discharges. Three of the four cells hold outright; only bounded-`P` remains, and it is
reduced to `BoundedCellApproach`. -/
theorem depth_three_decayExp_var_left (Q : EMLTree) (hQ : Q.depth ≤ 2) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (Q.eval x) →
      0 < exp x - log (Q.eval x) → -log (exp x - log (Q.eval x)) ≤ C + exp x :=
  depth_three_decayExp_var_left_of_gap expExpGapBelow_holds Q hQ

/-- **The bounded-`P` cell of `Depth3DecayExp`, unconditionally.** The companion to the `var` cell
above, and the same move: `BoundedCellApproach` is now a theorem, so the reduction discharges.

That leaves `Depth3DecayExp` with all four of its cells proved — `growing`, `const`, `var`, `bounded`
— and what remains between the cells and the proposition is the dispatch over `P`, not any further
analysis. `depth3DecayExp_holds` below is that dispatch. -/
theorem depth_three_decayExp_bounded_left (P Q : EMLTree) (hP : P.depth ≤ 2) (hQ : Q.depth ≤ 2)
    (K XK : Real) (hK : ∀ x : Real, XK ≤ x → exp (P.eval x) ≤ K) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (Q.eval x) →
      0 < exp (P.eval x) - log (Q.eval x) →
      -log (exp (P.eval x) - log (Q.eval x)) ≤ C + exp x :=
  depth_three_decayExp_bounded_left_of_gap boundedCellApproach_holds P Q hP hQ K XK hK

/-- **`Depth3DecayExp` holds.** The dispatch onto the four cells, and the obligation closes.

A trichotomy on `A`, and the point of interest is that it *is* a trichotomy — the four cells were
built one at a time against different hypotheses, and whether they cover an arbitrary depth-≤2 `A`
was never checked until this proof was written.

| `A` | why | cell |
| --- | --- | --- |
| `const c` | `exp c` is already the cell's subject | `depth_three_decayExp_const_left` |
| `var` | `exp x` against a doubly exponential target | `depth_three_decayExp_var_left` |
| `eml A₁ B₁`, `exp (A₁ x)` bounded | the node is capped: `exp (A₁ x) − log (B₁ x) ≤ Kb − Cl` | `depth_three_decayExp_bounded_left` |
| `eml A₁ B₁`, `exp (A₁ x)` growing | the node clears `exp x − x − C`, since `log (B₁ x) ≤ x + C` | `depth_three_decayExp_growing_left` |

The last two rows are where the depth budget is spent, and they line up exactly:
`depth_le_one_exp_bounded_or_grows` splits the *grandchild* `A₁` into bounded-or-growing with nothing
in between, and each half hands the corresponding cell precisely the hypothesis it asks for. The
bounded half needs `depth_le_one_log_lower_at_infinity` to floor `log (B₁ x)`, the growing half needs
`depth_le_one_log_le_linear` to cap it — the two directions of the same depth-≤1 log bound, one per
branch. No new analysis; the gap really was the dispatch.

**`var` is the load-bearing row, and the only one that needs the corrected rung.** `growing` and
`const` are `rung_weaken`ings of cells that prove the stronger `C + x`; `bounded` and `var` do not,
and `var` is where `Depth3DecayHard`'s counterexample lives. So this proof cannot be adapted to the
refuted sibling — see `depth3DecayExp_of_hard` for that separation, machine-checked. -/
theorem depth3DecayExp_holds : Depth3DecayExp := by
  intro A B hA hB
  cases A with
  | const c => exact depth_three_decayExp_const_left c B hB
  | var => exact depth_three_decayExp_var_left B hB
  | eml A₁ B₁ =>
      have hA₁ : A₁.depth ≤ 1 := by
        simp only [EMLTree.depth] at hA
        have := Nat.le_max_left A₁.depth B₁.depth; omega
      have hB₁ : B₁.depth ≤ 1 := by
        simp only [EMLTree.depth] at hA
        have := Nat.le_max_right A₁.depth B₁.depth; omega
      have hval : ∀ x : Real,
          (EMLTree.eml A₁ B₁).eval x = exp (A₁.eval x) - log (B₁.eval x) := fun _ => rfl
      rcases depth_le_one_exp_bounded_or_grows A₁ hA₁ with ⟨Kb, hKb⟩ | ⟨T, hT⟩
      · -- bounded grandchild: the node itself is capped, so the bounded cell applies
        obtain ⟨Cl, XC, hXC, hCl⟩ := depth_le_one_log_lower_at_infinity B₁ hB₁
        refine depth_three_decayExp_bounded_left (EMLTree.eml A₁ B₁) B hA hB
          (exp (Kb - Cl)) XC ?_
        intro x hx
        have hx1 : (1 : Real) ≤ x := le_trans hXC hx
        rw [hval x]
        refine exp_monotone ?_
        have v := add_le_add_wit (hKb x hx1) (neg_le_neg_wit (hCl x hx))
        have l : exp (A₁.eval x) + -log (B₁.eval x) = exp (A₁.eval x) - log (B₁.eval x) := by
          mach_mpoly [exp (A₁.eval x), log (B₁.eval x)]
        have r : Kb + -Cl = Kb - Cl := by mach_mpoly [Kb, Cl]
        rw [l, r] at v; exact v
      · -- growing grandchild: the node clears `exp x − x − C`
        obtain ⟨C, hC⟩ := depth_le_one_log_le_linear B₁ hB₁
        have hgrow : ∀ x : Real, 1 + exp T ≤ x →
            exp x - x - C ≤ (EMLTree.eml A₁ B₁).eval x := by
          intro x hx
          have hx1 : (1 : Real) ≤ x := by
            have v0 : (1 : Real) + 0 ≤ 1 + exp T := add_le_add_wit (le_refl 1) (le_of_lt (exp_pos T))
            have e : (1 : Real) + 0 = 1 := by mach_ring
            rw [e] at v0; exact le_trans v0 hx
          have hTx : T ≤ x := by
            have v0 : (0 : Real) + exp T ≤ 1 + exp T :=
              add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl _)
            have e : (0 : Real) + exp T = exp T := by mach_ring
            rw [e] at v0; exact le_trans (self_le_exp T) (le_trans v0 hx)
          rw [hval x]
          have v := add_le_add_wit (hT x hTx) (neg_le_neg_wit (hC x hx1))
          have l : exp x + -(x + C) = exp x - x - C := by mach_mpoly [exp x, x, C]
          have r : exp (A₁.eval x) + -log (B₁.eval x) = exp (A₁.eval x) - log (B₁.eval x) := by
            mach_mpoly [exp (A₁.eval x), log (B₁.eval x)]
          rw [l, r] at v; exact v
        obtain ⟨C', X₀, hX₀, h⟩ :=
          depth_three_decayExp_growing_left (EMLTree.eml A₁ B₁) B hB C (1 + exp T) hgrow
        exact ⟨C', X₀, hX₀, fun x hx _ _ => h x hx⟩

/-- **The refuted sibling implies this one — so the rung correction is sharp.**

`Depth3DecayHard` is `Depth3DecayExp` with `C + x` where this has `C + exp x`, and `x ≤ exp x`, so
Hard ⟹ Exp. Together with `not_depth3DecayHard` and `depth3DecayExp_holds` that pins the pair
exactly: the implication runs one way, the antecedent is **false**, the consequent is **true**. The
rung was not weakened further than the counterexample forced — one exponential is what it cost, and
the statement flips truth value across that single step.

Stated with an explicit binder rather than as `Depth3DecayHard → Depth3DecayExp`, and the difference
is not cosmetic: `tools/obligation_ledger_check.py` reads a theorem's conclusion as the tail after
its last top-level `:`, and strips binders of the obligation's own type before doing so. In arrow
form the tail begins `Depth3DecayHard`, so this theorem would be counted as a **discharger of a
refuted row** and the gate would report a contradiction that does not exist. The binder form is
stripped and reads correctly. A gate's parser is part of its scope. -/
theorem depth3DecayExp_of_hard (h : Depth3DecayHard) : Depth3DecayExp := by
  intro A B hA hB
  obtain ⟨C, X₀, hX₀, hb⟩ := h A B hA hB
  exact ⟨C, X₀, hX₀, fun x hx h1 h2 => rung_weaken (hb x hx h1 h2)⟩

/-! ### Obligations ledger

Twenty propositions in this corpus have been introduced as *named obligations* — stated so that a
partial result can be committed without overstating it. (It was four when the section was written;
the count is `grep -c` over the table below, and the gate compares the table to the corpus, not to
this sentence.) Their status, as of the last edit:

| obligation | where | status | discharged by |
| --- | --- | --- | --- |
| `TowerLowerBound` | `EMLCertifiedSynthesis` | **open** | — (only `TowerLowerBoundUpTo 4`); `towerReducesToSign_iff_towerLowerBound` makes this row and `TowerReducesToSign` ONE obligation |
| `SignHardCase` | here | **discharged** | `signHardCase_holds` (`EMLAnalyticDischarge`), on `eml_tree_analytic_on_interval` + `analytic_finite_zeros_compact` + `rolle_ct` |
| `DecayFloor` | `EMLDecayFloor` | **reduced** | `decayFloor_of_emlGermApproach` → `EmlGermApproach` — an *equivalence*, not a shrink; a three-row cycle, one open obligation (clamped half: `decayFloor_clamped`) |
| `EmlGermApproach` | `EMLGermApproach` | **reduced** | `emlGermApproach_of_growthEnvelope` → `GrowthEnvelope` — closes the cycle; the missing input as an *approach* question between two germs, the idiom an external theorem would be cited in |
| `GrowthEnvelope` | `EMLDecayFloorIsGrowth` | **reduced** | `growthEnvelope_of_decayFloor` → `DecayFloor` — the other half of the same cycle |
| `VarLeftEmlRightHard` | here | **discharged** | `varLeftEmlRightHard_of_band`, for band targets |
| `Depth3DecayHard` | here | **refuted** | `not_depth3DecayHard` (witness `dep3CounterRight`) |
| `Depth3DecayExp` | here | **discharged** | `depth3DecayExp_holds` (the corrected rung, `C + exp x`) |
| `ExpExpGapBelow` | here | **discharged** | `expExpGapBelow_holds` |
| `BoundedCellApproach` | here | **discharged** | `boundedCellApproach_holds` |
| `BoundedEmlCellApproach` | here | **discharged** | `boundedEmlCellApproach_holds` |
| `BoundedEmlCellApproachLarge` | here | **discharged** | `boundedEmlCellApproachLarge_holds` (the router) |
| `TowerReducesToSign` | `EMLCertifiedSynthesis` | **open** | — equivalent to `TowerLowerBound` ever since `signHardCase_holds` discharged its antecedent (`towerReducesToSign_iff_towerLowerBound`, `EMLTowerAfterSign`) |
| `NegativeTranslationGrowingLeft` | `EMLDepthTameness` | **discharged** | `negativeTranslationGrowingLeft_holds` (`EMLNegTranslation`), through `PinnedRightChild`; non-vacuity shipped as `growingLeft_growth_hypothesis_satisfiable` |
| `PinnedRightChild` | `EMLNegTranslation` | **discharged** | `pinnedRightChild_holds` — the band pins `A₁` to `u ± 1` and the five depth-≤1 forms are exhausted; the two that reach `exp x` die on the `−x` term |
| `FQueryLowerBound` | `EMLBasisOverhead` | **discharged** | `fQueryLowerBound_holds` (`EMLRationalGerm`) |
| `OneQueryDichotomy` | `EMLOneQueryForm` | **open** | — (the level-1 cancellation theorem; `pev_dichotomy` is its level-0 analogue) |
| `BoundedGermTranscendence` | `EMLFTranscendence` | **open** | — (typed; both unbounded rates are theorems, constant `S` is a counterexample) |
| `LogQueryLowerBound` | `EMLRationalGerm` | **discharged** | `logQueryLowerBound_holds` (`EMLLogNotRational`) |
| `FQueryLowerBoundDivFree` | `EMLZeroQueryBarrier` | **discharged** | `fQueryLowerBoundDivFree_holds` |
| `RatGermTrichotomy` | `EMLRationalGerm` | **discharged** | `ratGermTrichotomy_holds` (`PevLeading`) |
| `OneQueryLevelSet` | `EMLOneQueryGlobal` | **open** | — (the level-1 analogue of `zero_query_level_set`; `q_F(sign) ≥ 2` reduces to it, NOT to `OneQueryDichotomy`) |

`SignHardCase` and `Depth3DecayExp` were the two **cancellation** statements — the sign of
`exp a − log b` and how small it can be. The second is now a theorem, so what is left of that pair is
the sign question alone.

**Three rows closed together on 2026-08-18**, and they closed as one because they were always one:
`BoundedCellApproach` and `BoundedEmlCellApproach` were *reductions*, carrying no content of their
own, so the router proving `BoundedEmlCellApproachLarge` discharged all three in a single step. Worth
noting what that says about the **reduced** status — it is honest bookkeeping, not progress. Two rows
sat green for weeks while the thing they reduced to was open, and the gate was right to keep them
distinct from **discharged**.

**A reduction CYCLE — 2026-08-26.** `DecayFloor` and `GrowthEnvelope` each reduce to the other:
`recipTree` carries a ceiling into a floor at `+2` depth and a floor into a ceiling at `+3`
(`EMLDecayFloorIsGrowth`), and `decayFloor_iff_growthEnvelope` states the equivalence outright. Both
rows are therefore legitimately **reduced**, and every per-row check passes on both — the cited
theorem concludes the proposition, it does assume the residue, and the residue is a tracked row.
**And nothing has been reduced.** The two are one obligation written twice.

So the gate now walks the residue graph and reports cycles (`reduction_cycles`), because two rows
leaving the open column together, for a result that closed neither, is exactly the bookkeeping the
**reduced** status was introduced to prevent — one level up, where no per-row check can see it. The
count is reported twice on purpose — the row count inflates the debt, the obligation count alone
hides that several rows carry it, and neither number is readable without the other. Canary 11 is the
specimen, and it is required to stay silent on a legitimate linear chain, or it would be saying only
that reductions are suspicious.

**A second route to the same thing, and it had been open for three commits — 2026-08-26.** A
reduction cycle is not the only way two rows can be one obligation. `TowerReducesToSign` is literally
`SignHardCase → TowerLowerBound`; `signHardCase_holds` discharged the antecedent, so
`towerReducesToSign_iff_towerLowerBound` (`EMLTowerAfterSign`) makes the two rows **equivalent**. That
module's own docstring says exactly this — *"two ledger rows that looked like separate debts are one
debt stated twice"* — and the ledger went on reporting two, through and including the entry that
built `reduction_cycles` to catch precisely this shape.

It was invisible because **two checks each declined to look at it, and both were right to**.
`dischargers_of` skips any conclusion containing `↔`, so that `foo : P ↔ Q` cannot read as a proof of
`P` (canary 9) — and `EMLTowerAfterSign` states the equivalence as an `Iff` *on purpose*, citing that
rule. `reduction_cycles` walks the residue edges of **reduced** rows, and two rows marked **open**
contribute no edge. So the theorem fed into nothing at all. The lesson generalises past this gate: a
rule that says what a theorem does **not** establish must also say what it **does**, or the theorem
leaves the checker's field of view entirely rather than merely leaving one column of it.

`proved_equivalences` now reads them and `open_units` groups the open rows into obligations across
both routes. The corrected count is **8 open rows, 6 distinct open obligations** — the debt was
overstated by one, not understated, which is why nothing failed. Canaries 12–14 are the specimens:
an equivalence between two open rows collapses them (and the same rows *without* the equivalence must
stay two, or the check is only saying that open rows are suspicious); an equivalence to a
**discharged** row marks the other side stale, which is the same blind spot in the direction that
*understates* the corpus; and a **conditional** `(h : X) : a ↔ b` collapses nothing until `X` is
discharged, but is reported rather than dropped, since a silent skip is the defect being removed.

**`Depth3DecayExp` closed the same day**, once the dispatch onto its four cells was written
(`depth3DecayExp_holds`). That the cells covered an arbitrary depth-≤2 `A` was an expectation until
the dispatch type-checked; it needed no new analysis, only `depth_le_one_exp_bounded_or_grows` to
split the grandchild and the two directions of the depth-≤1 log bound to feed the two halves.

Its refuted sibling `Depth3DecayHard` is the *stronger* statement (`C + x`), and
`depth3DecayExp_of_hard` proves Hard ⟹ Exp. So the pair is pinned: implication one way, antecedent
false, consequent true. The rung correction is **sharp** — one exponential, and the statement flips
truth value across that single step.

**A third status was needed on 2026-08-15.** `Depth3DecayHard` is not open, it is **false** — see its
docstring for the witness. "Refuted" is checked the same way as "open" (no theorem may conclude it)
but a hit is reported as a contradiction rather than staleness, because proving a statement we have
recorded as false is a worse failure than proving one we recorded as unproven.

The last row exists because of a correction. This paragraph previously ended "`TowerLowerBound`
reduces to the first", which reads as a proved implication and is not one: `SignHardCase` yields
eventual sign-definiteness, which fixes the *ray* for a decay bound but not its *rate*, and the rate
at depth ≤ 2 comes from the depth-≤1 classification by hand. Rather than soften the sentence into
something unfalsifiable, the implication is now the named Prop `TowerReducesToSign` and sits in this
table under the same gate as everything else. That is the third time a claim of ours cited a theorem
that did not exist, and the first time the claim was in the ledger written to catch them.

**How this table is kept honest.** "Discharged" is directly machine-checkable — there is a theorem
whose conclusion is the proposition. "Open" is not, in the sense that matters mathematically: the
absence of a proof is not itself a theorem, and no gate can certify that none exists. But the failure
mode we actually feared was narrower and *is* checkable — an obligation gets discharged and its row
is never updated, so the ledger reports open work that is finished.

`tools/check_obligations.sh` closes exactly that gap, in both directions. It parses these rows and,
for each, searches the corpus for theorems whose **conclusion** is the named proposition (binders of
the form `(h : P)` are stripped first, so a *consumer* of an obligation does not read as a
*discharger* — that distinction is not pedantic, it is the error a hand audit of this very table made
first time round). A row marked open with such a theorem is STALE; a row marked discharged whose
cited theorem does not conclude it is BROKEN. The gate carries two convict specimens and fails if
either stops firing.

So the residual hand-maintained content is only the claim that nobody has a proof *outside* this
corpus. Everything inside it is now gated. -/

end MachLib
