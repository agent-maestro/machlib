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
  grows linearly. `depth_le_one_exp_bounded_forms` names the two bounded forms.
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

/-- **`superlinear_subexp_not_depth_le_three` cannot be lifted to depth 4 — the statement is false
there.** `f x = x + 1` satisfies all three band hypotheses and is computed at depth exactly 4 by
`xPlusOneTree`.

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
      ∧ t.depth = 4
      ∧ ∀ x : Real, 0 < x → t.eval x = f x := by
  obtain ⟨t, hteval, htdepth⟩ := x_plus_one_in_eml
  refine ⟨fun x => x + 1, t, ?_, ?_, ?_, htdepth, fun x _ => hteval x⟩
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

/-- **`d(x²) ≥ 4`.** The depth-3 band applied to `x²`, which requires discharging all four of its
hypotheses for that target.

Recorded explicitly because the number has been quoted from the general theorem without ever being
instantiated. `x_sq_not_depth_le_two` gave only `≥ 3`. -/
theorem x_sq_not_depth_le_three (t : EMLTree) (ht : t.depth ≤ 3)
    (h : ∀ x : Real, 0 < x → t.eval x = x * x) : False := by
  refine superlinear_subexp_not_depth_le_three (fun x => x * x) ?_ ?_ ?_ ?_ t ht h
  · -- unbounded: `K < x ≤ x·x`
    intro K X
    have hKe : K < exp K := by
      have t1 := one_add_le_exp K
      have e : (1 : Real) + K = K + 1 := by mach_ring
      rw [e] at t1; exact lt_of_lt_of_le (lt_succ_self K) t1
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
    · have hx1 : (1 : Real) ≤ 1 + exp K + exp X := by
        have v : (1 : Real) + 0 + 0 ≤ 1 + exp K + exp X :=
          add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt (exp_pos K)))
            (le_of_lt (exp_pos X))
        have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
        rw [e] at v; exact v
      have hsq : (1 + exp K + exp X) ≤ (1 + exp K + exp X) * (1 + exp K + exp X) := by
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
  · -- sub-exponential: `exp_beats_powNat` at `k = 0`
    intro C X
    obtain ⟨x, hxX, hx1, hlt⟩ := exp_beats_powNat 0 C X
    refine ⟨x, hxX, hx1, ?_⟩
    have e : powNat x (0 + 2) = x * x := by
      show x * (x * 1) = x * x
      mach_ring
    rw [e] at hlt
    have v := add_lt_add_left hlt (-x - C)
    have e1 : -x - C + (x * x + x + C) = x * x := by mach_mpoly [x, C]
    have e2 : -x - C + exp x = exp x - x - C := by mach_mpoly [exp x, x, C]
    rw [e1, e2] at v; exact v
  · -- superlinear: `x < x·x` once `x > 1`
    intro X
    have hgt : (1 : Real) < 1 + 1 + exp X := by
      have v : (1 : Real) + 0 + 0 < 1 + 1 + exp X :=
        lt_of_lt_of_le (add_lt_add_left (exp_pos X) ((1 : Real) + 0))
          (add_le_add_wit (add_le_add_wit (le_refl 1) (le_of_lt zero_lt_one_ax))
            (le_refl (exp X)))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    refine ⟨1 + 1 + exp X, ?_, le_of_lt hgt, ?_⟩
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
    refine ⟨1 + 1 + exp C + exp X, ?_, ?_, ?_⟩
    · have v : (0 : Real) + 0 + 0 + exp X ≤ 1 + 1 + exp C + exp X :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (le_of_lt zero_lt_one_ax)
          (le_of_lt zero_lt_one_ax)) (le_of_lt hCp)) (le_refl _)
      have e : (0 : Real) + 0 + 0 + exp X = exp X := by mach_ring
      rw [e] at v; exact le_trans (self_le_exp X) v
    · have v : (1 : Real) + 0 + 0 + 0 ≤ 1 + 1 + exp C + exp X :=
        add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1)
          (le_of_lt zero_lt_one_ax)) (le_of_lt hCp)) (le_of_lt hXp)
      have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
      rw [e] at v; exact v
    · have hx1 : (1 : Real) ≤ 1 + 1 + exp C + exp X := by
        have v : (1 : Real) + 0 + 0 + 0 ≤ 1 + 1 + exp C + exp X :=
          add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl 1)
            (le_of_lt zero_lt_one_ax)) (le_of_lt hCp)) (le_of_lt hXp)
        have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
        rw [e] at v; exact v
      have hx0 : (0 : Real) < 1 + 1 + exp C + exp X := lt_of_lt_of_le zero_lt_one_ax hx1
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



end MachLib
