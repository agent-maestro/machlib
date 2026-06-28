import MachLib.ForwardError

/-!
# Operator-basis soundness — the auto-certifier as one proven meta-theorem

The operator-basis research showed every nonneg-accumulation kernel's forward
error is a derived attribute of its expression tree (rounding-depth `d` ⇒
`((1+u)^d − 1)·exact`), and the certifier *emits a Lean proof per kernel* by
folding the per-operator `Renc` rules. The gap (flagged honestly in the
synthesis): that fold's correctness was a **validated heuristic**, not a theorem.

This file closes the gap for the `{+, ×}` arithmetic core. It reflects the
expression tree as a Lean inductive `OpTree`, defines its exact value, its
rounding-`depth`, and a relation `RoundedEval` capturing *any* per-node-rounded
evaluation, and proves — once, by structural induction folding
`renc_leaf`/`renc_round`/`renc_mul`/`renc_add` — that every such evaluation
encloses the exact value at `depth`, hence has forward error `≤ ((1+w)^depth −
1)·exact`. **One theorem, every nonneg `{+,×}` kernel** — the certifier's
soundness, proven rather than trusted.

`length_sq2_fwd_compose` (FPModel's shape) drops out as a one-line instance.
`sorryAx`-free; transcendental/division operators are the named next classes.
-/

namespace MachLib.Real

/-! ## `npow` is monotone in the EXPONENT — needed to align Renc exponents at a sum -/

/-- Base in `[0,1]`: higher exponent ⇒ smaller. -/
theorem npow_exp_anti {b : Real} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ {m n : Nat}, m ≤ n → npow n b ≤ npow m b
  | m, 0, h => by have : m = 0 := Nat.le_zero.mp h; subst this; exact le_refl _
  | m, n + 1, h => by
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        have step : npow (n + 1) b ≤ npow n b := by
          rw [npow_succ]
          exact le_trans (mul_le_mul_of_nonneg_right hb1 (npow_nonneg hb0 n))
                         (le_of_eq (one_mul_thm (npow n b)))
        exact le_trans step (npow_exp_anti hb0 hb1 hmn)
      · have : m = n + 1 := Nat.le_antisymm h hge; subst this; exact le_refl _

/-- Base `≥ 1`: higher exponent ⇒ larger. -/
theorem npow_exp_mono {b : Real} (hb1 : 1 ≤ b) :
    ∀ {m n : Nat}, m ≤ n → npow m b ≤ npow n b
  | m, 0, h => by have : m = 0 := Nat.le_zero.mp h; subst this; exact le_refl _
  | m, n + 1, h => by
      have hb0 : 0 ≤ b := le_trans (le_of_lt one_pos) hb1
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        have step : npow n b ≤ npow (n + 1) b := by
          rw [npow_succ]
          exact le_trans (le_of_eq (one_mul_thm (npow n b)).symm)
                         (mul_le_mul_of_nonneg_right hb1 (npow_nonneg hb0 n))
        exact le_trans (npow_exp_mono hb1 hmn) step
      · have : m = n + 1 := Nat.le_antisymm h hge; subst this; exact le_refl _

/-- **Lift** a relative enclosure to a larger exponent (a wider, still-valid box). -/
theorem renc_lift {w v ve : Real} {a a' : Nat}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hve : 0 ≤ ve) (haa : a ≤ a')
    (h : Renc a w v ve) : Renc a' w v ve := by
  obtain ⟨hl, hu⟩ := h
  have h1w_nn  : 0 ≤ 1 - w := sub_nonneg_of_le hw1
  have h1w_le1 : 1 - w ≤ 1 := by
    rw [sub_def]; have h2 := add_le_add_left (neg_nonpos_of_nonneg hw0) 1; rwa [add_zero] at h2
  have h1w'_ge : (1 : Real) ≤ 1 + w := le_add_of_nonneg_right hw0
  have hlo : npow a' (1 - w) ≤ npow a (1 - w) := npow_exp_anti h1w_nn h1w_le1 haa
  have hup : npow a (1 + w) ≤ npow a' (1 + w) := npow_exp_mono h1w'_ge haa
  exact ⟨le_trans (mul_le_mul_of_nonneg_right hlo hve) hl,
         le_trans hu (mul_le_mul_of_nonneg_right hup hve)⟩

/-- **Sum at differing exponents.** Lift both to `max a b`, then `renc_add`. -/
theorem renc_add_max {w x y p xe ye : Real} {a b : Nat}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hxe : 0 ≤ xe) (hye : 0 ≤ ye)
    (hx : Renc a w x xe) (hy : Renc b w y ye) (hp : RoundsW w p (x + y)) :
    Renc (Nat.max a b + 1) w p (xe + ye) :=
  renc_add hw0 hw1 hxe hye
    (renc_lift hw0 hw1 hxe (Nat.le_max_left a b) hx)
    (renc_lift hw0 hw1 hye (Nat.le_max_right a b) hy) hp

/-! ## The expression tree over the `{+, ×}` basis -/

/-- A nonneg-accumulation kernel: nonneg leaves (exact inputs or rounded nonneg
terms like `x²`) combined by `+` and `×`. -/
inductive OpTree where
  | leaf  (ve : Real)            -- an exact nonneg input
  | rleaf (ve : Real)            -- a rounded nonneg term (one rounding, e.g. `x²`)
  | add   (a b : OpTree)
  | mul   (a b : OpTree)

/-- The exact value of the tree. -/
noncomputable def OpTree.exact : OpTree → Real
  | .leaf ve  => ve
  | .rleaf ve => ve
  | .add a b  => OpTree.exact a + OpTree.exact b
  | .mul a b  => OpTree.exact a * OpTree.exact b
  termination_by structural t => t

/-- The rounding-depth: the `Renc` exponent. Products compound (add); nonneg sums
do not (max+1); a rounded leaf is depth 1, an exact leaf depth 0. -/
def OpTree.depth : OpTree → Nat
  | .leaf _   => 0
  | .rleaf _  => 1
  | .add a b  => Nat.max (OpTree.depth a) (OpTree.depth b) + 1
  | .mul a b  => OpTree.depth a + OpTree.depth b + 1
  termination_by structural t => t

/-- Every leaf value is nonneg (so every subexpression is). -/
def OpTree.Nonneg : OpTree → Prop
  | .leaf ve  => 0 ≤ ve
  | .rleaf ve => 0 ≤ ve
  | .add a b  => OpTree.Nonneg a ∧ OpTree.Nonneg b
  | .mul a b  => OpTree.Nonneg a ∧ OpTree.Nonneg b
  termination_by structural t => t

theorem OpTree.exact_nonneg : ∀ {t : OpTree}, t.Nonneg → 0 ≤ t.exact
  | .leaf _,  h => h
  | .rleaf _, h => h
  | .add a b, h => add_nonneg_ea (OpTree.exact_nonneg h.1) (OpTree.exact_nonneg h.2)
  | .mul a b, h => mul_nonneg (OpTree.exact_nonneg h.1) (OpTree.exact_nonneg h.2)
  termination_by structural t => t

/-- **Any per-node-rounded evaluation** of the tree at unit-roundoff `w`: leaves
are exact, rounded leaves and every internal `+`/`×` apply one `RoundsW w`. This
captures every concrete floating-point evaluation order the certifier would emit. -/
inductive RoundedEval (w : Real) : OpTree → Real → Prop where
  | leaf  (ve : Real) : RoundedEval w (.leaf ve) ve
  | rleaf {ve p : Real} (hp : RoundsW w p ve) : RoundedEval w (.rleaf ve) p
  | add   {a b : OpTree} {va vb p : Real}
      (ha : RoundedEval w a va) (hb : RoundedEval w b vb)
      (hp : RoundsW w p (va + vb)) : RoundedEval w (.add a b) p
  | mul   {a b : OpTree} {va vb p : Real}
      (ha : RoundedEval w a va) (hb : RoundedEval w b vb)
      (hp : RoundsW w p (va * vb)) : RoundedEval w (.mul a b) p

/-! ## The soundness meta-theorem -/

/-- **One theorem for every nonneg `{+,×}` kernel.** Any per-node-rounded
evaluation `v` of a nonneg tree `t` is a relative enclosure of `t.exact` at
exponent `t.depth`. Folds the per-operator `Renc` rules by structural induction. -/
theorem renc_sound {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : OpTree} {v : Real} (h : RoundedEval w t v) :
    t.Nonneg → Renc t.depth w v t.exact := by
  induction h with
  | leaf ve => exact fun hnn => renc_leaf hnn
  | rleaf hp => exact fun hnn => renc_round hw0 hw1 hnn hp
  | add _ _ hp iha ihb =>
      exact fun hnn => renc_add_max hw0 hw1 (OpTree.exact_nonneg hnn.1)
              (OpTree.exact_nonneg hnn.2) (iha hnn.1) (ihb hnn.2) hp
  | mul _ _ hp iha ihb =>
      exact fun hnn => renc_mul hw0 hw1 (OpTree.exact_nonneg hnn.1)
              (OpTree.exact_nonneg hnn.2) (iha hnn.1) (ihb hnn.2) hp

/-- **The forward-error meta-theorem.** Every nonneg `{+,×}` kernel's rounded
value has forward error `≤ ((1+w)^depth − 1)·exact` — the certifier's claim, now a
theorem (one fold, every kernel) rather than a per-kernel emitted proof. -/
theorem opTree_fwd_error {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {t : OpTree} {v : Real} (hev : RoundedEval w t v) (hnn : t.Nonneg) :
    abs (v - t.exact) ≤ (npow t.depth (1 + w) - 1) * t.exact :=
  renc_fwd hw0 hw1 (OpTree.exact_nonneg hnn) (renc_sound hw0 hw1 hev hnn)

/-- `length_sq2` (FPModel's shape) as a one-line INSTANCE of the meta-theorem:
`x² + y²` is `add (rleaf …) (rleaf …)`, depth `max 1 1 + 1 = 2`, recovering
`|s − (x²+y²)| ≤ ((1+w)² − 1)·(x²+y²)`. -/
theorem length_sq2_via_meta {w x y px py s : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpx : RoundsW w px (x * x)) (hpy : RoundsW w py (y * y))
    (hs : RoundsW w s (px + py)) :
    abs (s - (x * x + y * y)) ≤ (npow 2 (1 + w) - 1) * (x * x + y * y) :=
  opTree_fwd_error hw0 hw1
    (RoundedEval.add (RoundedEval.rleaf hpx) (RoundedEval.rleaf hpy) hs)
    ⟨mul_self_nonneg x, mul_self_nonneg y⟩

end MachLib.Real
