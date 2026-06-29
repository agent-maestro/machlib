import MachLib.FixedPoint
import MachLib.OperatorClamp3

/-!
# The fixed-point forward-error certifier — Hardware Leg A (general fold)

Forge's Verilog/RTL backend emits a **fixed-point** datapath: each operation truncates the
result back onto the `Q`-format grid, so the rounding error is **additive** — bounded by a
constant step `s = 2⁻ᶠ`, not a relative `(1+w)` factor (that is the float model,
`OperatorBasisComplete`). `FixedPoint.lean` proved the PID kernel's fixed-point forward error
by hand; this file *generalises* it: one structural induction (`fx_sound`) that bounds the
forward error of **any** kernel over the fixed-point arithmetic+clamp basis `{leaf, neg, +,
×, clamp}`. That is the EML→RTL equivalence backbone — a board-free formal forward-error
guarantee for the fixed-point lane, the same way `gexpr_sound` is for the float lane.

The certificate is `FxErr M E v ve`: magnitude `|ve| ≤ M` and **absolute** error
`|v − ve| ≤ E`. Each truncating op (`TruncW s`, the additive analogue of `RoundsW`) adds `s`;
multiply also adds the bilinear propagation. `sorryAx`-free; no new axioms.
-/

namespace MachLib.Real

/-- Additive (fixed-point) forward-error certificate: `|ve| ≤ M ∧ |v − ve| ≤ E`. -/
def FxErr (M E v ve : Real) : Prop := abs ve ≤ M ∧ abs (v - ve) ≤ E

theorem FxErr.mag {M E v ve : Real} (h : FxErr M E v ve) : abs ve ≤ M := h.1
theorem FxErr.err {M E v ve : Real} (h : FxErr M E v ve) : abs (v - ve) ≤ E := h.2
/-- `|v| ≤ M + E` (computed magnitude). -/
theorem FxErr.val_bound {M E v ve : Real} (h : FxErr M E v ve) : abs v ≤ M + E := by
  have key : abs v ≤ abs ve + abs (v - ve) := by
    have e : ve + (v - ve) = v := by mach_mpoly [v, ve]
    calc abs v = abs (ve + (v - ve)) := by rw [e]
      _ ≤ abs ve + abs (v - ve) := abs_add ve (v - ve)
  exact le_trans key (add_le_add_both h.1 h.2)

/-- One truncating fixed-point op: `|p − ve| ≤ s` (step `s = 2⁻ᶠ`). The additive analogue
of the float model's `RoundsW`. -/
def TruncW (s p ve : Real) : Prop := abs (p - ve) ≤ s

/-! ## the per-operator additive rules -/

theorem fxerr_leaf (ve : Real) : FxErr (abs ve) 0 ve ve :=
  ⟨le_refl _, le_of_eq (by rw [show ve - ve = (0 : Real) from by mach_mpoly [ve]]; exact abs_zero)⟩

/-- An exact input that has been truncated onto the grid (`|p − ve| ≤ s`). -/
theorem fxerr_round {s p ve : Real} (hp : TruncW s p ve) : FxErr (abs ve) s p ve :=
  ⟨le_refl _, hp⟩

theorem fxerr_neg {M E v ve : Real} (h : FxErr M E v ve) : FxErr M E (-v) (-ve) :=
  ⟨by rw [abs_neg]; exact h.1,
   by rw [show -v - -ve = -(v - ve) from by mach_mpoly [v, ve], abs_neg]; exact h.2⟩

/-- **Truncating add.** `fxadd a b` (within `s` of `a+b`) propagates the operand errors and
adds one step: `E = Ex + Ey + s`, magnitude `Mx + My`. -/
theorem fxerr_add {s Mx Ex vx xe My Ey vy ye p : Real} (hs : 0 ≤ s)
    (hx : FxErr Mx Ex vx xe) (hy : FxErr My Ey vy ye) (hp : TruncW s p (vx + vy)) :
    FxErr (Mx + My) (Ex + Ey + s) p (xe + ye) := by
  refine ⟨le_trans (abs_add xe ye) (add_le_add_both hx.1 hy.1), ?_⟩
  have hprop : abs ((vx + vy) - (xe + ye)) ≤ Ex + Ey := by
    rw [show (vx + vy) - (xe + ye) = (vx - xe) + (vy - ye) from by mach_mpoly [vx, vy, xe, ye]]
    exact le_trans (abs_add (vx - xe) (vy - ye)) (add_le_add_both hx.2 hy.2)
  rw [show p - (xe + ye) = (p - (vx + vy)) + ((vx + vy) - (xe + ye))
        from by mach_mpoly [p, vx, vy, xe, ye]]
  exact le_trans (abs_add _ _)
    (le_trans (add_le_add_both hp hprop) (le_of_eq (by mach_mpoly [s, Ex, Ey])))

/-- **Truncating multiply.** `fxmul a b` (within `s` of `a·b`) carries the bilinear
propagation plus one step: `E = Mx·Ey + My·Ex + Ex·Ey + s`, magnitude `Mx·My`. -/
theorem fxerr_mul {s Mx Ex vx xe My Ey vy ye p : Real} (hs : 0 ≤ s)
    (hx : FxErr Mx Ex vx xe) (hy : FxErr My Ey vy ye) (hp : TruncW s p (vx * vy)) :
    FxErr (Mx * My) (Mx * Ey + My * Ex + Ex * Ey + s) p (xe * ye) := by
  have hMx0 : 0 ≤ Mx := le_trans (abs_nonneg xe) hx.1
  have hMyEy0 : 0 ≤ My + Ey := le_trans (abs_nonneg vy) hy.val_bound
  refine ⟨?_, ?_⟩
  · rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hx.1 (abs_nonneg ye))
                   (mul_le_mul_of_nonneg_left hy.1 hMx0)
  · -- |vx·vy − xe·ye| ≤ Ex·(My+Ey) + Mx·Ey  (= Mx·Ey + My·Ex + Ex·Ey)
    have hprop : abs (vx * vy - xe * ye) ≤ Ex * (My + Ey) + Mx * Ey := by
      rw [show vx * vy - xe * ye = (vx - xe) * vy + xe * (vy - ye)
            from by mach_mpoly [vx, vy, xe, ye]]
      refine le_trans (abs_add _ _) (add_le_add_both ?_ ?_)
      · rw [abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hx.2 (abs_nonneg vy))
                       (mul_le_mul_of_nonneg_left hy.val_bound (le_trans (abs_nonneg _) hx.2))
      · rw [abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hx.1 (abs_nonneg (vy - ye)))
                       (mul_le_mul_of_nonneg_left hy.2 hMx0)
    rw [show p - xe * ye = (p - vx * vy) + (vx * vy - xe * ye)
          from by mach_mpoly [p, vx, vy, xe, ye]]
    exact le_trans (abs_add _ _)
      (le_trans (add_le_add_both hp hprop) (le_of_eq (by mach_mpoly [s, Ex, Ey, Mx, My])))

/-- **Clamp** (saturating, exact): error preserved, magnitude bounded by the range. -/
theorem fxerr_clamp {M E v ve lo hi : Real} (hlohi : lo ≤ hi) (h : FxErr M E v ve) :
    FxErr (max (abs lo) (abs hi)) E (clamp v lo hi) (clamp ve lo hi) := by
  refine ⟨?_, le_trans (clamp_lipschitz v ve lo hi) h.2⟩
  apply abs_le_of
  · exact le_trans (clamp_le_hi ve lo hi) (le_trans (le_abs_self hi) (le_max_right _ _))
  · exact le_trans (neg_le_neg (lo_le_clamp ve lo hi hlohi))
      (le_trans (neg_le_abs lo) (le_max_left _ _))

/-- **Joint-Lipschitz clamp** (computed/rounded edges). When a fixed-point clamp's `lo`/`hi`
are *truncated* values (e.g. `alpha·x` on the grid — the parametric ReLU) they carry their own
error; `clamp` is jointly 1-Lipschitz (it adds no truncation, `min`/`max` select an existing
grid value), so the additive errors sum: `E = Ev + Elo + Ehi`, magnitude `max Mlo Mhi`. The
fixed-point analogue of `aerr_clamp3`; reuses the same `clamp_lipschitz3`/`clamp_abs_le`. -/
theorem fxerr_clamp3 {Mv Ev v ve Mlo Elo lo loe Mhi Ehi hi hie : Real}
    (hv : FxErr Mv Ev v ve) (hlo : FxErr Mlo Elo lo loe) (hhi : FxErr Mhi Ehi hi hie) :
    FxErr (max Mlo Mhi) (Ev + Elo + Ehi) (clamp v lo hi) (clamp ve loe hie) := by
  refine ⟨?_, ?_⟩
  · refine le_trans (clamp_abs_le ve loe hie) ?_
    exact max_le (le_trans hlo.1 (le_max_left Mlo Mhi))
                 (le_trans hhi.1 (le_max_right Mlo Mhi))
  · refine le_trans (clamp_lipschitz3 v lo hi ve loe hie) ?_
    exact add_le_add_both (add_le_add_both hv.2 hlo.2) hhi.2

/-! ## the fold over a fixed-point arithmetic+clamp expression -/

inductive FxExpr where
  | leaf  (ve : Real)
  | rleaf (ve : Real)            -- an input truncated onto the grid (one step)
  | neg   (a : FxExpr)
  | add   (a b : FxExpr)
  | mul   (a b : FxExpr)
  | clampO (a : FxExpr) (lo hi : Real)
  | clampO3 (a lo hi : FxExpr)          -- clamp with COMPUTED (rounded) edges — joint additive error

noncomputable def FxExpr.exact : FxExpr → Real
  | .leaf ve     => ve
  | .rleaf ve    => ve
  | .neg a       => -(FxExpr.exact a)
  | .add a b     => FxExpr.exact a + FxExpr.exact b
  | .mul a b     => FxExpr.exact a * FxExpr.exact b
  | .clampO a lo hi => clamp (FxExpr.exact a) lo hi
  | .clampO3 a lo hi => clamp (FxExpr.exact a) (FxExpr.exact lo) (FxExpr.exact hi)
  termination_by structural t => t

noncomputable def FxExpr.Mbound : FxExpr → Real
  | .leaf ve     => abs ve
  | .rleaf ve    => abs ve
  | .neg a       => FxExpr.Mbound a
  | .add a b     => FxExpr.Mbound a + FxExpr.Mbound b
  | .mul a b     => FxExpr.Mbound a * FxExpr.Mbound b
  | .clampO _ lo hi => max (abs lo) (abs hi)
  | .clampO3 _ lo hi => max (FxExpr.Mbound lo) (FxExpr.Mbound hi)
  termination_by structural t => t

/-- Additive forward-error bound, parametric in the fixed-point step `s`. -/
noncomputable def FxExpr.Ebound (s : Real) : FxExpr → Real
  | .leaf _      => 0
  | .rleaf _     => s
  | .neg a       => FxExpr.Ebound s a
  | .add a b     => FxExpr.Ebound s a + FxExpr.Ebound s b + s
  | .mul a b     => FxExpr.Mbound a * FxExpr.Ebound s b + FxExpr.Mbound b * FxExpr.Ebound s a
                    + FxExpr.Ebound s a * FxExpr.Ebound s b + s
  | .clampO a _ _ => FxExpr.Ebound s a
  | .clampO3 a lo hi => FxExpr.Ebound s a + FxExpr.Ebound s lo + FxExpr.Ebound s hi
  termination_by structural t => t

def FxExpr.Valid : FxExpr → Prop
  | .leaf _      => True
  | .rleaf _     => True
  | .neg a       => FxExpr.Valid a
  | .add a b     => FxExpr.Valid a ∧ FxExpr.Valid b
  | .mul a b     => FxExpr.Valid a ∧ FxExpr.Valid b
  | .clampO a lo hi => FxExpr.Valid a ∧ lo ≤ hi
  | .clampO3 a lo hi => FxExpr.Valid a ∧ FxExpr.Valid lo ∧ FxExpr.Valid hi
  termination_by structural t => t

/-- A per-node-truncated fixed-point evaluation: each `+`/`×` truncates (`TruncW s`); the
saturating `clamp` is exact (min/max on the grid). -/
inductive FxRoundedEval (s : Real) : FxExpr → Real → Prop where
  | leaf  (ve : Real) : FxRoundedEval s (.leaf ve) ve
  | rleaf {ve p : Real} (hp : TruncW s p ve) : FxRoundedEval s (.rleaf ve) p
  | neg   {a : FxExpr} {va : Real} (ha : FxRoundedEval s a va) : FxRoundedEval s (.neg a) (-va)
  | add   {a b : FxExpr} {va vb p : Real} (ha : FxRoundedEval s a va) (hb : FxRoundedEval s b vb)
      (hp : TruncW s p (va + vb)) : FxRoundedEval s (.add a b) p
  | mul   {a b : FxExpr} {va vb p : Real} (ha : FxRoundedEval s a va) (hb : FxRoundedEval s b vb)
      (hp : TruncW s p (va * vb)) : FxRoundedEval s (.mul a b) p
  | clampO {a : FxExpr} {va lo hi : Real} (ha : FxRoundedEval s a va) :
      FxRoundedEval s (.clampO a lo hi) (clamp va lo hi)
  | clampO3 {a lo hi : FxExpr} {va vlo vhi : Real} (ha : FxRoundedEval s a va)
      (hlo : FxRoundedEval s lo vlo) (hhi : FxRoundedEval s hi vhi) :
      FxRoundedEval s (.clampO3 a lo hi) (clamp va vlo vhi)

/-- **The fixed-point certifier.** Any per-node-truncated evaluation of a `Valid` kernel over
the fixed-point arithmetic+clamp basis carries the additive forward-error certificate — one
structural induction folding the per-op rules. The fixed-point counterpart of `gexpr_sound`,
generalising the hand-proved PID bound to any such kernel. -/
theorem fx_sound {s : Real} (hs : 0 ≤ s) {t : FxExpr} {v : Real} (h : FxRoundedEval s t v) :
    t.Valid → FxErr t.Mbound (t.Ebound s) v t.exact := by
  induction h with
  | leaf ve            => exact fun _ => fxerr_leaf ve
  | rleaf hp           => exact fun _ => fxerr_round hp
  | neg _ iha          => exact fun hv => fxerr_neg (iha hv)
  | add _ _ hp iha ihb => exact fun hv => fxerr_add hs (iha hv.1) (ihb hv.2) hp
  | mul _ _ hp iha ihb => exact fun hv => fxerr_mul hs (iha hv.1) (ihb hv.2) hp
  | clampO _ iha       => exact fun hv => fxerr_clamp hv.2 (iha hv.1)
  | clampO3 _ _ _ iha ihlo ihhi =>
      exact fun hv => fxerr_clamp3 (iha hv.1) (ihlo hv.2.1) (ihhi hv.2.2)

/-- The forward-error corollary: `|v − exact| ≤ Ebound s`, any `Valid` fixed-point kernel. -/
theorem fx_fwd_error {s : Real} (hs : 0 ≤ s) {t : FxExpr} {v : Real}
    (h : FxRoundedEval s t v) (hv : t.Valid) : abs (v - t.exact) ≤ t.Ebound s :=
  (fx_sound hs h hv).err

/-- **A fixed-point multiply-accumulate-clamp kernel** — the shape of the PID datapath and
most control/DSP fixed-point math: `clamp(fxmul(c̃, x) + b, lo, hi)` with a quantized gain
`c̃` (`rleaf`, one step off the exact `c`), a truncating multiply and add, then saturation.
`fx_fwd_error` gives its forward error from the general fold — no per-kernel proof. The
hand-tuned `pid_fx_fwd_error` is tighter (it exploits exact accumulator adds); this is the
*general* bound for any such kernel. -/
theorem fx_mac_clamp_certified {s c vc x b p acc lo hi : Real} (hs : 0 ≤ s) (hlohi : lo ≤ hi)
    (hc : TruncW s vc c) (hp : TruncW s p (vc * x)) (hacc : TruncW s acc (p + b)) :
    abs (clamp acc lo hi
         - (FxExpr.clampO (.add (.mul (.rleaf c) (.leaf x)) (.leaf b)) lo hi).exact)
      ≤ (FxExpr.clampO (.add (.mul (.rleaf c) (.leaf x)) (.leaf b)) lo hi).Ebound s :=
  fx_fwd_error hs
    (FxRoundedEval.clampO (FxRoundedEval.add
      (FxRoundedEval.mul (FxRoundedEval.rleaf hc) (FxRoundedEval.leaf x) hp)
      (FxRoundedEval.leaf b) hacc))
    ⟨⟨⟨trivial, trivial⟩, trivial⟩, hlohi⟩

end MachLib.Real
