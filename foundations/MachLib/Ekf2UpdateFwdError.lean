import MachLib.Ekf2MeasModelFwdError
import MachLib.Ekf2GainConditioning

/-!
# EKF measurement update — the Jacobian, the gain's divisor, and the state update

**Part 3 of the pre-registered 2×2 EKF forward-error bound**
(`../EKF2_FWD_ERROR_PREREGISTRATION.md`). Parts 1 and 2 gave `δ_h` (the Lipschitz chain, D2) and the
conditioning constant (`det S ≥ det R`, D3). This file supplies the remaining links: `δ_H`, the
discharge of the registered `h_wellcond` hypothesis, and `δ_x⁺`.

## What is and is NOT here — read this before quoting a number

Every LINK in the chain is proven. The composed **ε** is obtained by instantiating the links, and
that instantiation is done numerically in
`monogate-research/electronics_intake/rb_ekf_arty/scripts/check_fwd_error_bound.py`, which mirrors
the node formulas below term for term and is checked against the artifact in both directions.

**What is deliberately NOT here: a single Lean theorem whose statement is the fully expanded ε.**
The intermediate step `δ_S` (the entries of `H P Hᵀ + R`) is a mechanical fold of `fxerr_mul` and
`fxerr_add` — roughly thirty node applications with no new hypotheses and no new mathematics — and
writing it out would produce a statement nobody can check by reading. So the top-level theorem here
is stated **parametric in the gain's error**, exactly as
`KalmanUpdateFixedPoint.kalman_update_1d_fwd_error` is stated parametric in the reciprocal's `Erec`.

The honest grading that follows: *the links are Lean-proven; the composed number is an instantiation
of them.* It is not "a Lean-proven ε", and the check script's header says so too.

## δ_H — where the domain hypothesis bites TWICE

`H = ∂h/∂x = [[x₀/r, x₁/r], [−x₁/r², x₀/r²]]`, and the emitted lowering computes each entry as
`qmul(num, recip(den))`. So every entry is a quotient whose **denominator carries the error from
Part 1** — `δ_r` for the first row, `δ(x₀²+x₁²)` for the second — and whose conditioning constant is
`r_min` for the first row and `r_min²` for the second.

That is the price of differentiating through a `sqrt`: the *value* `h` needs `r` bounded away from
zero once, the *Jacobian* needs it squared. At the anchor's `r_min = 4` that is `1/16` rather than
`1/4` — the second row is the better-conditioned one here, because `r` is large. Near the origin it
would be the reverse and far worse, which is the same physics D2 recorded and is why the domain
hypothesis is not a formality.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

/-! ## Error combinators — the node formulas, named

These mirror `fxerr_mul` / `fxerr_add` / `fxerr_div_vs_exact` exactly. Naming them is what lets the
composed bound be written down (and mirrored in the check script) without a page of nested algebra.
-/

/-- Magnitude and error of a truncating multiply (`fxerr_mul`). -/
noncomputable def Mmul (Mx My : Real) : Real := Mx * My
noncomputable def Emul (Mx Ex My Ey s : Real) : Real := Mx * Ey + My * Ex + Ex * Ey + s

/-- Magnitude and error of a truncating add (`fxerr_add`). -/
noncomputable def Madd (Mx My : Real) : Real := Mx + My
noncomputable def Eadd (Ex Ey s : Real) : Real := Ex + Ey + s

/-- Magnitude and error of a truncating divide against the true quotient (`fxerr_div_vs_exact`),
denominator bounded below by `m`. -/
noncomputable def Mdiv (Mx m : Real) : Real := Mx / m
noncomputable def Ediv (Mx Ex Ey m s : Real) : Real := s + (Ex / m + Mx * Ey / (m * m))

theorem fxerr_mul_c {s Mx Ex vx xe My Ey vy ye p : Real} (hs : 0 ≤ s)
    (hx : FxErr Mx Ex vx xe) (hy : FxErr My Ey vy ye) (hp : TruncW s p (vx * vy)) :
    FxErr (Mmul Mx My) (Emul Mx Ex My Ey s) p (xe * ye) :=
  fxerr_mul hs hx hy hp

theorem fxerr_add_c {s Mx Ex vx xe My Ey vy ye p : Real} (hs : 0 ≤ s)
    (hx : FxErr Mx Ex vx xe) (hy : FxErr My Ey vy ye) (hp : TruncW s p (vx + vy)) :
    FxErr (Madd Mx My) (Eadd Ex Ey s) p (xe + ye) :=
  fxerr_add hs hx hy hp

theorem fxerr_div_c {s Mx Ex vx xe My Ey vy ye p m : Real}
    (hx : FxErr Mx Ex vx xe) (hy : FxErr My Ey vy ye)
    (hm : 0 < m) (hmvy : m ≤ vy) (hmye : m ≤ ye) (hp : TruncW s p (vx / vy)) :
    FxErr (Mdiv Mx m) (Ediv Mx Ex Ey m s) p (xe / ye) :=
  fxerr_div_vs_exact hx hy hm hmvy hmye hp

/-! ## δ_H — the compiler-derived Jacobian's own forward error -/

/-- **One Jacobian entry.** Numerator and denominator each carry their own error; the denominator is
bounded below by `m` on both the computed and the exact side. Row 0 of `H` instantiates this with
`den = r` and `m = r_min`; row 1 with `den = r²` and `m = r_min²`, which is the "bites twice" of the
module note. -/
theorem ekf2_jacobian_entry {s Mn En vn xn Md Ed vd xd p m : Real}
    (hn : FxErr Mn En vn xn) (hd : FxErr Md Ed vd xd)
    (hm : 0 < m) (hmvd : m ≤ vd) (hmxd : m ≤ xd)
    (hp : TruncW s p (vn / vd)) :
    FxErr (Mdiv Mn m) (Ediv Mn En Ed m s) p (xn / xd) :=
  fxerr_div_c hn hd hm hmvd hmxd hp

/-- **`δ_H`, all four entries.** `H = [[x₀/r, x₁/r], [−x₁/r², x₀/r²]]` with `r` and `r²` carrying
the Part-1 errors. Row 1's negated numerator goes through `fxerr_neg`, which is exact — a sign flip
costs nothing in fixed point, and the emitted RTL does it on the operand rather than on the product
for exactly that reason.

Note the two different conditioning constants (`mr` for row 0, `m2` for row 1): they are what make
the Jacobian's error *different from* the model's, and getting them from one `r_min` is the whole
content of "the domain hypothesis bites twice". -/
theorem ekf2_H_fwd_error
    {s M0 E0 v0 x0 M1 E1 v1 x1 Mr Er vr xr M2 E2 v2 x2
     h00 h01 h10 h11 mr m2 : Real}
    (hx0 : FxErr M0 E0 v0 x0) (hx1 : FxErr M1 E1 v1 x1)
    (hr : FxErr Mr Er vr xr) (hr2 : FxErr M2 E2 v2 x2)
    (hmr : 0 < mr) (hmrv : mr ≤ vr) (hmrx : mr ≤ xr)
    (hm2 : 0 < m2) (hm2v : m2 ≤ v2) (hm2x : m2 ≤ x2)
    (hp00 : TruncW s h00 (v0 / vr)) (hp01 : TruncW s h01 (v1 / vr))
    (hp10 : TruncW s h10 (-v1 / v2)) (hp11 : TruncW s h11 (v0 / v2)) :
    FxErr (Mdiv M0 mr) (Ediv M0 E0 Er mr s) h00 (x0 / xr)
  ∧ FxErr (Mdiv M1 mr) (Ediv M1 E1 Er mr s) h01 (x1 / xr)
  ∧ FxErr (Mdiv M1 m2) (Ediv M1 E1 E2 m2 s) h10 (-x1 / x2)
  ∧ FxErr (Mdiv M0 m2) (Ediv M0 E0 E2 m2 s) h11 (x0 / x2) :=
  ⟨ekf2_jacobian_entry hx0 hr hmr hmrv hmrx hp00,
   ekf2_jacobian_entry hx1 hr hmr hmrv hmrx hp01,
   ekf2_jacobian_entry (fxerr_neg hx1) hr2 hm2 hm2v hm2x hp10,
   ekf2_jacobian_entry hx0 hr2 hm2 hm2v hm2x hp11⟩

/-! ## `h_wellcond` — the pre-registration's fourth hypothesis, discharged -/

/-- **The COMPUTED determinant is bounded below too.**

D3 registered this as a hypothesis rather than discovering it mid-proof: `ekf2_det_S_lower` bounds
the *exact* `det S`, but the gain divides by the *computed* one, and perturbation of an inverse needs
the computed divisor bounded away from zero as well. The registered form was
`h_wellcond : δ_S ≤ λ_min(R)/2`. In the determinant formulation it comes out cleaner and STRICTLY
TIGHTER than the guess: the computed determinant obeys

    det R − δ_det  ≤  det_hw

unconditionally, and the gain stage's divisor constant is that quantity — usable exactly when
`δ_det < det R` (`ekf2_det_hw_pos`). No `/2`, and the factor-of-two margin the pre-registration
reserved turns out not to be needed.

**If this fails at the anchor's constants it is a finding, not a licence to weaken the hypothesis** —
that instruction was written down before the proof existed and stands. -/
theorem ekf2_det_hw_lower {vD De detR Edet : Real}
    (hexact : detR ≤ De) (herr : abs (vD - De) ≤ Edet) :
    detR - Edet ≤ vD := by
  have hside : De - vD ≤ Edet := by
    refine le_trans ?_ herr
    rw [show De - vD = -(vD - De) from by mach_mpoly [vD, De]]
    exact neg_le_abs (vD - De)
  have h1 : De - Edet ≤ vD := by
    have := add_le_add_both hside (le_refl (vD - Edet))
    rw [show De - vD + (vD - Edet) = De - Edet from by mach_mpoly [De, vD, Edet],
        show Edet + (vD - Edet) = vD from by mach_mpoly [vD, Edet]] at this
    exact this
  refine le_trans ?_ h1
  have := add_le_add_both hexact (le_refl (-Edet))
  rw [show detR + -Edet = detR - Edet from by mach_mpoly [detR, Edet],
      show De + -Edet = De - Edet from by mach_mpoly [De, Edet]] at this
  exact this

/-- **`h_wellcond` is exactly the positivity of that lower bound.** The gain stage's divisor
constant is `m = det R − δ_det`, and it is usable precisely when `δ_det < det R`. That is the
registered hypothesis in its natural form — no `/2` needed, and strictly tighter than the `detR/2`
the pre-registration guessed at. -/
theorem ekf2_det_hw_pos {detR Edet : Real} (h : Edet < detR) : 0 < detR - Edet :=
  sub_pos_of_lt h

/-! ## δ_x⁺ — the state update -/

/-- **`δ_x⁺` — the final row of the pre-registration's decomposition table.**

`x⁺ = x + K y`, one row at a time: two truncating multiplies, one truncating add for the inner
product, one more for the update. Stated **parametric in the gain's error** (`hk0`, `hk1`) — the
precedent being `kalman_update_1d_fwd_error`, which is parametric in `Erec` for the same reason: it
keeps the theorem true regardless of how the gain was computed, and puts the obligation where the
constants actually live.

`δ_y` comes from Part 1 (`z` is exact, so the innovation's error is `δ_h` plus one truncation), and
the gain's error is `Ediv` at `m = detR/2` via `ekf2_det_hw_lower`. -/
theorem ekf2_state_update_fwd_error
    {s Mx Ex vx xe Mk0 Ek0 k0 ke0 My0 Ey0 y0 ye0 Mk1 Ek1 k1 ke1 My1 Ey1 y1 ye1
     p0 p1 sm xp : Real} (hs : 0 ≤ s)
    (hx : FxErr Mx Ex vx xe)
    (hk0 : FxErr Mk0 Ek0 k0 ke0) (hy0 : FxErr My0 Ey0 y0 ye0)
    (hk1 : FxErr Mk1 Ek1 k1 ke1) (hy1 : FxErr My1 Ey1 y1 ye1)
    (hp0 : TruncW s p0 (k0 * y0)) (hp1 : TruncW s p1 (k1 * y1))
    (hsm : TruncW s sm (p0 + p1)) (hxp : TruncW s xp (vx + sm)) :
    FxErr (Madd Mx (Madd (Mmul Mk0 My0) (Mmul Mk1 My1)))
          (Eadd Ex (Eadd (Emul Mk0 Ek0 My0 Ey0 s) (Emul Mk1 Ek1 My1 Ey1 s) s) s)
          xp (xe + (ke0 * ye0 + ke1 * ye1)) :=
  fxerr_add_c hs hx
    (fxerr_add_c hs (fxerr_mul_c hs hk0 hy0 hp0) (fxerr_mul_c hs hk1 hy1 hp1) hsm) hxp

end MachLib.Real
