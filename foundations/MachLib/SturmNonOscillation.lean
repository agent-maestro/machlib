/-
MachLib.SturmNonOscillation — a machine-checked non-oscillation certificate
for `y'' = r·y` with `r ≥ 0`.

This is the Lean half of the "won't-oscillate / bounded-zeros" certificate for
the verified-kernels product. The differential-Galois ↔ EML correspondence
(monogate-research `differential_galois_eml_depth_2026_06_24`) says a function
defined by `y'' = r·y` is EML-finite (no Infinite-Zeros Barrier) when it does not
oscillate, and `eml_cost.classify_ode` returns `EML-finite` exactly when `r ≥ 0`
(Sturm). THIS FILE PROVES the underlying analytic fact, so that verdict is backed
by a theorem, not a heuristic.

The fundamental unit of oscillation is a "positive arch": two consecutive zeros
`y(a)=y(b)=0` with `y > 0` strictly between. We prove `r ≥ 0` makes that
impossible. Hence a nontrivial solution of `y'' = r·y` with `r ≥ 0` cannot
oscillate — it has no arch, so its zeros cannot accumulate / repeat the
sign-change pattern.

Proof shape (Rolle + MVT, no IVT / first-zero machinery needed):
  1. `mono_of_deriv_nonneg`: a function with a non-negative derivative on `(a,b)`
     is non-decreasing (`f a ≤ f b`) — from the Mean Value Theorem.
  2. On the arch, `y'' = r·y ≥ 0` (r≥0, y>0), so `y'` is non-decreasing.
  3. Rolle on `y` over `[a,b]` gives an interior `m` with `y'(m) = 0`.
  4. `y'` non-decreasing + `y'(m)=0` ⇒ `y' ≥ 0` on `(m,b)` ⇒ `y` non-decreasing
     on `[m,b]` ⇒ `y(b) ≥ y(m) > 0`, contradicting `y(b) = 0`.

Derivatives are encoded with `MachLib.Differentiation.HasDerivAt`; `yp`, `ypp`
are the first/second derivative functions, `hode : ypp c = r c * y c` is the ODE.
-/

import MachLib.Differentiation
import MachLib.Rolle
import MachLib.Linarith

namespace MachLib

open Real

/-- A function whose derivative `df` is non-negative on `(a,b)` is non-decreasing
across the interval: `f a ≤ f b`. PROVED from the Mean Value Theorem (the
witnessed `f'` equals `df c` by `HasDerivAt_unique`, and `f'·(b−a) ≥ 0`). -/
theorem mono_of_deriv_nonneg (f df : Real → Real) {a b : Real} (hab : a < b)
    (hderiv : ∀ c, a < c → c < b → HasDerivAt f (df c) c)
    (hnn : ∀ c, a < c → c < b → 0 ≤ df c) :
    f a ≤ f b := by
  obtain ⟨c, f', hac, hcb, hd, heq⟩ :=
    mean_value_theorem f a b hab (fun c h1 h2 => ⟨df c, hderiv c h1 h2⟩)
  have hf' : f' = df c := HasDerivAt_unique f f' (df c) c hd (hderiv c hac hcb)
  have hprod : 0 ≤ f' * (b - a) := by
    rw [hf']
    exact Real.mul_nonneg (hnn c hac hcb) (Real.le_of_lt (Real.sub_pos_of_lt hab))
  rw [← heq] at hprod
  exact Real.le_of_sub_nonneg hprod

/-- **Sturm non-oscillation (no positive arch).** For `y'' = r·y` with `r ≥ 0` on
`(a,b)`, there is no "positive arch": `y` cannot have `y(a)=y(b)=0` while staying
strictly positive on `(a,b)`. Since an oscillating solution must contain such an
arch between consecutive zeros, `r ≥ 0` ⇒ non-oscillatory ⇒ EML-finite
(no Infinite-Zeros Barrier). This is the certificate `eml_cost.classify_ode`'s
`EML-finite` (Sturm, `r ≥ 0`) verdict rests on. -/
theorem sturm_no_positive_bump
    (y yp ypp r : Real → Real) {a b : Real} (hab : a < b)
    (hy  : ∀ c, a < c → c < b → HasDerivAt y (yp c) c)
    (hyp : ∀ c, a < c → c < b → HasDerivAt yp (ypp c) c)
    (hode : ∀ c, a < c → c < b → ypp c = r c * y c)
    (hr  : ∀ c, a < c → c < b → 0 ≤ r c)
    (hya : y a = 0) (hyb : y b = 0)
    (hbump : ∀ c, a < c → c < b → 0 < y c) :
    False := by
  -- (2) y'' = r·y ≥ 0 on the arch.
  have hypp_nn : ∀ c, a < c → c < b → 0 ≤ ypp c := by
    intro c h1 h2
    rw [hode c h1 h2]
    exact Real.mul_nonneg (hr c h1 h2) (Real.le_of_lt (hbump c h1 h2))
  -- (3) Rolle on y over [a,b]: an interior m with y'(m) = 0.
  obtain ⟨m, ham, hmb, hderiv0⟩ :=
    rolle y a b hab (by rw [hya, hyb]) (fun c h1 h2 => ⟨yp c, hy c h1 h2⟩)
  have hypm0 : yp m = 0 :=
    (HasDerivAt_unique y 0 (yp m) m hderiv0 (hy m ham hmb)).symm
  -- (4a) y' non-decreasing past m: 0 = y'(m) ≤ y'(c) for c ∈ (m,b).
  have hyp_nn : ∀ c, m < c → c < b → 0 ≤ yp c := by
    intro c hmc hcb
    have hmono : yp m ≤ yp c :=
      mono_of_deriv_nonneg yp ypp hmc
        (fun z h1 h2 => hyp z (Real.lt_trans_ax ham h1) (Real.lt_trans_ax h2 hcb))
        (fun z h1 h2 => hypp_nn z (Real.lt_trans_ax ham h1) (Real.lt_trans_ax h2 hcb))
    rwa [hypm0] at hmono
  -- (4b) y non-decreasing on [m,b]: y(m) ≤ y(b).
  have hymb : y m ≤ y b :=
    mono_of_deriv_nonneg y yp hmb
      (fun z h1 h2 => hy z (Real.lt_trans_ax ham h1) h2)
      (fun z h1 h2 => hyp_nn z h1 h2)
  -- (4c) contradiction: 0 < y(m) ≤ y(b) = 0.
  rw [hyb] at hymb
  exact Real.lt_irrefl_ax 0 (Real.lt_of_lt_of_le (hbump m ham hmb) hymb)

/-- **Sturm non-oscillation (no negative arch).** The mirror of
`sturm_no_positive_bump`: for `y'' = r·y` with `r ≥ 0`, `y` cannot have
`y(a)=y(b)=0` while staying strictly NEGATIVE on `(a,b)`. Proved by applying
`sturm_no_positive_bump` to `−y`, which solves the SAME equation
(`(−y)'' = −(r·y) = r·(−y)`) and is positive on the arch. Together the two
theorems say `r ≥ 0` forbids a sign-definite arch of EITHER orientation between
two zeros — the complete "no oscillation arch" statement. -/
theorem sturm_no_negative_bump
    (y yp ypp r : Real → Real) {a b : Real} (hab : a < b)
    (hy  : ∀ c, a < c → c < b → HasDerivAt y (yp c) c)
    (hyp : ∀ c, a < c → c < b → HasDerivAt yp (ypp c) c)
    (hode : ∀ c, a < c → c < b → ypp c = r c * y c)
    (hr  : ∀ c, a < c → c < b → 0 ≤ r c)
    (hya : y a = 0) (hyb : y b = 0)
    (hbump : ∀ c, a < c → c < b → y c < 0) :
    False := by
  refine sturm_no_positive_bump (fun x => -y x) (fun c => -(yp c)) (fun c => -(ypp c)) r hab
    (fun c h1 h2 => HasDerivAt_neg y (yp c) c (hy c h1 h2))
    (fun c h1 h2 => HasDerivAt_neg yp (ypp c) c (hyp c h1 h2))
    (fun c h1 h2 => ?_) hr ?_ ?_ (fun c h1 h2 => Real.neg_pos_of_neg (hbump c h1 h2))
  · -- -(ypp c) = r c * -(y c)
    show -(ypp c) = r c * -(y c)
    rw [hode c h1 h2]; exact (Real.mul_neg _ _).symm
  · show -(y a) = 0
    rw [hya]; exact Real.neg_zero
  · show -(y b) = 0
    rw [hyb]; exact Real.neg_zero

/-! ### Scoping note — the regular-singular `−1/4` threshold (next theorem)

`sturm_no_positive_bump`/`_negative_bump` cover `r ≥ 0`. The Euler / regular-
singular case `r = c/x²` is non-oscillatory for `c ≥ −1/4` even though `r < 0`
when `−1/4 ≤ c < 0` (the threshold near a regular singular point is `−1/4`, not
`0`). `eml_cost.certify_non_oscillation` returns `certified=False` there because
THIS theorem does not reach it. The cleanest Lean route to close that gap (the
Abel–Wronskian argument, no change of variables):

  • `v x := x^{1/2 + β}` with `β = √(c + 1/4) ≥ 0` is an EXPLICIT positive
    solution on `(0,∞)`: `v'' = (c/x²)·v` (indicial `m(m−1)=c`), `v > 0`.
  • Abel: the Wronskian `W := u'·v − u·v'` of two solutions of the SAME equation
    is constant (`W' = u''v − uv'' = (c/x²)uv − u(c/x²)v = 0`).
  • Hence `(u/v)' = (u'v − uv')/v² = W/v²` has constant sign, so `u/v` is
    monotone (or constant). On an arch `u(a)=u(b)=0` ⇒ `u/v` is `0` at both `a`
    and `b` (as `v>0`) — impossible for a strictly monotone function; and the
    constant case forces `u ≡ 0`.

All difficulty concentrates in the first bullet: differentiating the real power
`v = x^{1/2+β} = exp((1/2+β)·log x)` twice (needs the `exp`∘`log` chain rule for
a real exponent). That is the dedicated next piece; `mono_of_deriv_nonneg` and
the arch contradiction here are reused verbatim. -/

end MachLib
