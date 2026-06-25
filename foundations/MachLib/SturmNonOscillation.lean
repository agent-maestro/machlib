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

/-! ### Toward the regular-singular `−1/4` threshold — the explicit Euler solution

`sturm_no_positive_bump`/`_negative_bump` cover `r ≥ 0`. The Euler / regular-
singular case `r = c/x²` is non-oscillatory for `c ≥ −1/4` even though `r < 0`
when `−1/4 ≤ c < 0` (the oscillation threshold near a regular singular point is
`−1/4`, not `0`). The route to that theorem (Abel–Wronskian) needs an explicit
positive comparison solution `v = x^α`. THIS SECTION PROVES the keystone: `x^α`
is a positive solution of `x²v'' = (α²−α)v` — i.e. of `u'' = r·u` with
`r = (α²−α)/x²`, and `c = α²−α ≥ −1/4` exactly when a real `α` exists
(`α = ½ ± √(c+¼)`). The hard part (the real-power second derivative + the field
algebra) is done here; the remaining Abel assembly (below) is the next step. -/

/-- Left cancellation in a field: `a ≠ 0 → a·b = a·c → b = c`. PROVED from
`mul_inv`. Generally useful; the Euler keystone needs it for `1/x · 1/x`. -/
theorem mul_left_cancel₀ {a b c : Real} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have h1a : (1 / a) * a = 1 := by rw [Real.mul_comm]; exact Real.mul_inv a ha
  calc b = 1 * b := (Real.one_mul_thm b).symm
    _ = ((1 / a) * a) * b := by rw [h1a]
    _ = (1 / a) * (a * b) := by rw [Real.mul_assoc]
    _ = (1 / a) * (a * c) := by rw [h]
    _ = ((1 / a) * a) * c := by rw [Real.mul_assoc]
    _ = 1 * c := by rw [h1a]
    _ = c := Real.one_mul_thm c

/-- `(1/x)·(1/x) = 1/(x·x)`. The reciprocal-product fact MachLib lacked, from
`mul_inv` + `mul_left_cancel₀`. -/
theorem one_div_mul_one_div {x : Real} (hx : 0 < x) :
    (1 / x) * (1 / x) = 1 / (x * x) := by
  have hx_ne : x ≠ 0 := Real.ne_of_gt hx
  have hxx : x * x ≠ 0 := Real.ne_of_gt (Real.mul_pos hx hx)
  apply mul_left_cancel₀ hxx
  have hL : (x * x) * ((1 / x) * (1 / x)) = (x * (1 / x)) * (x * (1 / x)) := by mach_ring
  rw [Real.mul_inv x hx_ne, Real.one_mul_thm] at hL
  rw [hL, Real.mul_inv (x * x) hxx]

/-- `v(x) = x^α = exp(α · log x)`. -/
noncomputable def vpow (α x : Real) : Real := Real.exp (α * Real.log x)

/-- `x^α > 0`. -/
theorem vpow_pos (α x : Real) : 0 < vpow α x := Real.exp_pos _

/-- `(x^α)' = x^α · (α · (1/x))` for `x > 0` (chain rule, `exp ∘ (α·log)`). -/
theorem vpow_deriv (α x : Real) (hx : 0 < x) :
    HasDerivAt (vpow α) (vpow α x * (α * (1 / x))) x := by
  have hinner : HasDerivAt (fun y => α * Real.log y) (α * (1 / x)) x := by
    have h := HasDerivAt_mul (fun _ => α) Real.log 0 (1 / x) x
      (HasDerivAt_const α x) (HasDerivAt_log_pos x hx)
    have hval : (0 * Real.log x + α * (1 / x)) = α * (1 / x) := by
      rw [Real.zero_mul, Real.zero_add]
    rwa [hval] at h
  exact HasDerivAt_comp Real.exp (fun y => α * Real.log y)
    (α * (1 / x)) (Real.exp (α * Real.log x)) x hinner (HasDerivAt_exp (α * Real.log x))

/-- **Euler keystone.** `x^α` solves `x²v'' = (α²−α)v`: its second derivative
(of the first-derivative function `y ↦ v(y)·(α·(1/y))`) is `(α²−α)·(1/x²)·v(x)`.
So `v = x^α` is an explicit positive solution of `u'' = r·u` with `r = c/x²`,
`c = α²−α` (≥ −1/4 iff `α` is real). This is the keystone for the regular-
singular non-oscillation theorem. PROVED — real-power chain rule (`vpow_deriv`),
reciprocal rule, and `one_div_mul_one_div`; no sorryAx. -/
theorem vpow_deriv2 (α x : Real) (hx : 0 < x) :
    HasDerivAt (fun y => vpow α y * (α * (1 / y)))
      ((α * α - α) * (1 / (x * x)) * vpow α x) x := by
  have hx_ne : x ≠ 0 := Real.ne_of_gt hx
  have hxx : x * x ≠ 0 := Real.ne_of_gt (Real.mul_pos hx hx)
  have hg : HasDerivAt (fun y => α * (1 / y)) (α * (-1 / (x * x))) x := by
    have hinv : HasDerivAt (fun y => 1 / y) (-1 / (x * x)) x := by
      simpa using HasDerivAt_inv (fun y => y) 1 x hx_ne (HasDerivAt_id x)
    have h := HasDerivAt_mul (fun _ => α) (fun y => 1 / y) 0 (-1 / (x * x)) x
      (HasDerivAt_const α x) hinv
    have hval : (0 * (1 / x) + α * (-1 / (x * x))) = α * (-1 / (x * x)) := by
      rw [Real.zero_mul, Real.zero_add]
    rwa [hval] at h
  have hprod := HasDerivAt_mul (vpow α) (fun y => α * (1 / y))
    (vpow α x * (α * (1 / x))) (α * (-1 / (x * x))) x (vpow_deriv α x hx) hg
  have hval2 :
      (vpow α x * (α * (1 / x))) * (α * (1 / x)) + vpow α x * (α * (-1 / (x * x)))
        = (α * α - α) * (1 / (x * x)) * vpow α x := by
    have hL1 : (1 / x) * (1 / x) = 1 / (x * x) := one_div_mul_one_div hx
    have hneg : (-1 / (x * x)) = -(1 / (x * x)) := by
      rw [Real.div_def (-1) (x * x) hxx, Real.neg_mul, Real.one_mul_thm]
    rw [hneg]
    have hexpand :
        (vpow α x * (α * (1 / x))) * (α * (1 / x)) + vpow α x * (α * -(1 / (x * x)))
          = vpow α x * (α * α) * ((1 / x) * (1 / x)) + vpow α x * (-(α * (1 / (x * x)))) := by
      mach_ring
    rw [hexpand, hL1]; mach_ring
  rwa [hval2] at hprod

/-! ### Abel–Wronskian core (all algebra verified)

With the explicit positive solution `v = vpow α` (`vpow_pos`/`vpow_deriv`/
`vpow_deriv2`), the regular-singular non-oscillation theorem follows by the
Abel–Wronskian argument. The three lemmas below discharge ALL of its algebra
(no `sorry`); the only remaining step is the MVT sign-glue (pure logic).

Note: these used `ac_rfl` (Real's registered `Std.Commutative`/`Associative`
instances) for the multiplicative-AC steps that `mach_ring` cannot canonicalise
— the workaround for MachLib's incomplete ring tactic. -/

/-- **Abel.** The Wronskian `W = u'·v − u·v'` of two solutions of the Euler
equation `_'' = ((α²−α)/x²)·_` (with `v = x^α`) is constant: `W' = 0`. -/
theorem abel_euler_wronskian_deriv_zero
    (u up upp : Real → Real) (α x : Real) (hx : 0 < x)
    (hu : HasDerivAt u (up x) x) (hup : HasDerivAt up (upp x) x)
    (hode : upp x = (α * α - α) * (1 / (x * x)) * u x) :
    HasDerivAt (fun y => up y * vpow α y - u y * (vpow α y * (α * (1 / y)))) 0 x := by
  have ht1 := HasDerivAt_mul up (vpow α) (upp x) (vpow α x * (α * (1 / x))) x
    hup (vpow_deriv α x hx)
  have ht2 := HasDerivAt_mul u (fun y => vpow α y * (α * (1 / y)))
    (up x) ((α * α - α) * (1 / (x * x)) * vpow α x) x hu (vpow_deriv2 α x hx)
  have hsub := HasDerivAt_sub _ _ _ _ x ht1 ht2
  have hval :
      (upp x * vpow α x + up x * (vpow α x * (α * (1 / x))))
        - (up x * (vpow α x * (α * (1 / x))) + u x * ((α * α - α) * (1 / (x * x)) * vpow α x))
        = 0 := by
    rw [hode]
    have heq :
        (α * α - α) * (1 / (x * x)) * u x * vpow α x + up x * (vpow α x * (α * (1 / x)))
          = up x * (vpow α x * (α * (1 / x)))
            + u x * ((α * α - α) * (1 / (x * x)) * vpow α x) := by ac_rfl
    rw [heq, Real.sub_self]
  rwa [hval] at hsub

/-- The quotient `φ = u/v` has the explicit derivative (product + reciprocal). -/
theorem phi_euler_deriv (u up : Real → Real) (α x : Real) (hx : 0 < x)
    (hu : HasDerivAt u (up x) x) :
    HasDerivAt (fun y => u y * (1 / vpow α y))
      (up x * (1 / vpow α x)
        + u x * (-(vpow α x * (α * (1 / x))) / (vpow α x * vpow α x))) x := by
  have hv_ne : vpow α x ≠ 0 := Real.ne_of_gt (vpow_pos α x)
  have hinv := HasDerivAt_inv (vpow α) (vpow α x * (α * (1 / x))) x hv_ne (vpow_deriv α x hx)
  exact HasDerivAt_mul u (fun y => 1 / vpow α y) (up x)
    (-(vpow α x * (α * (1 / x))) / (vpow α x * vpow α x)) x hu hinv

/-- The bridge: `φ'(x)·v(x)² = W(x)`. Ties the quotient derivative to the
Wronskian (so the constant `W` controls the sign of `φ'`). -/
theorem phi_euler_identity (u up : Real → Real) (α x : Real) :
    (up x * (1 / vpow α x)
        + u x * (-(vpow α x * (α * (1 / x))) / (vpow α x * vpow α x)))
      * (vpow α x * vpow α x)
      = up x * vpow α x - u x * (vpow α x * (α * (1 / x))) := by
  have hv_ne : vpow α x ≠ 0 := Real.ne_of_gt (vpow_pos α x)
  have hvv_ne : vpow α x * vpow α x ≠ 0 :=
    Real.ne_of_gt (Real.mul_pos (vpow_pos α x) (vpow_pos α x))
  have h1 : (1 / vpow α x) * (vpow α x * vpow α x) = vpow α x := by
    rw [← Real.mul_assoc, Real.mul_comm (1 / vpow α x) (vpow α x),
        Real.mul_inv (vpow α x) hv_ne, Real.one_mul_thm]
  have h2 : (-(vpow α x * (α * (1 / x))) / (vpow α x * vpow α x)) * (vpow α x * vpow α x)
      = -(vpow α x * (α * (1 / x))) := by
    rw [Real.div_def (-(vpow α x * (α * (1 / x)))) (vpow α x * vpow α x) hvv_ne,
        Real.mul_assoc, Real.mul_comm (1 / (vpow α x * vpow α x)) (vpow α x * vpow α x),
        Real.mul_inv (vpow α x * vpow α x) hvv_ne, Real.mul_one_ax]
  rw [Real.mul_distrib_right, Real.mul_assoc (up x), Real.mul_assoc (u x),
      h1, h2, Real.mul_neg, ← Real.sub_def]

/-! ### Remaining step — the MVT sign-glue (pure logic, no algebra)

Everything algebraic is proved above. The full Euler `−1/4` non-oscillation
theorem closes by, for an arch `u(a)=u(b)=0`, `u>0` on `(a,b)`:
  • Rolle on `u` → interior `m`, `u(m)>0` ⇒ `φ(m) = u(m)/v(m) > 0`
    (`φ(a)=φ(b)=0` since `u(a)=u(b)=0`).
  • MVT on `φ` over `[a,m]` ⇒ `φ'(ξ₁)>0`; over `[m,b]` ⇒ `φ'(ξ₂)<0` (`ξ₁<m<ξ₂`).
  • `phi_euler_identity`: `W(ξᵢ)=φ'(ξᵢ)·v(ξᵢ)²`, so `W(ξ₁)>0`, `W(ξ₂)<0`.
  • `abel_euler_wronskian_deriv_zero` ⇒ `W'=0` ⇒ (MVT on `[ξ₁,ξ₂]`)
    `W(ξ₁)=W(ξ₂)` — contradiction (`>0 = <0`).
Reuses `mean_value_theorem`, `rolle`, `HasDerivAt_unique`, `phi_euler_deriv`. No
ring/field algebra remains — this is the dedicated logical finish. -/

end MachLib
