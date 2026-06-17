import MachLib.InnerKhovanskii

/-!
# MachLib.InnerKhovanskiiExp — h-extended inner-Khovanskii interface

`InnerKhovanskii` (from `InnerKhovanskii.lean`) handles the
`Σ T_k · exp(k · x)` pattern — the exponent inside the `exp` is
hard-coded to `k · x`. For non-degenerate chains (e.g.,
`IterExpChain (N+1)` organized by powers of `y_N = exp(y_{N-1})`),
the outer factor is `exp(k · h(x))` where `h(x) = y_{N-1}` — a chain
function, not just `x`.

This file ships the **h-extended interface** `InnerKhovanskiiExp` and
its measured variant `InnerKhovanskiiExpMeasured`, parametric over `h`:

- `h : Real → Real` and `h_deriv : Real → Real` describe the exponent
  function and its derivative.
- `h_HasDerivAt : ∀ x, HasDerivAt h (h_deriv x) x` is the analytic axiom.
- `scalarMul : Real → T → T` is the scaled-multiply operation whose eval
  automatically picks up the `h_deriv` factor:
  `eval (scalarMul k t) x = k · h_deriv x · eval t x`.

For `h = id` (SingleExp case), `h_deriv = const 1`, and `scalarMul k t =
mul (const k) t` — recovering the standard SingleExp scaledReduction.
For chain (`h = exp`, `h_deriv = exp`), `scalarMul k t = mul (mul (const k)
(varY 0)) t` or any other inner element with the right eval.

Closes against `mach_ring v2` (which adds an `ac_rfl` phase to v1's
distribution-only normalization); the v2 tactic handles the
post-distribution AC residues that show up in this file's algebraic
identities.

Zero Mathlib dependency. -/

namespace MachLib
namespace InnerKhovanskiiExpMod

open MachLib.Real
open MachLib.PolynomialEvidence (Poly)
open MachLib.PolynomialRootCount
open MachLib.InnerKhovanskiiMod (InnerKhovanskii)

/-! ## The h-extended structure -/

structure InnerKhovanskiiExp where
  T : Type
  eval : T → Real → Real
  derivative : T → T
  add : T → T → T
  /-- Scaled multiplication: `eval (scalarMul k t) x = k · h_deriv x · eval t x`. -/
  scalarMul : Real → T → T
  /-- The function inside the outer exp factor `exp(k · h x)`. -/
  h : Real → Real
  /-- The derivative of `h`. -/
  h_deriv : Real → Real
  eval_HasDerivAt : ∀ t : T, ∀ x : Real,
    HasDerivAt (eval t) (eval (derivative t) x) x
  eval_add : ∀ t1 t2 : T, ∀ x : Real,
    eval (add t1 t2) x = eval t1 x + eval t2 x
  eval_scalarMul : ∀ k : Real, ∀ t : T, ∀ x : Real,
    eval (scalarMul k t) x = k * h_deriv x * eval t x
  h_HasDerivAt : ∀ x : Real, HasDerivAt h (h_deriv x) x

namespace InnerKhovanskiiExp

/-! ## Generic evalAux -/

noncomputable def evalAux (IKE : InnerKhovanskiiExp) :
    List IKE.T → Nat → Real → Real
  | [],         _, _ => 0
  | t :: rest,  o, x =>
      IKE.eval t x * Real.exp ((natCast o) * IKE.h x) + evalAux IKE rest (o + 1) x

theorem evalAux_nil (IKE : InnerKhovanskiiExp) (o : Nat) (x : Real) :
    evalAux IKE [] o x = 0 := rfl

theorem evalAux_cons (IKE : InnerKhovanskiiExp) (t : IKE.T)
    (rest : List IKE.T) (o : Nat) (x : Real) :
    evalAux IKE (t :: rest) o x =
    IKE.eval t x * Real.exp ((natCast o) * IKE.h x) +
    evalAux IKE rest (o + 1) x := rfl

noncomputable def evalList (IKE : InnerKhovanskiiExp) (coeffs : List IKE.T)
    (x : Real) : Real :=
  evalAux IKE coeffs 0 x

theorem evalList_def (IKE : InnerKhovanskiiExp) (coeffs : List IKE.T) (x : Real) :
    evalList IKE coeffs x = evalAux IKE coeffs 0 x := rfl

theorem evalList_singleton (IKE : InnerKhovanskiiExp) (t : IKE.T) (x : Real) :
    evalList IKE [t] x = IKE.eval t x := by
  show IKE.eval t x * Real.exp ((natCast 0) * IKE.h x)
       + evalAux IKE [] (0 + 1) x = IKE.eval t x
  show IKE.eval t x * Real.exp ((natCast 0) * IKE.h x) + 0 = IKE.eval t x
  rw [show (natCast 0 : Real) = 0 from natCast_zero]
  rw [zero_mul, MachLib.Real.exp_zero, mul_one_ax, add_zero]

/-! ## Generic scaledReductionAux -/

noncomputable def scaledReductionAux (IKE : InnerKhovanskiiExp) (c : Real) :
    List IKE.T → Nat → List IKE.T
  | [],         _ => []
  | t :: rest,  o =>
      IKE.add (IKE.derivative t)
               (IKE.scalarMul ((natCast o) - c) t)
      :: scaledReductionAux IKE c rest (o + 1)

theorem scaledReductionAux_nil (IKE : InnerKhovanskiiExp) (c : Real) (o : Nat) :
    scaledReductionAux IKE c [] o = [] := rfl

theorem scaledReductionAux_cons (IKE : InnerKhovanskiiExp) (c : Real)
    (t : IKE.T) (rest : List IKE.T) (o : Nat) :
    scaledReductionAux IKE c (t :: rest) o =
    IKE.add (IKE.derivative t)
             (IKE.scalarMul ((natCast o) - c) t)
    :: scaledReductionAux IKE c rest (o + 1) := rfl

theorem length_scaledReductionAux (IKE : InnerKhovanskiiExp) (c : Real) :
    ∀ (coeffs : List IKE.T) (o : Nat),
    (scaledReductionAux IKE c coeffs o).length = coeffs.length := by
  intro coeffs
  induction coeffs with
  | nil => intro _; rfl
  | cons t rest ih =>
    intro o
    show (IKE.add (IKE.derivative t) (IKE.scalarMul ((natCast o) - c) t)
          :: scaledReductionAux IKE c rest (o + 1)).length
       = (t :: rest).length
    rw [List.length_cons, List.length_cons, ih (o + 1)]

/-! ## HasDerivAt for evalAux -/

theorem hasDerivAt_evalAux (IKE : InnerKhovanskiiExp) :
    ∀ (coeffs : List IKE.T) (o : Nat) (x : Real),
    HasDerivAt (fun y => evalAux IKE coeffs o y)
               (evalAux IKE (scaledReductionAux IKE 0 coeffs o) o x)
               x := by
  intro coeffs
  induction coeffs with
  | nil =>
    intro o x
    show HasDerivAt (fun _ => (0 : Real)) 0 x
    exact HasDerivAt_const 0 x
  | cons t rest ih =>
    intro o x
    show HasDerivAt
          (fun y => IKE.eval t y * Real.exp ((natCast o) * IKE.h y)
                    + evalAux IKE rest (o + 1) y)
          (evalAux IKE
            (IKE.add (IKE.derivative t)
                      (IKE.scalarMul ((natCast o) - 0) t)
             :: scaledReductionAux IKE 0 rest (o + 1))
            o x)
          x
    have hp : HasDerivAt (IKE.eval t) (IKE.eval (IKE.derivative t) x) x :=
      IKE.eval_HasDerivAt t x
    have hh : HasDerivAt IKE.h (IKE.h_deriv x) x := IKE.h_HasDerivAt x
    have hlinear : HasDerivAt (fun y => (natCast o) * IKE.h y)
                              ((natCast o) * IKE.h_deriv x) x := by
      have hconst : HasDerivAt (fun _ : Real => (natCast o)) 0 x :=
        HasDerivAt_const _ x
      have hmul := HasDerivAt_mul (fun _ => (natCast o)) IKE.h 0 (IKE.h_deriv x)
                    x hconst hh
      have h_simp : 0 * IKE.h x + (natCast o) * IKE.h_deriv x
                  = (natCast o) * IKE.h_deriv x := by mach_ring
      rw [h_simp] at hmul
      exact hmul
    have hexp_at : HasDerivAt Real.exp (Real.exp ((natCast o) * IKE.h x))
                              ((natCast o) * IKE.h x) :=
      HasDerivAt_exp _
    have hexp_comp := HasDerivAt_comp Real.exp (fun y => (natCast o) * IKE.h y)
                        ((natCast o) * IKE.h_deriv x)
                        (Real.exp ((natCast o) * IKE.h x)) x hlinear hexp_at
    have hterm := HasDerivAt_mul (IKE.eval t)
                    (fun y => Real.exp ((natCast o) * IKE.h y))
                    (IKE.eval (IKE.derivative t) x)
                    (Real.exp ((natCast o) * IKE.h x)
                      * ((natCast o) * IKE.h_deriv x)) x hp hexp_comp
    have hsum := HasDerivAt_add (fun y => IKE.eval t y
                                          * Real.exp ((natCast o) * IKE.h y))
                   (fun y => evalAux IKE rest (o + 1) y)
                   (IKE.eval (IKE.derivative t) x
                      * Real.exp ((natCast o) * IKE.h x)
                    + IKE.eval t x * (Real.exp ((natCast o) * IKE.h x)
                                        * ((natCast o) * IKE.h_deriv x)))
                   (evalAux IKE (scaledReductionAux IKE 0 rest (o + 1)) (o + 1) x)
                   x hterm (ih (o + 1) x)
    show HasDerivAt _ _ x
    show HasDerivAt
          (fun y => IKE.eval t y * Real.exp ((natCast o) * IKE.h y)
                    + evalAux IKE rest (o + 1) y)
          (IKE.eval (IKE.add (IKE.derivative t)
                              (IKE.scalarMul ((natCast o) - 0) t)) x
             * Real.exp ((natCast o) * IKE.h x)
           + evalAux IKE (scaledReductionAux IKE 0 rest (o + 1)) (o + 1) x)
          x
    rw [IKE.eval_add, IKE.eval_scalarMul]
    have hring :
        IKE.eval (IKE.derivative t) x * Real.exp ((natCast o) * IKE.h x)
          + IKE.eval t x * (Real.exp ((natCast o) * IKE.h x)
                              * ((natCast o) * IKE.h_deriv x))
        = (IKE.eval (IKE.derivative t) x
            + (natCast o - 0) * IKE.h_deriv x * IKE.eval t x)
          * Real.exp ((natCast o) * IKE.h x) := by mach_ring
    rw [hring] at hsum
    exact hsum

/-! ## Generic eval-combine

The pure-Real ring identity for the per-coefficient step, factored
through `expPoly_step_ring_identity` (already hand-proved against
mach_ring v2) via the substitution `pe := hd * pe`, `R := hd * R`. -/

theorem step_ring_identity_with_hd (pd n pe E S0 R c hd : Real) :
    (pd + n * hd * pe) * E + S0 + (pe * E + R) * (-c) * hd
    = (pd + (n - c) * hd * pe) * E + (S0 + R * (-c) * hd) := by
  -- Apply expPoly_step_ring_identity with the hd-substituted args.
  have h := MachLib.SingleExpKhovanskii.ExpPoly.expPoly_step_ring_identity
              pd n (hd * pe) E S0 (hd * R) c
  -- h : (pd + (n - 0) * (hd * pe)) * E + S0 + ((hd * pe) * E + hd * R) * -c
  --     = (pd + (n - c) * (hd * pe)) * E + (S0 + hd * R * -c)
  -- The LHS / RHS shapes differ from our target by associativity +
  -- commutativity (distributing hd over (pe*E + R) and reordering the
  -- final * hd vs * -c). mach_ring v2's ac_rfl phase closes these.
  have lhs_eq :
      (pd + (n - 0) * (hd * pe)) * E + S0 + ((hd * pe) * E + hd * R) * -c
      = (pd + n * hd * pe) * E + S0 + (pe * E + R) * (-c) * hd := by mach_ring
  have rhs_eq :
      (pd + (n - c) * (hd * pe)) * E + (S0 + hd * R * -c)
      = (pd + (n - c) * hd * pe) * E + (S0 + R * (-c) * hd) := by mach_ring
  rw [← lhs_eq, ← rhs_eq]
  exact h

theorem scaledReductionAux_eval_combine (IKE : InnerKhovanskiiExp) (c : Real)
    (x : Real) :
    ∀ (coeffs : List IKE.T) (o : Nat),
    evalAux IKE (scaledReductionAux IKE 0 coeffs o) o x
      + evalAux IKE coeffs o x * (-c) * IKE.h_deriv x
    = evalAux IKE (scaledReductionAux IKE c coeffs o) o x := by
  intro coeffs
  induction coeffs with
  | nil =>
    intro o
    show (0 : Real) + 0 * (-c) * IKE.h_deriv x = 0
    mach_ring
  | cons t rest ih =>
    intro o
    have hih := ih (o + 1)
    show (IKE.eval (IKE.add (IKE.derivative t)
                             (IKE.scalarMul ((natCast o) - 0) t)) x
            * Real.exp ((natCast o) * IKE.h x)
          + evalAux IKE (scaledReductionAux IKE 0 rest (o + 1)) (o + 1) x)
         + (IKE.eval t x * Real.exp ((natCast o) * IKE.h x)
            + evalAux IKE rest (o + 1) x) * (-c) * IKE.h_deriv x
       = IKE.eval (IKE.add (IKE.derivative t)
                            (IKE.scalarMul ((natCast o) - c) t)) x
            * Real.exp ((natCast o) * IKE.h x)
         + evalAux IKE (scaledReductionAux IKE c rest (o + 1)) (o + 1) x
    rw [← hih]
    rw [IKE.eval_add, IKE.eval_scalarMul]
    rw [IKE.eval_add, IKE.eval_scalarMul]
    rw [sub_zero]
    -- The remaining identity is exactly step_ring_identity_with_hd.
    exact step_ring_identity_with_hd
            (IKE.eval (IKE.derivative t) x) (natCast o) (IKE.eval t x)
            (Real.exp ((natCast o) * IKE.h x))
            (evalAux IKE (scaledReductionAux IKE 0 rest (o + 1)) (o + 1) x)
            (evalAux IKE rest (o + 1) x) c (IKE.h_deriv x)

/-! ## Rolle vehicle and zero-count transfer -/

noncomputable def mulNegExpH (IKE : InnerKhovanskiiExp) (coeffs : List IKE.T)
    (c : Real) : Real → Real :=
  fun x => evalList IKE coeffs x * Real.exp (-c * IKE.h x)

theorem mulNegExpH_zero_iff (IKE : InnerKhovanskiiExp) (coeffs : List IKE.T)
    (c x : Real) :
    mulNegExpH IKE coeffs c x = 0 ↔ evalList IKE coeffs x = 0 := by
  show evalList IKE coeffs x * Real.exp (-c * IKE.h x) = 0
        ↔ evalList IKE coeffs x = 0
  constructor
  · intro hz
    have hexp_ne : Real.exp (-c * IKE.h x) ≠ 0 := exp_ne_zero _
    rw [mul_comm] at hz
    exact MachLib.SingleExpKhovanskii.ExpPoly.mul_eq_zero_of_factor_ne_zero_local
            hexp_ne hz
  · intro hz; rw [hz, zero_mul]

theorem hasDerivAt_mulNegExpH_raw (IKE : InnerKhovanskiiExp) (coeffs : List IKE.T)
    (c x : Real) :
    HasDerivAt (mulNegExpH IKE coeffs c)
               (evalAux IKE (scaledReductionAux IKE 0 coeffs 0) 0 x
                  * Real.exp (-c * IKE.h x)
                + evalList IKE coeffs x
                  * (Real.exp (-c * IKE.h x) * (-c * IKE.h_deriv x)))
               x := by
  show HasDerivAt (fun y => evalList IKE coeffs y * Real.exp (-c * IKE.h y))
                  (evalAux IKE (scaledReductionAux IKE 0 coeffs 0) 0 x
                    * Real.exp (-c * IKE.h x)
                   + evalList IKE coeffs x
                     * (Real.exp (-c * IKE.h x) * (-c * IKE.h_deriv x))) x
  have hep : HasDerivAt (evalList IKE coeffs)
              (evalAux IKE (scaledReductionAux IKE 0 coeffs 0) 0 x) x :=
    hasDerivAt_evalAux IKE coeffs 0 x
  have hh : HasDerivAt IKE.h (IKE.h_deriv x) x := IKE.h_HasDerivAt x
  have hlinear : HasDerivAt (fun y => -c * IKE.h y) (-c * IKE.h_deriv x) x := by
    have hconst : HasDerivAt (fun _ : Real => -c) 0 x := HasDerivAt_const _ x
    have hmul := HasDerivAt_mul (fun _ => -c) IKE.h 0 (IKE.h_deriv x) x hconst hh
    have : 0 * IKE.h x + (-c) * IKE.h_deriv x = -c * IKE.h_deriv x := by mach_ring
    rw [this] at hmul
    exact hmul
  have hexp_at : HasDerivAt Real.exp (Real.exp (-c * IKE.h x)) (-c * IKE.h x) :=
    HasDerivAt_exp _
  have hexp_comp := HasDerivAt_comp Real.exp (fun y => -c * IKE.h y)
                      (-c * IKE.h_deriv x) (Real.exp (-c * IKE.h x)) x
                      hlinear hexp_at
  exact HasDerivAt_mul (evalList IKE coeffs) (fun y => Real.exp (-c * IKE.h y))
          (evalAux IKE (scaledReductionAux IKE 0 coeffs 0) 0 x)
          (Real.exp (-c * IKE.h x) * (-c * IKE.h_deriv x)) x hep hexp_comp

theorem scaledReduction_eval_zero_of_aux_deriv_zero
    (IKE : InnerKhovanskiiExp) (coeffs : List IKE.T) (c z : Real)
    (g'' : Real)
    (hg''_deriv : HasDerivAt (mulNegExpH IKE coeffs c) g'' z)
    (hg''_zero : g'' = 0) :
    evalList IKE (scaledReductionAux IKE c coeffs 0) z = 0 := by
  have hcanonical := hasDerivAt_mulNegExpH_raw IKE coeffs c z
  have huniq := HasDerivAt_unique (mulNegExpH IKE coeffs c) g''
                  (evalAux IKE (scaledReductionAux IKE 0 coeffs 0) 0 z
                    * Real.exp (-c * IKE.h z)
                   + evalList IKE coeffs z
                     * (Real.exp (-c * IKE.h z) * (-c * IKE.h_deriv z)))
                  z hg''_deriv hcanonical
  have hcan_zero :
      evalAux IKE (scaledReductionAux IKE 0 coeffs 0) 0 z * Real.exp (-c * IKE.h z)
        + evalList IKE coeffs z
          * (Real.exp (-c * IKE.h z) * (-c * IKE.h_deriv z)) = 0 := by
    rw [← huniq]; exact hg''_zero
  have hcombine := scaledReductionAux_eval_combine IKE c z coeffs 0
  have hfact :
      evalAux IKE (scaledReductionAux IKE 0 coeffs 0) 0 z * Real.exp (-c * IKE.h z)
        + evalList IKE coeffs z
          * (Real.exp (-c * IKE.h z) * (-c * IKE.h_deriv z))
      = Real.exp (-c * IKE.h z)
        * evalList IKE (scaledReductionAux IKE c coeffs 0) z := by
    show evalAux IKE (scaledReductionAux IKE 0 coeffs 0) 0 z * Real.exp (-c * IKE.h z)
          + evalAux IKE coeffs 0 z
            * (Real.exp (-c * IKE.h z) * (-c * IKE.h_deriv z))
        = Real.exp (-c * IKE.h z)
          * evalAux IKE (scaledReductionAux IKE c coeffs 0) 0 z
    rw [← hcombine]
    mach_ring
  rw [hfact] at hcan_zero
  have hexp_ne : Real.exp (-c * IKE.h z) ≠ 0 := exp_ne_zero _
  exact MachLib.SingleExpKhovanskii.ExpPoly.mul_eq_zero_of_factor_ne_zero_local
          hexp_ne hcan_zero

theorem zero_count_scaledReduction_transfer_raw
    (IKE : InnerKhovanskiiExp) (coeffs : List IKE.T) (c a b : Real) (hab : a < b)
    (N : Nat)
    (h_reduced_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt (mulNegExpH IKE coeffs c) f'' z ∧ f'' = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ evalList IKE coeffs z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzeros
  have hzeros_g : ∀ z ∈ zeros_f, a < z ∧ z < b ∧ mulNegExpH IKE coeffs c z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    exact (mulNegExpH_zero_iff IKE coeffs c z).mpr hfz
  have hdiff : ∀ x : Real, a < x → x < b →
                ∃ f' : Real, HasDerivAt (mulNegExpH IKE coeffs c) f' x := by
    intro x _ _
    refine ⟨_, hasDerivAt_mulNegExpH_raw IKE coeffs c x⟩
  exact zero_count_bound_by_deriv (mulNegExpH IKE coeffs c) a b hab hdiff N
          h_reduced_bound zeros_f hnodup hzeros_g

theorem zero_count_scaledReduction_transfer
    (IKE : InnerKhovanskiiExp) (coeffs : List IKE.T) (c a b : Real) (hab : a < b)
    (N : Nat)
    (h_red_bound_eval : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          evalList IKE (scaledReductionAux IKE c coeffs 0) z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ evalList IKE coeffs z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply zero_count_scaledReduction_transfer_raw IKE coeffs c a b hab N
  intro zeros' hnodup' hzeros'_prop
  apply h_red_bound_eval zeros' hnodup'
  intro z hz
  obtain ⟨haz, hzb, g'', hg''_deriv, hg''_zero⟩ := hzeros'_prop z hz
  refine ⟨haz, hzb, ?_⟩
  exact scaledReduction_eval_zero_of_aux_deriv_zero IKE coeffs c z g''
          hg''_deriv hg''_zero

end InnerKhovanskiiExp

/-! ## Measured h-extended interface + parametric main theorem -/

structure InnerKhovanskiiExpMeasured extends InnerKhovanskiiExp where
  measure : T → Nat
  length_one_bound : ∀ t : T, ∀ a b : Real, a < b →
    (∃ x : Real, eval t x ≠ 0) →
    ∀ zeros : List Real, zeros.Nodup →
    (∀ z ∈ zeros, a < z ∧ z < b ∧ eval t z = 0) →
    zeros.length ≤ measure t
  coeffStep_le : ∀ k : Real, ∀ t : T,
    measure (add (derivative t) (scalarMul k t)) ≤ measure t
  coeffStep_lt : ∀ t : T, measure t > 0 →
    measure (add (derivative t) (scalarMul 0 t)) < measure t

namespace InnerKhovanskiiExpMeasured

open InnerKhovanskiiExp

noncomputable def sumMeasure (IKEM : InnerKhovanskiiExpMeasured) :
    List IKEM.T → Nat
  | []        => 0
  | t :: rest => IKEM.measure t + sumMeasure IKEM rest

theorem sumMeasure_nil (IKEM : InnerKhovanskiiExpMeasured) :
    sumMeasure IKEM [] = 0 := rfl

theorem sumMeasure_cons (IKEM : InnerKhovanskiiExpMeasured) (t : IKEM.T)
    (rest : List IKEM.T) :
    sumMeasure IKEM (t :: rest) = IKEM.measure t + sumMeasure IKEM rest := rfl

theorem sumMeasure_scaledReductionAux_le (IKEM : InnerKhovanskiiExpMeasured)
    (c : Real) :
    ∀ (coeffs : List IKEM.T) (offset : Nat),
    sumMeasure IKEM
      (scaledReductionAux IKEM.toInnerKhovanskiiExp c coeffs offset)
      ≤ sumMeasure IKEM coeffs := by
  intro coeffs
  induction coeffs with
  | nil => intro _; exact Nat.le_refl _
  | cons head tail ih =>
    intro offset
    show sumMeasure IKEM
          (IKEM.add (IKEM.derivative head)
                     (IKEM.scalarMul ((natCast offset) - c) head)
           :: scaledReductionAux IKEM.toInnerKhovanskiiExp c tail (offset + 1))
       ≤ sumMeasure IKEM (head :: tail)
    rw [sumMeasure_cons, sumMeasure_cons]
    have h1 := IKEM.coeffStep_le ((natCast offset) - c) head
    have h2 := ih (offset + 1)
    omega

theorem sumMeasure_scaledReductionAux_lt (IKEM : InnerKhovanskiiExpMeasured) :
    ∀ (coeffs : List IKEM.T) (offset : Nat) (hne : coeffs ≠ []),
    IKEM.measure (coeffs.getLast hne) > 0 →
    sumMeasure IKEM
      (scaledReductionAux IKEM.toInnerKhovanskiiExp
        (natCast (offset + coeffs.length - 1)) coeffs offset)
      < sumMeasure IKEM coeffs := by
  intro coeffs
  induction coeffs with
  | nil => intros _ hne; exact absurd rfl hne
  | cons head tail ih =>
    intros offset _ hlast_pos
    by_cases htail : tail = []
    · subst htail
      have hoff : offset + 1 - 1 = offset := by omega
      have hlast_pos' : IKEM.measure head > 0 := hlast_pos
      have hstrict := IKEM.coeffStep_lt head hlast_pos'
      show sumMeasure IKEM
            (IKEM.add (IKEM.derivative head)
                     (IKEM.scalarMul ((natCast offset : Real) -
                                            (natCast (offset + 1 - 1))) head)
             :: scaledReductionAux IKEM.toInnerKhovanskiiExp
                  (natCast (offset + 1 - 1)) [] (offset + 1))
          < sumMeasure IKEM [head]
      rw [hoff]
      have hsub : (natCast offset : Real) - natCast offset = 0 := sub_self _
      rw [hsub]
      show IKEM.measure (IKEM.add (IKEM.derivative head)
                                   (IKEM.scalarMul 0 head))
           + sumMeasure IKEM ([] : List IKEM.T)
         < IKEM.measure head + sumMeasure IKEM ([] : List IKEM.T)
      rw [sumMeasure_nil]
      omega
    · have htail_ne : tail ≠ [] := htail
      have hgetlast : (head :: tail).getLast (List.cons_ne_nil head tail)
                    = tail.getLast htail_ne := List.getLast_cons htail_ne
      have hlast_pos_tail : IKEM.measure (tail.getLast htail_ne) > 0 := by
        rw [← hgetlast]
        exact hlast_pos
      have hlen : (head :: tail).length = tail.length + 1 := rfl
      have hoff_eq : offset + (tail.length + 1) - 1 = (offset + 1) + tail.length - 1 := by omega
      show sumMeasure IKEM
            (scaledReductionAux IKEM.toInnerKhovanskiiExp
              (natCast (offset + (head :: tail).length - 1))
              (head :: tail) offset)
          < sumMeasure IKEM (head :: tail)
      rw [hlen]
      show sumMeasure IKEM
            (IKEM.add (IKEM.derivative head)
                     (IKEM.scalarMul ((natCast offset : Real) -
                                            (natCast (offset + (tail.length + 1) - 1)))
                                            head)
             :: scaledReductionAux IKEM.toInnerKhovanskiiExp
                  (natCast (offset + (tail.length + 1) - 1)) tail (offset + 1))
          < sumMeasure IKEM (head :: tail)
      rw [hoff_eq]
      show IKEM.measure (IKEM.add (IKEM.derivative head)
                                  (IKEM.scalarMul ((natCast offset : Real)
                                    - (natCast ((offset + 1) + tail.length - 1)))
                                            head))
           + sumMeasure IKEM
               (scaledReductionAux IKEM.toInnerKhovanskiiExp
                 (natCast ((offset + 1) + tail.length - 1)) tail (offset + 1))
         < IKEM.measure head + sumMeasure IKEM tail
      have h_head_le := IKEM.coeffStep_le
                          ((natCast offset : Real) -
                           (natCast ((offset + 1) + tail.length - 1)))
                          head
      have h_tail_lt := ih (offset + 1) htail_ne hlast_pos_tail
      omega

/-! ## Parametric main theorem -/

theorem auto_bound_with_propagation_aux
    (IKEM : InnerKhovanskiiExpMeasured) :
    ∀ (M : Nat) (coeffs : List IKEM.T),
    coeffs.length + sumMeasure IKEM coeffs ≤ M →
    (∀ coeffs' : List IKEM.T,
       coeffs'.length + sumMeasure IKEM coeffs' ≤ M →
       (∃ x, evalList IKEM.toInnerKhovanskiiExp coeffs' x ≠ 0)) →
    (∀ coeffs' : List IKEM.T,
       ∀ (hne_c : coeffs' ≠ []),
       coeffs'.length ≥ 2 →
       coeffs'.length + sumMeasure IKEM coeffs' ≤ M →
       IKEM.measure (coeffs'.getLast hne_c) > 0) →
    ∀ (a b : Real), a < b →
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        evalList IKEM.toInnerKhovanskiiExp coeffs z = 0) →
      zeros.length ≤ M := by
  intro M
  induction M with
  | zero =>
    intro coeffs hM h_prop _h_strict_last a b _hab zeros _hnodup _hzeros
    have hne := h_prop coeffs hM
    have hlen : coeffs.length = 0 := by
      have h := Nat.zero_le (sumMeasure IKEM coeffs)
      omega
    have hempty : coeffs = [] := List.length_eq_zero.mp hlen
    exfalso
    obtain ⟨x, hx⟩ := hne
    apply hx
    rw [hempty]
    show evalAux IKEM.toInnerKhovanskiiExp [] 0 x = 0
    rfl
  | succ M' ih =>
    intro coeffs hM h_prop h_strict_last a b hab zeros hnodup hzeros
    have hne := h_prop coeffs hM
    match h_coeffs : coeffs with
    | [] =>
      exfalso
      obtain ⟨x, hx⟩ := hne
      apply hx
      show evalAux IKEM.toInnerKhovanskiiExp [] 0 x = 0
      rfl
    | [t] =>
      have hne_t : ∃ x : Real, IKEM.eval t x ≠ 0 := by
        obtain ⟨x, hx⟩ := hne
        refine ⟨x, ?_⟩
        rw [← evalList_singleton]
        exact hx
      have hzeros_t : ∀ z ∈ zeros, a < z ∧ z < b ∧ IKEM.eval t z = 0 := by
        intro z hz
        obtain ⟨ha, hb', hev⟩ := hzeros z hz
        refine ⟨ha, hb', ?_⟩
        rw [← evalList_singleton]
        exact hev
      have hbnd := IKEM.length_one_bound t a b hab hne_t zeros hnodup hzeros_t
      have h_sum_eq : sumMeasure IKEM ([t] : List IKEM.T) = IKEM.measure t := by
        show IKEM.measure t + sumMeasure IKEM ([] : List IKEM.T) = IKEM.measure t
        rw [sumMeasure_nil]; omega
      have h_len : ([t] : List IKEM.T).length = 1 := rfl
      rw [h_sum_eq, h_len] at hM
      omega
    | t1 :: t2 :: rest =>
      have hne_coeffs : (t1 :: t2 :: rest : List IKEM.T) ≠ [] :=
        List.cons_ne_nil _ _
      have hlen_ge_2 : (t1 :: t2 :: rest : List IKEM.T).length ≥ 2 := by simp
      have hlast_pos :
          IKEM.measure ((t1 :: t2 :: rest : List IKEM.T).getLast hne_coeffs) > 0 :=
        h_strict_last (t1 :: t2 :: rest) hne_coeffs hlen_ge_2 hM
      have h_strict := sumMeasure_scaledReductionAux_lt IKEM
                         (t1 :: t2 :: rest) 0 hne_coeffs hlast_pos
      have h_offset_eq :
          (0 : Nat) + (t1 :: t2 :: rest : List IKEM.T).length - 1
          = (t1 :: t2 :: rest : List IKEM.T).length - 1 := by omega
      rw [h_offset_eq] at h_strict
      have h_aux_len :=
        length_scaledReductionAux IKEM.toInnerKhovanskiiExp
          (natCast ((t1 :: t2 :: rest : List IKEM.T).length - 1))
          (t1 :: t2 :: rest) 0
      have h_measure :
          (scaledReductionAux IKEM.toInnerKhovanskiiExp
            (natCast ((t1 :: t2 :: rest : List IKEM.T).length - 1))
            (t1 :: t2 :: rest) 0).length
            + sumMeasure IKEM
                (scaledReductionAux IKEM.toInnerKhovanskiiExp
                  (natCast ((t1 :: t2 :: rest : List IKEM.T).length - 1))
                  (t1 :: t2 :: rest) 0)
            ≤ M' := by
        rw [h_aux_len]; omega
      have h_prop_red : ∀ coeffs' : List IKEM.T,
                        coeffs'.length + sumMeasure IKEM coeffs' ≤ M' →
                        (∃ x, evalList IKEM.toInnerKhovanskiiExp coeffs' x ≠ 0) := by
        intro coeffs' hcoeffs'
        exact h_prop coeffs' (by omega)
      have h_strict_last_red : ∀ coeffs' : List IKEM.T,
                                ∀ (hne_c : coeffs' ≠ []),
                                coeffs'.length ≥ 2 →
                                coeffs'.length + sumMeasure IKEM coeffs' ≤ M' →
                                IKEM.measure (coeffs'.getLast hne_c) > 0 := by
        intro coeffs' hne_c hlen_ge hmeas
        exact h_strict_last coeffs' hne_c hlen_ge (by omega)
      have hred_bound := ih _ h_measure h_prop_red h_strict_last_red a b hab
      have h_transfer := zero_count_scaledReduction_transfer IKEM.toInnerKhovanskiiExp
                          (t1 :: t2 :: rest)
                          (natCast ((t1 :: t2 :: rest : List IKEM.T).length - 1))
                          a b hab M' hred_bound
      have := h_transfer zeros hnodup hzeros
      omega

end InnerKhovanskiiExpMeasured

end InnerKhovanskiiExpMod
end MachLib
