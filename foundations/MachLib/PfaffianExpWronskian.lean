import MachLib.PfaffianExpEliminate
import MachLib.PfaffianLogWronskian

/-!
# `exp_hard` — the exp-Wronskian vehicle count (B3, analytic core)

The Rolle/Wronskian half of the resolved `exp_hard` construction. B1/B2 built `expEliminate c G top p`
(top exponential eliminated at the polynomial level, formal `degreeY_top = D`, leading coeff eval-zero) and
showed a depth-`≤D-1` recursor bounds its zeros. B3 supplies the **count that connects `p` to its
elimination**: on `(a,b)`,

  `#zeros(pfaffianChainFn c p) ≤ #zeros(pfaffianChainFn c (expEliminate c G top p)) + #zeros(c_D) + 1`,

where `c_D = leadingCoeffY top p`.

Mechanism — the exact exp analog of `log_wronskian_reduce_full`, with the **exp integrating factor**. The
log arm reduces against the vehicle `f·(1/c_D)`; the exp top needs the extra `y_top^D` factor, giving vehicle
`f·(1/V)` with `V = y_top^D · c_D`. Because the Pfaffian relation is `(y_top)' = G·y_top`, the log-derivative
of the exp factor is `(y_top^D)'/y_top^D = D·G`, so

  `(f/V)' = (y_top^D · eval(expEliminate)) / V²`   (the identity `expEliminate_wronskian_numerator`),

whose zeros — since `y_top^D ≠ 0` and `V² ≠ 0` off the bad set — are exactly the zeros of `expEliminate`.
The bad set is `{c_D = 0}` (there `V` degenerates), split off by `zero_count_bound_by_deriv_with_bad` exactly
as in the log arm. The vehicle-derivative-to-Wronskian field step is the **same** `wronskian_field_ne`.

Requires `y_top ≠ 0` on `(a,b)` (exp non-vanishing — discharged later from the encoder's positivity, like the
log arm's `c_D`-partition supplies `c_D ≠ 0` between its zeros). Grounded in `rolle`; no
`zero_count_bound_classical`.
-/

namespace MachLib.PfaffianExpWronskian

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpEliminate
open MachLib.PfaffianLogLead

/-- Sign-agnostic Wronskian field step (local copy — the log arm's is `private`). From the
reciprocal-vehicle derivative-zero equation, recover `cDv·A − cDp·B = 0`. -/
private theorem wronskian_field_ne (A B cDv cDp : Real) (hcDne : cDv ≠ 0)
    (h : A * (1 / cDv) + B * (-cDp / (cDv * cDv)) = 0) : cDv * A - cDp * B = 0 := by
  have hsq : cDv * cDv ≠ 0 := MachLib.Real.mul_ne_zero hcDne hcDne
  have h2 : (cDv * cDv) * (A * (1 / cDv)) + (cDv * cDv) * (B * (-cDp / (cDv * cDv))) = 0 := by
    rw [← Real.mul_distrib, h, Real.mul_zero]
  rw [show (cDv * cDv) * (A * (1 / cDv)) = (cDv * A) * (cDv * (1 / cDv)) from by mach_ring,
      MachLib.Real.mul_div_cancel_left hcDne,
      show (cDv * cDv) * (B * (-cDp / (cDv * cDv))) = B * ((cDv * cDv) * (-cDp / (cDv * cDv))) from by mach_ring,
      MachLib.Real.mul_div_cancel_left hsq] at h2
  have h3 : (cDv * A) * 1 + B * (-cDp) = cDv * A - cDp * B := by mach_ring
  rw [h3] at h2; exact h2

/-- **Chain-derivative of an exp power** (structural). For an exp top (`relations top = G·y_top`),
`chainTotalDeriv` of `y_top^D` evaluates to `D·G·y_top^D` — the polynomial form of `(y_top^D)' =
D·y_top^(D-1)·(G·y_top) = D·G·y_top^D`. Induction on `D`: the succ step uses
`cTD(y_top·y_top^k) = (G·y_top)·y_top^k + y_top·cTD(y_top^k)` and `natCast (k+1) = natCast k + 1`. -/
theorem eval_cTD_powY {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top)) (D : Nat)
    (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (chainTotalDeriv c (MultiPoly.pow (MultiPoly.varY top) D)) x env
      = natCast D * MultiPoly.eval G x env
          * MultiPoly.eval (MultiPoly.pow (MultiPoly.varY top) D) x env := by
  induction D with
  | zero =>
    show MultiPoly.eval (MultiPoly.const 0) x env
        = natCast 0 * MultiPoly.eval G x env * MultiPoly.eval (MultiPoly.pow (MultiPoly.varY top) 0) x env
    rw [MultiPoly.eval_const, MachLib.Real.natCast_zero]; mach_ring
  | succ k ih =>
    show MultiPoly.eval (MultiPoly.add
        (MultiPoly.mul (chainTotalDeriv c (MultiPoly.varY top)) (MultiPoly.pow (MultiPoly.varY top) k))
        (MultiPoly.mul (MultiPoly.varY top) (chainTotalDeriv c (MultiPoly.pow (MultiPoly.varY top) k)))) x env
      = natCast (k + 1) * MultiPoly.eval G x env
          * MultiPoly.eval (MultiPoly.pow (MultiPoly.varY top) (k + 1)) x env
    rw [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul,
        show chainTotalDeriv c (MultiPoly.varY top) = c.relations top from rfl, h_reltop,
        MultiPoly.eval_mul, ih, MachLib.Real.natCast_succ, MultiPoly.eval_pow_succ]
    mach_ring

/-- **The exp-Wronskian numerator identity** (★). With `V = y_top^D · c_D` (`D = degreeY_top p`,
`c_D = leadingCoeffY top p`), the Wronskian numerator `V·(cTD p) − (cTD V)·p` equals `y_top^D ·
expEliminate`. This is why the vehicle `f/V` has critical points exactly at the zeros of `expEliminate`
(after dividing out the nonzero `y_top^D`). Pure `eval` identity: expand `cTD V`, substitute
`eval_cTD_powY` and the `chainReduce`/`expEliminate` definitions, then `mach_ring`. -/
theorem expEliminate_wronskian_numerator {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (p : MultiPoly N) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p))
        (MultiPoly.leadingCoeffY top p)) x env * MultiPoly.eval (chainTotalDeriv c p) x env
      - MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul
          (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p))
          (MultiPoly.leadingCoeffY top p))) x env * MultiPoly.eval p x env
      = MultiPoly.eval (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p)) x env
          * MultiPoly.eval (expEliminate c G top p) x env := by
  have hV : MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul
        (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p))) x env
      = MultiPoly.eval (chainTotalDeriv c (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p))) x env
          * MultiPoly.eval (MultiPoly.leadingCoeffY top p) x env
        + MultiPoly.eval (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p)) x env
          * MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env := by
    show MultiPoly.eval (MultiPoly.add
        (MultiPoly.mul (chainTotalDeriv c (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p)))
          (MultiPoly.leadingCoeffY top p))
        (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p))
          (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)))) x env = _
    rw [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul]
  rw [hV, eval_cTD_powY c G top h_reltop (MultiPoly.degreeY top p) x env]
  show _ = MultiPoly.eval (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p)) x env
      * MultiPoly.eval (MultiPoly.sub
          (MultiPoly.mul (MultiPoly.leadingCoeffY top p)
            (chainReduce c (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) p))
          (MultiPoly.mul p (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)))) x env
  show _ = MultiPoly.eval (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p)) x env
      * MultiPoly.eval (MultiPoly.sub
          (MultiPoly.mul (MultiPoly.leadingCoeffY top p)
            (MultiPoly.sub (chainTotalDeriv c p)
              (MultiPoly.mul (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) p)))
          (MultiPoly.mul p (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)))) x env
  rw [MultiPoly.eval_mul, MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_sub, MultiPoly.eval_mul,
      MultiPoly.eval_mul, MultiPoly.eval_mul, MultiPoly.eval_const]
  mach_mpoly [MultiPoly.eval p x env, MultiPoly.eval G x env,
    MultiPoly.eval (MultiPoly.leadingCoeffY top p) x env,
    MultiPoly.eval (chainTotalDeriv c p) x env,
    MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env,
    MultiPoly.eval (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p)) x env,
    natCast (MultiPoly.degreeY top p)]

/-- `eval` of a `y`-power is nonzero when the base is (product of nonzeros). -/
theorem eval_pow_ne_zero {N : Nat} (q : MultiPoly N) (x : Real) (env : Fin N → Real)
    (hq : MultiPoly.eval q x env ≠ 0) :
    ∀ k : Nat, MultiPoly.eval (MultiPoly.pow q k) x env ≠ 0
  | 0 => by rw [MultiPoly.eval_pow_zero]; exact MachLib.Real.one_ne_zero
  | k + 1 => by rw [MultiPoly.eval_pow_succ]; exact MachLib.Real.mul_ne_zero hq (eval_pow_ne_zero q x env hq k)

/-- **B3 — the exp-Wronskian vehicle count (full, partition assembled).** On `(a,b)` where the exp variable
`y_top` is non-vanishing, `#zeros(pfaffianChainFn c p) ≤ Ne + K + 1`, where `Ne` bounds the zeros of
`expEliminate c G top p` and `K` bounds the zeros of `c_D = leadingCoeffY top p`. Exp analog of
`log_wronskian_reduce_full`: reciprocal vehicle `f·(1/V)` with `V = y_top^D·c_D`, bad set `{c_D = 0}`, the
critical points identified with the zeros of `expEliminate` via `expEliminate_wronskian_numerator` +
`wronskian_field_ne` (dividing out `y_top^D ≠ 0`). -/
theorem expEliminate_reduce_full {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (p : MultiPoly N) (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (hyt : ∀ z, a < z → z < b → MultiPoly.eval (MultiPoly.varY top) z (c.chainValues z) ≠ 0)
    (Ne : Nat)
    (heN : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ (pfaffianChainFn c (expEliminate c G top p)).eval z = 0) →
        zeros'.length ≤ Ne)
    (K : Nat)
    (hcDzero : ∀ zs : List Real, zs.Nodup →
        (∀ z ∈ zs, a < z ∧ z < b ∧
          MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0) → zs.length ≤ K) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros_f.length ≤ Ne + K + 1 := by
  -- eval of V := y_top^D · c_D is nonzero off the bad set (c_D ≠ 0), using y_top ≠ 0
  have hVne : ∀ z, a < z → z < b →
      MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) ≠ 0 →
      MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p))
        (MultiPoly.leadingCoeffY top p)) z (c.chainValues z) ≠ 0 := by
    intro z hza hzb hcDne
    rw [MultiPoly.eval_mul]
    exact MachLib.Real.mul_ne_zero
      (eval_pow_ne_zero (MultiPoly.varY top) z (c.chainValues z) (hyt z hza hzb) _) hcDne
  intro zeros_f hnd hz
  refine zero_count_bound_by_deriv_with_bad
    (fun z => (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval
        (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p))
          (MultiPoly.leadingCoeffY top p)) z (c.chainValues z)))
    (fun z => MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0)
    a b hab ?_ Ne K ?_ hcDzero zeros_f hnd ?_
  · -- differentiability off the bad set
    intro w hwa hwb hbad
    exact ⟨_, HasDerivAt_mul (pfaffianChainFn c p).eval
      (fun y => 1 / MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
        (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p)) y (c.chainValues y)) _ _ w
      (hasDerivAt_eval_natural (pfaffianChainFn c p) w (hcoh w hwa hwb))
      (HasDerivAt_inv (fun y => MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
          (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p)) y (c.chainValues y))
        (MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
          (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p))) w (c.chainValues w)) w
        (hVne w hwa hwb hbad) (multiPolyHasDerivAt_eval_with_chain c
          (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top) (MultiPoly.degreeY top p))
            (MultiPoly.leadingCoeffY top p)) w (hcoh w hwa hwb)))⟩
  · -- critical points off bad set ⇒ zeros of expEliminate
    intro zs hnd' hz'
    apply heN zs hnd'
    intro z hzmem
    obtain ⟨hza, hzb, hnbad, f'', hvd, hf''0⟩ := hz' z hzmem
    refine ⟨hza, hzb, ?_⟩
    have hcDne_z : MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) ≠ 0 := hnbad
    have hVne_z := hVne z hza hzb hcDne_z
    have hinv := HasDerivAt_inv (fun y => MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
        (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p)) y (c.chainValues y))
      (MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
        (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p))) z (c.chainValues z)) z
      hVne_z (multiPolyHasDerivAt_eval_with_chain c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
        (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p)) z (hcoh z hza hzb))
    have hvehd := HasDerivAt_mul (pfaffianChainFn c p).eval
      (fun y => 1 / MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
        (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p)) y (c.chainValues y)) _ _ z
      (hasDerivAt_eval_natural (pfaffianChainFn c p) z (hcoh z hza hzb)) hinv
    have huniq := HasDerivAt_unique _ _ _ z hvd hvehd
    rw [hf''0] at huniq
    -- wronskian_field_ne: V·(cTD p) − (cTD V)·p = 0
    have hwron : MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
            (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p)) z (c.chainValues z)
          * MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
        - MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
            (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p))) z (c.chainValues z)
          * MultiPoly.eval p z (c.chainValues z) = 0 :=
      wronskian_field_ne
        (MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z))
        (MultiPoly.eval p z (c.chainValues z))
        (MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
          (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p)) z (c.chainValues z))
        (MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY top)
          (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p))) z (c.chainValues z))
        hVne_z huniq.symm
    -- bridge via (★): numerator = y_top^D · expEliminate; divide out y_top^D ≠ 0
    rw [expEliminate_wronskian_numerator c G top h_reltop p z (c.chainValues z)] at hwron
    have hpwne := eval_pow_ne_zero (MultiPoly.varY top) z (c.chainValues z) (hyt z hza hzb)
      (MultiPoly.degreeY top p)
    show (pfaffianChainFn c (expEliminate c G top p)).eval z = 0
    have hpf : (pfaffianChainFn c (expEliminate c G top p)).eval z
        = MultiPoly.eval (expEliminate c G top p) z (c.chainValues z) := rfl
    rw [hpf]
    exact mul_eq_zero_of_factor_ne_zero hpwne hwron
  · -- the original zeros satisfy the vehicle-zero property
    intro z hzmem
    obtain ⟨hza, hzb, hpz⟩ := hz z hzmem
    refine ⟨hza, hzb, ?_⟩
    show (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval (MultiPoly.mul (MultiPoly.pow
      (MultiPoly.varY top) (MultiPoly.degreeY top p)) (MultiPoly.leadingCoeffY top p)) z (c.chainValues z)) = 0
    rw [hpz]; exact Real.zero_mul _

end MachLib.PfaffianExpWronskian
