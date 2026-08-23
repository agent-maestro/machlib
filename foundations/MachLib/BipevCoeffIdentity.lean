import MachLib.BipevElimMem

/-!
# From the eliminated coefficient to the count's identity

Step 3, and the last one that is not pure instantiation.

The eliminated coefficient at index `j`, with `top = v = pₘ` and `u = pⱼ`, is

```
C = (Q²·v' + m·D·v)·u  −  v·(Q²·u' + j·D·u)
```

and `cleared_relation_impossible` wants `(u'v − uv')·Q² ≈ Nc·D·(u·v)` with `Nc = (m−j)·1`. Both
sides split into the same four products, and the whole step is recognising that:

```
T₁ = (Q²·v')·u    T₂ = (m·D·v)·u    T₃ = v·(Q²·u')    T₄ = v·(j·D·u)
C ≈ 0   ⟺   T₁ + T₂ ≈ T₃ + T₄   ⟺   T₃ − T₁ ≈ T₂ − T₄
```

with `T₃ − T₁ ≈ Q²·(u'v − uv')` and `T₂ − T₄ ≈ (m−j)·D·u·v`. No new mathematics — `peq_pmul_comm`,
`pmul_assoc_pnorm`, `pnsum_pmul` and `peq_pnsum_sub`, all already proved.

## Two reusable pieces first

`peq_of_psub_nil` and `peq_sub_swap` are stated separately because they are ordinary algebra of
subtraction that this arc has needed repeatedly without naming: "a difference vanishing means the
sides agree", and "`A + B ≈ C + D` gives `C − A ≈ B − D`". Naming them keeps the identity's proof a
chain of recognisable steps rather than a block of `psub` unfolding.
-/

namespace MachLib

open Real

/-! ## Subtraction, named -/

theorem peq_of_psub_nil {A B : List Real} (h : PEq (psub A B) []) : PEq A B :=
  PEq.trans (peq_padd_psub_left A B).symm (peq_padd h (PEq.refl B))

/-- `A + B ≈ C + D` gives `C − A ≈ B − D`. -/
theorem peq_sub_swap {A B C D : List Real} (h : PEq (padd A B) (padd C D)) :
    PEq (psub C A) (psub B D) := by
  refine peq_of_psub_nil ?_
  -- both differences expand to `C + D − A − B`
  have hexp : psub (psub C A) (psub B D) = psub (padd C D) (padd A B) := by
    show padd (padd C (pscale (0 - 1) A))
          (pscale (0 - 1) (padd B (pscale (0 - 1) D)))
        = padd (padd C D) (pscale (0 - 1) (padd A B))
    have hinv : ((0 : Real) - 1) * (0 - 1) = 1 := by mach_ring
    rw [pscale_padd, pscale_pscale, hinv, pscale_one, pscale_padd,
        padd_assoc, padd_assoc,
        padd_left_comm D (pscale (0 - 1) A) (pscale (0 - 1) B),
        padd_comm D (pscale (0 - 1) B)]
  rw [hexp]
  exact PEq.trans (peq_psub h.symm (PEq.refl (padd A B))) (peq_psub_self (padd A B))

/-! ## The four products -/

theorem peq_T1 (QQ u v : List Real) :
    PEq (pmul (pmul QQ (pderiv v)) u) (pmul QQ (pmul u (pderiv v))) :=
  PEq.trans (pmul_assoc_pnorm QQ (pderiv v) u)
    (peq_pmul (PEq.refl QQ) (peq_pmul_comm (pderiv v) u))

theorem peq_T3 (QQ u v : List Real) :
    PEq (pmul v (pmul QQ (pderiv u))) (pmul QQ (pmul (pderiv u) v)) :=
  PEq.trans (peq_pmul_left_comm v QQ (pderiv u))
    (peq_pmul (PEq.refl QQ) (peq_pmul_comm v (pderiv u)))

theorem peq_T2 (D u v : List Real) (n : Nat) :
    PEq (pmul (pnsum n (pmul D v)) u) (pnsum n (pmul D (pmul u v))) := by
  rw [← pnsum_pmul]
  refine peq_pnsum n ?_
  exact PEq.trans (pmul_assoc_pnorm D v u) (peq_pmul (PEq.refl D) (peq_pmul_comm v u))

theorem peq_T4 (D u v : List Real) (n : Nat) :
    PEq (pmul v (pnsum n (pmul D u))) (pnsum n (pmul D (pmul u v))) := by
  refine PEq.trans (peq_pmul_comm v (pnsum n (pmul D u))) ?_
  rw [← pnsum_pmul]
  refine peq_pnsum n ?_
  exact pmul_assoc_pnorm D u v

/-! ## The identity

Both sides are the same four products, rearranged. -/

/-- **The eliminated coefficient, in the form the count consumes.** `C ≈ 0` at index `j` gives
exactly `(u'v − uv')·Q² ≈ (m−j)·1·D·(u·v)`. -/
theorem coeff_identity {QQ D u v : List Real} {m j : Nat} (hjm : j ≤ m)
    (hC : PEq (psub (pmul (padd (pmul QQ (pderiv v)) (pnsum m (pmul D v))) u)
                    (pmul v (padd (pmul QQ (pderiv u)) (pnsum j (pmul D u))))) []) :
    PEq (pmul (psub (pmul (pderiv u) v) (pmul u (pderiv v))) QQ)
        (pmul (pmul (pnsum (m - j) [1]) D) (pmul u v)) := by
  -- split both bracketed factors: exact, by left/right distributivity
  rw [pmul_padd_left, pmul_padd_right] at hC
  -- T₁ + T₂ ≈ T₃ + T₄, hence T₃ − T₁ ≈ T₂ − T₄
  have hswap := peq_sub_swap (peq_of_psub_nil hC)
  -- the goal's left side is T₃ − T₁
  have hleft : PEq (pmul (psub (pmul (pderiv u) v) (pmul u (pderiv v))) QQ)
      (psub (pmul v (pmul QQ (pderiv u))) (pmul (pmul QQ (pderiv v)) u)) := by
    refine PEq.trans (peq_pmul_comm _ QQ) ?_
    rw [pmul_psub_right]
    exact peq_psub (peq_T3 QQ u v).symm (peq_T1 QQ u v).symm
  -- and the right side is T₂ − T₄
  have hright : PEq (pmul (pmul (pnsum (m - j) [1]) D) (pmul u v))
      (psub (pmul (pnsum m (pmul D v)) u) (pmul v (pnsum j (pmul D u)))) := by
    refine PEq.trans (peq_pmul (peq_pnsum_const (m - j) D).symm (PEq.refl (pmul u v))) ?_
    rw [← pnsum_pmul]
    refine PEq.trans (peq_pnsum_sub hjm (pmul D (pmul u v))).symm ?_
    exact peq_psub (peq_T2 D u v m).symm (peq_T4 D u v j).symm
  exact PEq.trans hleft (PEq.trans hswap hright.symm)

end MachLib
