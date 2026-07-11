import MachLib.PfaffianChain
import MachLib.PfaffianGeneralReduce

/-!
# Format-dependent degree growth of `chainTotalDeriv` (general Pfaffian explicit bound, step 3 §1)

First foundational brick of the general single-variable Pfaffian *explicit* bound
(`monogate-research/roadmap/pfaffian-general-explicit-bound-design.md`). The design's step-1 go/no-go
(§3′) concluded, on paper, that the general reduce grows degrees not by `≤ +1` (the concrete tower's
special case) but by the chain's **Khovanskii format** — the degrees of its relation polynomials. This
file machine-checks that conclusion for the `degreeX` direction.

`degreeX_chainTotalDeriv_le` (`PfaffianChain.lean:524`) proves `chainTotalDeriv` never raises `degreeX`
*when the relations are x-free* (`degreeX (relations j) = 0`) — exactly the tower hypothesis. Here we
drop that hypothesis and pay the format: if every relation has `degreeX ≤ α`, then `chainTotalDeriv`
raises `degreeX` by at most `α`. This is the honest general shape (a chain-uniform bound cannot exist —
arbitrary relation degree ⇒ arbitrary growth), and the `α = 0` instance recovers the existing lemma.
-/

open MachLib.MultiPolyMod

namespace MachLib.PfaffianChainMod.PfaffianFn

/-- **Format-dependent `degreeX` growth of `chainTotalDeriv`.** If every chain relation has
`degreeX ≤ α`, then `chainTotalDeriv chain p` has `degreeX ≤ degreeX p + α`. The `varY j` arm is where
the format is paid (`chainTotalDeriv (varY j) = relations j`); `const`/`varX` cost nothing and
`add`/`sub`/`mul` propagate the `+α` through `Nat.max` / `+`. Structural induction on `p`, mirroring
`degreeX_chainTotalDeriv_le` with `= 0` replaced by `≤ α`. -/
theorem degreeX_chainTotalDeriv_le_format {n : Nat} (chain : PfaffianChain n) (α : Nat)
    (h_fmt : ∀ j : Fin n, MultiPoly.degreeX (chain.relations j) ≤ α) :
    ∀ p : MultiPoly n,
      MultiPoly.degreeX (chainTotalDeriv chain p) ≤ MultiPoly.degreeX p + α
  | .const c => by
    show MultiPoly.degreeX (MultiPoly.const 0 : MultiPoly n)
         ≤ MultiPoly.degreeX (MultiPoly.const c : MultiPoly n) + α
    simp only [MultiPoly.degreeX_const]
    omega
  | .varX => by
    show MultiPoly.degreeX (MultiPoly.const 1 : MultiPoly n)
         ≤ MultiPoly.degreeX (MultiPoly.varX : MultiPoly n) + α
    simp only [MultiPoly.degreeX_const, MultiPoly.degreeX_varX]
    omega
  | .varY j => by
    show MultiPoly.degreeX (chain.relations j)
         ≤ MultiPoly.degreeX (MultiPoly.varY j : MultiPoly n) + α
    simp only [MultiPoly.degreeX_varY]
    have := h_fmt j
    omega
  | .add p q => by
    show Nat.max (MultiPoly.degreeX (chainTotalDeriv chain p))
                 (MultiPoly.degreeX (chainTotalDeriv chain q))
         ≤ Nat.max (MultiPoly.degreeX p) (MultiPoly.degreeX q) + α
    have hp := degreeX_chainTotalDeriv_le_format chain α h_fmt p
    have hq := degreeX_chainTotalDeriv_le_format chain α h_fmt q
    apply Nat.max_le.mpr
    exact ⟨Nat.le_trans hp (Nat.add_le_add_right (Nat.le_max_left _ _) α),
           Nat.le_trans hq (Nat.add_le_add_right (Nat.le_max_right _ _) α)⟩
  | .sub p q => by
    show Nat.max (MultiPoly.degreeX (chainTotalDeriv chain p))
                 (MultiPoly.degreeX (chainTotalDeriv chain q))
         ≤ Nat.max (MultiPoly.degreeX p) (MultiPoly.degreeX q) + α
    have hp := degreeX_chainTotalDeriv_le_format chain α h_fmt p
    have hq := degreeX_chainTotalDeriv_le_format chain α h_fmt q
    apply Nat.max_le.mpr
    exact ⟨Nat.le_trans hp (Nat.add_le_add_right (Nat.le_max_left _ _) α),
           Nat.le_trans hq (Nat.add_le_add_right (Nat.le_max_right _ _) α)⟩
  | .mul p q => by
    show Nat.max (MultiPoly.degreeX (chainTotalDeriv chain p) + MultiPoly.degreeX q)
                 (MultiPoly.degreeX p + MultiPoly.degreeX (chainTotalDeriv chain q))
         ≤ (MultiPoly.degreeX p + MultiPoly.degreeX q) + α
    have hp := degreeX_chainTotalDeriv_le_format chain α h_fmt p
    have hq := degreeX_chainTotalDeriv_le_format chain α h_fmt q
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · omega
    · omega

/-- **Sanity check: the `α = 0` instance is exactly the tower lemma's hypothesis.** With x-free
relations (`degreeX (relations j) = 0`) the format bound gives `degreeX (chainTotalDeriv chain p) ≤
degreeX p` — recovering `degreeX_chainTotalDeriv_le`. -/
theorem degreeX_chainTotalDeriv_le_of_format_zero {n : Nat} (chain : PfaffianChain n)
    (h_rel_x : ∀ j : Fin n, MultiPoly.degreeX (chain.relations j) = 0) (p : MultiPoly n) :
    MultiPoly.degreeX (chainTotalDeriv chain p) ≤ MultiPoly.degreeX p := by
  have h := degreeX_chainTotalDeriv_le_format chain 0 (fun j => Nat.le_of_eq (h_rel_x j)) p
  omega

/-- **Format-dependent `degreeY i` growth of `chainTotalDeriv`** (any chain level `i`). If every chain
relation has `degreeY i ≤ β`, then `chainTotalDeriv chain p` has `degreeY i ≤ degreeY i p + β`. Same
structural induction as the `degreeX` version; the `varY k` arm needs no case split on `i = k` —
`degreeY i (chainTotalDeriv (varY k)) = degreeY i (relations k) ≤ β ≤ degreeY i (varY k) + β`
uniformly. Together with `degreeX_chainTotalDeriv_le_format` this is the per-variable degree-tower
input the general reduce's descent budget consumes; the top level's *exact* preservation is the sharper
`degreeYtop_cTD_eq_gen`. -/
theorem degreeY_chainTotalDeriv_le_format {n : Nat} (chain : PfaffianChain n) (i : Fin n) (β : Nat)
    (h_fmt : ∀ k : Fin n, MultiPoly.degreeY i (chain.relations k) ≤ β) :
    ∀ p : MultiPoly n,
      MultiPoly.degreeY i (chainTotalDeriv chain p) ≤ MultiPoly.degreeY i p + β
  | .const c => by
    show MultiPoly.degreeY i (MultiPoly.const 0 : MultiPoly n)
         ≤ MultiPoly.degreeY i (MultiPoly.const c : MultiPoly n) + β
    simp only [MultiPoly.degreeY_const]
    omega
  | .varX => by
    show MultiPoly.degreeY i (MultiPoly.const 1 : MultiPoly n)
         ≤ MultiPoly.degreeY i (MultiPoly.varX : MultiPoly n) + β
    simp only [MultiPoly.degreeY_const, MultiPoly.degreeY_varX]
    omega
  | .varY k => by
    show MultiPoly.degreeY i (chain.relations k)
         ≤ MultiPoly.degreeY i (MultiPoly.varY k : MultiPoly n) + β
    have := h_fmt k
    omega
  | .add p q => by
    show Nat.max (MultiPoly.degreeY i (chainTotalDeriv chain p))
                 (MultiPoly.degreeY i (chainTotalDeriv chain q))
         ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + β
    have hp := degreeY_chainTotalDeriv_le_format chain i β h_fmt p
    have hq := degreeY_chainTotalDeriv_le_format chain i β h_fmt q
    apply Nat.max_le.mpr
    exact ⟨Nat.le_trans hp (Nat.add_le_add_right (Nat.le_max_left _ _) β),
           Nat.le_trans hq (Nat.add_le_add_right (Nat.le_max_right _ _) β)⟩
  | .sub p q => by
    show Nat.max (MultiPoly.degreeY i (chainTotalDeriv chain p))
                 (MultiPoly.degreeY i (chainTotalDeriv chain q))
         ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) + β
    have hp := degreeY_chainTotalDeriv_le_format chain i β h_fmt p
    have hq := degreeY_chainTotalDeriv_le_format chain i β h_fmt q
    apply Nat.max_le.mpr
    exact ⟨Nat.le_trans hp (Nat.add_le_add_right (Nat.le_max_left _ _) β),
           Nat.le_trans hq (Nat.add_le_add_right (Nat.le_max_right _ _) β)⟩
  | .mul p q => by
    show Nat.max (MultiPoly.degreeY i (chainTotalDeriv chain p) + MultiPoly.degreeY i q)
                 (MultiPoly.degreeY i p + MultiPoly.degreeY i (chainTotalDeriv chain q))
         ≤ (MultiPoly.degreeY i p + MultiPoly.degreeY i q) + β
    have hp := degreeY_chainTotalDeriv_le_format chain i β h_fmt p
    have hq := degreeY_chainTotalDeriv_le_format chain i β h_fmt q
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · omega
    · omega

/-! ## The reduce's degree towers — `chainReduce c m p = chainTotalDeriv c p − m·p`

These combine the `chainTotalDeriv` bounds above with the multiplier term `m·p`. The reduce's per-level
growth is bounded by the format `α`/`β` provided the multiplier `m` is itself format-bounded — which it
is in the descent, where `m = degreeY_top(p)·G_top` and `G_top` is a chain-relation cofactor. These are
the exact per-variable growth facts the descent budget's per-level cap consumes (chainN §6, now general). -/

open MachLib.PfaffianGeneralReduce

/-- **Format-dependent `degreeX` growth of the general reduce.** With every relation and the multiplier
`m` of `degreeX ≤ α`, `chainReduce chain m p` grows `degreeX` by at most `α`. -/
theorem degreeX_chainReduce_le_format {n : Nat} (chain : PfaffianChain n) (α : Nat) (m p : MultiPoly n)
    (h_fmt : ∀ k : Fin n, MultiPoly.degreeX (chain.relations k) ≤ α)
    (h_m : MultiPoly.degreeX m ≤ α) :
    MultiPoly.degreeX (chainReduce chain m p) ≤ MultiPoly.degreeX p + α := by
  show Nat.max (MultiPoly.degreeX (chainTotalDeriv chain p))
               (MultiPoly.degreeX m + MultiPoly.degreeX p)
       ≤ MultiPoly.degreeX p + α
  have hcTD := degreeX_chainTotalDeriv_le_format chain α h_fmt p
  apply Nat.max_le.mpr
  refine ⟨?_, ?_⟩
  · omega
  · omega

/-- **Format-dependent `degreeY i` growth of the general reduce.** With every relation and the
multiplier `m` of `degreeY i ≤ β`, `chainReduce chain m p` grows `degreeY i` by at most `β`. -/
theorem degreeY_chainReduce_le_format {n : Nat} (chain : PfaffianChain n) (i : Fin n) (β : Nat)
    (m p : MultiPoly n)
    (h_fmt : ∀ k : Fin n, MultiPoly.degreeY i (chain.relations k) ≤ β)
    (h_m : MultiPoly.degreeY i m ≤ β) :
    MultiPoly.degreeY i (chainReduce chain m p) ≤ MultiPoly.degreeY i p + β := by
  show Nat.max (MultiPoly.degreeY i (chainTotalDeriv chain p))
               (MultiPoly.degreeY i m + MultiPoly.degreeY i p)
       ≤ MultiPoly.degreeY i p + β
  have hcTD := degreeY_chainTotalDeriv_le_format chain i β h_fmt p
  apply Nat.max_le.mpr
  refine ⟨?_, ?_⟩
  · omega
  · omega

/-! ## The descent multiplier is format-bounded

In the descent the reduce multiplier is `m = const (natCast (degreeY_top p)) · G`, where `G` is the
exp-top cofactor (`relations top = G · varY top`, from `IsExpChain`). These lemmas show `m` is bounded
by the same format as the relations, so `h_m` in the reduce degree towers is discharged automatically
for the actual descent — the scalar `const` factor adds nothing, and the `varY top` factor in the
relation only *helps* the inequality. -/

/-- `degreeX` of the descent multiplier `const c · G` is `≤ degreeX (relations top) = degreeX (G · varY
top)`: the scalar costs nothing (`degreeX (const c) = 0`) and `varY top` is x-free. -/
theorem degreeX_expMultiplier_le_relTop {n : Nat} (c : MachLib.Real) (G : MultiPoly n) (top : Fin n) :
    MultiPoly.degreeX (MultiPoly.mul (MultiPoly.const c) G)
      ≤ MultiPoly.degreeX (MultiPoly.mul G (MultiPoly.varY top)) := by
  show MultiPoly.degreeX (MultiPoly.const c) + MultiPoly.degreeX G
       ≤ MultiPoly.degreeX G + MultiPoly.degreeX (MultiPoly.varY top)
  simp only [MultiPoly.degreeX_const]
  omega

/-- `degreeY i` of the descent multiplier `const c · G` is `≤ degreeY i (relations top) = degreeY i
(G · varY top)`: the scalar costs nothing and the extra `varY top` factor only raises the right side. -/
theorem degreeY_expMultiplier_le_relTop {n : Nat} (c : MachLib.Real) (G : MultiPoly n) (top i : Fin n) :
    MultiPoly.degreeY i (MultiPoly.mul (MultiPoly.const c) G)
      ≤ MultiPoly.degreeY i (MultiPoly.mul G (MultiPoly.varY top)) := by
  show MultiPoly.degreeY i (MultiPoly.const c) + MultiPoly.degreeY i G
       ≤ MultiPoly.degreeY i G + MultiPoly.degreeY i (MultiPoly.varY top)
  simp only [MultiPoly.degreeY_const]
  omega

/-! ## The reduce multiplier `gradedMultStep` — generic degree bounds (depth-N multiplier)

`gradedMultStep G top p mLow = (natCast (degreeY top p))·G + mLow`. The depth-N reduce multiplier is
`gradedMultStep G ⟨top⟩ p (liftLastY m')` (`m'` the recursive depth-below multiplier), so its degree is
`≤ max (degree G) (degree mLow)` — the generic "combine" step of the recursive multiplier degree bound.
(`degree G ≤ degree (relations top) ≤ format`; `degree mLow` recurses.) The order-2 `bound2Mult` bounds
are the `N=2` instances. -/

/-- `degreeX (gradedMultStep G top p mLow) ≤ max (degreeX G) (degreeX mLow)` — the scalar `natCast` factor
adds nothing to `degreeX`. -/
theorem degreeX_gradedMultStep_le {N : Nat} (G : MultiPoly N) (top : Fin N) (p mLow : MultiPoly N) :
    MultiPoly.degreeX (MachLib.PfaffianGeneralReduce.gradedMultStep G top p mLow)
      ≤ Nat.max (MultiPoly.degreeX G) (MultiPoly.degreeX mLow) := by
  show Nat.max (MultiPoly.degreeX (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p)))
      + MultiPoly.degreeX G) (MultiPoly.degreeX mLow)
      ≤ Nat.max (MultiPoly.degreeX G) (MultiPoly.degreeX mLow)
  rw [MultiPoly.degreeX_const, Nat.zero_add]
  exact Nat.le_refl _

/-- `degreeY i (gradedMultStep G top p mLow) ≤ max (degreeY i G) (degreeY i mLow)`. -/
theorem degreeY_gradedMultStep_le {N : Nat} (G : MultiPoly N) (top i : Fin N) (p mLow : MultiPoly N) :
    MultiPoly.degreeY i (MachLib.PfaffianGeneralReduce.gradedMultStep G top p mLow)
      ≤ Nat.max (MultiPoly.degreeY i G) (MultiPoly.degreeY i mLow) := by
  show Nat.max (MultiPoly.degreeY i (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p)))
      + MultiPoly.degreeY i G) (MultiPoly.degreeY i mLow)
      ≤ Nat.max (MultiPoly.degreeY i G) (MultiPoly.degreeY i mLow)
  rw [MultiPoly.degreeY_const, Nat.zero_add]
  exact Nat.le_refl _

end MachLib.PfaffianChainMod.PfaffianFn
