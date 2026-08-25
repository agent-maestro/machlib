import MachLib.EMLDeclampUniform
import MachLib.EMLExplicitBoundEncoder
import MachLib.EMLBarrierBound

/-!
# The per-interval bound already exists; only non-vanishing is left

`(cz)` left the route needing "per-interval bounds on the trees `declamp` actually produces". Those
bounds are already in the corpus. `EMLExplicitBound.enc_combinedBound` takes an `EMLTree`, a context
chain, and `LogArgPosOn t (Icc a b)`, and returns an **explicit** zero bound

```
combinedBoundE (len t N) (enc t chain).1 (encTags t chain tags) p
```

which mentions **no interval** — it is a function of the tree and the barrier alone. It carries no
descent hypothesis (unlike `eml_eval_boundedZeros`, which takes `hdescent`), and its footprint cites
`analytic_finite_zeros_compact` and `rolle_ct`, both already disclosed in the `AxiomLedger`, and
**not** the deleted `zero_count_bound_classical`.

So the remaining input for the sign route collapses from *"bound the zeros"* to

> **`t.eval` is not identically zero on any interval beyond the ray.**

That is `enc_combinedBound`'s own `hne`, and it is a condition the route needs regardless: a function
vanishing on an interval has infinitely many zeros there and no bound of any kind.

## The endpoint shift, a third time

`enc_combinedBound` wants positivity on the **closed** `Icc a b`; `declamp_logArgPos` supplies it on
the **open** `(a', b')`. So the declamping is done on `(a − 1, b + 1)` and the bound applied on
`(a, b)`, which sits strictly inside. The ray therefore starts at `X₀ + 1`. Same shape as
`ray_shift_nbhd` and as the `R + 1` seed in `EMLZeroBoundRay` — the third place in this arc where a
closed/open mismatch costs exactly one unit.

Widening also keeps the finiteness argument intact: `declamp t (a−1) (b+1)` is still a member of
`declampVariants t`, so the maximum is still taken over the same finite list.
-/

namespace MachLib

open Real
open MachLib.EMLExplicitBound
open MachLib.MultiPolyMod MachLib.PfaffianChainMod MachLib.PfaffianGeneralReduce

/-- Positivity on a strictly larger open interval gives it on the closed one. -/
theorem logArgPosOn_Icc_of_logArgPos (t : EMLTree) (a b a' b' : Real)
    (hsub : ∀ x : Real, a ≤ x → x ≤ b → a' < x ∧ x < b')
    (h : LogArgPos t a' b') : LogArgPosOn t (Icc a b) := by
  induction t with
  | const c => exact True.intro
  | var => exact True.intro
  | eml t1 t2 ih1 ih2 =>
      obtain ⟨h1, h2, hpos⟩ := h
      refine ⟨ih1 h1, ih2 h2, fun x hx => ?_⟩
      obtain ⟨hx1, hx2⟩ := hsub x hx.1 hx.2
      exact hpos x hx1 hx2

/-- The explicit bound the encoder gives a **fixed** tree — no interval in it. -/
noncomputable def encBound (v : EMLTree) : Nat :=
  combinedBoundE (len v 0) (enc v emlEmptyChain).1 (encTags v emlEmptyChain ())
    (enc v emlEmptyChain).2

/-- **`encBound` bounds the tree's own zeros.** The empty context chain discharges every chain-side
hypothesis over `Fin 0`, and `enc_eval` bridges the barrier to `v.eval`. -/
theorem encBound_bounds (v : EMLTree) (a b : Real) (hab : a < b)
    (hlog : LogArgPosOn v (Icc a b))
    (hne : ∃ z, a < z ∧ z < b ∧ v.eval z ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ v.eval z = 0) → zeros.length ≤ encBound v := by
  have hbridge : ∀ z, (pfaffianChainFn (enc v emlEmptyChain).1 (enc v emlEmptyChain).2).eval z
      = v.eval z := fun z => enc_eval v emlEmptyChain z
  have hne' : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn (enc v emlEmptyChain).1 (enc v emlEmptyChain).2).eval z ≠ 0 := by
    obtain ⟨z, hza, hzb, hz0⟩ := hne
    exact ⟨z, hza, hzb, by rw [hbridge z]; exact hz0⟩
  have hb := enc_combinedBound v emlEmptyChain () a b hab
    trivial trivial (fun i _ _ => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlog (enc v emlEmptyChain).2 hne'
  intro zeros hnd hz
  exact hb zeros hnd (fun z hzm => by
    obtain ⟨ha, hbb, h0⟩ := hz z hzm
    exact ⟨ha, hbb, by rw [hbridge z]; exact h0⟩)

/-! ## The assembly -/

private theorem sub_one_lt_of_le {a x : Real} (h : a ≤ x) : a - 1 < x := by
  have v := add_lt_add_left zero_lt_one_ax (a - 1)
  have l : a - 1 + 0 = a - 1 := by mach_ring
  have r : a - 1 + 1 = a := by mach_ring
  rw [l, r] at v
  exact lt_of_lt_of_le v h

private theorem lt_add_one_of_le {b x : Real} (h : x ≤ b) : x < b + 1 := by
  have v := add_lt_add_left zero_lt_one_ax b
  have l : b + 0 = b := by mach_ring
  rw [l] at v
  exact lt_of_le_of_lt h v

private theorem le_sub_one_of_add_one_le {X a : Real} (h : X + 1 ≤ a) : X ≤ a - 1 := by
  have v := add_le_add_wit h (le_refl (-(1 : Real)))
  have e1 : X + 1 + -(1 : Real) = X := by mach_ring
  have e2 : a + -(1 : Real) = a - 1 := by mach_ring
  rw [e1, e2] at v; exact v

/-- **The remaining input, isolated.** Given sign-definiteness at every node (which the depth
induction supplies) and *non-vanishing on every interval beyond the ray*, the tree has one zero bound
serving all of them.

Everything else is discharged here: the declamped tree is coherent-encodable (`enc_combinedBound`),
its bound mentions no interval, and the finitely many variants are collapsed by a maximum. -/
theorem uniformZeroBoundFrom_of_nonvanishing (t : EMLTree) (X₀ : Real)
    (hst : ∀ a b : Real, X₀ ≤ a → a < b → LogArgStable t a b)
    (hnv : ∀ a b : Real, X₀ + 1 ≤ a → a < b → ∃ z, a < z ∧ z < b ∧ t.eval z ≠ 0) :
    ∃ N : Nat, UniformZeroBoundFrom t.eval (X₀ + 1) N := by
  refine ⟨listMaxF encBound (declampVariants t), fun a b hXa hab zeros hnd hz => ?_⟩
  have hab' : a - 1 < b + 1 :=
    lt_trans_ax (sub_one_lt_of_le (le_refl a)) (lt_add_one_of_le (le_of_lt hab))
  have hstab : LogArgStable t (a - 1) (b + 1) :=
    hst (a - 1) (b + 1) (le_sub_one_of_add_one_le hXa) hab'
  have heval := declamp_eval t (a - 1) (b + 1) hstab
  have hmem := declamp_mem_variants t (a - 1) (b + 1)
  have hlog : LogArgPosOn (declamp t (a - 1) (b + 1)) (Icc a b) :=
    logArgPosOn_Icc_of_logArgPos _ a b (a - 1) (b + 1)
      (fun x hxa hxb => ⟨sub_one_lt_of_le hxa, lt_add_one_of_le hxb⟩)
      (declamp_logArgPos t (a - 1) (b + 1) hstab)
  have hin : ∀ z : Real, a < z → z < b → (declamp t (a - 1) (b + 1)).eval z = t.eval z :=
    fun z hza hzb => heval z (lt_trans_ax (sub_one_lt_of_le (le_refl a)) hza)
      (lt_trans_ax hzb (lt_add_one_of_le (le_refl b)))
  have hne : ∃ z, a < z ∧ z < b ∧ (declamp t (a - 1) (b + 1)).eval z ≠ 0 := by
    obtain ⟨z, hza, hzb, hz0⟩ := hnv a b hXa hab
    exact ⟨z, hza, hzb, by rw [hin z hza hzb]; exact hz0⟩
  have hb := encBound_bounds (declamp t (a - 1) (b + 1)) a b hab hlog hne
    zeros hnd (fun z hzm => by
      obtain ⟨ha, hbb, h0⟩ := hz z hzm
      exact ⟨ha, hbb, by rw [hin z ha hbb]; exact h0⟩)
  exact Nat.le_trans hb (le_listMaxF encBound _ _ hmem)

/-- **And through the sign machinery.** On the existing obligation, a tree that never vanishes
identically on a far-out interval has a uniform zero bound — hence, by
`eventually_nonzero_of_uniformZeroBoundFrom`, is eventually non-vanishing outright. -/
theorem eventually_nonzero_of_nonvanishing_of_hard (h : SignHardCase) (t : EMLTree)
    (hnv : ∀ X₀ : Real, ∀ a b : Real, X₀ ≤ a → a < b → ∃ z, a < z ∧ z < b ∧ t.eval z ≠ 0) :
    ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x → t.eval x ≠ 0 := by
  obtain ⟨X₀, hX01, hst⟩ := logArgStable_of_evSign (evSign_of_hard h) t
  obtain ⟨N, hN⟩ :=
    uniformZeroBoundFrom_of_nonvanishing t X₀ hst (fun a b hXa hab => hnv (X₀ + 1) a b hXa hab)
  exact eventually_nonzero_of_uniformZeroBoundFrom hN

end MachLib
