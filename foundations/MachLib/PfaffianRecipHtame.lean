import MachLib.PfaffianRecipGrowthSpike
import MachLib.PfaffianChainExtend
import MachLib.IterExpDepthNDegreeY

/-!
# Toward `htame` — the reciprocal-linearity kernel for encoder chains

The `exp_hard` nested-rank descent (Design v2, `roadmap/exp-hard-mixed-measure-port.md`) narrowed the open
crux to one bounded condition, `htame`: for a reciprocal index `i` in the barrier chain, every HIGHER
relation must reference `y_i` to degree ≤ 1 (`degreeY i (relations l) ≤ 1` for `l > i`). The growth spike
already handles the level `i` itself (recip's own square is `+1`, absorbed); `htame` is about the levels
ABOVE it.

Every encoder relation has the shape `coeff · varY_top` (exp/log) or `−coeff · varYₘ²` (recip), with
`coeff = liftLastY (chainTotalDeriv …)` — the `cTD` of an encoded subtree-value. So `htame` reduces to:
**the `cTD` of an encoded value references a descendant recip `y_i` to degree ≤ 1.** The structural reason it
does: an encoded subtree-value never mentions a descendant node's *internal* recip variable — it consumes
that node through its log/exp OUTPUT — so the value is `y_i`-free, and a `y_i`-free polynomial's `cTD` can
only reintroduce `y_i` through the relations (each ≤ 1), never squared.

This file proves that kernel, `degreeY_i_cTD_le_one_of_free`, as pure-degree combinatorics (the log-spike
register). It is the load-bearing step of the `htame` structural induction; what remains is the encoder-side
invariant that feeds it — that encoded values are `y_i`-free for descendant recip `i`, and relations stay
`y_i`-linear — maintained node-by-node through `chainExtend` (documented at the foot).
-/

namespace MachLib.PfaffianRecipHtame

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianExpRecip

/-- **The reciprocal-linearity kernel.** If `p` is `y_i`-free (`degreeY i p = 0`) and every relation
references `y_i` to degree ≤ 1, then `chainTotalDeriv c p` references `y_i` to degree ≤ 1.

The `y_i`-freeness is what keeps the bound at `1` rather than `2`: with no `y_i` in `p`, every `y_i` in
`cTD p` is freshly introduced by a single relation substitution (each ≤ 1), and the product rule never
multiplies two such introductions (one factor stays `y_i`-free). This is exactly the situation of an encoder
coefficient over a descendant recip index. -/
theorem degreeY_i_cTD_le_one_of_free {n : Nat} (c : PfaffianChain n) (i : Fin n)
    (hrel : ∀ l : Fin n, i ≠ l → MultiPoly.degreeY i (c.relations l) ≤ 1) :
    ∀ p : MultiPoly n, MultiPoly.degreeY i p = 0 →
      MultiPoly.degreeY i (chainTotalDeriv c p) ≤ 1
  | .const _, _ => Nat.zero_le _
  | .varX, _ => Nat.zero_le _
  | .varY l, hp => hrel l (fun h => by
      have hh : (if i = l then (1 : Nat) else 0) = 0 := hp
      rw [if_pos h] at hh; omega)
  | .add p q, hp => by
      have hmax : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hp
      have hle : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) ≤ 0 := Nat.le_of_eq hmax
      have hp0 : MultiPoly.degreeY i p = 0 := Nat.le_zero.mp (Nat.max_le.mp hle).1
      have hq0 : MultiPoly.degreeY i q = 0 := Nat.le_zero.mp (Nat.max_le.mp hle).2
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p))
              (MultiPoly.degreeY i (chainTotalDeriv c q)) ≤ 1
      exact Nat.max_le.mpr
        ⟨degreeY_i_cTD_le_one_of_free c i hrel p hp0,
         degreeY_i_cTD_le_one_of_free c i hrel q hq0⟩
  | .sub p q, hp => by
      have hmax : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hp
      have hle : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) ≤ 0 := Nat.le_of_eq hmax
      have hp0 : MultiPoly.degreeY i p = 0 := Nat.le_zero.mp (Nat.max_le.mp hle).1
      have hq0 : MultiPoly.degreeY i q = 0 := Nat.le_zero.mp (Nat.max_le.mp hle).2
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p))
              (MultiPoly.degreeY i (chainTotalDeriv c q)) ≤ 1
      exact Nat.max_le.mpr
        ⟨degreeY_i_cTD_le_one_of_free c i hrel p hp0,
         degreeY_i_cTD_le_one_of_free c i hrel q hq0⟩
  | .mul p q, hp => by
      have hsum : MultiPoly.degreeY i p + MultiPoly.degreeY i q = 0 := hp
      have hp0 : MultiPoly.degreeY i p = 0 := by omega
      have hq0 : MultiPoly.degreeY i q = 0 := by omega
      have h1 := degreeY_i_cTD_le_one_of_free c i hrel p hp0
      have h2 := degreeY_i_cTD_le_one_of_free c i hrel q hq0
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p) + MultiPoly.degreeY i q)
              (MultiPoly.degreeY i p + MultiPoly.degreeY i (chainTotalDeriv c q)) ≤ 1
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- **`htame` from the encoder-side invariant, packaged.** If, at a reciprocal index `i`, every relation is
`y_i`-linear (`degreeY i (relations l) ≤ 1` for all `l`) — i.e. no relation references `y_i` squared, which
holds above `i` since only `i`'s own relation is the recip square — then `chainTotalDeriv` maps `y_i`-free
polys to `y_i`-linear polys. Combined with the encoder relation shape (`coeff · varY_top`, `coeff` a lifted
`cTD` of a `y_i`-free encoded value), this yields `htame` for the higher levels. The one remaining
obligation is the encoder invariant supplying the two hypotheses (`hrel`, and value `y_i`-freeness), proven
by induction over `enc` / `chainExtend` — see the module docstring. -/
theorem htame_relation_of_coeff_free {n : Nat} (c : PfaffianChain n) (i : Fin n)
    (hrel : ∀ l : Fin n, i ≠ l → MultiPoly.degreeY i (c.relations l) ≤ 1)
    (top : Fin n) (coeffBase : MultiPoly n) (hfree : MultiPoly.degreeY i coeffBase = 0)
    (hne : i ≠ top) :
    MultiPoly.degreeY i (MultiPoly.mul (chainTotalDeriv c coeffBase) (MultiPoly.varY top)) ≤ 1 := by
  show MultiPoly.degreeY i (chainTotalDeriv c coeffBase) + MultiPoly.degreeY i (MultiPoly.varY top) ≤ 1
  have hv : MultiPoly.degreeY i (MultiPoly.varY top) = 0 := by
    show (if i = top then 1 else 0) = 0; rw [if_neg hne]
  have := degreeY_i_cTD_le_one_of_free c i hrel coeffBase hfree
  omega

/-! ## The encoder cross-linearity invariant and its `chainExtend` preservation -/

/-- **Cross-linearity.** No relation references any OTHER variable to degree > 1 (a level's own reciprocal
square is the sole degree-2, the `j = l` case this excludes). Restricted to a reciprocal `j` and a higher
`l`, this is exactly the `htame` hypothesis `degreeY j (relations l) ≤ 1`. -/
def EncRelLinear {n : Nat} (c : PfaffianChain n) : Prop :=
  ∀ (l j : Fin n), j ≠ l → MultiPoly.degreeY j (c.relations l) ≤ 1

/-- **`chainExtend` preserves cross-linearity**, given the new top relation `nr` is itself cross-linear. The
old relations ride through `liftLastY`, which preserves below-top `degreeY` (`degreeY_liftLastY_low'`) and
zeroes the new top's (`degreeY_top_liftLastY`) — so no cross-degree can rise. This isolates the whole
per-step obligation to `nr`'s cross-linearity, the shape the three encoder steps (`stepCC`/`stepCD`/
`encEmlStepR`) must each supply. -/
theorem chainExtend_preserves_EncRelLinear {n : Nat} (c : PfaffianChain n) (ne : Real → Real)
    (nr : MultiPoly (n + 1)) (hc : EncRelLinear c)
    (hnr : ∀ j : Fin (n + 1), j ≠ (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) →
        MultiPoly.degreeY j nr ≤ 1) :
    EncRelLinear (chainExtend c ne nr) := by
  intro l j hjl
  by_cases hl : l.val < n
  · rw [chainExtend_relations_of_lt c ne nr l hl]
    by_cases hj : j.val < n
    · rw [MachLib.IterExpDepthN.degreeY_liftLastY_low' j hj]
      refine hc ⟨l.val, hl⟩ ⟨j.val, hj⟩ (fun h => hjl ?_)
      rw [Fin.mk.injEq] at h
      exact Fin.ext h
    · have hjv : j.val = n := by have := j.isLt; omega
      have hjn : j = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := Fin.ext hjv
      rw [hjn, MultiPoly.degreeY_top_liftLastY]
      exact Nat.zero_le _
  · have hlv : l.val = n := by have := l.isLt; omega
    have hln : l = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := Fin.ext hlv
    rw [hln, chainExtend_relations_last]
    exact hnr j (fun h => hjl (h.trans hln.symm))

/-! ## Value-side facts — encoder values are affine (`const` / `varX` / `y_exp − y_log`) -/

/-- **`cTD` of a node value `y_a − y_b` is cross-linear in EVERY index**, given both referenced relations
are fully linear (`degreeY k ≤ 1` for all `k`). The eml node value is the affine `exp − log`
(`encEmlStep`), so its `cTD` is a DIFFERENCE of two relations — a `max`, never a product — hence stays ≤ 1
wherever the relations do. The value-side companion to `degreeY_i_cTD_le_one_of_free`: that lemma covers
indices the value is FREE of; this covers indices the value references (the value's affineness is what
keeps `cTD` from squaring). -/
theorem degreeY_cTD_sub_vars_le_one {n : Nat} (c : PfaffianChain n) (a b : Fin n)
    (ha : ∀ k : Fin n, MultiPoly.degreeY k (c.relations a) ≤ 1)
    (hb : ∀ k : Fin n, MultiPoly.degreeY k (c.relations b) ≤ 1) (j : Fin n) :
    MultiPoly.degreeY j
        (chainTotalDeriv c (MultiPoly.sub (MultiPoly.varY a) (MultiPoly.varY b))) ≤ 1 := by
  show Nat.max (MultiPoly.degreeY j (c.relations a)) (MultiPoly.degreeY j (c.relations b)) ≤ 1
  exact Nat.max_le.mpr ⟨ha j, hb j⟩

/-- **The eml node value `y_{M+2} − y_{M+1}` is free of every descendant index `i ≤ M`** — in particular of
every reciprocal buried in the sub-chain. So encoder values are `y_i`-free for a descendant recip `i` (the
hypothesis `degreeY_i_cTD_le_one_of_free` needs): a node consumes its children through their exp/log OUTPUT
(`i = M+2` / `M+1`), never their internal recip. -/
theorem degreeY_node_value_low {M : Nat} (i : Fin (M + 3)) (hi : i.val ≤ M) :
    MultiPoly.degreeY i
        (MultiPoly.sub (MultiPoly.varY (⟨M + 2, by omega⟩ : Fin (M + 3)))
          (MultiPoly.varY (⟨M + 1, by omega⟩ : Fin (M + 3)))) = 0 := by
  have hne2 : ¬ (i = (⟨M + 2, by omega⟩ : Fin (M + 3))) := by
    intro h; have hv : i.val = M + 2 := by rw [h]
    omega
  have hne1 : ¬ (i = (⟨M + 1, by omega⟩ : Fin (M + 3))) := by
    intro h; have hv : i.val = M + 1 := by rw [h]
    omega
  show Nat.max (if i = (⟨M + 2, by omega⟩ : Fin (M + 3)) then 1 else 0)
        (if i = (⟨M + 1, by omega⟩ : Fin (M + 3)) then 1 else 0) = 0
  rw [if_neg hne2, if_neg hne1]; decide

end MachLib.PfaffianRecipHtame
