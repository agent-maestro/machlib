import MachLib.PfaffianRecipGrowthSpike
import MachLib.PfaffianChainExtend
import MachLib.IterExpDepthNDegreeY
import MachLib.EMLEncoder

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

/-- **`cTD` commutes with `liftLastY`.** For a value `p` over the base chain `c`, the chain-total-derivative
over any one-step extension of `c`, applied to `liftLastY p`, is the lift of the base `cTD`. Because `cTD`
of a lifted variable is the extended relation, which (`chainExtend_relations_of_lt`) is itself the lift of
the base relation; `add`/`sub`/`mul` are homomorphisms of both operations. **Key simplifier:** it collapses
every encoder coefficient `liftLastY(cTD (chainExtend base) (liftLastY value))` to `liftLastYBy _ (cTD base
value)` — a lift of a BASE-chain `cTD` — so recip/top-freeness of the coefficient becomes automatic (a lift
is free of the new top indices) and the `≤ 1` bound reduces to the base value's `cTD` bound. -/
theorem chainTotalDeriv_chainExtend_liftLastY {n : Nat} (c : PfaffianChain n) (ne : Real → Real)
    (nr : MultiPoly (n + 1)) :
    ∀ p : MultiPoly n,
      chainTotalDeriv (chainExtend c ne nr) (MultiPoly.liftLastY p)
        = MultiPoly.liftLastY (chainTotalDeriv c p)
  | .const _ => rfl
  | .varX => rfl
  | .varY i => by
      show (chainExtend c ne nr).relations (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))
          = MultiPoly.liftLastY (c.relations i)
      rw [chainExtend_relations_of_lt c ne nr (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) i.isLt]
  | .add p q => by
      show MultiPoly.add (chainTotalDeriv (chainExtend c ne nr) (MultiPoly.liftLastY p))
              (chainTotalDeriv (chainExtend c ne nr) (MultiPoly.liftLastY q))
          = MultiPoly.liftLastY (MultiPoly.add (chainTotalDeriv c p) (chainTotalDeriv c q))
      rw [chainTotalDeriv_chainExtend_liftLastY c ne nr p, chainTotalDeriv_chainExtend_liftLastY c ne nr q]
      rfl
  | .sub p q => by
      show MultiPoly.sub (chainTotalDeriv (chainExtend c ne nr) (MultiPoly.liftLastY p))
              (chainTotalDeriv (chainExtend c ne nr) (MultiPoly.liftLastY q))
          = MultiPoly.liftLastY (MultiPoly.sub (chainTotalDeriv c p) (chainTotalDeriv c q))
      rw [chainTotalDeriv_chainExtend_liftLastY c ne nr p, chainTotalDeriv_chainExtend_liftLastY c ne nr q]
      rfl
  | .mul p q => by
      show MultiPoly.add
              (MultiPoly.mul (chainTotalDeriv (chainExtend c ne nr) (MultiPoly.liftLastY p))
                (MultiPoly.liftLastY q))
              (MultiPoly.mul (MultiPoly.liftLastY p)
                (chainTotalDeriv (chainExtend c ne nr) (MultiPoly.liftLastY q)))
          = MultiPoly.liftLastY (MultiPoly.add (MultiPoly.mul (chainTotalDeriv c p) q)
              (MultiPoly.mul p (chainTotalDeriv c q)))
      rw [chainTotalDeriv_chainExtend_liftLastY c ne nr p, chainTotalDeriv_chainExtend_liftLastY c ne nr q]
      rfl

/-- **`liftLastY` preserves "≤ 1 at every index".** Below-top indices keep the base degree
(`degreeY_liftLastY_low'`); the new top is `0`. Iterated, this propagates a base value's `cTD` bound up
through the lift layers a coefficient wraps it in. -/
theorem degreeY_liftLastY_le_one {n : Nat} (X : MultiPoly n)
    (hX : ∀ j : Fin n, MultiPoly.degreeY j X ≤ 1) :
    ∀ j : Fin (n + 1), MultiPoly.degreeY j (MultiPoly.liftLastY X) ≤ 1 := by
  intro j
  by_cases hj : j.val < n
  · rw [MachLib.IterExpDepthN.degreeY_liftLastY_low' j hj]; exact hX ⟨j.val, hj⟩
  · have hjv : j.val = n := by have := j.isLt; omega
    have hjn : j = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := Fin.ext hjv
    rw [hjn, MultiPoly.degreeY_top_liftLastY]; exact Nat.zero_le _

/-! ## Step-relation cross-linearity — the `nr` obligations for `chainExtend_preserves_EncRelLinear` -/

/-- `degreeY` of a negation equals that of the argument (`neg p = sub 0 p`; the zero summand contributes 0).
Local copy to avoid importing the heavy encoder-descent module. -/
theorem degreeY_neg' {n : Nat} (i : Fin n) (p : MultiPoly n) :
    MultiPoly.degreeY i (MultiPoly.neg p) = MultiPoly.degreeY i p := by
  show Nat.max (MultiPoly.degreeY i (MultiPoly.const 0)) (MultiPoly.degreeY i p)
     = MultiPoly.degreeY i p
  exact Nat.max_eq_right (Nat.zero_le _)

/-- **The recip step (`stepCC`) new relation is cross-linear**, given the value's `cTD` is degree-≤1 at
every base index. `nr = −liftLastY(cTD cb w) · yₘ²`; at `j ≠ M` the square contributes 0, and
`degreeY j (liftLastY(cTD cb w))` peels (`degreeY_liftLastY_low'`) to `degreeY ⟨j⟩ (cTD cb w) ≤ 1` (`hw`).
This is `chainExtend_preserves_EncRelLinear`'s `hnr` for the reciprocal level, isolating everything to the
value-`cTD` bound `hw` (which the affine value lemmas supply). -/
theorem stepCC_nr_cross_linear {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M)
    (hw : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb w) ≤ 1)
    (j : Fin (M + 1)) (hj : j ≠ (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1))) :
    MultiPoly.degreeY j
        (MultiPoly.mul (MultiPoly.neg (MultiPoly.liftLastY (chainTotalDeriv cb w)))
          (MultiPoly.mul (MultiPoly.varY (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)))
                         (MultiPoly.varY (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1))))) ≤ 1 := by
  have hjM : j.val < M := by
    have h1 := j.isLt
    have h2 : j.val ≠ M := fun h => hj (Fin.ext h)
    omega
  have hvarY : MultiPoly.degreeY j (MultiPoly.varY (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1))) = 0 := by
    show (if j = (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) then 1 else 0) = 0
    rw [if_neg hj]
  show MultiPoly.degreeY j (MultiPoly.neg (MultiPoly.liftLastY (chainTotalDeriv cb w)))
      + (MultiPoly.degreeY j (MultiPoly.varY (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)))
        + MultiPoly.degreeY j (MultiPoly.varY (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)))) ≤ 1
  rw [degreeY_neg', MachLib.IterExpDepthN.degreeY_liftLastY_low' j hjM, hvarY]
  have := hw ⟨j.val, hjM⟩
  omega

/-- `degreeY i (varY i) = 1`. -/
theorem degreeY_varY_one {n : Nat} (i : Fin n) : MultiPoly.degreeY i (MultiPoly.varY i) = 1 := by
  show (if i = i then 1 else 0) = 1; rw [if_pos rfl]

/-- **`= 0` kernel.** If `p` is `y_i`-free and every substituted relation is `y_i`-FREE (not just ≤ 1),
then `cTD c p` is `y_i`-free. Used to show a log/exp coefficient — a `cTD` of a `y_i`-free value over a
chain whose lower (substituted) relations are `y_i`-free — is exactly `0` at the recip index just below
(the log references that recip with degree exactly 1, so its coefficient must be recip-free, not merely
≤ 1). -/
theorem degreeY_i_cTD_eq_zero_of_free {n : Nat} (c : PfaffianChain n) (i : Fin n)
    (hrel : ∀ l : Fin n, i ≠ l → MultiPoly.degreeY i (c.relations l) = 0) :
    ∀ p : MultiPoly n, MultiPoly.degreeY i p = 0 →
      MultiPoly.degreeY i (chainTotalDeriv c p) = 0
  | .const _, _ => rfl
  | .varX, _ => rfl
  | .varY l, hp => hrel l (fun h => by
      have hh : (if i = l then (1 : Nat) else 0) = 0 := hp
      rw [if_pos h] at hh; omega)
  | .add p q, hp => by
      have hmax : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hp
      have hle : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) ≤ 0 := Nat.le_of_eq hmax
      have hp0 : MultiPoly.degreeY i p = 0 := Nat.le_zero.mp (Nat.max_le.mp hle).1
      have hq0 : MultiPoly.degreeY i q = 0 := Nat.le_zero.mp (Nat.max_le.mp hle).2
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p))
              (MultiPoly.degreeY i (chainTotalDeriv c q)) = 0
      rw [degreeY_i_cTD_eq_zero_of_free c i hrel p hp0,
          degreeY_i_cTD_eq_zero_of_free c i hrel q hq0]
      decide
  | .sub p q, hp => by
      have hmax : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hp
      have hle : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) ≤ 0 := Nat.le_of_eq hmax
      have hp0 : MultiPoly.degreeY i p = 0 := Nat.le_zero.mp (Nat.max_le.mp hle).1
      have hq0 : MultiPoly.degreeY i q = 0 := Nat.le_zero.mp (Nat.max_le.mp hle).2
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p))
              (MultiPoly.degreeY i (chainTotalDeriv c q)) = 0
      rw [degreeY_i_cTD_eq_zero_of_free c i hrel p hp0,
          degreeY_i_cTD_eq_zero_of_free c i hrel q hq0]
      decide
  | .mul p q, hp => by
      have hsum : MultiPoly.degreeY i p + MultiPoly.degreeY i q = 0 := hp
      have hp0 : MultiPoly.degreeY i p = 0 := by omega
      have hq0 : MultiPoly.degreeY i q = 0 := by omega
      have h1 := degreeY_i_cTD_eq_zero_of_free c i hrel p hp0
      have h2 := degreeY_i_cTD_eq_zero_of_free c i hrel q hq0
      show Nat.max (MultiPoly.degreeY i (chainTotalDeriv c p) + MultiPoly.degreeY i q)
              (MultiPoly.degreeY i p + MultiPoly.degreeY i (chainTotalDeriv c q)) = 0
      rw [h1, h2, hp0, hq0]
      decide

/-- **Generic log step relation** `coeff·yₘ` (references the reciprocal `m` at degree 1) is ≤ 1 at EVERY
index, given `coeff` is recip-free there (`degreeY m coeff = 0`) and ≤ 1 elsewhere. In particular cross-linear
for `chainExtend_preserves_EncRelLinear`. The recip-freeness at `m` is exactly what the `= 0` kernel supplies. -/
theorem log_nr_cross_linear {N : Nat} (coeff : MultiPoly N) (m : Fin N)
    (hcoeffm : MultiPoly.degreeY m coeff = 0) (hcoeff : ∀ j : Fin N, MultiPoly.degreeY j coeff ≤ 1)
    (j : Fin N) :
    MultiPoly.degreeY j (MultiPoly.mul coeff (MultiPoly.varY m)) ≤ 1 := by
  show MultiPoly.degreeY j coeff + MultiPoly.degreeY j (MultiPoly.varY m) ≤ 1
  by_cases hjm : j = m
  · have h1 : MultiPoly.degreeY j coeff = 0 := by rw [hjm]; exact hcoeffm
    have h2 : MultiPoly.degreeY j (MultiPoly.varY m) = 1 := by rw [hjm]; exact degreeY_varY_one m
    omega
  · have hvarY : MultiPoly.degreeY j (MultiPoly.varY m) = 0 := by
      show (if j = m then 1 else 0) = 0; rw [if_neg hjm]
    rw [hvarY]; have := hcoeff j; omega

/-- **Generic exp step relation** `coeff·y_top` (references its own top) is ≤ 1 at EVERY index, given `coeff`
is top-free (`degreeY top coeff = 0`) and ≤ 1 elsewhere. -/
theorem exp_nr_cross_linear {N : Nat} (coeff : MultiPoly N) (top : Fin N)
    (hcoefftop : MultiPoly.degreeY top coeff = 0) (hcoeff : ∀ j : Fin N, MultiPoly.degreeY j coeff ≤ 1)
    (j : Fin N) :
    MultiPoly.degreeY j (MultiPoly.mul coeff (MultiPoly.varY top)) ≤ 1 := by
  show MultiPoly.degreeY j coeff + MultiPoly.degreeY j (MultiPoly.varY top) ≤ 1
  by_cases hjt : j = top
  · have h1 : MultiPoly.degreeY j coeff = 0 := by rw [hjt]; exact hcoefftop
    have h2 : MultiPoly.degreeY j (MultiPoly.varY top) = 1 := by rw [hjt]; exact degreeY_varY_one top
    omega
  · have hvarY : MultiPoly.degreeY j (MultiPoly.varY top) = 0 := by
      show (if j = top then 1 else 0) = 0; rw [if_neg hjt]
    rw [hvarY]; have := hcoeff j; omega

/-! ## The three step chains preserve cross-linearity (recip → log → exp) -/

/-- **The recip step preserves `EncRelLinear`**, given the base cross-linearity and the value's `cTD`
bound `∀ j', degreeY j' (cTD cb w) ≤ 1`. `stepCC cb w = chainExtend cb _ (−liftLastY(cTD cb w)·yₘ²)`;
`chainExtend_preserves_EncRelLinear` + `stepCC_nr_cross_linear`. -/
theorem stepCC_EncRelLinear {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M)
    (hcb : EncRelLinear cb) (hw : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb w) ≤ 1) :
    EncRelLinear (MachLib.stepCC cb w) := by
  unfold MachLib.stepCC
  exact chainExtend_preserves_EncRelLinear cb _ _ hcb (fun j hj => stepCC_nr_cross_linear cb w hw j hj)

/-- `cTD` over `stepCC` commutes with `liftLastY` (commutation, specialised — `stepCC = chainExtend cb`). -/
theorem cTD_stepCC_liftLastY {M : Nat} (cb : PfaffianChain M) (w p : MultiPoly M) :
    chainTotalDeriv (MachLib.stepCC cb w) (MultiPoly.liftLastY p)
      = MultiPoly.liftLastY (chainTotalDeriv cb p) := by
  unfold MachLib.stepCC
  exact chainTotalDeriv_chainExtend_liftLastY cb _ _ p

/-- `cTD` over `stepCD` commutes with `liftLastY` (`stepCD = chainExtend (stepCC cb w)`). -/
theorem cTD_stepCD_liftLastY {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M) (p : MultiPoly (M + 1)) :
    chainTotalDeriv (MachLib.stepCD cb w) (MultiPoly.liftLastY p)
      = MultiPoly.liftLastY (chainTotalDeriv (MachLib.stepCC cb w) p) := by
  unfold MachLib.stepCD
  exact chainTotalDeriv_chainExtend_liftLastY (MachLib.stepCC cb w) _ _ p

/-- **The log step preserves `EncRelLinear`.** Its coefficient `liftLastY(cTD (stepCC cb w)(liftLastY w))`
collapses (commutation) to `liftLastY²(cTD cb w)` — ≤1 everywhere (propagation from `hw`) and `= 0` at the
recip index `M` just below (a double lift is free of that index). `log_nr_cross_linear` then closes it. -/
theorem stepCD_EncRelLinear {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M)
    (hcb : EncRelLinear cb) (hw : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb w) ≤ 1) :
    EncRelLinear (MachLib.stepCD cb w) := by
  have hlift1 : ∀ j : Fin (M + 1),
      MultiPoly.degreeY j (MultiPoly.liftLastY (chainTotalDeriv cb w)) ≤ 1 :=
    degreeY_liftLastY_le_one _ hw
  have hlift2 : ∀ j : Fin (M + 2),
      MultiPoly.degreeY j (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb w))) ≤ 1 :=
    degreeY_liftLastY_le_one _ hlift1
  have hcoeffm : MultiPoly.degreeY (⟨M, by omega⟩ : Fin (M + 2))
      (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb w))) = 0 := by
    rw [MachLib.IterExpDepthN.degreeY_liftLastY_low' (⟨M, by omega⟩ : Fin (M + 2)) (by omega : M < M + 1)]
    exact MultiPoly.degreeY_top_liftLastY (chainTotalDeriv cb w)
  unfold MachLib.stepCD
  refine chainExtend_preserves_EncRelLinear (MachLib.stepCC cb w) _ _
    (stepCC_EncRelLinear cb w hcb hw) ?_
  intro j _
  rw [cTD_stepCC_liftLastY cb w w]
  exact log_nr_cross_linear (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb w)))
    (⟨M, by omega⟩ : Fin (M + 2)) hcoeffm hlift2 j

/-- **The exp step preserves `EncRelLinear`.** Its coefficient `liftLastY(cTD (stepCD cb w)(liftLastYBy 2
b1))` collapses (commutation, twice) to `liftLastY³(cTD cb b1)` — ≤1 everywhere (propagation from `hb1`)
and `= 0` at its own top `M+2` (a triple lift is free of the outermost index). `exp_nr_cross_linear` closes
it. Needs the base `cTD` bound for `b1 = ⟦t1⟧` as well as `w`. -/
theorem encEmlStepR_EncRelLinear {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (hcb : EncRelLinear cb) (hw : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb w) ≤ 1)
    (hb1 : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb b1) ≤ 1) :
    EncRelLinear (MachLib.encEmlStepR cb b1 w) := by
  have hlift1 : ∀ j : Fin (M + 1),
      MultiPoly.degreeY j (MultiPoly.liftLastY (chainTotalDeriv cb b1)) ≤ 1 :=
    degreeY_liftLastY_le_one _ hb1
  have hlift2 : ∀ j : Fin (M + 2),
      MultiPoly.degreeY j (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb b1))) ≤ 1 :=
    degreeY_liftLastY_le_one _ hlift1
  have hlift3 : ∀ j : Fin (M + 3), MultiPoly.degreeY j
      (MultiPoly.liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb b1)))) ≤ 1 :=
    degreeY_liftLastY_le_one _ hlift2
  have hcofftop : MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3))
      (MultiPoly.liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb b1)))) = 0 :=
    MultiPoly.degreeY_top_liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb b1)))
  unfold MachLib.encEmlStepR
  refine chainExtend_preserves_EncRelLinear (MachLib.stepCD cb w) _ _
    (stepCD_EncRelLinear cb w hcb hw) ?_
  intro j _
  simp only [MachLib.liftLastYBy]
  rw [cTD_stepCD_liftLastY cb w (MultiPoly.liftLastY b1), cTD_stepCC_liftLastY cb w b1]
  exact exp_nr_cross_linear
    (MultiPoly.liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb b1))))
    (⟨M + 2, by omega⟩ : Fin (M + 3)) hcofftop hlift3 j

/-! ## `encLift` preserves "≤ 1 at every index" (toward the `enc` induction) -/

/-- `liftLastYBy k` preserves "≤ 1 at every index" (iterate `degreeY_liftLastY_le_one`). -/
theorem degreeY_liftLastYBy_le_one {n : Nat} (k : Nat) (X : MultiPoly n)
    (hX : ∀ j : Fin n, MultiPoly.degreeY j X ≤ 1) :
    ∀ j : Fin (n + k), MultiPoly.degreeY j (MachLib.liftLastYBy k X) ≤ 1 := by
  induction k with
  | zero => exact hX
  | succ k ih => exact degreeY_liftLastY_le_one (MachLib.liftLastYBy k X) ih

/-- **`encLift` preserves "≤ 1 at every index".** Const/var lifts are the identity; an eml node lift is
`liftLastYBy 3 ∘ encLift ∘ encLift`, each preserving the bound. Used to transport a base value's `cTD`
bound up the encoder's variable additions. -/
theorem degreeY_encLift_le_one (t : EMLTree) {N : Nat} (X : MultiPoly N)
    (hX : ∀ j : Fin N, MultiPoly.degreeY j X ≤ 1) :
    ∀ j : Fin (MachLib.len t N), MultiPoly.degreeY j (MachLib.encLift t X) ≤ 1 := by
  induction t generalizing N X with
  | const c => exact hX
  | var => exact hX
  | eml t1 t2 ih1 ih2 =>
    exact degreeY_liftLastYBy_le_one 3 (MachLib.encLift t1 (MachLib.encLift t2 X))
      (ih1 (MachLib.encLift t2 X) (ih2 X hX))

/-! ## `cTD` commutes with `encLift` over `enc`'s extension (the final transport) -/

/-- `cTD` over `encEmlStepR` commutes with `liftLastY` (`encEmlStepR = chainExtend (stepCD cb w)`). -/
theorem cTD_encEmlStepR_liftLastY {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (p : MultiPoly (M + 2)) :
    chainTotalDeriv (MachLib.encEmlStepR cb b1 w) (MultiPoly.liftLastY p)
      = MultiPoly.liftLastY (chainTotalDeriv (MachLib.stepCD cb w) p) := by
  unfold MachLib.encEmlStepR
  exact chainTotalDeriv_chainExtend_liftLastY (MachLib.stepCD cb w) _ _ p

/-- `cTD` over `encEmlStepR` collapses a `liftLastYBy 3` of a base value to `liftLastYBy 3` of the base
`cTD` — the three step commutations composed. This is the eml-node case of the `enc`/`encLift` commutation. -/
theorem cTD_encEmlStepR_liftLastYBy3 {M : Nat} (cb : PfaffianChain M) (b1 w Q : MultiPoly M) :
    chainTotalDeriv (MachLib.encEmlStepR cb b1 w) (MachLib.liftLastYBy 3 Q)
      = MachLib.liftLastYBy 3 (chainTotalDeriv cb Q) := by
  show chainTotalDeriv (MachLib.encEmlStepR cb b1 w)
        (MultiPoly.liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY Q)))
      = MultiPoly.liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb Q)))
  rw [cTD_encEmlStepR_liftLastY cb b1 w (MultiPoly.liftLastY (MultiPoly.liftLastY Q)),
      cTD_stepCD_liftLastY cb w (MultiPoly.liftLastY Q), cTD_stepCC_liftLastY cb w Q]

/-- **`cTD` commutes with `encLift` over `enc`'s extension.** `cTD (enc t chain).1 (encLift t v) =
encLift t (cTD chain v)`. Leaves: `enc` returns the chain unchanged and `encLift` is the identity. Node:
`(enc (eml t1 t2) chain).1` is a triple `chainExtend` (`encEmlStepR`) and `encLift (eml t1 t2)` is
`liftLastYBy 3 ∘ encLift t1 ∘ encLift t2`, so `cTD_encEmlStepR_liftLastYBy3` collapses the outer three
lifts and the two IHs handle the inner encLifts. This transports a base value's `cTD` bound to the value the
parent node feeds its coefficients (`w = encLift t1 ⟦t2⟧`). -/
theorem cTD_enc_encLift : ∀ (t : EMLTree) {N : Nat} (chain : PfaffianChain N) (v : MultiPoly N),
    chainTotalDeriv (MachLib.enc t chain).1 (MachLib.encLift t v)
      = MachLib.encLift t (chainTotalDeriv chain v)
  | .const _, _, _, _ => rfl
  | .var, _, _, _ => rfl
  | .eml t1 t2, N, chain, v => by
      show chainTotalDeriv
            (MachLib.encEmlStepR (MachLib.enc t1 (MachLib.enc t2 chain).1).1
              (MachLib.enc t1 (MachLib.enc t2 chain).1).2 (MachLib.encLift t1 (MachLib.enc t2 chain).2))
            (MachLib.liftLastYBy 3 (MachLib.encLift t1 (MachLib.encLift t2 v)))
          = MachLib.liftLastYBy 3 (MachLib.encLift t1 (MachLib.encLift t2 (chainTotalDeriv chain v)))
      rw [cTD_encEmlStepR_liftLastYBy3 (MachLib.enc t1 (MachLib.enc t2 chain).1).1
            (MachLib.enc t1 (MachLib.enc t2 chain).1).2 (MachLib.encLift t1 (MachLib.enc t2 chain).2)
            (MachLib.encLift t1 (MachLib.encLift t2 v)),
          cTD_enc_encLift t1 (MachLib.enc t2 chain).1 (MachLib.encLift t2 v),
          cTD_enc_encLift t2 chain v]

/-! ## The node value's `cTD` bound (for the `enc` induction's carried invariant) -/

/-- The exp relation (top of `encEmlStepR`) is ≤ 1 at every index (collapse + `exp_nr_cross_linear`). -/
theorem encEmlStepR_exp_rel_le_one {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (hb1 : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb b1) ≤ 1) (k : Fin (M + 3)) :
    MultiPoly.degreeY k ((MachLib.encEmlStepR cb b1 w).relations (⟨M + 2, by omega⟩ : Fin (M + 3))) ≤ 1 := by
  have hlift3 : ∀ j : Fin (M + 3), MultiPoly.degreeY j
      (MultiPoly.liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb b1)))) ≤ 1 :=
    degreeY_liftLastY_le_one _ (degreeY_liftLastY_le_one _ (degreeY_liftLastY_le_one _ hb1))
  have hcofftop : MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3))
      (MultiPoly.liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb b1)))) = 0 :=
    MultiPoly.degreeY_top_liftLastY _
  unfold MachLib.encEmlStepR
  rw [chainExtend_relations_last (MachLib.stepCD cb w) _ _]
  simp only [MachLib.liftLastYBy]
  rw [cTD_stepCD_liftLastY cb w (MultiPoly.liftLastY b1), cTD_stepCC_liftLastY cb w b1]
  exact exp_nr_cross_linear
    (MultiPoly.liftLastY (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb b1))))
    (⟨M + 2, by omega⟩ : Fin (M + 3)) hcofftop hlift3 k

/-- The log relation (index `M+1` of `encEmlStepR`, a lift of `stepCD`'s top) is ≤ 1 at every index. -/
theorem encEmlStepR_log_rel_le_one {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (hw : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb w) ≤ 1) (k : Fin (M + 3)) :
    MultiPoly.degreeY k ((MachLib.encEmlStepR cb b1 w).relations (⟨M + 1, by omega⟩ : Fin (M + 3))) ≤ 1 := by
  have hlog : ∀ j : Fin (M + 2),
      MultiPoly.degreeY j ((MachLib.stepCD cb w).relations (⟨M + 1, by omega⟩ : Fin (M + 2))) ≤ 1 := by
    intro j
    have hlift2 : ∀ i : Fin (M + 2),
        MultiPoly.degreeY i (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb w))) ≤ 1 :=
      degreeY_liftLastY_le_one _ (degreeY_liftLastY_le_one _ hw)
    have hcoeffm : MultiPoly.degreeY (⟨M, by omega⟩ : Fin (M + 2))
        (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb w))) = 0 := by
      rw [MachLib.IterExpDepthN.degreeY_liftLastY_low' (⟨M, by omega⟩ : Fin (M + 2)) (by omega : M < M + 1)]
      exact MultiPoly.degreeY_top_liftLastY (chainTotalDeriv cb w)
    unfold MachLib.stepCD
    rw [chainExtend_relations_last (MachLib.stepCC cb w) _ _, cTD_stepCC_liftLastY cb w w]
    exact log_nr_cross_linear (MultiPoly.liftLastY (MultiPoly.liftLastY (chainTotalDeriv cb w)))
      (⟨M, by omega⟩ : Fin (M + 2)) hcoeffm hlift2 j
  unfold MachLib.encEmlStepR
  rw [chainExtend_relations_of_lt (MachLib.stepCD cb w) _ _ (⟨M + 1, by omega⟩ : Fin (M + 3))
      (by omega : M + 1 < M + 2)]
  exact degreeY_liftLastY_le_one _ hlog k

/-- **The eml node value `y_{M+2} − y_{M+1}` has `cTD` ≤ 1 at every index** — both top relations are ≤ 1
everywhere (`degreeY_cTD_sub_vars_le_one`). This is the value-`cTD` bound the `enc` induction carries for a
node result. -/
theorem encEmlStepR_node_value_le_one {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (hw : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb w) ≤ 1)
    (hb1 : ∀ j' : Fin M, MultiPoly.degreeY j' (chainTotalDeriv cb b1) ≤ 1) (k : Fin (M + 3)) :
    MultiPoly.degreeY k (chainTotalDeriv (MachLib.encEmlStepR cb b1 w)
      (MultiPoly.sub (MultiPoly.varY (⟨M + 2, by omega⟩ : Fin (M + 3)))
        (MultiPoly.varY (⟨M + 1, by omega⟩ : Fin (M + 3))))) ≤ 1 :=
  degreeY_cTD_sub_vars_le_one (MachLib.encEmlStepR cb b1 w) _ _
    (encEmlStepR_exp_rel_le_one cb b1 w hb1) (encEmlStepR_log_rel_le_one cb b1 w hw) k

/-! ## The `enc` induction: `EncRelLinear (enc t chain).1` -/

/-- The carried invariant: the chain is cross-linear AND its value has `cTD` ≤ 1 at every index (needed so a
parent node can feed this value to its coefficients). -/
def EncGood {n : Nat} (c : PfaffianChain n) (v : MultiPoly n) : Prop :=
  EncRelLinear c ∧ ∀ j : Fin n, MultiPoly.degreeY j (chainTotalDeriv c v) ≤ 1

/-- **`enc` preserves `EncGood`.** Induction on `t`: leaves return the chain unchanged with value `const`/
`varX` (cTD `= 0`); an eml node is `encEmlStepR`, whose `EncRelLinear` comes from `encEmlStepR_EncRelLinear`
fed by the transported `hw` (`cTD_enc_encLift` + `degreeY_encLift_le_one`) and the carried `hb1`, and whose
node value's `cTD` bound is `encEmlStepR_node_value_le_one`. -/
theorem enc_EncGood (t : EMLTree) : ∀ {N : Nat} (chain : PfaffianChain N), EncRelLinear chain →
    EncGood (MachLib.enc t chain).1 (MachLib.enc t chain).2 := by
  induction t with
  | const c => intro N chain hchain; exact ⟨hchain, fun j => Nat.zero_le _⟩
  | var => intro N chain hchain; exact ⟨hchain, fun j => Nat.zero_le _⟩
  | eml t1 t2 ih1 ih2 =>
    intro N chain hchain
    obtain ⟨hr2rel, hr2v⟩ := ih2 chain hchain
    obtain ⟨hr1rel, hr1v⟩ := ih1 (MachLib.enc t2 chain).1 hr2rel
    have hw : ∀ j, MultiPoly.degreeY j
        (chainTotalDeriv (MachLib.enc t1 (MachLib.enc t2 chain).1).1
          (MachLib.encLift t1 (MachLib.enc t2 chain).2)) ≤ 1 := by
      intro j
      rw [cTD_enc_encLift t1 (MachLib.enc t2 chain).1 (MachLib.enc t2 chain).2]
      exact degreeY_encLift_le_one t1 _ hr2v j
    exact ⟨encEmlStepR_EncRelLinear _ _ _ hr1rel hw hr1v,
      encEmlStepR_node_value_le_one _ _ _ hw hr1v⟩

/-- **`enc` produces a cross-linear chain** — the `htame` interface. -/
theorem enc_EncRelLinear (t : EMLTree) {N : Nat} (chain : PfaffianChain N) (hchain : EncRelLinear chain) :
    EncRelLinear (MachLib.enc t chain).1 :=
  (enc_EncGood t chain hchain).1

end MachLib.PfaffianRecipHtame
