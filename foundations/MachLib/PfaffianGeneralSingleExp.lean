import MachLib.PfaffianGeneralHnzWF

/-!
# Generalize — the single-exponential (depth-1 / y₀-level) machinery for general exp-type chains

The depth-2 base descent `hBaseHnz` bottoms out at the single-exp descent on the leading `y₁`-coefficient
(a `y₁`-free `MultiPoly 2`), reducing its `y₀`-structure. `singleExpMeasureCanon` is chain-agnostic, but
the ∀N reduce `seReduce` and its descent (`ChainExp2*`, ~1900 lines) are IterExp-specific (`G₀ = 1`). The
KEY de-risking fact: for a general `G₀` the reduce's leading `y₀`-coefficient is *identically* `(lc)'ₓ`
(the `G₀` terms cancel — `d·G₀·lcY₀` from the identity injection meets `d·G₀·lcY₀` from the `cdegY0·G₀`
multiplier), so the descent reuses the IterExp result plus a 2-case split. This file ports the y₀-level cTD
machinery (`degreeY0_cTD_eq_of_y1free`, `leadingCoeffY0_cTD_eval`) to arbitrary exp-type chains, threading
the extra `G₀` factor.
-/
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.IterExpTopIdentity
open MachLib.ChainExp2NoZeros
open MachLib.IterExpChainMod

private theorem degY1L {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a = 0 :=
  Nat.le_zero.mp (h ▸ Nat.le_max_left _ _)
private theorem degY1R {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b = 0 :=
  Nat.le_zero.mp (h ▸ Nat.le_max_right _ _)
private theorem degY1Ls {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a = 0 :=
  Nat.le_zero.mp (h ▸ Nat.le_max_left _ _)
private theorem degY1Rs {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b = 0 :=
  Nat.le_zero.mp (h ▸ Nat.le_max_right _ _)

/-- **General y₀-degree preservation.** For a `y₁`-free `q`, `chainTotalDeriv c'` preserves the `y₀`-degree,
for any exp-type chain (`relations 0 = G₀·y₀`, `degreeY₀ G₀ = 0`). Generalizes `degreeY0_cTD_eq_of_y1free`
(only the `varY 0` case changes: `degreeY₀(relations 0) = 1` from exp-type, not `rfl`). -/
theorem degreeY0_cTD_eq_of_y1free_gen {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0) (q : MultiPoly 2) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 →
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q)
      = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
  have hvar0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) = 1 := by
    show (if (⟨0, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2) then 1 else 0) = 1; rw [if_pos rfl]
  induction q with
  | const c => intro _; rfl
  | varX => intro _; rfl
  | varY j =>
    intro hy1
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ =>
      show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (c'.relations (⟨0, by omega⟩ : Fin 2))
         = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
      rw [hrel0, degreeY_mul' (⟨0, by omega⟩ : Fin 2) G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)), hG0, hvar0]
    | 1, _ => simp [MultiPoly.degreeY] at hy1
  | add p q ihp ihq =>
    intro hy1
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' p))
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q))
       = Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
    rw [ihp (degY1L hy1), ihq (degY1R hy1)]
  | sub p q ihp ihq =>
    intro hy1
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' p))
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q))
       = Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
    rw [ihp (degY1Ls hy1), ihq (degY1Rs hy1)]
  | mul p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' p)
                  + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p
                  + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q))
       = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q
    rw [ihp hp1, ihq hq1]; exact Nat.max_self _

private theorem lcYvY {n : Nat} (i : Fin n) :
    MultiPoly.leadingCoeffY i (MultiPoly.varY i) = MultiPoly.const 1 := by
  show (if i = i then MultiPoly.const 1 else MultiPoly.varY i) = MultiPoly.const 1; rw [if_pos rfl]
private theorem dgvY {n : Nat} (i : Fin n) : MultiPoly.degreeY i (MultiPoly.varY i) = 1 := by
  show (if i = i then 1 else 0) = 1; rw [if_pos rfl]
private theorem lAgt {n} (i : Fin n) (p q : MultiPoly n) (h : MultiPoly.degreeY i q < MultiPoly.degreeY i p) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q) = MultiPoly.leadingCoeffY i p := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)) = MultiPoly.leadingCoeffY i p
  rw [if_pos h]
private theorem lAlt {n} (i : Fin n) (p q : MultiPoly n) (h : MultiPoly.degreeY i p < MultiPoly.degreeY i q) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q) = MultiPoly.leadingCoeffY i q := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)) = MultiPoly.leadingCoeffY i q
  rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt h)), if_pos h]
private theorem lAeq {n} (i : Fin n) (p q : MultiPoly n) (h : MultiPoly.degreeY i p = MultiPoly.degreeY i q) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q) = MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q) := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)
  rw [if_neg (by omega), if_neg (by omega)]
private theorem lSgt {n} (i : Fin n) (p q : MultiPoly n) (h : MultiPoly.degreeY i q < MultiPoly.degreeY i p) :
    MultiPoly.leadingCoeffY i (MultiPoly.sub p q) = MultiPoly.leadingCoeffY i p := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY i q)
        else MultiPoly.sub (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)) = MultiPoly.leadingCoeffY i p
  rw [if_pos h]
private theorem ncadd (a b : Nat) : natCast (a + b) = natCast a + natCast b := by
  induction b with
  | zero => rw [Nat.add_zero, natCast_zero, add_zero]
  | succ n ih => rw [show a+(n+1)=(a+n)+1 from rfl, natCast_succ, natCast_succ, ih, add_assoc]

set_option maxHeartbeats 8000000 in
theorem leadingCoeffY0_cTD_eval_gen {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0)
    (q : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 →
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q)) x env
    = MultiPoly.eval (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
        * MultiPoly.eval (MultiPoly.mul G0 (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env := by
  induction q with
  | const c => intro _; show (0:Real) = 0 + natCast 0 * _; rw [natCast_zero]; mach_ring
  | varX => intro _; show (1:Real) = 1 + natCast 0 * _; rw [natCast_zero]; mach_ring
  | varY j =>
    intro hy1
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ =>
      show MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (c'.relations (⟨0, by omega⟩ : Fin 2))) x env
        = MultiPoly.eval (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))) x env
          + natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
            * MultiPoly.eval (MultiPoly.mul G0 (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))) x env
      rw [hrel0, lcY_mul (⟨0, by omega⟩ : Fin 2) G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)),
          leadingCoeffY_eq_self_of_degreeY_zero (⟨0, by omega⟩ : Fin 2) G0 hG0, lcYvY, dgvY,
          show chainTotalDeriv c' (MultiPoly.const 1) = MultiPoly.const 0 from rfl]
      simp only [MultiPoly.eval_const, MultiPoly.eval_mul]
      rw [natCast_succ, natCast_zero]; mach_ring
    | 1, _ => simp [MultiPoly.degreeY] at hy1
  | add p q ihp ihq =>
    intro hy1
    have hp1 := degY1L hy1
    have hq1 := degY1R hy1
    have hpe := degreeY0_cTD_eq_of_y1free_gen G0 hrel0 hG0 p hp1
    have hqe := degreeY0_cTD_eq_of_y1free_gen G0 hrel0 hG0 q hq1
    rw [show chainTotalDeriv c' (MultiPoly.add p q) = MultiPoly.add (chainTotalDeriv c' p) (chainTotalDeriv c' q) from rfl]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.add p q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [lAlt (⟨0, by omega⟩ : Fin 2) _ _ (by rw [hpe, hqe]; exact hlt), lAlt (⟨0, by omega⟩ : Fin 2) p q hlt, hd]; exact ihq hq1
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.add p q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
        show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [lAeq (⟨0, by omega⟩ : Fin 2) _ _ (by rw [hpe, hqe]; exact heq), lAeq (⟨0, by omega⟩ : Fin 2) p q heq, hd,
          show chainTotalDeriv c' (MultiPoly.add (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) = MultiPoly.add (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)) (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) from rfl]
      simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
      rw [heq] at ihp; rw [ihp hp1, ihq hq1]; mach_ring
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.add p q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p := Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [lAgt (⟨0, by omega⟩ : Fin 2) _ _ (by rw [hpe, hqe]; exact hgt), lAgt (⟨0, by omega⟩ : Fin 2) p q hgt, hd]; exact ihp hp1
  | sub p q ihp ihq =>
    intro hy1
    have hp1 := degY1Ls hy1
    have hq1 := degY1Rs hy1
    have hpe := degreeY0_cTD_eq_of_y1free_gen G0 hrel0 hG0 p hp1
    have hqe := degreeY0_cTD_eq_of_y1free_gen G0 hrel0 hG0 q hq1
    rw [show chainTotalDeriv c' (MultiPoly.sub p q) = MultiPoly.sub (chainTotalDeriv c' p) (chainTotalDeriv c' q) from rfl]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.sub p q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [MultiPoly.leadingCoeffY_sub_of_lt (⟨0, by omega⟩ : Fin 2) _ _ (by rw [hpe, hqe]; exact hlt),
          MultiPoly.leadingCoeffY_sub_of_lt (⟨0, by omega⟩ : Fin 2) p q hlt, hd,
          show chainTotalDeriv c' (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) = MultiPoly.sub (MultiPoly.const 0) (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) from rfl]
      simp only [MultiPoly.eval_sub, MultiPoly.eval_const, MultiPoly.eval_mul] at ihp ihq ⊢
      rw [ihq hq1]; mach_ring
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.sub p q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
        show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨0, by omega⟩ : Fin 2) _ _ (by rw [hpe, hqe]; exact heq),
          MultiPoly.leadingCoeffY_sub_of_eq (⟨0, by omega⟩ : Fin 2) p q heq, hd,
          show chainTotalDeriv c' (MultiPoly.sub (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) = MultiPoly.sub (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)) (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) from rfl]
      simp only [MultiPoly.eval_sub, MultiPoly.eval_mul] at ihp ihq ⊢
      rw [heq] at ihp; rw [ihp hp1, ihq hq1]; mach_ring
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.sub p q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p := Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [lSgt (⟨0, by omega⟩ : Fin 2) _ _ (by rw [hpe, hqe]; exact hgt), lSgt (⟨0, by omega⟩ : Fin 2) p q hgt, hd]; exact ihp hp1
  | mul p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul p q) = 0 := hy1
      rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) p q] at h2; omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul p q) = 0 := hy1
      rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) p q] at h2; omega
    have hpe := degreeY0_cTD_eq_of_y1free_gen G0 hrel0 hG0 p hp1
    have hqe := degreeY0_cTD_eq_of_y1free_gen G0 hrel0 hG0 q hq1
    rw [show chainTotalDeriv c' (MultiPoly.mul p q) = MultiPoly.add (MultiPoly.mul (chainTotalDeriv c' p) q) (MultiPoly.mul p (chainTotalDeriv c' q)) from rfl]
    have hcond : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul (chainTotalDeriv c' p) q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul p (chainTotalDeriv c' q)) := by
      show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' p) + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q)
      rw [hpe, hqe]
    rw [lAeq (⟨0, by omega⟩ : Fin 2) _ _ hcond,
        show MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul (chainTotalDeriv c' p) q) = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' p)) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) from rfl,
        show MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul p (chainTotalDeriv c' q)) = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q)) from rfl,
        show MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul p q) = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) from rfl,
        show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul p q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q from rfl,
        ncadd,
        show chainTotalDeriv c' (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) = MultiPoly.add (MultiPoly.mul (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) from rfl]
    simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
    rw [ihp hp1, ihq hq1]
    generalize MultiPoly.eval (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)) x env = A at *
    generalize MultiPoly.eval (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env = B at *
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) x env = LP at *
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) x env = LQ at *
    generalize MultiPoly.eval G0 x env = Gv at *
    generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) = Na at *
    generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) = Nb at *
    mach_ring

/-- The general single-exp reduce (multiplier `cdegY0·G₀`, generalizing IterExp's `const(cdegY0)`). -/
noncomputable def seReduceGen (c' : PfaffianChain 2) (G0 : MultiPoly 2) (q : MultiPoly 2) : MultiPoly 2 :=
  MultiPoly.sub (chainTotalDeriv c' q)
    (MultiPoly.mul (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) G0) q)

private theorem dgc {c : Real} : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.const c) = 0 := rfl

/-- **Sub-brick 1 (general).** The leading `y₀`-coefficient of `seReduceGen` evaluates to the derivative
part `cTD c' (lcY₀ q)` — the `d·G₀·lcY₀` injection cancels the `(cdegY0·G₀)·q` multiplier's leading coeff. -/
theorem seReduceGen_lcY0_eval {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0) (q : MultiPoly 2) (x : Real) (env : Fin 2 → Real)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (seReduceGen c' G0 q)) x env
    = MultiPoly.eval (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env := by
  unfold seReduceGen
  have hmy0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) G0) = 0 := by
    rw [degreeY_mul' (⟨0, by omega⟩ : Fin 2) _ G0, dgc, hG0]
  have hdd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q)
      = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) G0) q) := by
    rw [degreeY_mul' (⟨0, by omega⟩ : Fin 2) _ q, hmy0, Nat.zero_add,
        degreeY0_cTD_eq_of_y1free_gen G0 hrel0 hG0 q hy1]
  have hlcm : MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2)
      (MultiPoly.mul (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) G0) q)
      = MultiPoly.mul (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) G0) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) := by
    rw [lcY_mul (⟨0, by omega⟩ : Fin 2) _ q, leadingCoeffY_eq_self_of_degreeY_zero (⟨0, by omega⟩ : Fin 2) _ hmy0]
  rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨0, by omega⟩ : Fin 2) _ _ hdd, MultiPoly.eval_sub,
      leadingCoeffY0_cTD_eval_gen G0 hrel0 hG0 q x env hy1, hlcm]
  simp only [MultiPoly.eval_mul, MultiPoly.eval_const]
  mach_ring

/-- **cTD is chain-independent on y-free polynomials.** -/
theorem cTD_yfree_eq_IterExp {c' : PfaffianChain 2} (P : MultiPoly 2)
    (hd0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) P = 0)
    (hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) P = 0) :
    chainTotalDeriv c' P = chainTotalDeriv (IterExpChain 2) P := by
  induction P with
  | const c => rfl
  | varX => rfl
  | varY j =>
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ => exact absurd hd0 (by show (if (⟨0, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2) then 1 else 0) ≠ 0; rw [if_pos rfl]; decide)
    | 1, _ => exact absurd hd1 (by show (if (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) then 1 else 0) ≠ 0; rw [if_pos rfl]; decide)
  | add p q ihp ihq =>
    have hp0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p = 0 := by
      have hle : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.add p q) := Nat.le_max_left _ _; omega
    have hq0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = 0 := by
      have hle : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.add p q) := Nat.le_max_right _ _; omega
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q) := Nat.le_max_left _ _; omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q) := Nat.le_max_right _ _; omega
    show MultiPoly.add (chainTotalDeriv c' p) (chainTotalDeriv c' q) = MultiPoly.add _ _
    rw [ihp hp0 hp1, ihq hq0 hq1]
  | sub p q ihp ihq =>
    have hp0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p = 0 := by
      have hle : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.sub p q) := Nat.le_max_left _ _; omega
    have hq0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = 0 := by
      have hle : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.sub p q) := Nat.le_max_right _ _; omega
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q) := Nat.le_max_left _ _; omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q) := Nat.le_max_right _ _; omega
    show MultiPoly.sub (chainTotalDeriv c' p) (chainTotalDeriv c' q) = MultiPoly.sub _ _
    rw [ihp hp0 hp1, ihq hq0 hq1]
  | mul p q ihp ihq =>
    have hp0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p = 0 := by
      have h2 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul p q) = 0 := hd0
      rw [degreeY_mul' (⟨0, by omega⟩ : Fin 2) p q] at h2; omega
    have hq0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = 0 := by
      have h2 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul p q) = 0 := hd0
      rw [degreeY_mul' (⟨0, by omega⟩ : Fin 2) p q] at h2; omega
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul p q) = 0 := hd1
      rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) p q] at h2; omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul p q) = 0 := hd1
      rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) p q] at h2; omega
    show MultiPoly.add (MultiPoly.mul (chainTotalDeriv c' p) q) (MultiPoly.mul p (chainTotalDeriv c' q)) = MultiPoly.add _ _
    rw [ihp hp0 hp1, ihq hq0 hq1]

/-- **`seReduceGen` preserves the y₀-degree** (for y1-free q). -/
theorem degreeY0_seReduceGen {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0) (q : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0) :
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (seReduceGen c' G0 q) = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
  unfold seReduceGen
  have hmy0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) G0) = 0 := by
    rw [degreeY_mul' (⟨0, by omega⟩ : Fin 2) _ G0, (show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) = 0 from rfl), hG0]
  show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q)) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul (MultiPoly.mul (MultiPoly.const _) G0) q)) = _
  rw [degreeY0_cTD_eq_of_y1free_gen G0 hrel0 hG0 q hy1, degreeY_mul' (⟨0, by omega⟩ : Fin 2) _ q, hmy0, Nat.zero_add]
  exact Nat.max_self _

end MachLib.PfaffianGeneralReduce
