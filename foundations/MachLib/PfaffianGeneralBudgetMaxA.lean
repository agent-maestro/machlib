import MachLib.PfaffianGeneralBudgetN5Alpha
import MachLib.IterExpDepthNBudgetMax

/-!
# α-generalized monotone budget cap `budgetMaxA` (general Pfaffian explicit bound, depth induction)

The depth induction (`pfaffian_khovanskii_bound_gen_explicit`) needs the per-poly `budgetN5A α m D q`
bounded by a function of `D` (and the format `α`) ALONE, so the depth-below bound can be evaluated at a
`D`-only argument. `budgetMaxA α m D` is that cap: `invPhiG` at `degreeY_top := D` and `ir :=
descentBoundA α (m+2) D` (the α-scaled caps). The α-version of `budgetMax`; the two facts the induction
consumes — `budgetN5A α m D q ≤ budgetMaxA α m D` (degrees `≤ D`) and `budgetMaxA α m` monotone in `D` —
port their `budgetMax` proofs verbatim, swapping `descentBound`/`rankRec` for `descentBoundA`/`rankRecA`.
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.ExplicitBound

/-- The α-scaled monotone-in-`D` budget cap: `invPhiG` at the `D`-caps with the α-format inner rank. -/
def budgetMaxA (α m D : Nat) : Nat :=
  invPhiG (descentBoundA α (m + 2)) 0 D (descentBoundA α (m + 2) D) D

/-- **`budgetN5A α m D q ≤ budgetMaxA α m D`** when `q`'s degrees are `≤ D` (`α ≥ 1`). Raises the inner
rank to its cap (`rankRecA_inner_lt`) then the level `degreeY_top` to `D` (`hpy`). -/
theorem budgetN5A_le_budgetMaxA (α m : Nat) (hα : 1 ≤ α) (p : MultiPoly (m + 3)) (D : Nat)
    (hpx : MultiPoly.degreeX p + 2 ≤ D) (hpy : ∀ i : Fin (m + 3), MultiPoly.degreeY i p ≤ D) :
    budgetN5A α m D p ≤ budgetMaxA α m D := by
  unfold budgetN5A budgetMaxA
  refine Nat.le_trans
    (invPhiG_mono_ir (descentBoundA α (m + 2)) (fun {_ _} h => descentBoundA_mono α (m + 2) h) 0
      (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) D
      (Nat.le_of_lt (rankRecA_inner_lt α m hα p D hpx hpy)))
    (invPhiG_mono_d (descentBoundA α (m + 2)) (fun {_ _} h => descentBoundA_mono α (m + 2) h) 0
      (descentBoundA α (m + 2) D) D (hpy _))

/-- `budgetMaxA α m` is monotone in `D` — the cap the `NgenA` recurrence needs. -/
theorem budgetMaxA_mono (α m : Nat) {D D' : Nat} (h : D ≤ D') :
    budgetMaxA α m D ≤ budgetMaxA α m D' := by
  unfold budgetMaxA
  have hcap : ∀ {B B' : Nat}, B ≤ B' → descentBoundA α (m + 2) B ≤ descentBoundA α (m + 2) B' :=
    fun {_ _} hh => descentBoundA_mono α (m + 2) hh
  exact Nat.le_trans
    (invPhiG_mono_d (descentBoundA α (m + 2)) hcap 0 (descentBoundA α (m + 2) D) D h)
    (Nat.le_trans
      (invPhiG_mono_ir (descentBoundA α (m + 2)) hcap 0 D' D (descentBoundA_mono α (m + 2) h))
      (invPhiG_mono_B (descentBoundA α (m + 2)) hcap 0 D' (descentBoundA α (m + 2) D') h))

end MachLib.IterExpDepthN
