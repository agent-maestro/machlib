import MachLib.MultiVarTwoExpRolle
import MachLib.ArcCount

/-!
# Global two-exponential bound with M discharged (Gate 2d, two-exp — arc count wired in)

Combines the arc-count bound (`arc_count_le`: arcs separated by critical points ⟹ `#arcs ≤ #critical + 1`)
with the Khovanskii–Rolle multi-arc bound (`khovanskii_rolle_multiarc`: `#solutions ≤ M·(N+1)`). The result
`khovanskii_rolle_full` no longer takes the arc count `M` as a free input: with the arcs' representatives
`ChainSep`-separated by critical points and the critical points bounded by `Ncrit`, the total intersection
count is `≤ (Ncrit + 1)·(N + 1)`.

So both structural inputs to `khovanskii_iterate` are now expressed as Khovanskii–Rolle counts: `N` bounds
the Jacobian zeros per arc, and `M = Ncrit + 1` where `Ncrit` bounds the critical points `{f=0, fᵧ=0}` — a
count of the SAME kind (`khovanskii_rolle_count`/`_curve`), one level down. The topological arc count is
thereby reduced to the combinatorial `#arcs ≤ #critical + 1` plus a lower-level count.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real

/-- **Global bound with the arc count discharged.** Arcs carry a representative x-value (`.1`) and their
intersection points (`.2`); adjacent representatives are separated by a critical point (`ChainSep sep`),
critical points are `Ncrit`-bounded, and each arc has `≤ N+1` intersections (per-arc T.1). Then the total
number of intersections is `≤ (Ncrit + 1)·(N + 1)` — `M = Ncrit + 1`, no longer a free input. -/
theorem khovanskii_rolle_full (sep : Real → Prop) (Ncrit N : Nat)
    (hNcrit : ∀ ss : List Real, ss.Nodup → (∀ s ∈ ss, sep s) → ss.length ≤ Ncrit)
    (hd : Real × List Real) (s : List (Real × List Real))
    (hchain : ChainSep sep hd.1 (s.map (fun a => a.1)))
    (harc : ∀ arc ∈ (hd :: s), arc.2.length ≤ N + 1) :
    ((hd :: s).flatMap (fun a => a.2)).length ≤ (Ncrit + 1) * (N + 1) := by
  have hM : (hd :: s).length ≤ Ncrit + 1 := by
    have hac := arc_count_le sep Ncrit hNcrit hd.1 (s.map (fun a => a.1)) hchain
    rwa [show (hd.1 :: s.map (fun a => a.1)).length = (hd :: s).length from by
      simp [List.length_map]] at hac
  exact khovanskii_rolle_multiarc (hd :: s) (Ncrit + 1) N hM harc

end TwoExp
end MultiVarMod
end MachLib
