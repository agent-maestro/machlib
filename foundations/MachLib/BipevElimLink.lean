import MachLib.BipevTailNonzero

/-!
# The elimination link

The composition's second link: from the relation and the cleared differentiated relation, both
holding eventually, to the **eliminated** relation holding eventually.

`bipev_elim_eq_zero` is pointwise, so the link is one tail intersection. The lockstep length
condition is `dcoeffs_length_eq`, written two commits ago.

## The shape lemma, again written first

Reaching the `j`-th eliminated coefficient needs to know *what* `dcoeffs` has at index `j`:
`padd (Q²·L') ((i+j)·D·L)` when the family starts at index `i`. `dcoeffs_getElem` says so.

That is the fourth shape lemma in this arc written for a family whose defining module never needed
it — and the second written *before* the theorem rather than after a failed application. The rule
from two commits ago is holding.
-/

namespace MachLib

open Real

/-! ## What `dcoeffs` holds at an index -/

theorem dcoeffs_getElem : ∀ (Ls : List (List Real)) (QQ D : List Real) (i j : Nat) (L : List Real),
    Ls[j]? = some L →
    (dcoeffs QQ D i Ls)[j]?
      = some (padd (pmul QQ (pderiv L)) (pnsum (i + j) (pmul D L))) := by
  intro Ls
  induction Ls with
  | nil => intro QQ D i j L hL; simp at hL
  | cons A As ih =>
      intro QQ D i j L hL
      cases j with
      | zero =>
          simp at hL
          rw [← hL, show i + 0 = i from by omega]
          rfl
      | succ k =>
          simp at hL
          show (dcoeffs QQ D (i + 1) As)[k]? = _
          rw [ih QQ D (i + 1) k L hL, show i + 1 + k = i + (k + 1) from by omega]

/-! ## The link -/

/-- **The eliminated relation holds on a tail.** One tail intersection over `bipev_elim_eq_zero`. -/
theorem evRel_elimCoeffs {S : Real → Real} {Ls Cs : List (List Real)} {top topD : List Real}
    (hlen : Ls.length = Cs.length) (h1 : EvRel S Ls) (h2 : EvRel S Cs) :
    EvRel S (elimCoeffs top topD Ls Cs) := by
  obtain ⟨X1, hX1, hr1⟩ := h1
  obtain ⟨X2, hX2, hr2⟩ := h2
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX1 hX2
  exact ⟨X, hX, fun x hx =>
    bipev_elim_eq_zero hlen (hr1 x (le_trans hle1 hx)) (hr2 x (le_trans hle2 hx))⟩

/-- **The `j`-th coefficient identity holds**, for a minimal relation split at its leading
coefficient. This is the composition's second and third links joined: eliminate, descend, and read
off the coefficient at `j`. -/
theorem elim_coeff_vanishes {S : Real → Real} {Ms Ls₀ : List (List Real)}
    {QQ D v u : List Real} {j : Nat}
    (hmin : ∀ Ns : List (List Real), ProperRel S Ns → Ms.length ≤ Ns.length)
    (hMs : Ms = Ls₀ ++ [v])
    (hrel : EvRel S Ms)
    (hdiff : EvRel S (dcoeffs QQ D 0 Ms))
    (hu : Ls₀[j]? = some u) :
    EvZeroF (pev (psub
      (pmul (padd (pmul QQ (pderiv v)) (pnsum (0 + Ls₀.length) (pmul D v))) u)
      (pmul v (padd (pmul QQ (pderiv u)) (pnsum (0 + j) (pmul D u)))))) := by
  -- stated at `Ls₀ ++ [v]`, not `Ms`: rewriting `hMs` first would leave this pattern unmatched
  have hsplit : dcoeffs QQ D 0 (Ls₀ ++ [v])
      = dcoeffs QQ D 0 Ls₀ ++ [padd (pmul QQ (pderiv v)) (pnsum (0 + Ls₀.length) (pmul D v))] :=
    dcoeffs_concat Ls₀ QQ D v 0
  have hlenLC : Ls₀.length = (dcoeffs QQ D 0 Ls₀).length := dcoeffs_length_eq Ls₀ QQ D
  have hlen : Ms.length = (dcoeffs QQ D 0 Ms).length := dcoeffs_length_eq Ms QQ D
  have helim : EvRel S (elimCoeffs v
      (padd (pmul QQ (pderiv v)) (pnsum (0 + Ls₀.length) (pmul D v))) Ms (dcoeffs QQ D 0 Ms)) :=
    evRel_elimCoeffs hlen hrel hdiff
  rw [hMs, hsplit] at helim
  have hlt : Ls₀.length < Ms.length := by rw [hMs]; simp
  refine elim_coeff_evZero_drop hmin hlenLC helim hlt hu ?_
  exact dcoeffs_getElem Ls₀ QQ D 0 j u hu

end MachLib
