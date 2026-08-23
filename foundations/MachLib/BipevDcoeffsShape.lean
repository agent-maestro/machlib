import MachLib.BipevElimDrop

/-!
# `dcoeffs`, in the shapes the composition needs

The same two facts `elimCoeffs` needed last commit, for the other family. The elimination consumes
`Ms` and `dcoeffs QQ D 0 Ms` **in lockstep**, so it needs them to have equal length; and the drop
needs both split at their last coefficient. Neither was stated when `dcoeffs` was defined, because
`BipevClearedDeriv` only ever evaluated it — nothing there asked about its shape.

## The index at the split position

`dcoeffs` carries a running index, so splitting off the last coefficient has to say *which* index it
lands at: for `dcoeffs QQ D j (Ls ++ [L])` the appended entry is at index `j + |Ls|`, not `j`. That
is the only content in `dcoeffs_concat`, and getting it wrong would produce a coefficient with the
wrong multiple of `D` — which would then fail to match `coeff_identity`, whose whole point is that
the multiple is `m − j`.

This is the third family in a row (`bipev`, `elimCoeffs`, `dcoeffs`) where the composition needed a
length lemma and a concat lemma that the defining module had no reason to prove. Worth stating as a
pattern: **a recursive family gets used in lockstep with another one before it gets used alone**, so
its shape lemmas are due at the first pairing, not at its definition.
-/

namespace MachLib

open Real

theorem dcoeffs_length : ∀ (Ls : List (List Real)) (QQ D : List Real) (j : Nat),
    (dcoeffs QQ D j Ls).length = Ls.length := by
  intro Ls
  induction Ls with
  | nil => intro QQ D j; rfl
  | cons L Ls ih =>
      intro QQ D j
      show (dcoeffs QQ D (j + 1) Ls).length + 1 = Ls.length + 1
      rw [ih QQ D (j + 1)]

/-- Splitting off the last coefficient. The appended entry sits at index `j + |Ls|` — the running
index matters, and a wrong index here would silently produce the wrong multiple of `D`. -/
theorem dcoeffs_concat : ∀ (Ls : List (List Real)) (QQ D L : List Real) (j : Nat),
    dcoeffs QQ D j (Ls ++ [L])
      = dcoeffs QQ D j Ls
          ++ [padd (pmul QQ (pderiv L)) (pnsum (j + Ls.length) (pmul D L))] := by
  intro Ls
  induction Ls with
  | nil =>
      intro QQ D L j
      show [padd (pmul QQ (pderiv L)) (pnsum j (pmul D L))]
          = [padd (pmul QQ (pderiv L)) (pnsum (j + 0) (pmul D L))]
      rw [show j + 0 = j from by omega]
  | cons A As ih =>
      intro QQ D L j
      show padd (pmul QQ (pderiv A)) (pnsum j (pmul D A)) :: dcoeffs QQ D (j + 1) (As ++ [L])
          = (padd (pmul QQ (pderiv A)) (pnsum j (pmul D A)) :: dcoeffs QQ D (j + 1) As) ++ _
      rw [ih QQ D L (j + 1), show j + 1 + As.length = j + (As.length + 1) from by omega]
      rfl

/-- The two families the elimination consumes have equal length. -/
theorem dcoeffs_length_eq (Ls : List (List Real)) (QQ D : List Real) :
    Ls.length = (dcoeffs QQ D 0 Ls).length := (dcoeffs_length Ls QQ D 0).symm

end MachLib
