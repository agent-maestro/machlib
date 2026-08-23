import MachLib.BipevRatFn
import MachLib.PolyNsum

/-!
# Reaching a named coefficient of the eliminated family

Step 2 of the composition, and it is smaller than it looked.

The descent (`all_coeffs_evZero_of_shorter'`) concludes `∀ A ∈ Es, EvZeroF (pev A)` — a statement
about **membership**, not about indices. So extracting "the coefficient at index `j`" does not need
an indexing theory at all: it needs only that the `j`-th combination *is a member* of
`elimCoeffs top topD Ls Cs`, which is one induction stepping `j` and the two lists together.

Worth recording because the natural reading of "extract the coefficient at index `j`" suggests
`List.get`, lengths, and off-by-one bookkeeping. The descent's conclusion was already in the weaker
and more convenient form, and matching the shape the consumer produces — rather than the shape the
statement suggests — made the step three lines.

That is the same lesson as `PolyDerivShort`'s two commits ago: **size a step by what its consumer
actually delivers.**
-/

namespace MachLib

open Real

/-- The `j`-th eliminated combination is a member of the eliminated family. -/
theorem elimCoeffs_mem : ∀ (Ls Cs : List (List Real)) (j : Nat) (top topD L C : List Real),
    Ls[j]? = some L → Cs[j]? = some C →
    psub (pmul topD L) (pmul top C) ∈ elimCoeffs top topD Ls Cs := by
  intro Ls
  induction Ls with
  | nil => intro Cs j top topD L C hL _; simp at hL
  | cons A As ih =>
      intro Cs j top topD L C hL hC
      cases Cs with
      | nil => simp at hC
      | cons B Bs =>
          cases j with
          | zero =>
              simp at hL hC
              show psub (pmul topD L) (pmul top C)
                  ∈ psub (pmul topD A) (pmul top B) :: elimCoeffs top topD As Bs
              rw [← hL, ← hC]
              exact List.mem_cons_self
          | succ k =>
              simp at hL hC
              show psub (pmul topD L) (pmul top C)
                  ∈ psub (pmul topD A) (pmul top B) :: elimCoeffs top topD As Bs
              exact List.mem_cons_of_mem _ (ih Bs k top topD L C hL hC)

/-- **The named coefficient vanishes eventually.** The descent's conclusion, specialised to the
index the coefficient identity is about. -/
theorem elim_coeff_evZero {S : Real → Real} {Ms Es : List (List Real)}
    (hmin : ∀ Ns : List (List Real), ProperRel S Ns → Ms.length ≤ Ns.length)
    {Ls Cs : List (List Real)} {top topD L C : List Real} {j : Nat}
    (hEs : Es = elimCoeffs top topD Ls Cs)
    (hrel : EvRel S Es) (hlt : Es.length < Ms.length)
    (hL : Ls[j]? = some L) (hC : Cs[j]? = some C) :
    EvZeroF (pev (psub (pmul topD L) (pmul top C))) := by
  refine all_coeffs_evZero_of_shorter' hmin hrel hlt _ ?_
  rw [hEs]
  exact elimCoeffs_mem Ls Cs j top topD L C hL hC

end MachLib
