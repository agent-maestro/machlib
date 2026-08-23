import MachLib.BipevCoeffIdentity

/-!
# The eliminated family is the same length — the descent needs its truncation

The argument-matching slip the previous commit predicted, found by trying to apply
`elim_coeff_evZero`.

`elimCoeffs` is pointwise, so `elimCoeffs top topD Ms Cs` has **the same length as `Ms`**. Its top
entry is killed — it evaluates to zero everywhere — but it is still *there*. So
`Es.length < Ms.length` is false as stated, and the descent does not apply to `Es`; it applies to
`Es.dropLast`.

Two facts close the gap:

* `elimCoeffs_concat` — elimination commutes with splitting off the last coefficient, so the
  truncation of the eliminated family *is* the eliminated family of the truncations;
* `elimCoeffs_top_eval` (already proved) — the split-off entry is `c_m·p_m − p_m·c_m`, which
  evaluates to zero, so `evRel_dropLast` applies.

Then the `j`-th coefficient for `j < m` is a member of the *truncated* family, which is strictly
shorter than `Ms`, and the descent goes through.

## Why this was worth predicting rather than discovering

The previous commit said what remained was "bookkeeping over roughly fifteen arguments" and that any
surprise would be an argument-matching slip. It was exactly that: no lemma was wrong, no mathematics
was missing, and the fix is two length facts. Naming the expected failure mode in advance is what
made it cheap to recognise when it appeared.
-/

namespace MachLib

open Real

/-! ## Elimination commutes with splitting off the last coefficient -/

theorem elimCoeffs_length : ∀ (Ls Cs : List (List Real)) (top topD : List Real),
    Ls.length = Cs.length → (elimCoeffs top topD Ls Cs).length = Ls.length := by
  intro Ls
  induction Ls with
  | nil => intro Cs top topD hlen; cases Cs with
    | nil => rfl
    | cons _ _ => exact absurd hlen (by simp)
  | cons L Ls ih =>
      intro Cs top topD hlen
      cases Cs with
      | nil => exact absurd hlen (by simp)
      | cons C Cs =>
          show (elimCoeffs top topD Ls Cs).length + 1 = Ls.length + 1
          rw [ih Cs top topD (by simpa using hlen)]

theorem elimCoeffs_concat : ∀ (Ls Cs : List (List Real)) (top topD L C : List Real),
    Ls.length = Cs.length →
    elimCoeffs top topD (Ls ++ [L]) (Cs ++ [C])
      = elimCoeffs top topD Ls Cs ++ [psub (pmul topD L) (pmul top C)] := by
  intro Ls
  induction Ls with
  | nil => intro Cs top topD L C hlen; cases Cs with
    | nil => rfl
    | cons _ _ => exact absurd hlen (by simp)
  | cons A As ih =>
      intro Cs top topD L C hlen
      cases Cs with
      | nil => exact absurd hlen (by simp)
      | cons B Bs =>
          show psub (pmul topD A) (pmul top B) :: elimCoeffs top topD (As ++ [L]) (Bs ++ [C])
              = (psub (pmul topD A) (pmul top B) :: elimCoeffs top topD As Bs) ++ _
          rw [ih Bs top topD L C (by simpa using hlen)]
          rfl

/-! ## The descent, applied to the truncation -/

/-- **The `j`-th eliminated coefficient vanishes eventually**, for `j` below the killed index. The
statement takes the *untruncated* family, because that is what the elimination produces, and does
the drop internally. -/
theorem elim_coeff_evZero_drop {S : Real → Real} {Ms : List (List Real)}
    (hmin : ∀ Ns : List (List Real), ProperRel S Ns → Ms.length ≤ Ns.length)
    {Ls₀ Cs₀ : List (List Real)} {top topD L C : List Real} {j : Nat}
    (hlenLC : Ls₀.length = Cs₀.length)
    (hrel : EvRel S (elimCoeffs top topD (Ls₀ ++ [top]) (Cs₀ ++ [topD])))
    (hlt : Ls₀.length < Ms.length)
    (hL : Ls₀[j]? = some L) (hC : Cs₀[j]? = some C) :
    EvZeroF (pev (psub (pmul topD L) (pmul top C))) := by
  rw [elimCoeffs_concat Ls₀ Cs₀ top topD top topD hlenLC] at hrel
  -- the split-off entry evaluates to zero, so the truncation is still a relation
  have hZ : EvZeroF (pev (psub (pmul topD top) (pmul top topD))) :=
    ⟨1, le_refl 1, fun x _ => elimCoeffs_top_eval top topD x⟩
  have hrel₀ : EvRel S (elimCoeffs top topD Ls₀ Cs₀) := evRel_dropLast hrel hZ
  have hlen₀ : (elimCoeffs top topD Ls₀ Cs₀).length = Ls₀.length :=
    elimCoeffs_length Ls₀ Cs₀ top topD hlenLC
  refine all_coeffs_evZero_of_shorter' hmin hrel₀ (by omega) _ ?_
  exact elimCoeffs_mem Ls₀ Cs₀ j top topD L C hL hC

end MachLib
