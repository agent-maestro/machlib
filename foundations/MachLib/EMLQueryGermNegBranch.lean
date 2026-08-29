import MachLib.EMLQueryGermZeroBranch

/-!
# The query germ's NEGATIVE branch — `u` eventually negative

The last of `ratGerm_eventual_sign`'s three cases. Where `u = pev P / pev Q` is eventually negative,
totalisation gives

```
Fbasis (u x) = exp (u x) + log₀ (u x) = exp (u x) + 0 = exp (u x)
```

so on that ray the germ is `bipev N x (exp (u x))` — **a polynomial in `x` and `exp (P/Q)`, with no
logarithm anywhere in it.**

## Why this does NOT need declamping

The obvious route is `EMLDeclampEncoder`: the germ's tree fails `LogArgPosOn` at its `logTree u`
node, and `declamp` rewrites exactly such nodes. That route is available and its uniformity problem
is solved (`uniformZeroBoundFrom_of_reachableBounds`) — but it costs, and `declamp_logArgPos` gives
positivity only on the `(a,b)` the tree was declamped for, which is not the shape the reachable form
then asks for.

**None of that is needed, because the germ does not have to be built through `Fbasis` at all.** Once
totalisation has removed the log, `exp (u x)` is directly an EML node — `expOf t = eml t (const 1)`,
whose log argument is the constant `1`. Assembling the germ from `expOf` and the `Gen` combinators
gives a tree whose `LogArgPosOn` obligation is **unconditional except for `pev Q x ≠ 0`**:

| piece | what `LogArgPosOn` costs |
|---|---|
| `polyE L = toEML (pevTerm L)` | nothing — no `F`, no `div` |
| `addGen`, `mulGen` | nothing — they shift through `domTree` |
| `divGen a b` | `b.eval x ≠ 0` |
| `expOf t` | nothing — its log argument is `const 1` |

So the branch that *looked* hardest (a failing positivity hypothesis) is the one needing the fewest
hypotheses, because the failing hypothesis was an artefact of routing through `Fbasis`. The lesson is
the same one this arc keeps paying for: **the difficulty was in the chosen representation, not in the
object.**
-/

namespace MachLib

open Real

/-! ## The germ's tree, built to be positivity-free -/

/-- A coefficient list as an EML tree, through the `L_F` translation. No `F` and no `div`, so both
side conditions are vacuous. -/
noncomputable def polyE (L : List Real) : EMLTree := toEML (pevTerm L)

theorem polyE_eval (L : List Real) (x : Real) : (polyE L).eval x = pev L x := by
  rw [polyE, toEML_eval (pevTerm L) x (pevTerm_divSafe L x), pevTerm_eval]

theorem polyE_logArgPos (L : List Real) (S : RealSet) : LogArgPosOn (polyE L) S :=
  logArgPosOn_toEML (pevTerm L) S (fun x _ => pevTerm_divSafe L x) (pevTerm_fArgsPos L S)

/-- `exp (P/Q)` as an EML tree. The `exp` is `expOf`, whose log argument is the constant `1`. -/
noncomputable def expRatE (P Q : List Real) : EMLTree := expOf (divGen (polyE P) (polyE Q))

theorem expRatE_eval {P Q : List Real} {x : Real} (hQ : pev Q x ≠ 0) :
    (expRatE P Q).eval x = exp (pev P x / pev Q x) := by
  have hb : (polyE Q).eval x ≠ 0 := by rw [polyE_eval]; exact hQ
  rw [expRatE, expOf_eval, divGen_eval hb, polyE_eval, polyE_eval]

theorem expRatE_logArgPos (P Q : List Real) (S : RealSet)
    (hQ : ∀ x : Real, S x → pev Q x ≠ 0) : LogArgPosOn (expRatE P Q) S :=
  logArgPosOn_expOf _ S
    (logArgPosOn_divGen _ _ S (polyE_logArgPos P S) (polyE_logArgPos Q S)
      (fun x hx => by rw [polyE_eval]; exact hQ x hx))

/-- A bivariate polynomial as an EML tree, Horner, with the second variable supplied as a tree. -/
noncomputable def bipevE : List (List Real) → EMLTree → EMLTree
  | [],      _ => .const 0
  | L :: Ls, u => addGen (polyE L) (mulGen u (bipevE Ls u))

theorem bipevE_eval : ∀ (N : List (List Real)) (u : EMLTree) (x : Real),
    (bipevE N u).eval x = bipev N x (u.eval x)
  | [], _, _ => rfl
  | L :: Ls, u, x => by
      rw [bipevE, addGen_eval, mulGen_eval, bipevE_eval Ls u x, polyE_eval]
      rfl

/-- **The whole tree's positivity obligation is just the denominator.** Every combinator above
contributes nothing; `divGen` contributes `pev Q x ≠ 0`. -/
theorem bipevE_logArgPos : ∀ (N : List (List Real)) (u : EMLTree) (S : RealSet),
    LogArgPosOn u S → LogArgPosOn (bipevE N u) S
  | [], _, _, _ => True.intro
  | L :: Ls, u, S, hu =>
      logArgPosOn_addGen _ _ S (polyE_logArgPos L S)
        (logArgPosOn_mulGen _ _ S hu (bipevE_logArgPos Ls u S hu))

/-- The germ's tree on the negative ray. -/
noncomputable def negGermTree (N : List (List Real)) (P Q : List Real) : EMLTree :=
  bipevE N (expRatE P Q)

theorem negGermTree_logArgPos (N : List (List Real)) (P Q : List Real) (S : RealSet)
    (hQ : ∀ x : Real, S x → pev Q x ≠ 0) : LogArgPosOn (negGermTree N P Q) S :=
  bipevE_logArgPos N _ S (expRatE_logArgPos P Q S hQ)

/-! `Fbasis_of_nonpos` (`Fbasis u = exp u` for `u ≤ 0`) is **not** redefined here — `EMLQueryComplexity`
has it. I wrote it again and the compiler rejected the duplicate name, which is now the third such
catch in this arc and the third to be caught *because the obvious name was chosen*. -/

/-- **On the negative ray, the tree computes the germ.** -/
theorem negGermTree_eval {N : List (List Real)} {P Q : List Real} {x : Real}
    (hQ : pev Q x ≠ 0) (hneg : pev P x / pev Q x ≤ 0) :
    (negGermTree N P Q).eval x = bipev N x (Fbasis (pev P x / pev Q x)) := by
  rw [negGermTree, bipevE_eval, expRatE_eval hQ, Fbasis_of_nonpos hneg]

/-! ## The bound -/

/-- **The negative branch, bounded on an interval.** `encBound (negGermTree N P Q)` is a `Nat` built
from the tree alone — no `a`, no `b` — so the *constant* is already interval-independent.

**But the statement is per-interval, and deliberately so.** `encBound_bounds` needs a nonzero witness
**inside** `(a,b)`, and `¬ EvZeroF` does not supply one: it gives non-vanishing arbitrarily far out,
not inside a nominated bounded interval. So this has the same shape as the positive branch's
`queryTerm_zero_bound`, and for the same reason.

The hypotheses are exactly the ray's own data plus that witness. **No positivity of `u` appears** —
routing through `expOf` rather than `Fbasis` removes the obligation instead of discharging it. -/
theorem negGerm_zero_bound (N : List (List Real)) (P Q : List Real) (a b : Real) (hab : a < b)
    (hQ : ∀ x : Real, Icc a b x → pev Q x ≠ 0)
    (hneg : ∀ x : Real, Icc a b x → pev P x / pev Q x ≤ 0)
    (hne : ∃ z : Real, a < z ∧ z < b ∧ bipev N z (Fbasis (pev P z / pev Q z)) ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ bipev N z (Fbasis (pev P z / pev Q z)) = 0) →
      zeros.length ≤ encBound (negGermTree N P Q) := by
  have hmem : ∀ z : Real, a < z → z < b → Icc a b z :=
    fun z h1 h2 => ⟨le_of_lt h1, le_of_lt h2⟩
  have hlog : LogArgPosOn (negGermTree N P Q) (Icc a b) :=
    negGermTree_logArgPos N P Q (Icc a b) hQ
  have hne' : ∃ z : Real, a < z ∧ z < b ∧ (negGermTree N P Q).eval z ≠ 0 := by
    obtain ⟨w, h1, h2, h0⟩ := hne
    exact ⟨w, h1, h2, by
      rw [negGermTree_eval (hQ w (hmem w h1 h2)) (hneg w (hmem w h1 h2))]; exact h0⟩
  intro zeros hnd hz
  refine encBound_bounds (negGermTree N P Q) a b hab hlog hne' zeros hnd ?_
  intro z hzmem
  obtain ⟨h1, h2, h0⟩ := hz z hzmem
  exact ⟨h1, h2, by
    rw [negGermTree_eval (hQ z (hmem z h1 h2)) (hneg z (hmem z h1 h2))]; exact h0⟩

/-! ## What still separates these branches from the antecedent

The **zero** branch reaches `UniformZeroBoundFrom` outright, because `poly_root_count_bound` needs a
nonzero witness only *somewhere*, and then bounds every interval.

The **positive** and **negative** branches do not, and this module is where that becomes explicit:
`encBound_bounds` wants a nonzero witness **inside each interval**, and `¬ EvZeroF` gives
non-vanishing only eventually. Supplying it needs the germ to be non-vanishing *somewhere in every
subinterval beyond the ray* — which follows from analyticity plus `¬ EvZeroF` by an identity-theorem
argument, and is **not proved here**.

So the honest count is: **one branch of three is a `UniformZeroBoundFrom` producer; two are
interval-local bounds awaiting one shared lemma.** I had described the positive branch as closed
without noticing this, and writing the negative branch is what surfaced it.
-/

end MachLib
