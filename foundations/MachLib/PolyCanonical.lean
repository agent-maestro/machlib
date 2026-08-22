import MachLib.EMLRationalGerm

/-!
# Canonical polynomials — the representation decision for the Euclid spine

`List Real` does not identify polynomials: `[1]` and `[1, 0]` are the same *function* and different
*lists*. Every algebraic notion the Euclid spine needs — degree, divisibility, gcd, irreducibility,
multiplicity — is a **coefficient-level** statement, so that noncanonicity has to be deleted once,
here, rather than routed around at every use.

## The choice, and the two rejected alternatives

**Chosen: normalise once, carry the invariant at type level.** `pnorm` strips trailing (high-power)
zero coefficients; `PolyNF` bundles a list with the proof that it is normalised. Canonical
polynomials are equal exactly when their coefficient lists are equal, which is what makes the rest
of the spine syntactic.

*Rejected — `pev` as the equality relation.* Defining `P ≡ Q` as `∀ x, pev P x = pev Q x` looks
lighter, but Euclid eventually needs to run it backwards: `(∀ x, pev P x = 0) → P` is the zero
polynomial. That buys polynomial extensionality and root machinery merely to *identify zero* — the
wrong dependency direction for a layer that is supposed to be prior to all of it. **`pev` belongs at
the semantic boundary, as the interpretation theorem, not as the algebra's equality.**

*Rejected — a quotient of `List Real` by trailing-zero equivalence.* Mathematically clean,
mechanically unnecessary, and it makes division opaque. There is exactly one source of
noncanonicity; delete it, do not quotient by it.

## Why the order axioms stay out

The tempting way to get a degree is to read it off `pev_leading_form`, which already extracts an
exponent for any nonzero list. It carries `ltR`, `leR`, `lt_total`, `lt_trans_ax`,
`add_lt_add_left`, `le_iff_lt_or_eq`, `lt_irrefl_ax` — the whole ordered-real base. Importing that
into a purely algebraic layer would be a regression, and the axiom ledger would show it.

So the zero test on coefficients is **classical equality** (`Classical.propDecidable`, file-local),
never `instDecLT`/`instDecLE`, which would drag `ltR`/`leR` in through the back door for nothing
more than trimming a list. **For a normalised nonzero polynomial the degree is just `length - 1`**,
so division can reuse the `deflate_length` termination pattern with no analysis anywhere.

## Cancellation lives inside normalisation

Raw list addition does **not** preserve the invariant: `[1,1] + [-1,-1]` cancels its leading term.
Rather than predict that, the canonical operations are *defined* as `pnorm (raw …)`, so every
cancellation is normalisation rather than a side condition. This is the same move that made the
rational-germ work go through: choose the representation in which cancellation is canonical
computation.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Normalisation

Split into a one-step `pconsN` and a fold, deliberately. Written as a single `match` on `pnorm cs`,
every unfolding step needs the equation compiler's `match` shape spelled out at each use; factored
this way `pnorm (c :: cs) = pconsN c (pnorm cs)` is `rfl` and each lemma is one case split. Same
doctrine as everywhere else here: decompose before reaching for automation. -/

/-- Prepend a coefficient to an already-normalised tail, preserving normality. The only place the
zero test happens, and it is **classical equality** — never `instDecLT`/`instDecLE`, which would
drag `ltR`/`leR` into the algebra layer merely to trim a list. -/
noncomputable def pconsN (c : Real) : List Real → List Real
  | []      => if c = 0 then [] else [c]
  | d :: ds => c :: d :: ds

/-- Strip trailing (high-power) zero coefficients. Coefficient lists are little-endian —
`pev [c₀, c₁, …] x = c₀ + x·(c₁ + …)` — so the *last* entry is the leading coefficient. -/
noncomputable def pnorm : List Real → List Real
  | []      => []
  | c :: cs => pconsN c (pnorm cs)

/-- The invariant: empty, or the last coefficient is nonzero. Stated through `getLast?` so no
nonemptiness proof has to be carried, and so `[]` satisfies it vacuously. -/
def PNormal (p : List Real) : Prop := ∀ c : Real, p.getLast? = some c → c ≠ 0

theorem pNormal_nil : PNormal [] := by intro c hc; exact absurd hc (by simp)

/-- `pconsN` preserves the invariant — the one-step core of `pnorm_normal`. -/
theorem pconsN_normal (c : Real) : ∀ t : List Real, PNormal t → PNormal (pconsN c t) := by
  intro t
  cases t with
  | nil =>
      intro _
      by_cases hc : c = 0
      · show PNormal (if c = 0 then [] else [c])
        rw [if_pos hc]; exact pNormal_nil
      · show PNormal (if c = 0 then [] else [c])
        rw [if_neg hc]
        intro b hb
        have hbc : c = b := by simpa using hb
        rw [← hbc]; exact hc
  | cons d ds =>
      intro ht
      show PNormal (c :: d :: ds)
      intro b hb
      refine ht b ?_
      simpa using hb

/-- `pconsN` is the Horner step under evaluation — the one-step core of `pev_pnorm`. -/
theorem pev_pconsN (c : Real) : ∀ (t : List Real) (x : Real),
    pev (pconsN c t) x = c + x * pev t x := by
  intro t
  cases t with
  | nil =>
      intro x
      by_cases hc : c = 0
      · show pev (if c = 0 then [] else [c]) x = c + x * pev ([] : List Real) x
        rw [if_pos hc, hc]
        show (0 : Real) = 0 + x * 0
        mach_ring
      · show pev (if c = 0 then [] else [c]) x = c + x * pev ([] : List Real) x
        rw [if_neg hc]
        rfl
  | cons d ds => intro x; rfl

/-- **`pnorm` produces a normalised list.** -/
theorem pnorm_normal : ∀ L : List Real, PNormal (pnorm L) := by
  intro L
  induction L with
  | nil => exact pNormal_nil
  | cons a as ih => exact pconsN_normal a (pnorm as) ih

/-- **The interpretation theorem — the only bridge to `pev`.** Normalising does not change the
polynomial function, so every algebraic fact proved on canonical lists transports. -/
theorem pev_pnorm : ∀ (L : List Real) (x : Real), pev (pnorm L) x = pev L x := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a as ih =>
      intro x
      show pev (pconsN a (pnorm as)) x = a + x * pev as x
      rw [pev_pconsN a (pnorm as) x, ih x]

/-- A normalised list is its own normal form — so `pnorm` is canonical, not merely idempotent. -/
theorem pnorm_eq_self : ∀ L : List Real, PNormal L → pnorm L = L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a as ih =>
      cases as with
      | nil =>
          intro hL
          have ha : a ≠ 0 := hL a rfl
          show pconsN a (pnorm ([] : List Real)) = [a]
          show pconsN a [] = [a]
          show (if a = 0 then [] else [a]) = [a]
          rw [if_neg ha]
      | cons b bs =>
          intro hL
          have hsub : PNormal (b :: bs) := by
            intro c hc; refine hL c ?_; simpa using hc
          show pconsN a (pnorm (b :: bs)) = a :: b :: bs
          rw [ih hsub]
          rfl

theorem pnorm_idem (L : List Real) : pnorm (pnorm L) = pnorm L :=
  pnorm_eq_self (pnorm L) (pnorm_normal L)

/-! ## Convict specimens

`pnorm` is the representation decision, so it is specimened **before** anything is built on it. A
normaliser that quietly did nothing, or quietly did too much, would not be caught by any downstream
theorem: every later statement is *about* normalised lists, so a wrong normaliser makes them
vacuously fine rather than false. The invariant lemmas above are not a substitute either —
`pnorm_normal` is satisfied by the constant function `fun _ => []`.

Nothing here can be `decide`d: `Real` is axiomatised and the coefficient test is classical. These
are proofs. -/

theorem pnorm_nil_zero : pnorm [(0 : Real)] = [] := by
  show (if (0 : Real) = 0 then [] else [(0 : Real)]) = []
  rw [if_pos rfl]

/-- Already canonical: unchanged. -/
theorem pnorm_specimen_canonical : pnorm [(1 : Real)] = [1] := by
  show (if (1 : Real) = 0 then [] else [(1 : Real)]) = [1]
  rw [if_neg one_ne_zero]

/-- One trailing zero is stripped. -/
theorem pnorm_specimen_one_trailing : pnorm [(1 : Real), 0] = [1] := by
  show pconsN (1 : Real) (pnorm [(0 : Real)]) = [1]
  rw [pnorm_nil_zero]
  show (if (1 : Real) = 0 then [] else [(1 : Real)]) = [1]
  rw [if_neg one_ne_zero]

/-- Trailing zeros are stripped to exhaustion, not one at a time. -/
theorem pnorm_specimen_two_trailing : pnorm [(1 : Real), 0, 0] = [1] := by
  have h : pnorm [(0 : Real), 0] = [] := by
    show pconsN (0 : Real) (pnorm [(0 : Real)]) = []
    rw [pnorm_nil_zero]
    show (if (0 : Real) = 0 then [] else [(0 : Real)]) = []
    rw [if_pos rfl]
  show pconsN (1 : Real) (pnorm [(0 : Real), 0]) = [1]
  rw [h]
  show (if (1 : Real) = 0 then [] else [(1 : Real)]) = [1]
  rw [if_neg one_ne_zero]

/-- An all-zero list is the zero polynomial. -/
theorem pnorm_specimen_all_zero : pnorm [(0 : Real), 0] = [] := by
  show pconsN (0 : Real) (pnorm [(0 : Real)]) = []
  rw [pnorm_nil_zero]
  show (if (0 : Real) = 0 then [] else [(0 : Real)]) = []
  rw [if_pos rfl]

/-- **The discriminating specimen.** An *interior* zero must survive: `[0, 1]` is `x`, and a
normaliser that removed zero coefficients rather than *trailing* zero coefficients would return
`[1]`, which is the constant `1`. Every other specimen here passes under that wrong implementation;
this one convicts it. -/
theorem pnorm_specimen_interior_zero_survives : pnorm [(0 : Real), 1] = [0, 1] := by
  show pconsN (0 : Real) (pnorm [(1 : Real)]) = [0, 1]
  rw [pnorm_specimen_canonical]
  rfl

/-- **Leading cancellation.** `(1 + x) + (−1 − x)` is the zero polynomial, and raw list addition
cannot see it — `padd` returns a length-2 list whose entries only *evaluate* to zero. This is the
case that makes the canonical operations normalise after the raw operation rather than assume the
raw operation preserved the invariant. -/
theorem pnorm_specimen_leading_cancellation :
    pnorm (padd [(1 : Real), 1] [0 - 1, 0 - 1]) = [] := by
  have e : padd [(1 : Real), 1] [(0 : Real) - 1, 0 - 1] = [(0 : Real), 0] := by
    show [(1 + ((0 : Real) - 1)), (1 + ((0 : Real) - 1))] = [(0 : Real), 0]
    have h : (1 + ((0 : Real) - 1)) = 0 := by mach_ring
    rw [h]
  rw [e]
  exact pnorm_specimen_all_zero

/-- Normalisation does not move the polynomial function — the specimen form of `pev_pnorm`. -/
theorem pnorm_specimen_value_preserved (x : Real) :
    pev (pnorm [(1 : Real), 0, 0]) x = pev [(1 : Real), 0, 0] x := pev_pnorm _ x

/-! ## The canonical type -/

/-- A polynomial in canonical form: coefficients with no trailing zeros. Two `PolyNF` are equal
exactly when their coefficient lists are, `normal` being a `Prop` and so proof-irrelevant. -/
structure PolyNF where
  coeffs : List Real
  normal : PNormal coeffs

namespace PolyNF

/-- The canonical form of an arbitrary coefficient list. -/
noncomputable def of (L : List Real) : PolyNF := ⟨pnorm L, pnorm_normal L⟩

/-- Evaluation, through the underlying coefficients. -/
noncomputable def eval (p : PolyNF) (x : Real) : Real := pev p.coeffs x

/-- `of` does not change the function it denotes — `pev_pnorm`, packaged. -/
theorem eval_of (L : List Real) (x : Real) : (of L).eval x = pev L x := pev_pnorm L x

/-- The zero polynomial. -/
def zero : PolyNF := ⟨[], fun _ h => absurd h (by simp)⟩

/-- **Degree, zero-aware.** `none` for the zero polynomial; otherwise `length - 1`, which is exact
because the representation is canonical. This is the fact that lets division terminate on a list
length rather than on an analytic leading form. -/
def pdeg (p : PolyNF) : Option Nat :=
  match p.coeffs with
  | []     => none
  | _ :: t => some t.length

/-- The leading coefficient of a nonzero canonical polynomial: its last entry. -/
noncomputable def plead (p : PolyNF) : Option Real := p.coeffs.getLast?

/-- `pdeg` is `none` exactly on the zero polynomial. -/
theorem pdeg_eq_none_iff (p : PolyNF) : p.pdeg = none ↔ p.coeffs = [] := by
  cases h : p.coeffs with
  | nil => simp [pdeg, h]
  | cons a t => simp [pdeg, h]

/-- For a nonzero canonical polynomial the leading coefficient exists and is **nonzero** — the
invariant, cashed out. -/
theorem plead_ne_zero {p : PolyNF} {c : Real} (h : p.plead = some c) : c ≠ 0 :=
  p.normal c h

/-! ## Canonical operations — cancellation happens inside `pnorm`

Raw addition does not preserve the invariant (`[1,1] + [-1,-1]` cancels its leading term), so the
canonical operations normalise after the raw operation rather than assuming it was unnecessary. -/

noncomputable def add (p q : PolyNF) : PolyNF := of (padd p.coeffs q.coeffs)
noncomputable def sub (p q : PolyNF) : PolyNF := of (psub p.coeffs q.coeffs)
noncomputable def mul (p q : PolyNF) : PolyNF := of (pmul p.coeffs q.coeffs)
noncomputable def scale (r : Real) (p : PolyNF) : PolyNF := of (pscale r p.coeffs)

theorem eval_add (p q : PolyNF) (x : Real) : (p.add q).eval x = p.eval x + q.eval x := by
  show pev (pnorm (padd p.coeffs q.coeffs)) x = pev p.coeffs x + pev q.coeffs x
  rw [pev_pnorm, pev_padd]

theorem eval_sub (p q : PolyNF) (x : Real) : (p.sub q).eval x = p.eval x - q.eval x := by
  show pev (pnorm (psub p.coeffs q.coeffs)) x = pev p.coeffs x - pev q.coeffs x
  rw [pev_pnorm, pev_psub]

theorem eval_mul (p q : PolyNF) (x : Real) : (p.mul q).eval x = p.eval x * q.eval x := by
  show pev (pnorm (pmul p.coeffs q.coeffs)) x = pev p.coeffs x * pev q.coeffs x
  rw [pev_pnorm, pev_pmul]

theorem eval_scale (r : Real) (p : PolyNF) (x : Real) : (scale r p).eval x = r * p.eval x := by
  show pev (pnorm (pscale r p.coeffs)) x = r * pev p.coeffs x
  rw [pev_pnorm, pev_pscale]

end PolyNF

end MachLib
