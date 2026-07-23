import MachLib.AbsoluteFoldNest
import MachLib.AbsoluteFoldLocal
import MachLib.HyperbolicLipschitz
import MachLib.TransNodes

/-!
# The absolute fold over NESTED arithmetic + LOCAL-Lipschitz transcendental trees

`AbsoluteFoldNest` closed arbitrary nesting for the GLOBALLY-Lipschitz `tr1` primitives — no domain
needed, so the recursion was free. This closes the harder case flagged there (and in
`AbsoluteFoldLocal`'s own scope note) as the remaining open piece: arbitrary nesting for
LOCAL-Lipschitz primitives (`exp`,`log`,`sqrt`,`asin`,`acos`,`sinh`,`cosh`,`tan`,`log10`), where each
occurrence needs its OWN bounded domain `[lo,hi]`, and both the computed *and* exact value of the
subtree it sits over must be shown to land in it.

**The coupling `AbsoluteFoldLocal` flagged**: at a nested local-Lipschitz node, the domain condition on
the COMPUTED input (`toR (evalEML … e).toF ∈ [lo,hi]`) is a fact about a float value produced by
evaluating an arbitrarily deep subtree — it is not "given" the way a leaf variable's value is. The fix
here is NOT to derive the computed-value range from the exact-value range plus the accumulated error
(which would need directed-rounding interval arithmetic, genuinely harder); it is to require BOTH
ranges as *separate, explicit* hypotheses at every `tr1` occurrence — exactly what the non-recursive
`pipeline_tr1_of_arith_local` already does at the top level. `IsFoldLocal` just repeats that same
two-hypothesis shape at *every* node, recursively, instead of only the outermost one. No new
domain-tracking machinery is invented; the existing per-primitive obligation is threaded through the
tree.

**Why the Lipschitz data lives on the constructor, not a global parameter** (unlike
`AbsoluteFoldNest`'s `Lip1 : Trans1 → Real`): the Lipschitz constant genuinely differs by primitive
AND by the domain chosen at that occurrence (`exp hi`, `1/lo`, `1/(√lo+√lo)`, `1/√(1-R²)`, `cosh R`,
`sinh R`, `1/cos²R`, …) — there is no single closed-form function of `(t, lo, hi)` covering all of
them uniformly, and the SAME primitive can appear twice in one tree with different domains. So
`IsFoldLocal.tr1` carries the per-occurrence `(L, lo, hi, hLnn, hLip)` bundle directly, exactly
mirroring `pipeline_tr1_of_arith_local`'s own argument list — pure plumbing over the Lipschitz lemmas
already proven in `ExpLipschitz`/`TransNodes`/`SqrtNode`/`Log10Lipschitz`/`InverseTrigBounded`/
`HyperbolicLipschitz`/`TanLipschitz`. No new math, no new axioms.

Like `AbsoluteFoldNest`, the bound stays EXISTENTIAL (`∃ E, AbsEnc E …`), so the recursion composes
cleanly — each node's error is whatever `absenc_*`/`absenc_lip_local` witnesses. The per-primitive
rounding bound is a single theorem-level function `Eround1 : Trans1 → Real` (the absolute-disclosure
shape `FPGrounding.lean` uses for each `real_X_eps`, generalised to an abstract parameter here rather
than instantiated concretely). `sorryAx`-free.
-/

namespace Certcom

open MachLib.Real

/-- The nestable fragment for LOCAL-Lipschitz primitives: arithmetic plus `tr1` nodes, where each
occurrence carries its own witnessed domain `[lo,hi]`, Lipschitz certificate, range obligations on
both the computed and exact value of the subtree underneath it, AND — since 2026-07-22 — its own
point-specific rounding fact (`hround`).

**Why `hround` moved from a separate, universally-quantified pipeline parameter into this
constructor, per occurrence** (erratum-driven redesign, alongside `FPGrounding.lean`'s domain-
restricted primitive axioms): the ORIGINAL design had `nested_fold_local`/`pipeline_nested_local`
take one shared `hround : ∀ t a, abs (…) ≤ Eround1 t` — universally quantified over EVERY primitive
at EVERY input, with no domain restriction, because that's what the (erroneously unconditional)
primitive axioms made possible. Once those axioms became honestly domain-restricted, several
primitives need an EXTRA validity condition beyond plain `lo ≤ · ≤ hi` interval membership — `log`/
`sqrt`/`log10` need positivity (`0 < lo`), `asin`/`acos`/`tan` need their argument strictly inside
their true domain (`R < 1`, `R < π/2`) — and these conditions are DIFFERENT per primitive, with no
single uniform shape. A totalized `∀ t, …` dispatcher covering all 14 primitives at ARBITRARY `lo`/
`hi` genuinely cannot exist for those six (the same overclaim the erratum fixed, just moved one level
up); patching around it by picking an oversized fallback bound for the "invalid" branches would
silently reintroduce the very false-axiom problem this whole redesign removes. The honest fix: since
`pipeline_tr1_of_arith_local` (the FLAT, single-level version) already takes `hround` POINT-
SPECIFIC — one inequality at the one input value that occurrence actually uses, not a universal
statement — give `IsFoldLocal.tr1` the same shape, exactly alongside the Lipschitz data it already
carries per-occurrence. The caller building an `IsFoldLocal` proof term supplies whatever rounding
fact is appropriate for THAT primitive at THAT domain, using whatever validity condition it happens
to need (`real_log_rounds` needs `0 < lo` in scope; `real_cosh_rounds` needs nothing extra) — no
totalization, no universal quantification, no primitive-agnostic dispatcher required. -/
inductive IsFoldLocal (toR : Float → MachLib.Real)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (env : Env) : EML → Prop
  | lit (c : Float) : IsFoldLocal toR i1 i2 realOf1 env (.lit c)
  | var (s : String) : IsFoldLocal toR i1 i2 realOf1 env (.var s)
  | add (a b : EML) : IsFoldLocal toR i1 i2 realOf1 env a → IsFoldLocal toR i1 i2 realOf1 env b →
      IsFoldLocal toR i1 i2 realOf1 env (.bin .add a b)
  | sub (a b : EML) : IsFoldLocal toR i1 i2 realOf1 env a → IsFoldLocal toR i1 i2 realOf1 env b →
      IsFoldLocal toR i1 i2 realOf1 env (.bin .sub a b)
  | mul (a b : EML) : IsFoldLocal toR i1 i2 realOf1 env a → IsFoldLocal toR i1 i2 realOf1 env b →
      IsFoldLocal toR i1 i2 realOf1 env (.bin .mul a b)
  | neg (a : EML) : IsFoldLocal toR i1 i2 realOf1 env a →
      IsFoldLocal toR i1 i2 realOf1 env (.neg a)
  | tr1 (t : Trans1) (a : EML) (L lo hi Eround : MachLib.Real)
      (hLnn : 0 ≤ L)
      (hLip : ∀ p q : MachLib.Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi →
          abs (realOf1 t p - realOf1 t q) ≤ L * abs (p - q))
      (hflx_lo : lo ≤ toR (evalEML i1 i2 env a).toF) (hflx_hi : toR (evalEML i1 i2 env a).toF ≤ hi)
      (hxe_lo : lo ≤ exactRn toR realOf1 env a) (hxe_hi : exactRn toR realOf1 env a ≤ hi)
      (hround : abs (toR (i1 t (evalEML i1 i2 env a).toF)
          - realOf1 t (toR (evalEML i1 i2 env a).toF)) ≤ Eround) :
      IsFoldLocal toR i1 i2 realOf1 env a → IsFoldLocal toR i1 i2 realOf1 env (.tr1 t a)

/-- **Absolute forward error over a nested arithmetic + LOCAL-Lipschitz transcendental tree.** For any
`IsFoldLocal e`, T2's `evalEML` for `e`, through `toR`, is within SOME absolute bound of the exact real
`exactRn … e` — one structural induction, `tr1` discharged by `absenc_lip_local` using the
per-occurrence Lipschitz + range + rounding data the constructor carries.

**No separate `hround` parameter** (erratum-driven redesign, 2026-07-22 — see `IsFoldLocal`'s own
docstring for the full motivation): earlier this theorem took one shared, universally-quantified
`hround : ∀ t a, abs (…) ≤ Eround1 t`, which is impossible to state honestly once several primitives
need validity conditions beyond plain interval membership (`log` needs `0 < lo`, `asin` needs
`R < 1`, …) that don't fit one primitive-agnostic shape. `IsFoldLocal.tr1` now carries its own
point-specific `hround` per occurrence instead — exactly what this theorem's `tr1` case consumes
directly, no totalization required. -/
theorem nested_fold_local {toR : Float → MachLib.Real} (br : FPBridge toR)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env) :
    ∀ e : EML, IsFoldLocal toR i1 i2 realOf1 env e →
      ∃ E, AbsEnc E (toR (evalEML i1 i2 env e).toF) (exactRn toR realOf1 env e) := by
  intro e he
  induction he with
  | lit c => exact ⟨0, absenc_exact (toR c)⟩
  | var s => exact ⟨0, absenc_exact (toR (env s).toF)⟩
  | add a b _ _ iha ihb =>
      obtain ⟨Ea, iha⟩ := iha; obtain ⟨Eb, ihb⟩ := ihb
      exact ⟨_, absenc_add iha ihb (br.add (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF)⟩
  | sub a b _ _ iha ihb =>
      obtain ⟨Ea, iha⟩ := iha; obtain ⟨Eb, ihb⟩ := ihb
      exact ⟨_, absenc_sub iha ihb (br.sub (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF)⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨Ea, iha⟩ := iha; obtain ⟨Eb, ihb⟩ := ihb
      exact ⟨_, absenc_mul iha ihb (br.mul (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF)⟩
  | neg a _ iha =>
      obtain ⟨Ea, iha⟩ := iha
      refine ⟨Ea, ?_⟩
      show AbsEnc Ea (toR (-(evalEML i1 i2 env a).toF)) (-(exactRn toR realOf1 env a))
      rw [br.neg (evalEML i1 i2 env a).toF]
      exact absenc_neg iha
  | tr1 t a L lo hi Eround hLnn hLip hflx_lo hflx_hi hxe_lo hxe_hi hround _ iha =>
      obtain ⟨Ea, iha⟩ := iha
      exact ⟨_, absenc_lip_local hLnn hLip iha hflx_lo hflx_hi hxe_lo hxe_hi hround⟩

/-- **The nested LOCAL-Lipschitz pipeline, through the emitted C.** For any `IsFoldLocal e`, the value
the emitted C computes, through `toR`, is within some absolute bound of the exact `exactRn … e` —
arbitrary nesting of arithmetic and LOCAL-Lipschitz transcendentals, each with its own domain and its
own point-specific rounding fact (carried by `IsFoldLocal.tr1` itself — see its docstring; no separate
`hround` parameter needed here, unlike this theorem's pre-2026-07-22 form). -/
theorem pipeline_nested_local {toR : Float → MachLib.Real} (br : FPBridge toR)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (e : EML) (he : IsFoldLocal toR i1 i2 realOf1 env e) :
    ∃ E, AbsEnc E (toR (evalC r1 r2 env (emitC e)).toF) (exactRn toR realOf1 env e) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env]
  exact nested_fold_local br realOf1 i1 i2 env e he

/-! ## Bridges to the arithmetic fragment: lifting a plain `IsArith` kernel into the nested fold -/

/-- **Every arithmetic tree is (trivially) in the nested-local fragment** — `IsArith`'s constructors
are a strict subset of `IsFoldLocal`'s (no `tr1` case exercised). Lets a `pidRawEML`-style arithmetic
leaf feed directly into a `tr1` node built on top of it, without re-deriving its structure by hand. -/
theorem isFoldLocal_of_isArith {toR : Float → MachLib.Real}
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (env : Env) :
    ∀ {e : EML}, IsArith e → IsFoldLocal toR i1 i2 realOf1 env e := by
  intro e he
  induction he with
  | lit c => exact .lit c
  | var s => exact .var s
  | add a b _ _ iha ihb => exact .add _ _ iha ihb
  | sub a b _ _ iha ihb => exact .sub _ _ iha ihb
  | mul a b _ _ iha ihb => exact .mul _ _ iha ihb
  | neg a _ iha => exact .neg _ iha

/-- **`exactRn` agrees with the plain arithmetic `exactR` on an `IsArith` tree** — since `exactRn`'s
non-`tr1` cases are definitionally identical to `exactR`'s, and `IsArith` never exercises `.tr1`. Lets
a nested certificate's conclusion be stated in terms of the familiar `exactR` (as every flat
`pid_X_grounded` already is) instead of the more general `exactRn`. -/
theorem exactRn_eq_exactR_of_arith {toR : Float → MachLib.Real}
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (env : Env) :
    ∀ {e : EML}, IsArith e → exactRn toR realOf1 env e = exactR toR env e := by
  intro e he
  induction he with
  | lit c => rfl
  | var s => rfl
  | add a b _ _ iha ihb =>
      show exactRn toR realOf1 env a + exactRn toR realOf1 env b
        = exactR toR env a + exactR toR env b
      rw [iha, ihb]
  | sub a b _ _ iha ihb =>
      show exactRn toR realOf1 env a - exactRn toR realOf1 env b
        = exactR toR env a - exactR toR env b
      rw [iha, ihb]
  | mul a b _ _ iha ihb =>
      show exactRn toR realOf1 env a * exactRn toR realOf1 env b
        = exactR toR env a * exactR toR env b
      rw [iha, ihb]
  | neg a _ iha =>
      show -(exactRn toR realOf1 env a) = -(exactR toR env a)
      rw [iha]

/-! ## Non-vacuity: two genuine levels of LOCAL-Lipschitz nesting -/

/-- Real semantics for the two primitives the demo below nests: `.sinh ↦ sinh`, `.ln ↦ log`. -/
private noncomputable def demoRealOf1 : Trans1 → MachLib.Real → MachLib.Real
  | .sinh => sinh
  | .ln => log
  | _ => fun _ => 0

/-- **`log(sinh(x) + y)` is in the nested-local fragment.** A LOCAL-Lipschitz primitive (`log`,
one-sided domain `[lo,hi]`, `lo>0`) sitting over an arithmetic subtree that ITSELF contains another
LOCAL-Lipschitz primitive (`sinh`, symmetric domain `[-R,R]`) — exactly the shape `AbsoluteFoldNest`
could not cover. The range/positivity obligations at each level are supplied as explicit hypotheses
(the caller's job, matching every flat `pid_X_grounded` instance in `FPGrounding.lean`); this is the
STRUCTURAL demonstration that two real, distinct per-primitive Lipschitz certificates (`sinh_lip_local`,
`log_lip_local`) compose through the recursion, not a numeric instance. -/
example {toR : Float → MachLib.Real} (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (env : Env) (R lo hi Eround1 Eround2 : MachLib.Real) (hlo : 0 < lo)
    (hflx_lo1 : -R ≤ toR (evalEML i1 i2 env (.var "x")).toF)
    (hflx_hi1 : toR (evalEML i1 i2 env (.var "x")).toF ≤ R)
    (hxe_lo1 : -R ≤ exactRn toR demoRealOf1 env (.var "x"))
    (hxe_hi1 : exactRn toR demoRealOf1 env (.var "x") ≤ R)
    (hround1 : abs (toR (i1 .sinh (evalEML i1 i2 env (.var "x")).toF)
        - sinh (toR (evalEML i1 i2 env (.var "x")).toF)) ≤ Eround1)
    (hflx_lo2 : lo ≤ toR (evalEML i1 i2 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y"))).toF)
    (hflx_hi2 : toR (evalEML i1 i2 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y"))).toF ≤ hi)
    (hxe_lo2 : lo ≤ exactRn toR demoRealOf1 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y")))
    (hxe_hi2 : exactRn toR demoRealOf1 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y")) ≤ hi)
    (hround2 : abs (toR (i1 .ln (evalEML i1 i2 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y"))).toF)
        - log (toR (evalEML i1 i2 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y"))).toF)) ≤ Eround2) :
    IsFoldLocal toR i1 i2 demoRealOf1 env
      (.tr1 .ln (.bin .add (.tr1 .sinh (.var "x")) (.var "y"))) :=
  .tr1 .ln _ (1 / lo) lo hi Eround2 (le_of_lt (one_div_pos_of_pos hlo)) (log_lip_local lo hi hlo)
    hflx_lo2 hflx_hi2 hxe_lo2 hxe_hi2 hround2
    (.add _ _
      (.tr1 .sinh _ (cosh R) (-R) R Eround1 (le_of_lt (cosh_pos R)) (sinh_lip_local R)
        hflx_lo1 hflx_hi1 hxe_lo1 hxe_hi1 hround1 (.var "x"))
      (.var "y"))

end Certcom
