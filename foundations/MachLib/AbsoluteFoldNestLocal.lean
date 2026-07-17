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
occurrence carries its own witnessed domain `[lo,hi]`, Lipschitz certificate, and range obligations on
both the computed and exact value of the subtree underneath it. -/
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
  | tr1 (t : Trans1) (a : EML) (L lo hi : MachLib.Real)
      (hLnn : 0 ≤ L)
      (hLip : ∀ p q : MachLib.Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi →
          abs (realOf1 t p - realOf1 t q) ≤ L * abs (p - q))
      (hflx_lo : lo ≤ toR (evalEML i1 i2 env a).toF) (hflx_hi : toR (evalEML i1 i2 env a).toF ≤ hi)
      (hxe_lo : lo ≤ exactRn toR realOf1 env a) (hxe_hi : exactRn toR realOf1 env a ≤ hi) :
      IsFoldLocal toR i1 i2 realOf1 env a → IsFoldLocal toR i1 i2 realOf1 env (.tr1 t a)

/-- **Absolute forward error over a nested arithmetic + LOCAL-Lipschitz transcendental tree.** For any
`IsFoldLocal e`, T2's `evalEML` for `e`, through `toR`, is within SOME absolute bound of the exact real
`exactRn … e` — one structural induction, `tr1` discharged by `absenc_lip_local` using the
per-occurrence Lipschitz + range data the constructor carries. -/
theorem nested_fold_local {toR : Float → MachLib.Real} (br : FPBridge toR)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (Eround1 : Trans1 → MachLib.Real)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env)
    (hround : ∀ (t : Trans1) (a : Float),
        abs (toR (i1 t a) - realOf1 t (toR a)) ≤ Eround1 t) :
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
  | tr1 t a L lo hi hLnn hLip hflx_lo hflx_hi hxe_lo hxe_hi _ iha =>
      obtain ⟨Ea, iha⟩ := iha
      exact ⟨_, absenc_lip_local hLnn hLip iha hflx_lo hflx_hi hxe_lo hxe_hi
        (hround t (evalEML i1 i2 env a).toF)⟩

/-- **The nested LOCAL-Lipschitz pipeline, through the emitted C.** For any `IsFoldLocal e`, the value
the emitted C computes, through `toR`, is within some absolute bound of the exact `exactRn … e` —
arbitrary nesting of arithmetic and LOCAL-Lipschitz transcendentals, each with its own domain. -/
theorem pipeline_nested_local {toR : Float → MachLib.Real} (br : FPBridge toR)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (Eround1 : Trans1 → MachLib.Real)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hround : ∀ (t : Trans1) (a : Float),
        abs (toR (i1 t a) - realOf1 t (toR a)) ≤ Eround1 t)
    (e : EML) (he : IsFoldLocal toR i1 i2 realOf1 env e) :
    ∃ E, AbsEnc E (toR (evalC r1 r2 env (emitC e)).toF) (exactRn toR realOf1 env e) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env]
  exact nested_fold_local br realOf1 Eround1 i1 i2 env hround e he

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
    (env : Env) (R lo hi : MachLib.Real) (hlo : 0 < lo)
    (hflx_lo1 : -R ≤ toR (evalEML i1 i2 env (.var "x")).toF)
    (hflx_hi1 : toR (evalEML i1 i2 env (.var "x")).toF ≤ R)
    (hxe_lo1 : -R ≤ exactRn toR demoRealOf1 env (.var "x"))
    (hxe_hi1 : exactRn toR demoRealOf1 env (.var "x") ≤ R)
    (hflx_lo2 : lo ≤ toR (evalEML i1 i2 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y"))).toF)
    (hflx_hi2 : toR (evalEML i1 i2 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y"))).toF ≤ hi)
    (hxe_lo2 : lo ≤ exactRn toR demoRealOf1 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y")))
    (hxe_hi2 : exactRn toR demoRealOf1 env (.bin .add (.tr1 .sinh (.var "x")) (.var "y")) ≤ hi) :
    IsFoldLocal toR i1 i2 demoRealOf1 env
      (.tr1 .ln (.bin .add (.tr1 .sinh (.var "x")) (.var "y"))) :=
  .tr1 .ln _ (1 / lo) lo hi (le_of_lt (one_div_pos_of_pos hlo)) (log_lip_local lo hi hlo)
    hflx_lo2 hflx_hi2 hxe_lo2 hxe_hi2
    (.add _ _
      (.tr1 .sinh _ (cosh R) (-R) R (le_of_lt (cosh_pos R)) (sinh_lip_local R)
        hflx_lo1 hflx_hi1 hxe_lo1 hxe_hi1 (.var "x"))
      (.var "y"))

end Certcom
