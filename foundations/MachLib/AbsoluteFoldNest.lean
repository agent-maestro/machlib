import MachLib.AbsoluteFold

/-!
# The absolute fold over NESTED arithmetic + transcendental trees

`AbsoluteFold` handled the arithmetic fragment; `pipeline_tr1_of_arith` put ONE transcendental layer on
top. This closes the recursion: `IsFold` allows `tr1` nodes ANYWHERE (transcendental-of-transcendental,
arithmetic-of-transcendental, …), for the primitives marked globally-Lipschitz by `globLip`, and
`nested_fold` proves the emitted C stays within *some* absolute bound of the exact interpretation over
the whole nested tree.

The move that makes recursion clean: the bound is EXISTENTIAL (`∃ E, AbsEnc E …`), not a closed-form
`absErr`. So the `tr1` step needs no weakening (the witnessed `E` may depend on the float eval) — each
node just assembles its `E` from the sub-bounds via the corresponding `absenc_*` lemma. `exactRn` (the
exact real interpretation, now with a `tr1` case `realOf1 t (exactRn e)`) is the only new recursive
definition; it is `noncomputable` + mutual-with-`List` like `evalEML`/`exactR`, so it reduces.

Scope: the GLOBALLY-Lipschitz `tr1` primitives (`sin`/`cos`/`tanh`/`arctan`/`abs`). The local-Lipschitz
ones (`exp`/`log`/…) need per-node domain tracking through the nesting — a further extension. `tr2`
decomposes into `tr1` + arithmetic. `sorryAx`-free.
-/

namespace Certcom

open MachLib.Real

/- Exact real interpretation of a nested arithmetic + `tr1` tree; `tr1` maps through `realOf1`. -/
mutual
  noncomputable def exactRn (toR : Float → MachLib.Real)
      (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (env : Env) : EML → MachLib.Real
    | .lit c => toR c
    | .var s => toR (env s).toF
    | .bin op a b =>
        match op with
        | .add => exactRn toR realOf1 env a + exactRn toR realOf1 env b
        | .sub => exactRn toR realOf1 env a - exactRn toR realOf1 env b
        | .mul => exactRn toR realOf1 env a * exactRn toR realOf1 env b
        | _ => 0
    | .neg a => -(exactRn toR realOf1 env a)
    | .tr1 t e => realOf1 t (exactRn toR realOf1 env e)
    | .elet _ _ _ => 0
    | .tr2 _ _ _ => 0
    | .cond _ _ _ => 0
    | .vlit es => exactRns toR realOf1 env es
    | .idx _ _ => 0
    | .vsum _ => 0
    | .dot _ _ => 0
  noncomputable def exactRns (toR : Float → MachLib.Real)
      (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (env : Env) : List EML → MachLib.Real
    | [] => 0
    | e :: es => exactRn toR realOf1 env e + exactRns toR realOf1 env es
end

/-- The nestable fragment: arithmetic (`lit`/`var`/`+`/`−`/`×`/neg) plus `tr1` nodes for the primitives
that `globLip` marks globally-Lipschitz. -/
inductive IsFold (globLip : Trans1 → Prop) : EML → Prop
  | lit (c : Float) : IsFold globLip (.lit c)
  | var (s : String) : IsFold globLip (.var s)
  | add (a b : EML) : IsFold globLip a → IsFold globLip b → IsFold globLip (.bin .add a b)
  | sub (a b : EML) : IsFold globLip a → IsFold globLip b → IsFold globLip (.bin .sub a b)
  | mul (a b : EML) : IsFold globLip a → IsFold globLip b → IsFold globLip (.bin .mul a b)
  | neg (a : EML) : IsFold globLip a → IsFold globLip (.neg a)
  | tr1 (t : Trans1) (a : EML) : globLip t → IsFold globLip a → IsFold globLip (.tr1 t a)

/-- **Absolute forward error over a nested arithmetic + transcendental tree.** For any `IsFold e`, T2's
`evalEML` for `e`, through `toR`, is within SOME absolute bound of the exact real `exactRn … e` — one
structural induction, each node discharged by its `absenc_*` lemma. `tr1` uses `absenc_lip` with the
primitive's global Lipschitz (`hLip`) + rounding spec (`hround`); no weakening thanks to the existential
bound. -/
theorem nested_fold {toR : Float → MachLib.Real} (br : FPBridge toR)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (Lip1 : Trans1 → MachLib.Real)
    {globLip : Trans1 → Prop}
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env)
    (hLnn : ∀ t, globLip t → 0 ≤ Lip1 t)
    (hLip : ∀ t, globLip t → ∀ p q : MachLib.Real,
        abs (realOf1 t p - realOf1 t q) ≤ Lip1 t * abs (p - q))
    (hround : ∀ (t : Trans1) (a : Float),
        abs (toR (i1 t a) - realOf1 t (toR a)) ≤ u * abs (realOf1 t (toR a))) :
    ∀ e : EML, IsFold globLip e →
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
  | tr1 t a hglob _ iha =>
      obtain ⟨Ea, iha⟩ := iha
      exact ⟨_, absenc_lip (hLnn t hglob) (hLip t hglob) iha
        (hround t (evalEML i1 i2 env a).toF)⟩

/-- **The nested pipeline, through the emitted C.** For any `IsFold e`, the value the emitted C computes,
through `toR`, is within some absolute bound of the exact `exactRn … e` — arbitrary nesting of arithmetic
and globally-Lipschitz transcendentals. -/
theorem pipeline_nested {toR : Float → MachLib.Real} (br : FPBridge toR)
    (realOf1 : Trans1 → MachLib.Real → MachLib.Real) (Lip1 : Trans1 → MachLib.Real)
    {globLip : Trans1 → Prop}
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hLnn : ∀ t, globLip t → 0 ≤ Lip1 t)
    (hLip : ∀ t, globLip t → ∀ p q : MachLib.Real,
        abs (realOf1 t p - realOf1 t q) ≤ Lip1 t * abs (p - q))
    (hround : ∀ (t : Trans1) (a : Float),
        abs (toR (i1 t a) - realOf1 t (toR a)) ≤ u * abs (realOf1 t (toR a)))
    (e : EML) (he : IsFold globLip e) :
    ∃ E, AbsEnc E (toR (evalC r1 r2 env (emitC e)).toF) (exactRn toR realOf1 env e) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env]
  exact nested_fold br realOf1 Lip1 i1 i2 env hLnn hLip hround e he

/-- Non-vacuity: `sin(x·y − z·w)` — a transcendental over the cancelling determinant — is in the nested
fragment (for any `globLip` marking `sin`). So `pipeline_nested` genuinely covers transcendentals composed
over cancelling arithmetic, and by recursion `tanh(sin(x·y − z·w))`, etc. -/
example (globLip : Trans1 → Prop) (hsin : globLip .sin) :
    IsFold globLip (.tr1 .sin detEML) :=
  .tr1 _ _ hsin (.sub _ _ (.mul _ _ (.var "x") (.var "y")) (.mul _ _ (.var "z") (.var "w")))

end Certcom
