/-
# The last rung: the minimal-relation identity, on a bounded interval

`(gk)` twinned `minimal_grel_identity`'s last dependency and said "unblocked is not done." This is
done: the whole descent / minimality / identity chain now runs on a bounded component, which is where
`OneQueryLevelSet`'s residue lives and where `GEvRel` structurally could not reach.

The port needed nothing new. Every dependency was twinned in `(gi)`–`(gk)`, and the index
bookkeeping — `split_last`, `gdrel_getElem`, `gscaleSub_getElem`, the `List.getElem?_append_*`
lemmas — never mentions a tail, so it carries across untouched.

## What the chain now provides, and what it still does not

Provided, on `(a,b)`: a minimal proper relation forces an identity on its **top two coefficients**,
and any relation shorter than minimal has **every** coefficient vanishing, and length 1 is
**impossible**.

Not provided: a germ. Nothing here exhibits an `Fbasis ∘ S` satisfying `GDerivAt` and a proper
interval relation on a component of `{S > 0}` — which is the thing the residue is about, and the
thing this whole chain is waiting for. The machinery is complete and unaimed.
-/
import MachLib.GermIntervalDeriv
import MachLib.GermDerivEntry

namespace MachLib

open Real

private theorem gIntervalZero_congr {f g : Real → Real} {a b : Real}
    (h : GIntervalZero f a b) (he : ∀ x, f x = g x) : GIntervalZero g a b :=
  fun x hax hxb => (he x) ▸ h x hax hxb

private theorem split_last_i {α : Type} : ∀ (l : List α) (n : Nat), l.length = n + 1 →
    ∃ (l₀ : List α) (a : α), l = l₀ ++ [a] ∧ l₀.length = n := by
  intro l n hn
  have hne : l ≠ [] := by intro h; rw [h] at hn; simp at hn
  exact ⟨l.dropLast, l.getLast hne, (List.dropLast_concat_getLast hne).symm, by
    rw [List.length_dropLast, hn]; omega⟩

/-- **The identity a minimal germ-coefficient relation forces on its top two coefficients —
on a bounded interval.**

Twin of `minimal_grel_identity`. Every dependency was twinned in `(gi)`–`(gk)`; the index
bookkeeping is generic and ports untouched. -/
theorem minimal_gIntervalRel_identity {u v : Real → Real}
    {cs es cs₀ es₀ : List (Real → Real)} {cd ed cd1 ed1 : Real → Real} {m : Nat} {a b : Real}
    (hu : ∀ x : Real, a < x → x < b → HasDerivAt u (v x) x)
    (hdd : ∀ x : Real, a < x → x < b → GDerivAt x cs es)
    (hmin : ∀ ns : List (Real → Real), GIntervalProperRel u ns a b → cs.length ≤ ns.length)
    (hrel : GIntervalRel u cs a b)
    (hcs : cs = cs₀ ++ [cd]) (hes : es = es₀ ++ [ed])
    (hlen0 : cs₀.length = m + 1) (hlenes : es₀.length = m + 1)
    (hcd1 : cs₀[m]? = some cd1) (hed1 : es₀[m]? = some ed1) :
    GIntervalZero
      (fun x => cd x * (ed1 x + v x * (natMul (m + 1) 1 * cd x)) - ed x * cd1 x) a b := by
  have hlen : cs.length = m + 2 := by rw [hcs]; simp [hlen0]
  have hlenE : es.length = m + 2 := by rw [hes]; simp [hlenes]
  have hcsIdx : cs[m + 1]? = some cd := by
    rw [hcs, List.getElem?_append_right (by omega), hlen0]; simp
  have hesTop : es[m + 1]? = some ed := by
    rw [hes, List.getElem?_append_right (by omega), hlenes]; simp
  have hesIdx : es[m]? = some ed1 := by
    rw [hes, List.getElem?_append_left (by omega)]; exact hed1
  have hdrel : GIntervalRel u (gdrel v cs es) a b := gIntervalRel_gdrel hu hdd hrel
  have hdlen : (gdrel v cs es).length = m + 2 := by
    rw [gdrel_length (by rw [hlen, hlenE]), hlen]
  obtain ⟨ds₀, dtop, hsplit, hds0⟩ := split_last_i (gdrel v cs es) (m + 1) hdlen
  obtain ⟨bt, hbt, hbtval⟩ := gdrel_getElem_top (v := v) hesTop hlen
  have hdtop : dtop = bt := by
    have hg : (gdrel v cs es)[m + 1]? = some dtop := by
      rw [hsplit, List.getElem?_append_right (by omega), hds0]; simp
    rw [hg] at hbt; exact Option.some_inj.mp hbt
  obtain ⟨b', hb', hb'val⟩ := gdrel_getElem (v := v) hesIdx hcsIdx
  have hds0Idx : ds₀[m]? = some b' := by
    rw [← hb', hsplit, List.getElem?_append_left (by omega)]
  have hgs : GIntervalRel u (gscaleSub cd dtop cs₀ ds₀) a b :=
    gIntervalRel_cancel_top (by rw [hlen0, hds0]) (hcs ▸ hrel) (hsplit ▸ hdrel)
  have hgslen : (gscaleSub cd dtop cs₀ ds₀).length = m + 1 := by
    rw [gscaleSub_length cd dtop cs₀ ds₀ (by rw [hlen0, hds0]), hlen0]
  have hentry := gscaleSub_getElem cd dtop cs₀ ds₀ m cd1 b' hcd1 hds0Idx
  have hall := all_gcoeffs_intervalZero_of_shorter' hmin hgs (by omega)
  refine gIntervalZero_congr (hall _ (List.mem_of_getElem? hentry)) (fun x => ?_)
  show cd x * b' x - dtop x * cd1 x = _
  rw [hb'val x, hdtop, hbtval x]

end MachLib
