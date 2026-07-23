import MachLib.CosNotInEMLAnyDepth
import MachLib.EMLAnyDepthBarrierUnconditional

/-!
# Re-routing the cos barrier off `zero_count_bound_classical`

Mirror of `EMLExplicitBoundSinBarrier.lean` for cosine — originally an independent re-derivation
via `EMLExplicitBound.enc_combinedBound`, still depending on `eml_pfaffian_validon_from_cos_equality`
(a separate, deliberately-still-open axiom) plus the two small classical-citation facts
`pi_div_one_plus_one_pos`/`pi_div_one_plus_one_lt_pi` from `CosNotInEMLAnyDepth.lean`.

**Superseded 2026-07-23**, unlike the sin sibling this file mirrors. `EMLAnyDepthBarrierUnconditional
.lean`'s `cos_not_in_eml_any_depth_unconditional` (added 2026-07-22, same arc) proves the identical
statement WITHOUT the open-axiom dependency — a strictly stronger result, no explicit-bound content
lost. Unlike `sin_not_in_eml_any_depth` (kept axiom-dependent because twelve other files cite it by
name and rewiring was judged too risky), this file's own `cos_not_in_eml_any_depth` had exactly zero
real callers outside itself when checked (only prose cross-references in
`EMLAnyDepthBarrierUnconditional.lean`/`KhovanskiiLemma.lean`/`TowerSeparation.lean`, no actual
applications) — this file was simply never wired into `MachLib.lean`'s aggregator, so nothing was
ever in a position to depend on it either way.

Found by `scripts/check_aggregator.sh`'s "no ungated orphan modules" gate (2026-07-23): this file,
having never been built, was never checked against the 2026-07-22 discharge and so never flagged as
redundant. Retired to a one-line corollary rather than added to `AxiomLedger.lean`'s
`legacyAxiomCallSiteAllowlist` — that allowlist is for grandfathering existing dependents, and this
one has none, so the honest fix is removing the open-axiom dependency entirely, not grandfathering it.

One structural difference from the sin barrier this file's original derivation carried, kept here for
the historical record: cos's zeros are at `i·π + π/2` starting at `i = 0` (giving `π/2` itself), which
would collide with the natural choice of strictly-interior left endpoint `a' = π/2` needed for
`logArgPosOn_Icc_of_validOn`'s open→closed bridge. Using the zeros `i = 1, …, M+1` instead (still
`M + 1` distinct zeros, all `> π/2`) sidesteps this with no new fact needed — moot now that the proof
below no longer goes through this route, but the reasoning stays true of the original derivation.
-/

namespace MachLib

open MachLib.Real

/-- **`cos` is not in the EML hierarchy at any depth.** Delegates to
`cos_not_in_eml_any_depth_unconditional` (`EMLAnyDepthBarrierUnconditional.lean`) — see this file's
header for why the original axiom-dependent derivation was retired rather than kept. -/
theorem cos_not_in_eml_any_depth (k : Nat) :
    ¬ InEMLDepth (fun x : Real => Real.cos x) k :=
  cos_not_in_eml_any_depth_unconditional k

end MachLib
