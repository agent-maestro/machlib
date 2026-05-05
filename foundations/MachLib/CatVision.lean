-- MachLib/CatVision.lean
--
-- Hand-completed proof for one of the @verify obligations from
-- the cat-vision experiment at
-- monogate-research/exploration/cat_vision/.
--
-- The auto-generated files in that directory's `lean/` carry the
-- theorem statements with `sorry` proof obligations; this file
-- discharges the lower-bound obligation on `rod_sensitivity`
-- against MachLib foundations to prove the pipeline works
-- end-to-end. The remaining bounds (`≤ 1` upper bounds, tapetum
-- monotone/bounded) follow the same pattern and are open
-- obligations on `MachLib.Forge` extending its numerical-bound
-- lemma library.

import MachLib.Basic
import MachLib.Exp
import MachLib.Forge

open MachLib
open MachLib.Real

namespace CatVision

noncomputable def ROD_PEAK_NM  : Real := 498.0
noncomputable def ROD_SIGMA_NM : Real :=  50.0

/-- The body of `rod_sensitivity` from `eml/rod_sensitivity.eml`,
    re-stated as a Lean function. The EML compiler's Lean backend
    emits exactly this expression. -/
noncomputable def rod_sensitivity (wavelength_nm : Real) : Real :=
  exp (-((wavelength_nm - ROD_PEAK_NM) * (wavelength_nm - ROD_PEAK_NM))
        / (2.0 * ROD_SIGMA_NM * ROD_SIGMA_NM))

/-- The first half of the @verify(lean) obligation from the EML
    source: `rod_sensitivity λ ≥ 0` for all λ. Trivial from
    `MachLib.Forge.exp_nonneg`. -/
theorem rod_sensitivity_nonneg (wavelength_nm : Real) :
    0 ≤ rod_sensitivity wavelength_nm := by
  unfold rod_sensitivity
  exact exp_nonneg _

end CatVision
