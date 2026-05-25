# MachLib Proof Spine v1

Date: 2026-05-25

Status: `MACHLIB_PROOF_SPINE_V1_READY`

## Purpose

This packet makes the Lean verification role concrete: ten small
EML / Forge / Explorer / CapCard-facing obligations now have named
MachLib artifacts in `MachLib.ProofSpine`.

This is not a broad theorem-library claim and not a public theorem
promotion. It is an internal evidence spine for checked artifacts.

## Obligations

- `eml_exp_branch_checked`
  - family: `eml_primitive`
  - statement: `eml x 1 = exp x`
  - Lean: `MachLib.ProofSpine.eml_exp_branch_checked`
  - surfaces: Explorer EML primitive bridge, Forge lowering contract
- `eml_log_branch_checked`
  - family: `eml_primitive`
  - statement: `eml 0 y = 1 - log y`
  - Lean: `MachLib.ProofSpine.eml_log_branch_checked`
  - surfaces: Explorer EML primitive bridge, Forge lowering contract
- `exp_zero_checked`
  - family: `normalization`
  - statement: `exp 0 = 1`
  - Lean: `MachLib.ProofSpine.exp_zero_checked`
  - surfaces: EML IR lowering, SuperBEST rewrite hygiene
- `exp_sub_checked`
  - family: `exp_rewrite`
  - statement: `exp (x - y) = exp x / exp y`
  - Lean: `MachLib.ProofSpine.exp_sub_checked`
  - surfaces: EML IR lowering, Forge obligation shape
- `sin_cos_pythagorean_checked`
  - family: `trig_identity`
  - statement: `sin x * sin x + cos x * cos x = 1`
  - Lean: `MachLib.ProofSpine.sin_cos_pythagorean_checked`
  - surfaces: Explorer identity table, Forge rotation witnesses
- `cos_sin_pythagorean_swapped_checked`
  - family: `trig_identity`
  - statement: `cos x * cos x + sin x * sin x = 1`
  - Lean: `MachLib.ProofSpine.cos_sin_pythagorean_swapped_checked`
  - surfaces: Forge matrix witnesses, Explorer row notes
- `cosh_sinh_pythagorean_checked`
  - family: `hyperbolic_identity`
  - statement: `cosh x * cosh x - sinh x * sinh x = 1`
  - Lean: `MachLib.ProofSpine.cosh_sinh_pythagorean_checked`
  - surfaces: PETAL curriculum, EML hyperbolic bridge
- `cosh_exp_decomposition_checked`
  - family: `hyperbolic_to_exp`
  - statement: `cosh x = (exp x + exp (-x)) / (1 + 1)`
  - Lean: `MachLib.ProofSpine.cosh_exp_decomposition_checked`
  - surfaces: PETAL curriculum, EML IR lowering
- `nonneg_product_guard_checked`
  - family: `guard_contract`
  - statement: `0 <= a -> 0 <= b -> 0 <= a * b`
  - Lean: `MachLib.ProofSpine.nonneg_product_guard_checked`
  - surfaces: Forge guard obligations, Monogate OS guard vocabulary
- `saturate_lower_guard_checked`
  - family: `guard_contract`
  - statement: `0 <= max 0 (min x 1)`
  - Lean: `MachLib.ProofSpine.saturate_lower_guard_checked`
  - surfaces: Forge clamp obligations, CapCard evidence cards

## Boundaries

- Internal evidence reference only.
- Not marketplace-ready.
- No package publish.
- No PETAL/API or Hugging Face upload.
- No safety-certification or controller-status claim.
- No public theorem/proof/open-problem claim.
