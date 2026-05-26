# MachLib Forge/eFrog Factored Root Packet Contract

Date: 2026-05-25

This is a report-only compatibility contract. It does not change Forge
or eFrog behavior.

## Proposed Shape

```json
{
  "coeffs": [
    "Real"
  ],
  "normalization": {
    "kind": "normalized_coeff_list",
    "last_nonzero_required": true
  },
  "factorization": [
    {
      "kind": "constant",
      "value": "c",
      "nonzero_certificate": "c != 0"
    },
    {
      "kind": "linear",
      "root": "r"
    }
  ],
  "root_packet_expected": [
    "deduplicated roots"
  ],
  "evidence_obligations": [
    "RootListSound",
    "RootListDistinct",
    "RootListDegreeBound"
  ],
  "boundary": {
    "forge_compiler_behavior_changed": false,
    "efrog_behavior_changed": false,
    "arbitrary_root_discovery_claim": false
  }
}
```

## Required Evidence

- normalized coefficient list
- nonzero constant certificate when a constant scale is present
- explicit linear-factor root list or imported factorization evidence
- deduplicated expected root list
- `RootListSound`, `RootListDistinct`, and `RootListDegreeBound` obligations

## Non-Claims

- no arbitrary factorization discovery
- no arbitrary root-count theorem
- no Forge compiler behavior change
- no eFrog behavior change
- no public theorem/proof/open-problem claim
