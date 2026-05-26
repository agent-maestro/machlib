# MachLib Factored Root Packet v14

Date: 2026-05-25

Status: `MACHLIB_FACTORED_ROOT_PACKET_V14_READY`

## Checked

v14 adds the first root-enumerator layer above individual examples.
Known finite-root packets can now be composed into factored products;
constant times explicit linear factors can be packetized; repeated
linear roots use the existing unique-union machinery instead of
claiming duplicate roots.

- `RootEnumeratorSound`
- `rootEnumeratorSound_of_packet`
- `RootCountForKnownPacketTarget`
- `rootCountForKnownPacketTarget_checked`
- `linearFiniteRootPacket`
- `foldNormalizedProductPacket`
- `factoredLinearProductPacket`
- `repeatedLinearProductPacket`
- `RootCountForLinearFactorProductsTarget`
- `rootCountForLinearFactorProductsTarget_checked`
- `RootCountForRepeatedLinearProductsTarget`
- `rootCountForRepeatedLinearProductsTarget_checked`
- `RootCountForFactoredTarget`
- `rootCountForFactoredTarget_checked`
- `RootCountForArbitraryCoeffTarget`

## Forge/eFrog Certificate Shape

Future emitters should provide normalized coefficients, explicit
factorization evidence, and the expected deduplicated root packet.
This task does not change Forge or eFrog behavior.

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

## Still Open

- arbitrary root discovery for normalized coefficient lists
- factorization search or certificate import from Forge/eFrog
- RootCountInductionTarget proof for arbitrary coefficients
- public Explorer/CapCard surfacing of these internal packets

## Boundary

- This checks factored and known-packet root-count paths, not arbitrary root discovery.
- `RootCountInductionTarget` remains defined but not proved.
- No Forge compiler or eFrog behavior was changed.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.
