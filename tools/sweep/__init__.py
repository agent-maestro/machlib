"""C-239 BFS proof-sweep tooling.

Walks ``foundations/MachLib/Discovered/*.lean`` to extract per-theorem
sorry sites, drives ``MultiProofSearch`` against each via
``LeanKernelVerifier``, and records results to
``exploration/C239_bfs_proof_sweep/results.jsonl``.

See ``exploration/C239_bfs_proof_sweep/PLAN.md`` for the design.
"""
