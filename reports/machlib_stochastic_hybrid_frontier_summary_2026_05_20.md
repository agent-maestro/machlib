# MachLib Stochastic Hybrid Frontier Summary - 2026-05-20

## Scope
Local-only OBSERVATION-tier stochastic/hybrid process evidence records.

## Image-inspired process split
- Diffusion-like finite trace: `dx_tau = F(x_tau)d_tau + sigma dW_tau`.
- Jump/counting finite trace: `dn(tau) = R(x_tau)d_tau + d_epsilon(tau)`.
- Hybrid trace alignment between finite continuous windows and discrete event labels.

## Diffusion/increment records
Finite increment reconstruction passes for the bounded fixture.

## Jump/counting records
Finite transition extraction and one-hot count indicators pass for the bounded fixture.

## Hybrid records
Finite alignment metadata passes for path length, state length, and event count.

## What is validated
- Records: 12
- Execution: PASS
- Roundtrip: WARN
- Zero-Mathlib: PASS

## What is not claimed
No stochastic calculus formalization, SDE theorem, Markov theorem, production controller evidence, certified safety, hardware truth, or public theorem/proof/open-problem result is claimed.

## Next safe experiments
Schema hardening, richer finite fixtures, and internal Command Center display review.
