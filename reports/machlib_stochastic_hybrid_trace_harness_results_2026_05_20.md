# MachLib Stochastic Hybrid Trace Harness Results - 2026-05-20

| record_id | status | check |
| --- | --- | --- |
| diffusion_trace_schema_v0 | PASS | diffusion increment reconstruction |
| stochastic_increment_record_v0 | PASS | x_tau = x0 + cumulative sum dx |
| drift_diffusion_signature_v0 | PASS | F, dt, sigma, dW placeholder fields present |
| brownian_noise_placeholder_v0 | PASS | dW is placeholder only |
| euler_maruyama_step_placeholder_v0 | PASS | bounded deterministic Euler-style step placeholder |
| jump_counting_process_record_v0 | PASS | finite jump transition extraction |
| transition_rate_record_v0 | PASS | R(x) placeholder shape only; no rate-estimation theorem |
| discrete_state_trace_record_v0 | PASS | finite state/time trace length |
| hybrid_continuous_discrete_trace_v0 | PASS | hybrid trace finite alignment metadata |
| transition_count_matrix_record_v0 | PASS | finite transition count matrix |
| stochastic_no_overclaim_boundary_v0 | PASS | stochastic/SDE/Markov overclaim boundary present |
| production_control_no_go_boundary_v0 | PASS | production/safety/hardware no-go boundary present |
