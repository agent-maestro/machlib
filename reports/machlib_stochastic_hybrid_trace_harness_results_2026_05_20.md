# MachLib Stochastic Hybrid Trace Harness Results - 2026-05-20

| record_id | status | check |
| --- | --- | --- |
| diffusion_trace_schema_v0 | PASS | x_tau = x0 + sum(dx) |
| stochastic_increment_record_v0 | PASS | finite increment list |
| drift_diffusion_signature_v0 | PASS | F(x), dt, sigma, dW fields present |
| brownian_noise_placeholder_v0 | PASS | symbolic placeholder only |
| euler_maruyama_step_placeholder_v0 | PASS | bounded deterministic step fixture |
| jump_counting_process_record_v0 | PASS | finite transition extraction |
| transition_rate_record_v0 | PASS | rate placeholder shape only |
| discrete_state_trace_record_v0 | PASS | state trace shape |
| hybrid_continuous_discrete_trace_v0 | PASS | continuous increments paired with jump labels |
| transition_count_matrix_record_v0 | PASS | finite transition count matrix |
| stochastic_no_overclaim_boundary_v0 | PASS | theory overclaim blocker present |
| production_control_no_go_boundary_v0 | PASS | production and safety overclaim blocker present |
