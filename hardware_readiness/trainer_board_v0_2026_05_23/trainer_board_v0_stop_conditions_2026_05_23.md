# Trainer Board v0 Stop Conditions

Stop immediately and preserve the current state for review if any condition is
observed:

- unknown wiring
- LED has no resistor
- motor, relay, coil, solenoid, mains, or high-current load present
- board heats
- smell or smoke
- unstable USB or power
- serial output missing required fields
- guard telemetry missing
- output exceeds `safe_output_limit`
- clamped frames absent when expected
- unexpected hardware behavior
- operator discomfort

Blackwell did not run the live session. These are operator-side future stop
conditions.
