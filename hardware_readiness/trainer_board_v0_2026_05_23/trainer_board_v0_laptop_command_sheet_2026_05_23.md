# Trainer Board v0 Laptop Command Sheet

FUTURE LAPTOP COMMANDS - NOT RUN BY BLACKWELL

These commands are copied into this packet as operator handoff text only.
Blackwell did not run hardware commands, open serial, flash firmware, wire,
power, solder, actuate, or capture live data.

## Pre-Hardware Validators

```powershell
python tools\validate_kernel_spec.py kernels\threshold_reflex_v0
python tools\validate_trace.py kernels\threshold_reflex_v0\traces\golden_trace.jsonl
python tools\replay_trace.py kernels\threshold_reflex_v0\traces\golden_trace.jsonl
python scripts\validate_serial_frame.py --file telemetry\example_frames\simulated_serial_stream.jsonl
python inspector\scripts\inspect_reflex.py --serial telemetry\example_frames\simulated_serial_stream.jsonl --summary-only
```

## Future Firmware Compile/Flash Placeholder

Run only after operator approval and only from the electronics/laptop workflow:

```powershell
REM FUTURE LAPTOP COMMAND - NOT RUN BY BLACKWELL
REM compile threshold_reflex_v0 firmware using the approved electronics repo command
REM flash ESP32 only after explicit approval
```

## Future Serial Capture Placeholder

Run only after operator approval:

```powershell
REM FUTURE LAPTOP COMMAND - NOT RUN BY BLACKWELL
REM capture raw serial JSONL to evidence\trainer_board_v0\first_reflex_demo_YYYY_MM_DD\raw_serial.jsonl
```

## Future Validation, Replay, and Packet Manifest

```powershell
python scripts\validate_serial_frame.py --file evidence\trainer_board_v0\first_reflex_demo_YYYY_MM_DD\raw_serial.jsonl
python inspector\scripts\inspect_reflex.py --serial evidence\trainer_board_v0\first_reflex_demo_YYYY_MM_DD\raw_serial.jsonl --summary-only
python tools\make_packet.py evidence\trainer_board_v0\first_reflex_demo_YYYY_MM_DD --out evidence\trainer_board_v0\first_reflex_demo_YYYY_MM_DD\PACKET_MANIFEST.json
```

## Boundary

These are future laptop commands. They are not proof of a hardware run, not
live serial evidence, not certified safety, not production controller evidence,
and not DARPA acceptance.
