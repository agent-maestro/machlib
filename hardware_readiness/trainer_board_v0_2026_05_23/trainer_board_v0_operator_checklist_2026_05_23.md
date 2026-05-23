# Trainer Board v0 Operator Checklist

1. Confirm hardware approval.
2. Confirm ESP32 board identity.
3. Confirm no motors, relays, coils, solenoids, mains, or high-current loads.
4. Confirm LED series resistor is 220 or 330 ohm.
5. Confirm potentiometer endpoints and wiper.
6. Confirm GPIO pin plan: pot wiper GPIO34, LED GPIO25, shared GND, 3V3 logic only.
7. Photograph parts unpowered.
8. Photograph wiring unpowered.
9. Run non-hardware validators first.
10. Flash only after approval.
11. Capture serial only after approval.
12. Save raw serial.
13. Run validator.
14. Run replay.
15. Write findings.
16. Create packet manifest.
17. Do not claim certified safety or production controller status.
