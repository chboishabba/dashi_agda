# Filsinger ideal-available components: source-bounded maximum cut (2026-11-10)

This tranche extends existing stacked PR #1487 and borrows the canonical typed circuit/netlist owners from PR #1482. It does not produce a second component ontology or override the original observations.

## Assumption convention
Interpret unknown *engineering* components charitably: ideal controlled switches, rectification, suitable insulated magnetic windings, stable frequency control, low-loss resonant tank, energy-storage management, and optional external antenna/collector. These are **design allowances**, not observed facts or an assertion the experimenter used a particular design. Never assume infinite ground energy, cosmic-ray delivery, perfect replenishment of atmospheric charge, or extra power hidden in the word 'ideal'.

Original recording explicitly narrates **white 3.33µF capacitor hot terminal -> Earth-negative**. This remains a described connection, not independently traced continuity. Blue ~2µF/10kV part is tentative. The 7.8kHz sound is **acoustic**, not a measured switching waveform.

## Local Python receipt
`/mnt/data/filsinger_ideal_component_maxcut.py` was executed with **18/18 standard-library unit tests PASS** after fixing an incorrect expected Q rounding constant. Locally generated `filsinger_ideal_component_results.json` and `filsinger_ideal_component_loss.png`. A narrow source-only subset is committed as `scripts/filsinger_ideal_component_witness.py`, but execution of that exact committed file has not been independently verified. No CI dependency.

## Calculation
At hypothetical electrical `f=7800Hz`, white capacitor `C=3.33µF`, `Vpk=1500V`, and conditional input `P=6.7W`:
- `U=3.74625J`; ideal fill `0.55914s` (or `1.1183s` at 50% transfer efficiency).
- Fully *dissipating* and recharging that energy each hypothetical electrical cycle: `29.22075kW`.
- If white capacitor is itself **full-amplitude resonant tank**, preserving its 1.5kV peak with 6.7W loss replacement demands `Q >= 27402.89` at assumed 7.8kHz.
- **Ideal alternative witness:** suppose `C_tank=5nF`, `Q=100`, same assumed `Vpk=1500V` and electrical frequency. Then `L=83.27mH`, `U_tank=0.005625J`, `P_loss = 2.757W`. This stays under 6.7W *before* allocating remaining power to charging, controls and other losses. The assumed capacitor, coil, amplitude and Q are **NOT** identified Filsinger parts; 83mH at 7.8kHz may be demanding in a particular physical winding. This is a consistency witness, not a reconstructed production design.
- `Q=50` gives the largest capacitor for 6.7W full tank-loss allocation `C<=6.076nF`; `Q=100` gives `C<=12.152nF`, if the 1500V peak actually spans the tank capacitor.

## Physical non-identifiability remains
Both (a) floating ground-reference shift and (b) ideal LC differential reversal can produce the narrated meter sign change with no new external power. Bias can increase electrode charge collection, but additional *net harvested work* requires actual field/chemical/RF replenishment and signed source accounting.

## Maximum remaining cut
1. Real component/pin correspondence, return conductor, diode/bridge branches, meter terminals and capacitor polarity.
2. Electrical clock, measured effective tank C/L/Q, input RMS/real power and time-resolved capacitor energy.
3. Independently calibrated environmental source/load, simultaneous ground and elevated antenna terminal `v(t)i(t)` integration, including electrode chemistry, external grid/RF coupling and loss.
4. Optional ELF source transfer onto existing Tesla PR #1464, not mere 7800:7.83 numerical comparison.
5. Agda kernel check for stacked circuit-owner/adapter declarations; no fake proof receipts.

All model source attribution is explicit; high-voltage physical testing requires appropriately qualified personnel.
