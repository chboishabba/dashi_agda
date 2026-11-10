# Filsinger ZVS shunts × acoustic microvariation maximum cut (2026-11-10)

## User-source update and provenance
The new user-supplied Instagram-reel transcript says the presenter calls the driver **ZVS**, places approximately **1 MΩ resistive shunts across each 3.3 µF capacitor**, and varies the drive voltage, observing a frequency/voltage response. The earlier black/red insulated ~6-inch objects are consequently plausible shunt resistors. This is a source-identified **candidate**, not a part-number or direct resistance/continuity measurement. Narrated original capacitor hot-terminal → Earth-negative connection remains preserved as a *separate* reported edge in the adapter from #1487. An elevated antenna is hypothesised but not seen.

## Question: can 1 MΩ cause the small wavering in the ~7.8 kHz audio?
**Directly, in a simple ideal RLC tank, essentially not. Indirectly through the ZVS driver and load dynamics, yes in principle.**

For R = 1 MΩ, C = 3.33 µF, conditional electrical frequency f = 7800 Hz (the actual 7.8 kHz is *acoustic*):
- RC = 3.33 s; RC corner = 0.047794 Hz. RC decay is not a self-oscillation.
- Capacitive reactance magnitude = 6.127 Ω.
- Shunt equivalent Q for a parallel RLC branch: Q_R = 2π f R C = **163,199**.
- If all other tank losses gave Q_loaded = 100, the *additional conductance* from a 1 MΩ resistor is only Q_loaded/Q_R ≈ **0.000613** of existing loss; the simple damped natural-frequency fractional shift due to this isolated shunt is about **4.7×10^-12**, not enough for ~40 Hz drift.
- At 1500 V DC, however, this resistor consumes **2.25 W per branch**. Two identical branches both at 1500 V consume 4.5 W, substantial relative to the earlier reported 6.7 W **if** that reading measures real total input.
- Hence indirect driver-mediated effects are plausible: bias/charge voltage changes, switching threshold, loading of high-voltage supply, thermal drift, feedback in self-oscillating ZVS, varying core state. Those cannot be distinguished without actual meter-terminal/switching measurements. Shunt heating and power rating are unverified and high voltage is potentially lethal.

## Local acoustic check
Original MP3 /mnt/data/ReelAudio-93787.mp3 processed with local Python/ffmpeg using a 0.8s Hann periodogram sliding by 0.2s, 35.4–65s, restricting peak to 7600–8050 Hz and using a narrowband contrast gate. **14/14 circuit and source-bound checks PASS** in /mnt/data/filsinger_shunt_modulation_maxcut.py; 126 of 144 time windows exceeded the 15dB spectral-contrast selection. The **median strong acoustic ridge** is 7812.75 Hz. On a cleaner ~36.4–60.4s interval, the acoustic ridge drifts from roughly 7783.5 to 7825 Hz, slope ~1.64 Hz/s (simple linear fit), with residual variation around that trend. The tiny residual fluctuations are not enough to establish a stable separate low-frequency oscillator, subharmonic, or environmental source. No synced resistor/charge voltage record; do not claim causal correlation.

## Reused repo owners and delivered model
- #1482 canonical `Circuit36927ComponentGraphExact` resistor/nominal-value/pin graph.
- #1487 candidate hot-terminal to Earth-negative wire (not electrically verified).
- #1486 capacitor-energy and ground-source nonidentifiability.
- #1464 historical Tesla 6Hz / Schumann 7.83Hz non-promotion.
- New `FilsingerZVSShunt36927AdapterExact.agda`: two 1MΩ candidate resistors, converted to **1,000,000,000 milliohms** each, connected to no fabricated physical node, with selected source/connection proof interfaces. No duplicated generic component ontology.
- New `scripts/filsinger_zvs_shunt_microvariation_cut.py` conditional 14-test numerical checks. Local test provenance corresponds to a separately executable local program. The exact committed script has not been fetched and run within the current shell, so no same-file runtime receipt or Agda-kernel PASS claimed.

## Remaining max cut
P0 actual physical shunt IDs, whether values are 1MΩ per cap vs meter-resistance equivalent, each resistor's two endpoints, both HV meter terminals, actual circuit bridge, ZVS oscillator topology, and `Vcap(t)`.
P0 measured electrical switching frequency and simultaneous acoustic capture; check frequency trajectory against bias/charge and thermal behaviour.
P1 fit nonlinear resonant model including real transformer inductance/capacitance, driver switch losses, loaded-Q and resistor dissipation; energy-integrate measured supply/ground/antenna ports.
P2 test measured independent ELF coupling, not a coincidence between ~7800 Hz and ~7.83 Hz.

**The shunt can be operationally significant without itself providing the high-frequency resonant frequency.** No measured Earth-derived power is inferred.
