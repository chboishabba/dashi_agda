# DASHI Smith / Filsinger: source-port and shunt-power maximum cut

**15 November 2026. Research continuation of Agda PR #1515.**

## Source/evidence discipline

The target is Smith's described *small driven excitation + modified coupling to larger electromagnetic reservoir*, not perpetual motion. Published research on the global atmospheric current, Schumann modes and nonlinear ionospheric conversion establishes external physics, **not performance of this particular apparatus**. Distinguish four levels on every statement: (i) narrator/compiled-source claim, (ii) source photographs and original acoustic observation, (iii) mathematical consequence of specified coefficients, (iv) measured source-to-load port work. Never silently promote (i)–(iii) to (iv).

**Source occasions must not be conflated.** Filsinger says in the [shunt/ZVS reel](https://www.instagram.com/reel/DfiqPnkPnP5/) that he uses 1 MΩ with 3.3 µF components, compares 2 MΩ and 4 MΩ and describes resistance/loading as tuning. The [Earth-electrode reel](https://www.instagram.com/reel/Dfi1D7CPzyM/) reports 3.8 V / 0.4 W and 48 V across capacitors: **48 V is NOT a measured Earth-port open-circuit Thévenin voltage**. The [commercial midpoint/spark-gap reel](https://www.instagram.com/reel/Dfu9Jseviz9/) concerns a different proposed Smith circuit including midpoint, rectifiers and dump. The earlier ~15 V input and ~6–7.3 W driver readings, 1,500 V capacitor observation and alleged high-voltage meter/shunts are not simultaneously metered on all suspected components. The number of *individually shunted capacitors* and each's actual voltage waveform are not pin-traced. A 15 V, 6 A rated supply is a capability rating, **not measured 90 W consumption**.

Original PDF `High-Power_Devices_of_Don_Smith_1g.pdf` remains source of original/editorial figure distinctions: Figure 10 p28, Figure 11 p29, separate 17+17-turn L2 p49–51, Fig31 p55 reversal proposed by EVGRAY *silverhealtheu*, later neon Fig40 p65, and different commentator secondary proposals p81–82. No Smith-to-Filsinger netlist equivalence is claimed.

## Closed conditional mathematical subgates THIS round

### SP1. Shunt work is a first-class timed energy port

For each independently loaded capacitor with a **real** shunt R, `P_R(t)=V_C(t)^2/R`; the correct cycle average is **`V_C,RMS²/R`** and this remains true if switching/FM changes the waveform. At 3.3 µF, 1,500 V **DC** and 1 MΩ:
- one hypothetical cap: `P_R = 2.25 W`, `U_C = 3.7125 J`, voltage e-fold `RC = 3.3 s`, isolated stored-energy e-fold `RC/2 = 1.65 s`;
- 2 separate equally energised shunts: 4.50 W; 3: **6.75 W**;
- changing 3 equal shunts to 2 MΩ: **3.375 W**, 4 MΩ: **1.6875 W**.

For a 1,500 V **sinusoidal peak**, 3 × 1 MΩ each dissipate **3.375 W**, not 6.75 W. At 1,500 V **25%-duty rectangular peak**, 1.6875 W. Thus the 6.75 W proximity to the reported ~6.7 W driver observation is a **sensitivity/possible budget-conflict test**, not a source confirmation or an energy discovery. Resistive time-variable loading may alter oscillator bias, switching point, phase and magnetic nonlinearities far more than the megohm's direct effect on an ideal 7.8kHz tank frequency.

Source accounting with energy units for a common interval and *matching clocks*:

`W_driver + W_environment + W_released_storage = W_all_shunts + W_other_dissipation + W_remaining`.

The finite Agda `shuntWorkNoGreaterThanAllInputs` and `noDriveOnly670Equals675` make this explicit, with 100th-watt unit **only for a deliberately assumed simultaneous steady 3-shunt DC example**. The real-port V²/R identity is validated in Python/SymPy, **not yet accepted by Agda kernel**.

### SP2. Fixed finite source: time-varying matching ceiling and precise escape condition

For a hypothetical stationary Thévenin source with open-circuit `V_oc(t)` and positive **real** source resistance `R_s(t)`, and arbitrary receiving current `I(t)`, `V_terminal = V_oc − R_s I`, hence

`P_terminal = (V_oc − R_s I) I = V_oc²/(4 R_s) − R_s (I − V_oc/(2R_s))²`.

Consequently `W_source_to_port <= ∫ V_oc(t)²/(4 R_s(t)) dt`. This is exact even with arbitrarily timed receiving impedance and negative instantaneous current, provided the instantaneous fixed-source Thévenin **assumptions** hold. A time-varying electromagnetic source with reactive memory / retarded feedback is **not** representable by this static equation; it needs the *coupled* Maxwell/port-Hamiltonian operator already source-authored in DASHI. The bound cannot be used to disprove the full Smith thesis, but gives a clean falsification test of the simpler passive-source interpretation.

Necessary max internal source resistance for **0.4 W** is 0.625 Ω at `V_oc=1V`, 62.5 Ω at 10V and 1440 Ω at 48V. These are hypothetical **source port** voltages, not inferred from capacitor/multimeter displays. For source-resistance identification under an unchanged source across two matched loaded observations, `(V_1, I_1)` and `(V_2, I_2)` give `R_s = (V_1−V_2)/(I_2−I_1)`, `V_oc = V_1+R_s I_1`. If bias/phase alters the source during the load sweep, that inversion is invalid and the source-responsive model must be used.

### SP3. Distinct physical global-circuit capacitor models; access vs storage

- [Rycroft et al. 2025](https://www.mdpi.com/2073-4433/16/3/348) estimate an effective **global-circuit capacitor** `C≈2.47 F` and characteristic time ≈8 minutes, with a distinct ~1.5 F interpretation. [Haldoupis et al. 2017](https://doi.org/10.1016/j.jastp.2017.08.012) show that the simplistic literal Earth–ionosphere spherical capacitor fails to account for real vertical charge/conductivity structure. An older [review](https://pmc.ncbi.nlm.nih.gov/articles/PMC7782448/) uses ~0.7 F. **These are different models, not interchangeable component values.**
- The AC Schumann cavity modes are NOT simply the DC GEC relaxation pole. A lumped DC capacitor does not represent ionospheric height-dependent Hall/Pedersen conductivity, lightning-induced ELF waves, magnetosonic conversion, propagation delay or the direct receiving geometry.
- At an assumed uniform global 250kV, modeled electrostatic storage spans ~**21.9–77.2 GJ** over `C=.7–2.47F`. Draining 0.4W for 30 minutes from that **entire** store without replenishment requires ~0.0012–0.0041V global droop. Capacity clearly isn't the key obstacle *in that global illustration*; **source-access admittance is**.
- The undisturbed fair-weather return current is roughly 1–3 pA/m². [2026 long-run Borok field study](https://doi.org/10.1016/j.asr.2026.01.090) found mean `2.36 pA/m²`, mode `1.25 pA/m²`. For 250kV the **full global column potential** times undisturbed current is `0.3125–0.59 µW/m²`, requiring ~0.68–1.28km² of equivalent full-column throughput for 0.4W in an idealized unchanged-source accounting. This is *not a hard receiving aperture bound* for a nonlinear, redirected field or a local RF/telluric source. It defines the gain/transport the 'funnel' model must derive.

### SP4. Separate irreducible source and output signatures

A capacitor's `1500V` reading or 7.8kHz sound alone cannot identify a positive Earth-source real-work port. The Agda `meterAloneCannotDetermineNaturalInput` makes a finite source-identifiability counterexample, while the existing acoustic non-identifiability theorem remains in its owner. A matched circuit experiment would instrument: capacitor voltage **and waveform** at each actual shunt; true input DC real power; electrical output resistive load real power; earth/plate terminal complex V/I at the **same time**; capacitor state before/after, and matched ungrounded/bias states. Any high-voltage implementation requires professional-grade instrumentation and safeguards; this document is **analysis**, not build instructions.

## Remaining original-world maximum cut (strict: do not falsely decrement)

| ID | Exact acceptance obligation | Status |
|---|---|---|
| `S0_originalSmithFilsingerSourceGraphWeld` | Pin-level capacitor/meter/shunt/spark/rectifier/Earth/antenna connectivity of one selected original unit, traced to the specific reel and/or original figure | OPEN |
| `P1_sameOriginalShuntRmsAndDriverEnergyBalance` | Same-time actual shunt RMS and input power traces; no unit or occasion mixing | OPEN |
| `P2_sourceLoadDependentVocsRsOrRetardedKernel` | Two-load matched source V/I pair if stationary; otherwise establish a causal, measured nonlinear source-response port operator | OPEN |
| `R1_sameOriginalFullNonlinearState` | MOSFET/ZVS timing, core B–H loss, effective capacitances, diode recovery, coupled modes, positive/negative power, ground and air field interactions in one model | OPEN |
| `R2_MixedScaleMaxwellEarthIonosphereResponse` | Appropriate real finite geometry, material laws and retarded Maxwell/ionospheric plasma modes, with separately sourced DC, ELF, VLF, RF, telluric contributions | OPEN |
| `R3_naturalFieldWorkPositiveAfterMatchedControls` | Signed environmental work shown positive after **all** driver, modulator, loss, storage and load terms across a matched cycle | OPEN |
| `D1_KernelCheckSourcePortAndExistingOwners` | Pinned Agda 2.9 exact-head check of original source contracts, finite donor and new shunt budgets | OPEN: Agda/Nix unavailable locally |
| `D2_evidenceToSameApparatusBidi` | Formal promotion witness from source claims/observations to selected real physical device | OPEN |

**Closed this round (conditional):** `SP1` exact source-specific shunt sensitivity; `SP2` time-variable fixed-Thévenin upper bound; `SP3` externally attributed global reservoir model distinction and access calculation; `SP4` cap-voltage source-identification negative control. These are **four conditional mathematical/source subgates**, not proof that original physical gates were satisfied.

## Prior art / source references carried forward

DASHI canonical crosswalk already includes [Tesla US787412A](https://patents.google.com/patent/US787412A/en), [Hings US3361957A](https://patents.google.com/patent/US3361957A/en), [Plauson US1540998A](https://patents.google.com/patent/US1540998A/en), [Smith Mexican application](https://patents.google.com/patent/MXNL02000035A/en), [Lyden US12136824B2](https://patents.google.com/patent/US12136824B2/en), [Earth Energies 675](https://patents.google.com/patent/US20150102675A1/en) and [676](https://patents.google.com/patent/US20150102676A1/en), [US12185058B2](https://patents.google.com/patent/US12185058B2/en) independent ultrasonic sideband phase, [US20180310111A1](https://patents.google.com/patent/US20180310111A1/en) virtual sources, [Papadopoulos 2011 two-stage ionospheric current theory](https://doi.org/10.1029/2011GL047368), and [experimental ICD study](https://doi.org/10.1029/2011GL049263). Paper/patent/reel evidence tiers remain distinct. This round adds 2025–2026 global capacitor/current evidence and a *source-specific component energy constraint*, not a new assertion about Smith's actual input/output performance.

## Local acceptance

`python -m pytest -q test_source_port.py` => 31/31 PASS. `python analytic_source_bounds.py` => 5 exact symbolic identities PASS. Original previous model `analytic_port_lemmas.py` and `reciprocal_reservoir.py` replay from prior user package PASS; Agda kernel NOT run. The GitHub branch contains source-authored Agda and scripts, but exact-head replay must remain explicit and must not be represented as the local-package result.