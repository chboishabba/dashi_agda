# Smith / Filsinger causal nonlinear transfer: integrated maximum cut (2026-11-15)

## Ownership and exact status
Canonical owners reused: `DASHI.Physics.Motors.Circuit36927ComponentGraphExact`, `Circuit36927SwitchStateExact`, `Circuit36927RecoveryEnergyBoundExact`, `DASHI.Promotion.MaxwellExteriorCalculusAdapter`, `DonSmithFilsingerClaimBidiExact` and `SmithFilsingerReflectedPortBidiExact`. ZVS is a driver implementation; spark gap is a conditional capacitor-bank dump/switch, not a new energy source. New source-qualified time-indexed adapter lives at `SmithFilsingerTimeIndexedTransferExact.agda`. **Agda kernel verification not performed:** no Agda/Nix installed in local runtime.

## Actual source interpretation (147-page user PDF)
- **P28 fig10**: resonant electromagnetic power system; **p29 fig11**: a different generator arrangement. Do not fuse.
- **P49–51 / fig28**: L1 wire length one quarter of the remaining L2 section, split L2 17+17 turns, movable L1 and a geometric 240-degree winding endpoint, not measured electrical quadrature.
- **P65 fig40**: later circuit *passed to the compiler/editor* for a neon-tube driver; not proved to be Filsinger's exact commercial unit.
- **P81–82 figs53–55**: oppositely described secondary branches, proposed diode and grounding variations. Some are commentary/variants, not original Smith test evidence.
- **Filsinger narrated reels**: independent Earth-connected ZVS, 1/2/4 MΩ loading, midpoint-accessible transformer and diode branches, multiple blue and white capacitors, spark-gap dump, *proposed* portable 1:1.618 antenna. Each video occasion and author attribution remains distinct.

## New mathematical work, not recycled gates
- **Timed pump and nonlinear mixer energy lemma:** for generalized coordinates `x,y`, with `H=.5(vx²+vy²)+.5k1(t)x²+.5k2(t)y²+g(t)x²y+.25lambda(t)x⁴`, the exact identity is
`dH/dt=Fx vx+Fn vy-Rx vx²-Ry vy²+.5k1dot x²+.5k2dot y²+gdot x²y+.25lambdadot x⁴`.
SymPy checks that expression identically; a positive stabilizing quartic prevents an unbounded artificial negative potential. Cross-forces are derivative-consistent: `-2gxy` on x, `-gx²` on y. The modulation actuator must pay the separate work integral, and it may absorb energy depending on phase.
- **Two-timescale test**: fast oscillatory pumping with a slow envelope and quadratic `x²y` mixer generates slow components (including second-harmonic envelope components). Conserved work tracked for driver, independent natural-mode source, modulator, useful output, loss and stored energy. Four selected phases (0,90,180,270 deg) yield useful model work 7.92, 9.92, 8.40, 5.46 units; independently supplied natural-source work remains ~0.1013–0.1017 units and modulator work changes significantly including negative extraction. This is **not** a net environmental harvest result. Integration work residual <0.0005 model energy units.
- **Causal propagation**: exact discrete retarded sampling and `exp[-alpha d-i omega(d/v)]` test source-dependent channel arrival, attenuation and phase; the actual Earth/ionosphere parameters remain unselected. Maxwell is not instantaneous and local electron drift velocity is not the field-front speed.
- **Audio inverse search:** 16 *overlapping* source-derived 8-s windows from the original 7.8kHz acoustic envelope, 3–5Hz peaks approximately drifting. Fit a positive Lorentzian strength model to the *hypothetical doubled* peaks; scan Q=3,5,10,20 and candidate centre frequencies 6–10Hz, compare against 2,000 frequency-label permutations. Best R²=0.165746, permutation-adjusted p=0.563218; fixed 7.83Hz Q5 **positive** fit R²=0 (unconstrained negative-slope model R²≈0.004). This analysis does NOT identify natural-reservoir phase/power. Audio calibration gain × mechanical transfer × electrical oscillation has a scaling non-identifiability: actual source work cannot be uniquely recovered from uncalibrated sound, even with perfect backprop.
- **Physical back-calculation:** ideal Earth Thevenin source feeding 0.4W with 1kΩ source R requires open-circuit voltage >=40V. Filsinger's 48V reading was on capacitors, not measured source `Voc`. At illustrative RF `S=63uW/m²` and total conversion efficiency 0.63, `A_eff>=10078.105m²`. These are conditional required values; not device-size or site field measurements.

## Explicit attribution correction / prior art
- Donald Lee Smith [MXNL02000035A](https://patents.google.com/patent/MXNL02000035A/en) is an **application publication, discontinued**, not a granted tested device.
- Nikola Tesla [US787412A](https://patents.google.com/patent/US787412A/en): terrestrial power transmission.
- Donald L. Hings [US3361957A](https://patents.google.com/patent/US3361957A/en): telluric transducer.
- Hermann Plauson [US1540998A](https://patents.google.com/patent/US1540998A/en): atmospheric energy conversion.
- Earth Energies applications [US20150102675A1](https://patents.google.com/patent/US20150102675A1/en) (Dinwiddie, Wright, Ames; grant family US9564268B2) and [US20150102676A1](https://patents.google.com/patent/US20150102676A1/en) (Dinwiddie, Wright; abandoned): **not Marani**, contrary to an earlier unsupported attribution.
- [US20150280518A1](https://patents.google.com/patent/US20150280518A1/en): Omer Stupac, Earth electricity; [US9331603B2](https://patents.google.com/patent/US9331603B2/en): Clint McCowen / Ion Power Group, energy collection.
- Virtual sound/phase patents: [US20180310111A1](https://patents.google.com/patent/US20180310111A1/en) for phase-corrected virtual-source delays, and [US20170289722A1](https://patents.google.com/patent/US20170289722A1/en) for focused ultrasound/nonlinear acoustic demodulation.
- Ionospheric two-stage **theory** [doi:10.1029/2011GL047368](https://doi.org/10.1029/2011GL047368) and HAARP **experiment** [doi:10.1029/2011GL049263](https://doi.org/10.1029/2011GL049263): heated F-region diamagnetic current -> magnetosonic wave -> lower E-region Hall current secondary radiator. High-power HF facility, **not** measured Filsinger efficiency.
- Original narrated reel links: [shunt/ZVS](https://www.instagram.com/reel/DfiqPnkPnP5/), [Earth grounds](https://www.instagram.com/reel/Dfi1D7CPzyM/), [midpoint commercial architecture](https://www.instagram.com/reel/Dfu9Jseviz9/).
These are lineage/physics analogues; patent status never substitutes for a measured transfer coefficient or device operation.

## Exact remaining original-world proof gates
- **R1** actual smith Figure10/11/40 and Filsinger terminal/wire continuity (including diode polarities, all blue bank and meter pins). Source graph transformation is not netlist equivalence.
- **R2** simultaneous electrical switching f(t), V(t), I(t) and acoustic transfer calibration; existing acoustic analysis is not such a measurement.
- **R3** same-object finite-conductivity open Maxwell/ionosphere spatial solution with driven boundary, constitutive `sigma(E,T,n)`, retarded kernel and *measured or source-derived* coefficients, no instantaneous action.
- **R4** distinct natural, Earth electrochemical/geoelectric, atmospheric, RF and ionizing particle signed input-port receipts, with independent control and load current/power factor.
- **R5** **Agda 2.9 kernel typecheck** of new module and dependencies; local source-written finite lemmas are not claimed kernel accepted.

## Local acceptance receipt
Local full research package ran 29/29 Pytest checks, SymPy exact Hamiltonian identity, 4-phase nonlinear receiver work integration, causal delayed-line checks and 2,000-permutation source-audio inverse model. Full auditable code, original-source page crops, plots, structured source manifest, actual source-derived CSV, and results are attached in the conversation package `smith_filsinger_integrated_maxcut_20261115.zip`. Source-dependent physical gates above remain explicitly open.
