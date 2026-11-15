# V2 reluctance × Don Smith time-dependent nonlinear pump — next maximum cut

## Original source boundaries
- **@madscience369 V2:** reported rotor ~2354 RPM, ~45 W load output, ~285–287 W motor-meter readout. No video-confirmed source netlist, phase count, pulse algorithm, shaft torque or external source.
- **Donald Smith/Filsinger:** separately sourced transformer, timed pump, spark dump, nonlinear mixing, ZVS, switched capacitor/inductor recovery and signed input-work arguments (see merged PR #1507 and `Docs/research/SmithFilsingerCausalNonlinearSourceRollup20261115.md`). These are independently developed claims and DASHI test models, not evidence of a matching V2 architecture.
- **Holmstrom/Resonate369:** distinct C07/V1/Dodecatron provenance in merged PR #1482. Tesla rotating-field/polyphase prior art does not grant a universal three-six-nine design theorem.
- **New work:** a source-independent cross-domain reversible co-energy identity and pulse-window efficiency optimisation for an *invented* linear winding, not measurements of V2 or reproduction of a Smith design.

## Exact nonlinear source of controller work
For differentiable and reversible magnetic co-energy \(W'(\mathbf i,\theta,u)\), let
\(\boldsymbol\lambda=\partial_{\mathbf i}W'\), \(\tau=\partial_\theta W'\), \(f_u=\partial_u W'\), and field energy \(U=\mathbf i\cdot\boldsymbol\lambda-W'\).
Then
\[\mathbf i\cdot\dot{\boldsymbol\lambda}=\dot U+\tau\omega+f_u\dot u.\]
The independent controller must supply/receive signed \(f_u\dot u\). If \(u\) only gates conduction and does not alter constitutive \(W'\), actuator energy enters through separate gate/bus losses instead; do not count it twice. Rotational modulation \(\theta(t)\) is not an independent unmetered pump: its work is \(\tau\omega\).

For example \(W'=\tfrac12 L(\theta,u)i^2-\tfrac14\beta(u)i^4\), \(\lambda=Li-\beta i^3\). A physically admissible operating domain must retain positive differential inductance and nonnegative field energy; hysteresis and eddy/core losses require dissipative internal states. The symbolic identity and linear limit are proved by SymPy in the checked script, not yet by a differentiable calculus proof in Agda.

For generator polarity \(\omega>0\) and \(L(\theta)=L_0+A\cos(k\theta)\), the electromagnetic reaction torque \(\tau=\frac12i^2L_\theta\) is negative on the falling-inductance slope. Concentrating the switch-on current there reduces copper energy per unit braking work, provided peak current, finite rise time and switching losses permit it. Conversely gating on rising inductance produces motoring torque.

## Closed analytic pulse-window benchmark
For a **single constructed coil** with conductance window \(\sin(k\theta)>q\), \(0\le q<1\), fixed current \(I\) while active:
- duty fraction \(d(q)=\arccos(q)/\pi\);
- mean generation slope \(s(q)=\sqrt{1-q^2}/\pi\);
- mean mechanical extraction \(P_m=\tfrac12 A k\omega I^2 s(q)\);
- copper loss \(P_R=R I^2 d(q)\).
At fixed mechanical extraction, the ideal copper cost becomes
\[P_R/P_m =\frac{2R\arccos(q)}{Ak\omega\sqrt{1-q^2}}.\]
Narrower pulses lower this ratio but require larger \(I\), leading to voltage, current, switch, thermal and core penalties. This shows a genuine controlled efficiency mechanism without presupposing a specific 3/6/9 phase count.

The tested *hypothetical* case is RPM=2354 (source reported), P_mech=45W (arbitrary objective; **not the source-reported output mapping**), L0=40mH, A=12mH, k=4, R=1Ω, max I=8A, 2 mJ fixed switching work +0.15 mJ/A² per transition, 0.5W other loss. A 981-sample q-grid gives baseline q=0: load-equivalent net **30.80 W**, optimum q=0.76: **33.86 W**, a **3.06 W** conditional improvement at fixed 45W mechanical extraction. The optimiser's search is a grid search over a restricted pulse family, not globally optimal control.

A high switching-energy countermodel *reverses* the efficiency benefit. Low switching energy, soft switching/ZVS, diode/active recovery, limited high-Q circulation and phase-dependent coupling are therefore high priority, not rhetorical afterthoughts.

## Mechanism owners and transfer contracts
1. **Source timings:** circuit switch state `Circuit36927SwitchStateExact`, but continuous finite di/dt, diode states and gate-drive work are new open analytic/physical laws.
2. **Recovery:** `Circuit36927RecoveryEnergyBoundExact` ensures a closed passive recovery stage cannot gain stored energy; it does not forbid higher useful output from lower dissipation under a fixed mechanical input.
3. **Nonlinear timed pump:** `SmithFilsingerTimeIndexedTransferExact` and paired Hamiltonian script distinguish driver, modulator, natural input and reversible storage. Keep original attribution; transfer the mathematical identity only.
4. **Magnetic mechanics:** existing PR #1511 conditional permeance and 3/6/9 phase test; extend to nonlinear and coupled multi-winding co-energy, not merely source-independent harmonic count.
5. **Observation:** original V2 rotor-to-scope frequency map (39.23Hz rotor vs ~60Hz displayed channel, source of channel unknown) and calibrated signed powers remain OPEN.

## Phase gates / exact next lemmas
- **P0.1** `v2PulsedNonlinearCoenergyIdentity`: exact smooth reversible calculus, current/angle/modulator terms and sign convention; SymPy checked, kernel calculus bridge OPEN.
- **P0.2** `v2PulseWindowClosedFormAndHighCurrentCounterexample`: closed trigonometric duty/extraction/copper formula; numerical quadrature and negative control pass; analytic Agda REAL+interval bridge OPEN.
- **P0.3** `v2ReversibleClampRecoveryImprovesUsefulWorkConditional`: finite Nat conditional proof added; test physical rerouting and overhead OPEN.
- **P1.1** `v2PulseControllerFiniteSlewAndBusVoltageEnvelope`: actual finite-bus, switching and harmonics globally bounded, not sample-only.
- **P1.2** `v2NonlinearMutualSaturationHysteresisAndCoenergyWeld`: same-source \(\lambda(\theta,\mathbf i,T)\), positive incremental inductance plus dissipative losses.
- **P1.3** `v2JointPhaseCountPulseConverterParetoCertified`: optimise m, angle windows, phase assignments, pulse timing, gate work, torque ripple, voltage, current and thermal costs simultaneously; retaining nonmultiples.
- **P2.1** `v2OriginalPulseAndWindingSourceReceipt`: original reel and full schematic evidence, no inferred topology.
- **P2.2** `v2SignedShaftControllerAndStorageExperiment`: contemporaneous shaft torque, speed, electrical waveforms, external supply and temperature/metrology.
- **P3** pinned Agda 2.9 kernel, reproducible numerical runner and independent data; source-written != kernel checked.

## Verification
`python -m pytest -q tests/test_v2_pulse_nonlinear_recovery.py`: 20/20 PASS at authoring. Exact source scripts and receipt must be run in the repository's pinned environment before repository acceptance. No measured anomalous energy, no exact V2 identity, no source-identical Smith/Filsinger hardware, no unmeasured natural work.