# Feynman path integral × TSFV × diamond optical observation — max-cut 2026-10-23

## Repo-native prior art used
- `DASHI/Physics/Foundations/ActionPhaseLiftBoundaryExact.agda`: explicit calibration is required to promote structural action to quantum phase S/hbar; no automatic phase.
- `DASHI/Physics/Foundations/TSFVFeynmanDerivationObligationsExact.agda`: explicitly retains physical admissibility, calibrated action/phase, amplitude measure, continuum propagator and experimental discriminator as distinct unpaid arrows.
- `DASHI/Physics/Foundations/StationaryCoherenceClassificationExact.agda`: stationary point is not necessarily shortest path, and stationary-phase asymptotic estimates are separate from stationary labels.
- `DASHI/Physics/Closure/TSFVBidirectionalCausticBridgeExact.agda`: two-boundary admissibility and observation projection; some distinct histories produce the same coarse observation.
- `DASHI/Physics/Closure/TSFVActionPhaseWeightSeparationExact.agda`: quantum phase, Gibbs weights and MDL priors are distinct.
- `DASHI/Physics/QuantumSensors/NVTSFVHistoryOpticalNonidentifiabilityExact.agda`: observed coarse photon mean can merge distinct histories.

## New finite theorem and executable
`DASHI/Physics/QuantumSensors/NVTSFVFinitePathInterferenceExact.agda` supplies Gaussian-rational amplitudes, coherent addition before squaring, incoherent addition after squaring, and a two-path opposite-phase example: coherent intensity zero whereas incoherent intensity is two. These are elementary quantum interference facts, included here as an executable finite bridge without claiming a Feynman integral.

`scripts/check_nv_tsfv_feynman_interference.py` calculates relative-phase interference `I(theta)=2+2 cos(theta)` for two equal amplitudes and a path distinguishability/visibility parameter `v`: `I_v(theta)=2+2v cos(theta)`. v=0 suppresses cross terms, v=1 recovers ideal coherent interference. This is a model of distinguishing-environment states via their overlap, not an empirical NV visibility value.

## Observation semantics and scientific restrictions
Amplitudes of indistinguishable alternatives add; probabilities or intensities require the Born rule and normalization. Distinguishable path labels/decoherence suppress cross terms. A spin-resolved ODMR fluorescence mean is normally obtained from driven dissipative NV dynamics and photodetection, *not* automatically from a free-electron all-path sum. Neither a history label nor Candidate256 action is a calibrated S/hbar. Finite destructive interference is not a proof of continuum stationary phase, nor that light follows one objectively selected path.

For optogenetics and mitochondria, source-specific coherence/decoherence and laser coupling must be established before transferring amplitude-level interference to biochemical outcome distributions. The legitimate common architecture is history admission -> physical action/phase -> amplitude sum -> detector measurement with path/environment distinguishability -> causal interpretation.

## Pending high-alpha proof cuts
1. A concrete physically derived S/hbar phase from an optical propagation model with dimensions and an experimental source.
2. Finite multi-path composition and unitarity (or explicitly conditioned nonunitary instrument) on the existing `OrdinaryComplexQutrit` complex matrices, with normalization and POVM.
3. Physically sourced NV optical pump and measurement operator dynamics; distinguish coherent microwave spin evolution from incoherent photon emission/detection.
4. Quantified optical visibility/dephasing and timing-resolved SPAD controls; calibrated, rather than postulated, phase and path overlaps.
5. Continuum propagator and rigorously quantified stationary-phase approximation, not a mere formal path-integral symbol.
6. TSFV Candidate256 and history fibre to optical paths must have a typed physical realization witness; otherwise do not claim they denote the same histories.

CI/Agda kernel intentionally not run at user request. New code is source-written and script is committed, without claiming local execution receipts. Original mathematical and physical prior art remains attributed to quantum mechanics and Feynman.
