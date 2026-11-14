# Diamond MCG / causal bioEM max-cut — phase 2 handoff (2026-10-22)

## Work committed in this continuation

- NVFiniteResonanceReadoutExact.agda: signed labelled axial NV transitions and symbolic ODMR datum. This is **not** an optical fluorescence measurement.
- DiamondMCGAxialResonanceBridgeExact.agda: exact finite-mode current -> Biot-Savart magnetic field -> sensor-axis projection -> NV axial Zeeman-splitting theorem; reuses owner modules.
- BioEMErrorBudgetExact.agda: conditional deterministic error transport with triangle inequality, monotonicity, transitivity and associativity as explicit assumptions. This is not a bound established for any measured experiment.
- BioEMGaugeFibreBoundaryExact.agda (prior tranche): gauge-invariant readout; no geometric reduction or extra-dimension physics asserted.

## Status by promised deliverable

| Gate | Status | Blocking physical evidence or theorem |
| --- | --- | --- |
| Finite spin basis and axial Zeeman branches | source-written | exact-head kernel receipt |
| Finite current -> field -> axial splitting | source-written | continuum/tissue transfer and quantitative calibration |
| Full transverse, strain, hyperfine Hamiltonian | open | construction using concrete complex qutrit matrix owner |
| Optical pump/microwave/fluorescence and ODMR likelihood | open | optical dynamics, positivity, normalisation, fit against published data |
| Cardiac conductor geometry | open | conductivity tensor, boundary conditions, source distribution, mode truncation bound |
| Experimental noise/error budget | abstract theorem written | calibrated numerical error inputs, confidence intervals, processing and RF confounders |
| Optogenetic memory causal intervention | typed scaffold written | channelrhodopsin currents and controlled intervention data |
| 5D electromagnetic geometry | gauge-fibre abstraction only | exact donor PR, Kaluza–Klein metric reduction and physical compatibility proof |
| EM–GW/antigravity comparison | donor PRs located | concrete same-apparatus discriminator, no exotic gravitational inference |
| Lean mirror / external evidence replay | open | separate port/evidence artefacts |

## Next substantive max-cut, independent of CI

1. Identify concrete matrix API and fully implement three spin-1 matrices including transverse magnetic field and strain; prove Hermiticity in ordinary complex qutrit.
2. Implement ODMR observation likelihood calibrated to source figures, and connect symbolic lines to identifiable sensor frequencies under linewidth conditions.
3. Compile cardiac source currents via a biologically grounded conductive volume, prove magnetic-field approximation and propagate the bound through the NV sensor.
4. Run a source-acquisition and disagreement ledger on exact experiments (paper datasets, frequencies, sensor layout, photon statistics, pre-processing) before empirical promotion.
5. Extract exact gauge/gravity donor modules from PR #1099, #1163, #1217 only after their branch import dependencies are available.

## Proof boundary

Source-written Agda declarations are not kernel-checked theorems. A composition identity is not a physical calibration. Magnetic waveform observability is not unique inversion of the cardiac current, nor evidence of an experienced memory state. Attribution remains with the respective experimental and mathematical source authors.
