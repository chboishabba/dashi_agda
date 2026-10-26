# NV photon-readout observer refinement, 26 October 2026

## Existing physical-model owners
- Diamond MCG #1238 owns `NVSpinOneAxialExact`, `NVPhotonBinaryLikelihoodExact`, `NVFiniteResonanceReadoutExact`, `NVODMRDetuningSymmetryExact`, `NVFiveLevelOpticalMasterExact`, and the optical/rate/calibration evidence boundaries.
- The immediately preceding stacked NV weld #1269 owns a reversible C3-label ↔ QutritBasis chart and a physical axial-energy collision at zero magnetic field.
- Consumer-relative observer collision and experimental discriminator methodology is present in parallel Agda #1266 and #1267; this file implements a device-model-specific theorem rather than restating generic theory.

## Exact finite discriminator now source-written

`NVPhotonObserverRefinementExact.agda` consumes the prior photon likelihood with its normalization and nonnegativity obligations intact, and defines
`observe_p(s) = (NV.energy p (labelToKet s), Photon.photon (response s))`.
At zero field, the two `m_s=±1` states share the same rational axial energy.

1. If their binary photon fractions are equal, the refined joint observations collide. A universal exact inverse decoder is impossible; constructive proof reuses the prior finite constructor disequality.
2. If their binary photon fractions differ, the joint observations are different at arbitrary axial-field parameters. The theorem demands an explicit disequality witness supplied by an actual model/experiment.

**A distinguishing distribution is not a single-shot zero-error classifier**: both Bernoulli responses may assign positive probability to the same outcome. A perfect observational inversion theorem needs stronger disjoint-support conditions, which are neither assumed nor observed here.

## Relevant physical details from prior art
`NVFiniteResonanceReadoutExact` predicts labelled transitions `D±γB`, but they coalesce at B=0; raw spectral/ODMR readings require linewidth and resolution evidence. `NVODMRDetuningSymmetryExact` uses a phenomenological Lorentzian denominator and does not supply physical contrast data. `NVPhotonBinaryLikelihoodExact` represents a single binary detection gate and does not claim a calibrated Poisson count model.

## Experiment acceptance contract
Use a declared platform/defect and two prepared states. Predeclare the microwave+laser pulse protocol, magnetic field and orientation, nuisance drifts, detector background and dead time, readout windows, sample size, blinded train/held-out split, and a statistical test of equal outcome distributions. Estimate state-conditioned photon response with uncertainty, and compare to the energy-only observer baseline. Keep raw data hashes, source-root provenance, device/platform identifiers, and separate readout fidelity from MCG magnetometer sensitivity or computational gate fidelity.

## Cross-PR discipline
- No import from unmerged #1261 crystal D4h branch, which is not diamond's NV C3v site group.
- No import of unmerged #1262 finite SUSY-QM into physical MCG owner. Its supercharge is conditional on ideal degeneracy and grading.
- No inference of hardware cross-core entanglement, quantum advantage, exotic TSFV mechanism, or observed spacetime SUSY.
- Source-written; no Agda kernel receipt or CI claimed.
