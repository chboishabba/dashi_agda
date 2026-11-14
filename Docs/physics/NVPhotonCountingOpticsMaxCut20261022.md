# NV photon-counting optical max-cut — 2026-10-22

## New outputs
1. `DASHI/Physics/QuantumSensors/NVPhotonBinaryLikelihoodExact.agda`: normalized two-outcome likelihood with explicit nonnegativity predicates/witnesses. The proof of normalization for the canonical p/(1-p) constructor is rational ring algebra. It **does not** assert the Poisson photon-count law or experimentally observed probabilities.
2. `scripts/check_nv_optical_photon_statistics.py`: SymPy symbolic sums for a Poisson count, requiring nonnegative mean mu; checks total mass one, E[N]=mu, E[N²]=mu+mu² and the variance, plus the NV bright/dark contrast mean and finite gauge-flux sensor gain. Exact symbolic identities, not a source-calibrated sensor.

## Cross-pollination, source reuse
- `DASHI/Physics/Optics/OpticalPhenomenaKernelBridge.agda`: optics propagation and constitutive/approximation regime.
- `DASHI/Physics/Semiconductor/Device/LitavisSPADMultimodalObservationExact.agda`: detector photon-counting architecture but not the particular NV instrument.
- `DASHI/Biology/LiMinyongPhotopharmacologyBidiExact.agda`: molecular photointervention candidate; different chemistry from opsins, mitochondrial mid-IR or NV centres.
- `DASHI/Biology/OptogeneticMemoryObservationBoundaryExact.agda`: neural intervention-to-behaviour controls.
- `DASHI/Biology/Levin/MitopolaritonOptogeneticFactorialExact.agda`: distinct mid-IR and opsin interventions with null-additivity check.

## Concrete unresolved physics
- Need actual OD(M)R transfer: calibrated excitation/microwave/pump rates and spin-dependent optical populations; the mathematical predicted mean from `NVOpticalPhotonReadoutExact` does not supply these.
- Poisson photon count assumption is conditional and may require overdispersion, detector afterpulsing, deadtime, blinking and non-Poisson statistics. Nonnegativity of the **mean** and detector photon response must be separately verified from source parameters.
- Need physical sensor geometry, NV crystal axes, photonic collection efficiency, RF pickup, thermal drift, calibrated linewidth, gradiometer transfer and heart/brain current model.
- Source-validation of mitochondrial IR resonance, spectral fits, actual ATP data, and optogenetic neural perturbations remain separate.
- KK/Einstein–Maxwell is not a substitute for optical pumping and measurement data.

## Verification contract
`python3 scripts/check_nv_optical_photon_statistics.py` can reproduce the symbolic identities with SymPy. This audit does not attach a verified exact-head CI/kernel receipt and is source-written only. Never promote a script filename or a stated assertion to a witnessed result without execution. Preserve classical probability/optics attribution.
