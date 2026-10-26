# NV optical five-state dynamics × TSFV history fibres — max-cut (2026-10-23)

## Prior-art audit in default-branch repository

- `DASHI/Physics/Closure/TSFVBidirectionalCausticBridgeExact.agda` defines admissible history fibres, then observation projection. Projection cannot determine admissibility retroactively.
- `DASHI/Physics/Closure/TSFVHistoryConditionedChoiceBridgeExact.agda` gives two distinct ordered histories ABC and ACB with the same coarse observation, yet different history-sensitive choices. This is a genuine non-factorization theorem on a synthetic finite history carrier, not an experimentally observed optical-memory process.
- `DASHI/Physics/Closure/TSFVNonseparableTransitionKernelExact.agda` builds a Candidate256 pair transition mismatch with explicit T-invariance; this is a structural action candidate, not an NV optical rate.
- `DASHI/Physics/Closure/TSFVActionPhaseWeightSeparationExact.agda` enforces distinct action candidate / quantum phase / Gibbs weight / MDL prior roles. Its missing action-to-phase calibration precludes a quantum TSFV transfer.
- `DASHI/Biology/Physical/FiniteChemicalMasterGeneratorExact.agda` (Gillespie chemical master-equation prior art) provides the existing generator methodology used by `NVFiveLevelOpticalMasterExact`.

## Implemented on PR #1238

1. `DASHI/Physics/QuantumSensors/NVTSFVHistoryOpticalNonidentifiabilityExact.agda` composes actual TSFV history projection with a coarse two-category expected photon-mean map. ABC and ACB map definitionally to the same value, and the existing history-sensitive choice counterexample proves that no single photon-mean decoder can recover the target choices for all histories. This is a *negative observability theorem*, not an assertion of exotic quantum history causation.
2. `scripts/check_nv_five_level_stationary_tsfv.py` constructs a five-state CTMC with explicit positive rational rates, solves a stationary distribution by linear algebra, asserts Qp=0, positivity and unit mass, computes expected radiative photon rate, and illustrates the loss of temporal ordering under coarse projection.

## Relevance to optical physics and experiments

A time-integrated NV fluorescence total, without event timing or protocol context, can discard history information. Source-attested SPAD timing/histogram owners offer possible measurement modalities to **test** whether timing is helpful, but don't guarantee unique recovery. In optogenetics, mid-IR mitochondrial actuation and NV illumination have different photophysical/biological mechanisms; common history-sensitive inference architecture is legitimate, but shared microscopic dynamics has not been demonstrated.

## Real next proof/experiment gates

1. Positive CTMC semigroup / steady-state proof with symbolic rates and explicit ergodicity conditions, plus a checked reduction to earlier two-population model under declared timescale separation.
2. Event-resolved likelihood, detector deadtime, afterpulsing and laser timing; injectivity/identifiability under a *specified* collection of time-resolved observables rather than one coarse mean.
3. Physical NV multilevel rate parameters and crystal geometry derived or measured in source-attested data; real diamond-MCG ECG/MCG instrument configuration.
4. Optical spin-coherent GKSL owner using existing constructive complex qutrit machinery.
5. If proposing TSFV phase effects, provide `S/hbar` calibration, complete complex amplitudes and interference observables. None is supplied here.
6. Biological causality: explicit optogenetic and mitochondrial experimental outcomes with proper heating and photon-dose controls.

## Status

Both additions are source-written/committed only; no Agda kernel check or CI requested. The stationary script was committed as a reproducible fixture; this document does not claim it was executed. Existing TSFV mathematics and attribution preserved.
