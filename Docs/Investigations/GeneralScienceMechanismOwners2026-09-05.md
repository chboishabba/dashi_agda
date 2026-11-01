# General science mechanism owners — 2026-09-05

This tranche moves the underlying science out of person-specific investigative fixtures and into reusable domain owners.

## Materials: nickel-base superalloys

`DASHI/Physics/Materials/NickelBaseSuperalloyMechanismExact.agda`

Owns the generic chain:

`composition -> processing -> microstructure -> measured property`.

Key mechanisms include a Ni-rich gamma matrix, ordered gamma-prime approximately Ni3(Al,Ti), solid-solution strengthening, chromia/alumina protective scales, thermo-mechanical history, solution treatment and ageing.

Firewalls include:

- same composition != same microstructure;
- gamma-prime present != optimal strength;
- oxidation resistance != burn resistance;
- public composition != tacit process history.

Highest-value residuals: exact heat treatment, gamma-prime fraction/size, grain/secondary-phase state, oxide scale and protocol-specific mechanical/burn tests.

## Nuclear: autonomous fission instrumentation and control

`DASHI/Physics/Nuclear/FissionInstrumentationControlReliabilityExact.agda`

Owns the functional chain:

`sense -> condition -> estimate -> decide -> actuate -> protect -> telemetry -> diagnose`.

Qualification is separated into component characterisation, radiation tests, thermal tests, combined environments, ageing/drift, calibration, fault injection and integrated system validation.

Firewalls include:

- radiation-hard != mission-qualified;
- surviving sensor != reliable closed control loop;
- public component specification != qualified system;
- nominal calibration != end-of-life calibration.

## Plasma: reduced fluid-kinetic Fourier-Hermite numerics

`DASHI/Physics/Plasma/ReducedFluidKineticHermiteNumericsExact.agda`

Owns strong-guide-field ordering, reduced MHD / KRMHD / KREHM model relations, perpendicular Fourier/pseudo-spectral representation, Hermite velocity-space hierarchy, operator splitting, closure/truncation and verification hierarchy.

Firewalls include:

- converged discrete solution != full kinetic truth;
- correct RMHD limit != correct kinetic closure;
- more Hermite moments != automatic physical accuracy.

Highest-value residuals: ordering receipt, closure justification, Hermite/spatial/temporal convergence, invariant budget and cross-code benchmarks.

## Accelerator physics: flash radiography

`DASHI/Physics/Accelerators/FlashRadiographyPhysicsExact.agda`

Owns:

`pulsed power -> electron injection -> induction acceleration -> beam transport -> bremsstrahlung target -> object transmission -> detector -> reconstruction -> inference`.

The resolution budget separately tracks source spot, pulse/motion blur, detector blur, scatter, photon statistics and geometry.

Firewalls include:

- high beam energy != small source spot;
- high dose != high resolution;
- radiograph != density field without inversion;
- same image != unique hydrodynamic state.

## Chemistry/spectroscopy: cryogenic messenger-tag action spectroscopy

`DASHI/Chemistry/Spectroscopy/CryogenicMessengerTagActionSpectroscopyExact.agda`

Owns:

`ion generation -> mass selection -> cryogenic cooling -> messenger attachment -> IR excitation -> tag predissociation -> fragment/depletion readout -> action spectrum -> structural assignment`.

Assignment is explicitly model-mediated through candidate structures and quantum-chemical spectra.

Firewalls include:

- same mass != same structure;
- one matching band != structural identification;
- messenger tag != guaranteed non-perturbative probe;
- clean laboratory discrimination != unique planetary biosignature.

## Generalisation bridges

`DASHI/Physics/BoundaryScienceGeneralisationBridgesExact.agda` maps the existing bounded case fixtures onto these domain owners while preserving the direction:

`generic domain science -> case-specific refinement`,

not the reverse.

`DASHI/Physics/BoundaryScienceEverything.agda` aggregates the generic science and the current case adapters.

## Current science frontier

The highest-value next work is now domain-scientific rather than biographical:

1. microstructure-resolved superalloy property modelling;
2. mission-environment I&C reliability and common-cause/fault-tolerance modelling;
3. reduced-model asymptotic applicability plus numerical convergence/closure;
4. calibrated radiographic forward/inverse modelling with uncertainty propagation;
5. spectroscopy assignment uncertainty, conformer coverage, mixture interference and sensitivity/specificity;
6. continued POAMS separation between source-proposed mechanism, preliminary observation, replication and established physics.
