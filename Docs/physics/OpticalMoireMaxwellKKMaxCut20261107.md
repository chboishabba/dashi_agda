# Optical moiré / Maxwell / KK: reuse-first max-cut (2026-11-07)

## Original source and ownership
Prompting optical result: Dev and Shen, *Freespace “twistronics”: moiré structured light for optical supertopologies*, Light: Science & Applications (2026), https://www.nature.com/articles/s41377-026-02533-w. This is external experimental work. The source's actual input complex fields, Stokes maps, raw detector arrays and uncertainties must be acquired before source-faithful reproduction is asserted.

Existing repository owners:
- DASHI/Moonshine/TwistronicsRelativeRegistrationComparatorExact.agda: typed relative registration, observer refinement and sensitivity witness.
- PR #1163: selected MATBG/Bistritzer–MacDonald reciprocal and C3 moiré geometry, band calculation and source calibration.
- PR #1272: Fourier optical phase observation and inverse/spectral tests.
- DASHI/Physics/Optics/OpticalPhenomenaKernelBridge.agda, FresnelZonePlateDiffuserCodecBridgeExact.agda: optical consumers.
- PR #1460: Lorentz31 / Euclidean-vs-Lorentzian Hodge and same-source KK/OS requirements.
- PR #1241: conditional five-dimensional KK source and reduction, not an independently observed optical metric.
- PR #1099: electromagnetic stress/GR coupling; not needed for optical-vacuum propagation.

## Implemented here
- OpticalMoireRegistrationMaxwellKKExact.agda is a *thin specialization* of the existing moiré registration carrier to selected Jones superposition and Stokes observation.
- Inherited exact proofs keep both constituent optical slots fixed as registration varies; given a registration-sensitive Stokes witness, observation sensitivity is inherited.
- Physical Maxwell and KK predicates are separate fields, preventing automatic promotion of an optical moiré observation into a 5D gravity claim.

## Decisive remaining original physical leaves
O1: Exact source-native Jones/polarization amplitude, phase and rotation action, including polarization-basis changes. A relative-registration carrier alone does not derive it.
O2: Prove and/or check source-free Maxwell transverse/angular-spectrum propagation for the *same* fields, including longitudinal E and numerical convergence.
O3: Produce a mathematically justified Stokes map and topological degree with nonzero-intensity/singularity, domain-boundary and discretization conditions.
O4: Reproduce source configuration angles, measured skyrmion/skyrmionium structures and their topological transitions using the source's parameters and data rather than unsupported illustrative fixtures.
O5: Same-apparatus propagation/obstruction intensity and polarization records, uncertainty-calibrated comparison and stability of the selected topology.
K1: Only for a *separate KK interpretation*: actual 5D Einstein–matter solution, reduced metric equal to the measured optical observer metric, same source, stress and units. This is NOT a prerequisite for a conventional free-space Maxwell optical moiré experiment.

## Critical distinctions
Graphene electronic Berry topology is not the same invariant as optical Stokes skyrmion degree.
A finite-window numerical skyrmion integral need not be integer-valued without boundary control.
An optical phase/topology experiment does not establish exotic gravity.
Agda source present does not mean exact-head Agda kernel acceptance.
No raw source paper arrays or same-apparatus empirical reproduction are claimed acquired by this branch.
