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


## 2026-11-07 source-exact functional-form advancement

- The original Dev--Shen optical paper's primary identifier is DOI **10.1038/s41377-026-02533-w**, *Light: Science & Applications* **15**, article **396** (published 6 November 2026). The new Agda source atlas uses canonical `AttributedSourceCore`. The source retains all credit for the original Fourier-Gaussian interference and the observed topological phenomena.
- Paper Eq (1) has Gaussian Fourier beamlets at `(α_j,β_j)=γ(cos δ_j,sin δ_j)`, `δ_j=π(2j−1)/N`, `γ=d/sqrt(2(1−cos(2π/N)))`, with circular components `e_R+μ exp(i(θ0+2πm(j−1)/N)) e_L`. This structure, including N=3,4,6, is implemented in `scripts/check_optical_moire_source_eq1.py`.
- The numerical routine uses an explicit circular-to-Cartesian Jones convention, Cartesian angular-spectrum Maxwell propagation, longitudinal `E_z=−(k_x E_x+k_y E_y)/k_z` on the propagating support, and normalized Stokes directions. Synthetic source parameters are **not** claims about the experiment's absolute beam calibration.
- A separate local implementation of the same source Eq(1) functional form passed N=3/4/6, helical-index/twist sensitivity, Maxwell transversality (~1.41e−17), spectral propagation norm (~1.39e−17), constant-polarization degree-zero and missing-intensity fail-closed checks. **The exact committed script has not yet been separately executed against this PR head.** No Agda kernel check has been run.
- The paper reports C4 dark spots and a small LCP correction `δ` to remove singularities. The current replay intentionally refuses to promote any undefined-Stokes patch to a topological degree. Source-specific `δ` magnitude/phase and genuine topology preservation must be recovered from supplementary material before implementing a physically faithful correction.
- Original experimental topological configurations include 13.2° (C6), 27.8° nested C6, 16.26° (C4), 30° quasicrystalline textures and measured propagation/obstruction. Naming the angles is **not** reproduction; selected synthetic computations are not the original physical arrays.
- The article advertises a primary data repository at https://doi.org/10.21979/N9/AJB6FD . The file contents were **not** acquired or validated in this round.

### Attribution and implementation separation

Original external physics: Dev & Shen (2026), BM (2011) and the appropriate optical/geometric antecedents as cited in those original works.
Original repository contribution: thin Agda specialization and independently coded Eq(1) numerical replay, source attribution, tests, same-object consumer boundary. They are **not** the original discovery of optical supertopologies or a novel Maxwell law.

### True end-to-end terminal gates

1. Source-exact supplementary beam parameters, intensity-null correction and polarization calibration.
2. Source-array/figure acquisition with hashes, coordinates and instrument provenance.
3. Numerically converged closed-cell/topological-boundary Stokes charge vs source observations, including measured uncertainties and singularities.
4. Same model and source records for z-propagation and obstacle recovery, with convergence and no aliasing/diffraction claims beyond measured regimes.
5. A separately motivated KK metric-reduction/physical same-source proof only if claiming KK physical identity. It is not a dependency for ordinary optical propagation.
