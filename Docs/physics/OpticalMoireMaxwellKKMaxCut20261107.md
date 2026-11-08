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

## 8 November 2026 — original-data and same-source Maxwell replication cut

### Original research authority
- Dev, Vasu and Shen, Yijie, Light: Science & Applications 15, article 396 (6 Nov 2026), DOI 10.1038/s41377-026-02533-w (article CC BY 4.0). Optical supertopologies and all published experiments remain credited solely to their original authors.
- Dev and Shen, DR-NTU (Data) DOI 10.21979/N9/AJB6FD, V2, CC BY-NC 4.0; 690 original MATLAB files, classified by the repository as simulation data. The repository file-specific provenance must be verified before a file can be described as an observed detector measurement.
- DASHI owns the independent analyzer, numerical same-field Maxwell implementation, source-file verification, receipts and formal adaptor. Citation does not import theorem authority, imply agreement or transfer physical results across graphene, KK and EM.

### Public original-data discovery and checksum certificate
The source V2 listing at https://researchdata.ntu.edu.sg/dataset.xhtml?persistentId=doi:10.21979/N9/AJB6FD identifies a six-channel case C4/10_35/0:
IA.mat MD5 87654da380569dc738acf12cd395a053
ID.mat MD5 6e076bcb8d703f227164dbcefbbdbbea
IH.mat MD5 52ce9afe15061244e26913b4ce1fdb13
IL.mat MD5 3a89e1788ae2db4822f3d921a8662d3a
IR.mat MD5 4ab487441fbbb6cf8ac02f3bad983f76
IV.mat MD5 d35cce39aced9ffee7463945a937a781
These checksums belong to the original repository, not to DASHI. The data consumer rejects a downloaded selected case with nonmatching MD5 and separately records SHA-256. Direct file download was stopped by the publisher's anti-bot page in this environment; **no original MATLAB array bytes were processed**.

### Implemented original research reuse / independent analysis
- scripts/replicate_dev_shen_original_matlab.py: original six-polarizer MATLAB file intake; strict finite aligned arrays; Stokes reconstruction from H/V, D/A, R/L; validity gating; solid-angle open-domain topology; original MD5 and computed SHA-256; explicit source-data/simulation classification; synthetic stereographic BP test.
- scripts/check_optical_moire_full_maxwell_propagation.py: source Eq(1) Gaussian Fourier ring; transverse and longitudinal E; B=(k cross E)/omega; independent divergence E/B, Faraday and Ampere residual checks; z propagation and circular-obstruction recovery, same-source and source-aligned for N=3/4/6.
- scripts/check_optical_moire_source_eq1.py retains the canonical source-function-form owner; the real original data are never manufactured by the forward simulation.

### Local execution results and limitations
Independent local analogous numerical implementations executed: six-channel synthetic BP charge -0.9835863 (OPEN domain, no integer degree certificate), synthetic no-intensity fail-closed PASS, max vacuum Maxwell residual 1.6012e-16, synthetic obstacle local field error at z=0, 0.2, 0.5 m of 1.0, 0.052646, 0.002306 (128 grid). At z=.5 m for n=96/128/192/256, relative errors 0.002501/0.002306/0.002082/0.002228. This is selected wavelength 532 nm, transverse width 3 mm, selected angular spectrum, not an apparatus-calibrated comparison; FFT-periodic-domain effects are not excluded by these values. Additional eight reported angle/symmetry labels and 24 resolution/z points were computed synthetically. Exact committed HEAD Python script and Agda kernel acceptance have not been executed.

### Original data analyzer command
python scripts/replicate_dev_shen_original_matlab.py --test
python scripts/replicate_dev_shen_original_matlab.py --root /original/NTU-V2 --list
python scripts/replicate_dev_shen_original_matlab.py --root /original/NTU-V2 --case C4/10_35/0 --out /tmp/original-c4
python scripts/check_optical_moire_full_maxwell_propagation.py --test

### Precise unclosed experimental replication obligations
1. Acquire the primary original MATLAB bytes for each selected source case and verify V2 MD5 plus computed SHA-256. The source site anti-bot restriction is a data-access blocker, not a theoretical lemma.
2. Confirm per-file experimental-versus-simulation status, instrument dark/flat/polarization gain, optical axis/handedness and spatial registration; obtain supplementary singularity correction delta and boundary/contour definitions.
3. Independently calculate closed-contour/cell topological counts for original C6 and C4 angle sweeps; quantify resolution convergence and source comparison, retaining error bars/replicate provenance. An OPEN field-of-view integral is never automatically an integer degree.
4. Compare recorded z-series and obstruction sequences with a same-apparatus source model; compute honest uncertainty and predictive held-out fidelity. Synthetic recovery is not experimental recovery.
5. Optional KK same-source Einstein-matter metric reduction remains a separate physical identification task, not a prerequisite for Maxwell optics.

No CI is required by this research task. Do not promote code presence, publication citation, synthetic numerical fit or self-selected parameters to an original experimental replication.
