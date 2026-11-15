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

## 8 November 2026 — Bloch and Poincare reused, no duplicate ontology

Original source: Dev and Shen (2026), article DOI 10.1038/s41377-026-02533-w, original DR-NTU dataset DOI 10.21979/N9/AJB6FD. Prior Bloch-band and reciprocal-lattice literature remains separate. Existing DASHI physical donors include:
- PR #1163 BM/magic-angle graphene first-shell Bloch plane-wave machinery;
- DASHI/Physics/CondensedMatter/HexagonalSqrt3R30ReciprocalFoldingExact.agda exact determinant-three, M^T N=3I, and C3 folding classes;
- DASHI/Physics/CondensedMatter/CoQuarterTaSeTwoPhysicalSymmetryExact.agda reciprocal-axis Bloch symmetry;
- PR #1076 original magnetic Seitz/Bloch + same-object ARPES implementation;
- PR #1115 isolated-subspace Berry/projector/Wilson diagnostics;
- optics PR #1272 and Maxwell/KK donor owners #1460/#1241.

New `scripts/check_optical_moire_bloch_poincare.py` tests the Jones->Poincare/Bloch-sphere map directly from normalized optical Jones pairs. Over 100 independent deterministic complex Jones pairs it checks norm-one, invariance under global Jones phase and the pure polarization identity
`abs(<u,v>)^2 / (||u||^2||v||^2) == (1+dot(stokes(u),stokes(v)))/2`.
Finite plane-wave Bloch translation test is `sum_j ||c_j||² |exp(i q_j·R)-exp(i k0·R)|² / sum_j ||c_j||²`: the commuting reciprocal integer-wave example is near zero, and adding an irrational x-frequency gives a nonzero residual for the **selected translation**. It does NOT prove no possible periods exist globally.

Locally run analog of the committed test (100 samples, seeded): max Stokes-norm error 2.22e-16; global-phase 4.81e-16; fidelity formula 3.33e-16; commensurate translation 1.61e-15; selected irrational-mode translation 0.6571. No claim is made that an optical polarization sphere is a physical electronic Bloch band, nor that source experimental data have been reproduced.

For the source's 30-degree quasicrystalline example, generic periodic Bloch-cell machinery is NOT silently applied: translation symmetry must be checked, with quasiperiodic reciprocal star and finite-window approximants when true periodic cells are unavailable. For supercell fields, Bloch translation pertains to the complex vector field and its common phase; Stokes textures can have a distinct/smaller periodicity owing to global-phase cancellation. The two periodicity claims require separate consumers. Native field-space electromagnetic diffraction is independent of electronic band-energy eigenvalues.

Source paper explicitly reports measured n=7 bag interior 6.83, surrounding opposite-polarity -0.81 and total 6.02; these are **original Dev/Shen measurements** (not DASHI outputs). The topology count n-1=6 is their ideal relation and 30-degree higher-order quasi-crystal example has distinct boundary semantics. This provides an actual benchmark receipt target once original arrays are acquired; no numeric comparison can be asserted from source-angle settings alone.

## 8 November — closed-boundary optical degree consumer (Bloch/Stokes cut)

Prior art: Bloch phase, Jones/Poincare representation and solid-angle skyrmion topology. Original physical optical-superlattice results: Dev and Shen (2026), DOI 10.1038/s41377-026-02533-w; original simulation dataset DOI 10.21979/N9/AJB6FD. DASHI contributes numerical input validation and a conditional finite mesh test, not the topology mathematics or observed experimental discovery.

**Implemented and executed locally:** `scripts/check_optical_moire_closed_stokes_degree.py` sums oriented spherical geodesic triangle solid angles. It refuses polarization nulls, non-unit Stokes vectors, nonconstant boundary, and near-antipodal triangles. The synthetic stereographic compactification on 41x41, 81x81 and 161x161 grids returns finite mesh charge -1 on all three, with exactly constant boundary in floating arithmetic; deliberately broken boundary and missing Stokes samples are rejected. This is a tested **piecewise-geodesic finite mesh diagnostic**, not exact interval-certified continuum degree, physical image certification or a measured replication.

`scripts/replicate_dev_shen_original_matlab.py` now writes BOTH the prior `open_patch_charge` with `integer_degree_certified:false` and a separate `closed_boundary_topology_diagnostic`, only valid when that source case independently meets the boundary and triangle gates. Integer-degree claims must additionally certify physical domain compactification or periodic identification and field continuity between samples. Experimental source arrays remain unacquired due to direct endpoint access; the source data analyzer has not processed those bytes.

**Maximum remaining cut:** no generic Bloch algebra is needed. Acquire original data bytes and confirm source authors' per-file simulation-versus-experiment labeling, image geometry, calibration, polarization handedness, dark/flat, singularity correction, contour and error model. Then compare genuine source topological counts/propagation observations. KK/EM same-source metric identification is separate and unnecessary for Maxwell optical reconstruction.

## 8 November 2026 — terminal z-plane original-data comparator

**Source-first comparison specification** from Dev & Shen, *Light: Science & Applications* 15, 396 (2026), DOI 10.1038/s41377-026-02533-w:
- Fig. 4 coaxial propagation tests target C6 theta 13.2 and 16.4 degrees; C4 theta 10.35 and approximately 12.7 degrees; z=0 to 40 cm in the figure. These are published author measurements and remain theirs.
- Fig. 3 source-defined skyrmion bag reports inner charge 6.83, surrounding -0.81, combined 6.02, ideal 6. Fig. 4 reports C4 n=25 and n=13 clusters, with separate details on how variation between 7 skyrmions generates error bars.
- Self-healing arises primarily from surviving optical angular-spectrum components; Stokes topology is the tracked robust object, not itself a mechanism causing wave-optical reconstruction.
- The publicly exposed V2 NTU dataset is labelled *simulation data* and has 690 files; its published MATLAB bytes remain inaccessible to the current environment. Do not call those files measured images without source-file validation.

New script `scripts/compare_original_optical_moire_z.py` reuses the existing six-channel MATLAB parser in `replicate_dev_shen_original_matlab.py` with no second parser. It requires all six channels per z plane; checks common image shape, pair-intensity consistency and nonzero Stokes overlap; computes finite-open-patch charge, mean and 95th-percentile Poincare geodesic error relative to z0; records original-file SHA-256 and refuses to certify an integer degree or experimental replication. It refuses missing planes and calibration failures rather than substituting simulated results.

**Executed local fixture:** independently coded parallel two-plane six-channel synthetic test passed, including fail-closed missing z=20. This verifies implementation shape only. Direct original dataset endpoint is not accessible here (web result redirects to non-fetchable NTU citation page and local container DNS fails); no original MATLAB bytes were processed and no original numerical topology comparison was made.

Command (when source data are available):
`python scripts/compare_original_optical_moire_z.py --root /data/NTU-V2 --prefix C4/10_35 --z 0 10 20 30 40 --out /tmp/C4-propagation.json`

**Still unclosed:** original calibrated arrays, independently confirmed observed-vs-simulated status, within-plane spatial registration, topology segmentation and masks, experimental uncertainty and genuine replication of each cited measurement. Physically independent apparatus replication requires actual apparatus data and cannot be furnished by a numerical code or publication citation.
