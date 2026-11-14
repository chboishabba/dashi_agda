# Diamond / NV / crystal / quantum cross-PR integration (2026-10-26)

## Source-specific donor inventory
- PR #1262: `NVSpinOneC3HamiltonianObstructionExact` distinguishes an order-three *label permutation* from a symmetry of physical spin-one zero-field splitting: Sz² eigenvalues (1,0,1) are not preserved by cycling +1 → 0 → -1. Also contains finite SUSY factorisation and spin-one / multicore adapters. Treat these as distinct from spatial C3.
- PR #1238: `NVCrystalOrientationExact` owns four **unoriented** diamond <111> axis labels; `DiamondMCGFiniteBridgeExact` provides a rational finite Fourier-mode magnetic readout, not a calibrated material or MCG reconstruction. The PR includes finite optical, ODMR, TSFV, and C3 model work, whose source/model/experiment boundaries remain theirs.
- PRs #1115 and #1076: magnetic Seitz/Bloch machinery for Co1/4TaSe2, a separate material and magnetic symmetry group. Reuse only typed interfaces, not space-group identities.
- PR #1261: seven/fourteen/thirty-two source-attributed catalogue, B4 Weyl donors, tetragonal D4h signed matrices, Fourier lattice and atomic 369 species contracts. Tetragonal 4/mmm is NOT the diamond-cubic point group.

## Correct diamond hierarchy

Diamond's ideal bulk structure has cubic point group m-3m = O_h (48 elements) and space-group type Fd-3m (#227); face-centred cubic Bravais translations with a two-atom basis displaced by (1/4,1/4,1/4). It is nonsymmorphic; neither the fcc Bravais type nor a bare W(B3) matrix group completely determines it. The four unoriented <111> axes are a four-point O_h-set. Orientation of a particular substitutional N–vacancy defect reduces local symmetry (ideal C3v), while the spin-one Hilbert space/zero-field splitting is a distinct *representation*, not the same four-point set.

## New source-scoped PR #1261 adapter

`DiamondNVFourAxisPermutationExact.agda` has four independent axis constructors corresponding to the orientations from PR #1238 and order-three cyclic coordinate permutation plus order-four cubic z-rotation as permutations of the *unoriented axis set*. The z-quarter-turn mapping is verified from signed triples after quotient by ±1. These operations are crystal-axis permutations, not spin-level permutations.

No direct import of #1238/#1262 is made because those files may reside on unmerged branches. When merging, create a literal two-way equivalence with the original `NVAxis` and prove equivariance to the O_h/W(B3) lattice action; use exact donor symbols, and add source-branch receipt.

## Typed integration gates

1. `CubicFccMetric`: exact fcc basis, centring, primitive translations, reciprocal bcc and integral coordinate charts, then prove the W(B3) action preserves the fcc lattice.
2. `DiamondTwoSublattice`: two labelled orbital/atomic basis sites with species-preserving diamond-specific space-group operations (Seitz fractional translations, origin setting).
3. `NVDefectStabilizer`: mark N and vacancy positions, derive stabiliser of their *ordered* sites. A C3 site rotation is not any cyclic permutation of the three spin-one states.
4. `NVSpinAndBloch`: carry spin-orbit, orbital, strain, Zeeman and site symmetries on separately typed representations; require U_g H(k) U_g† = H(gk), including Seitz phases where appropriate.
5. `MCGMeasuredCalibration`: keep sensor-axis projection, optical readout, causal intervention, noise, calibration and tissue model evidence as separate receipts.
6. `TSFVHistory`: only apply phase/history transports after proving they preserve the actual physical evolution law; no generic historical chart analogy proves a new sensor mechanism.

## Attribution and verification
Classical Fd-3m, O_h, diamond-cubic basis, fcc and C3v are established crystallography, not original results. Source code and interpretation of PRs #1262/#1238/#1115/#1076 retain native authorship and dated PR provenance. This bridge is an independently authored finite adapter and roadmap. The Agda file has not been compiler checked in this session; it does not establish material identity, quantum advantage, instrument calibration or experimental detection.
