# Approved crystal/NV/optogenetic maximum-cut — 2026-10-22

## Implemented artifacts
- `DASHI/Physics/QuantumSensors/NVCrystalOrientationExact.agda`: finite four diamond-NV <111> orientation labels, unnormalised rational directional magnetic projections and uniform-field identity. Includes explicit strain/reference parameters. No space-group proof or crystallographic defect spectral calibration.
- `scripts/check_diamond_nv_crystal_optogenetic_maxcut.py`: concrete SymPy spin-one `Sx,Sy,Sz`, all three commutators, Hermitian `H=D Sz²+E(Sx²-Sy²)+gamma (Bx Sx+By Sy+Bz Sz)`, axial reduction to prior NVSpinOneAxialExact, trace identity, finite projective POVM normalization/orthogonality, four signed <111> orientation second moment, and the additive-null two-factor optical intervention contrast. All are symbolic exact checks, not evidence of observed photon statistics or mitochondrial-neural causation.

## Repo reuse audit
- Direct quantum owner: `DASHI/Algebra/Quantum/OrdinaryComplexQutrit.agda` and `QutritMatrixGates.agda`. Their abstract star-semiring 3x3 matrices avoid a duplicate operator algebra; numeric SymPy serves as a concrete exact executable exemplar pending a formally witnessed Agda matrix instance.
- Crystal example: `DASHI/Physics/CondensedMatter/AltermagnetCrystalActionBridgeExact.agda` owns a finite C2 action on a different material; its group-action methodology, not its actual crystal generator, transfers to NV.
- Jordan–von Neumann `UnificationJordanVonNeumannAdapterBoundary.agda` concerns polarization/inner products and has unpaid hypotheses. Exceptional Jordan/Albert material from PR #1106 is conceptually separate and has no established NV defect representation.
- Mitochondrial `MitochondrialCristaOscillatorBoundary` / `MitopolaritonTwoModeSpectrumExact`, `MitopolaritonOptogeneticFactorialExact`, and optogenetic engram `OptogeneticMemoryObservationBoundaryExact` own the distinct experimental lanes.
- PR #1239 KK gauge and PR #1238 exact 5D metric fixture are not physical generators of these spin or biology degrees of freedom.

## Hard scientific boundaries
1. A four-axis geometric model requires normalized [111] vectors for field units: replace unnormalized projection by /sqrt(3) in a constructed real carrier, with orientation degeneracy/calibration.
2. Full spin-one matrix is symbolically checked in SymPy, **not yet a kernel-checked Agda concrete complex Matrix3 proof**. Finite projector completeness is not an optical-pump/microwave-fluorescence POVM.
3. Crystal strain E and environmental noise must be calibrated from actual crystal/NV defect spectroscopy, with hyperfine/N-14, N-15, and 13-C terms where appropriate.
4. Real diamond MCG photon shot-noise, fluorescence contrast, ODMR linewidth, microwave waveform, thermal/RF/vibration/gradiometry and 3D sensor orientation remain experimental receipts.
5. Mitochondrial mid-IR and classical visible-light opsin excitation must be independently controlled; physiological currents, ATP changes and neural responses cannot be inferred from a symbolic four-arm contrast.
6. KK Einstein–Maxwell reduction and Monster/Jordan/SU3 classification are independent physics programmes; do not conflate them with biosensing.

## Validation
Source-written only in Agda; CI intentionally skipped at user request. The script is committed for local execution via `python3 scripts/check_diamond_nv_crystal_optogenetic_maxcut.py`. A verified execution receipt is **not claimed in this document**.

## Ranked next steps
(1) concrete `OrdinaryComplexQutrit` Agda Matrix3 spin operators plus Hermiticity; (2) source-specific crystal/sensor optical likelihood and calibration; (3) quantitative tissue-current transfer with actual geometry and uncertainty; (4) mitochondrial and opsin experimental result comparison with negative controls; (5) physical dimensioned same-object bridge if KK is to be used.
