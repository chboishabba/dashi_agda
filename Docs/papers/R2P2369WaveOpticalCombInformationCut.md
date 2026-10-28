# R2P2 369 wave bridge: preserve signed comb beat and full wave state

**Date:** 2026-10-28. **Status:** source-written Agda module and regression tests on the draft R2P2 PR branch; GitHub file readback available. **No Agda kernel execution, CI run, laboratory phase/clock measurement or empirically calibrated network result is asserted.**

## Source priority and provenance

- **User-supplied video (secondary)**: Veritasium, *No device could prove Einstein wrong... until now*, 2026-10-23, https://www.youtube.com/watch?v=eyZEqSPeMwg. It motivates comparing the mountaintop and Boulder ytterbium clocks; its narrated expected shift and comb figures are not authoritative raw time-series data.
- **R2P2 primary experiment**: Triano et al., APS DAMOP 2026, https://meetings-archive.aps.org/damop/2026/g07/7/ . Its abstract reports two Yb lattice clocks and ~69 km atmospheric / ~81 km fibre link; it does not supply a fully calibrated and independently replayed Einstein-deviation result here.
- **Original optical time/frequency transfer prior art**: Caldwell, Triano and Sinclair, *High-precision optical time and frequency transfer*, *Advances in Optics and Photonics* 17, 375–440 (2025), DOI https://doi.org/10.1364/AOP.545290. Time and frequency transfer, frequency-comb phase/timing and technical noise are separate. Authors retain scientific ownership.
- **NIST engineering primary context**: NIST, *Optical Two-way Time-frequency Transfer*, https://www.nist.gov/programs-projects/optical-two-way-time-frequency-transfer ; Sinclair, Caldwell, Deschenes, Bergeron, Swann and Newbury (2023), *Impact of Strong Atmospheric Turbulence on Two-Way Optical Time Transfer*, https://www.nist.gov/publications/impact-strong-atmospheric-turbulence-two-way-optical-time-transfer. Ideal two-way reciprocity is not an automatic identity for moving or turbulent paths; calibrated nonreciprocity matters.
- **Wave formalism background**: Ingrid Daubechies, *Ten Lectures on Wavelets*, SIAM, 1992, DOI https://doi.org/10.1137/1.9781611970104. This is historical wavelet/multiresolution mathematics, not experimental R2P2 optical physics.
- **Current assessment**: Krelina, Tefek, Seskir, Durak, *Quantum protocols for time synchronisation and distribution: a critical assessment*, *EPJ Quantum Technology*, published 2026-10-26, https://link.springer.com/article/10.1140/epjqt/s40507-026-00576-x . It compares quantum clock synchronisation with classical optical transfer and does not endorse treating finite 369 phase tags as physical quantum timing resources.

**DASHI original owners preserved:**

1. `DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact` — `SymbolicCoding`, `encode`, `decodeAfterEncode`: full carrier value survives as exact fibre; trit is an observer.
2. `DASHI.Foundations.Base369SymmetryWaveRound9Validation` — previously verified source-written `symbolicCodingRetainsExactCarrier`.
3. `DASHI.Core.IndexedRelationalHyperfabricSpineExact` and `DASHI.Core.IntersectionalNonFactorability` — original generic collision/nonfactorability and recharting impossibility. Ownership is retained, including this module's separate original attribution to Kimberlé Crenshaw as a *conceptual* root, not the author of the DASHI theorem.
4. `DASHI.Core.IndexedRelationalPadicWaveContinuousAdaptersExact` — pre-existing wave fully-encoded sufficiency and finite `ShiftWaveRefinementSeam` projection theorem.
5. `DASHI.Physics.Base369PhaseBridge` and `DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact` — original 3/6/9 phase quotient rotation laws, a documented obstructed nonary block projection, and separation of local operator symmetry from propagated/role-dependent symmetry.
6. `DASHI.Physics.WaveAlgorithmLift` — original finite sign/phase involution; the generic reversible, norm-preserving and interference obligations remain separately stated, not discharged by this adapter.
7. `DASHI.Physics.Closure.Base369PolyphaseKernelBoundary` and `DASHI.Foundations.Base369PolyphaseCharacters` — source-written finite C3 exponent/additivity, no complex optical phase calibration.
8. `DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw` — source-written dimensionless phase and redshift observable surfaces, no numeric acquisition.
9. `DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact` — previously constructed synthetic comb teeth with `f_CEO` and a signed beat, primary/secondary source distinction.
10. `DASHI.Physics.Closure.R2P2369AtomicQuantumDiamondArchitectureExact` — experiment-level composition. This work does not edit ESD surfaces or import unmerged PR #1117/#1292.

Prior Ibrahim Monster 3B ownership remains separate. No character coincidence, matching 369 label, synthetic wave receipt, or refinement diamond is a proof of shared Monster, Hilbert-space, electromagnetic, atomic or spacetime representation.

## Max-cut: a sign-erasure counterexample

An optical frequency comb tooth obeys

```text
nu_n = n * f_rep + f_CEO
nu_optical = nu_n +/- abs(f_beat)
```

The previously defined **synthetic** R2P2 witness has `n=3`, `f_rep=10 Hz`, `f_CEO=2 Hz`, `abs(f_beat)=4 Hz`. It yields tooth `32 Hz` and two distinct possible optical carriers `36 Hz` / `28 Hz`.

Define `BeatBranch = aboveTooth | belowTooth`. The coarse signed-agnostic 369 trit observer `absoluteBeatOrientation` deliberately maps **both** branches to `sspZero`; it records *only* that the unsigned quantity was selected. The full observable `branchOpticalHz` maps those branches to **36** and **28**.

The new Agda module `DASHI/Physics/Closure/R2P2369WaveOpticalCombInformationCutExact.agda` now proves:

- `sameAbsoluteBeatOrientation` — both branches are indistinguishable at this coarse trit.
- `differentSignedOpticalHz` — optical Hz remains different.
- `beatSignInformationCollision` — **reuse** original `NonFactorabilityWitness`, not reimplement it.
- `absoluteBeatTritCannotRecoverOpticalHz` — no decoder from that trit alone can recover optical Hz.
- `renamingTritCannotRestoreBeatSign` — **any** post-processing chart of the erased trit remains insufficient. This uses the original generic rechart theorem, not a new arithmetic result.
- `signedBeatEncodeDecode` and `fullBeatWaveFibreDeterminesOpticalHz` — the **existing** exact-wave `encode` retains the full branch in its fibre; it is an adequate *mathematical* observation.
- `waveEncodedStateIsSufficient` and `shiftFiniteWaveFineProjectsToCoarse` — existing generic adequacy and wave refinement seam explicitly connected.
- `finiteWaveAlgorithmTritInvolution` and `finiteC3OneStepIsAdditive` — the older wave algorithm and C3 character proofs are imported, not duplicated.
- `clockPhaseIsDimensionless` and `redshiftIsDimensionless` — inherited SI dimension semantics.
- `sixPhaseCoarseRotationLaw`, `ninePhaseCoarseRotationLaw` and `nonaryBlockCoarsePhaseRotationObstruction` — direct reuse of the earlier 369 physical phase bridge. Not every coarse nonary quotient respects the selected cyclic phase rotation.
- `sourceLocalSwapIsEquivariant` and `sourcePropagatedSwapCanFail` — direct reuse of original 369 branch-geometry witnesses. A locally symmetric swap does not imply context-dependent propagation symmetry; this supplies a formal caution for proposed two-way optical link cancellation, **not** real link data.

This is a **source-written exact finite information-loss cut**. The use of 3/6/9 is a convenient mathematical example only. It does not generate a physical clock frequency, a preferred optical resonance, or a physical discretisation of wave phase.

## Physical wave model and remaining experimental wall

The mathematical owner gives **symbolic quantisation and exact-state fibre transport**. Its finite integer-pair wave carrier, four-class phase table, generic wave algorithm and C3 phase characters do not automatically produce a Maxwell field, a measured optical phase or the real optical-time-transfer servo. A realistic physical chain needs:

```text
laser/atom Hamiltonian and state preparation
  -> optical transition (measured clock oscillator)
  -> frequency comb (signed beat, mode n, f_rep, f_CEO)
  -> unwrapped bidirectional optical phase and time stamps
  -> phase noise, slips, atmospheric/fibre reciprocal and nonreciprocal transfer
  -> calibrated same-epoch clock ratio and covariance
  -> surveyed geopotential and weak-field GR prediction
  -> source-bound residual and candidate-specific hypothesis test
```

**The strongest justified result** is that a coarse 369 trit is not sufficient to identify a signed optical comb tooth, while the older fibre-encoded wave constructor can preserve it. Any physical `carrier phase` or `gravitation` interpretation remains conditional on a real producer and calibration. Two-way transfer reciprocity is a model assumption tested against real turbulence and moving-platform effects; finite local commutation or equality of two symbolic directions is not evidence that atmospheric phase cancels.

**Pareto / snowball**: preserving the signed beat, clock-to-link phase traces, provenance and full covariance has greater empirical value than another 369/C3/Monster analogy. After pinned Agda and Python execution, the next real wall is a public, hash-pinned R2P2 dataset with the experiment's instrument/sampling/reciprocity/uncertainty conventions. Do not promote a synthetic receipt to experimental evidence.

**Checks requested**, explicitly **not yet executed**:

```sh
python -m unittest discover -s tests -p 'test_r2p2_*.py' -v
nix develop .# --command bash scripts/run_agda29_parallel_check.sh DASHI/Physics/Closure/R2P2369WaveOpticalCombInformationCutExact.agda
nix develop .# --command bash scripts/run_agda29_parallel_check.sh DASHI/Physics/Closure/R2P2369AtomicQuantumDiamondArchitectureExact.agda
```

All three TOE roots import the new wave adapter. Their direct theorem projections are `toeR2P2WaveSignedBeatRetained`, `unifierR2P2WaveSignedBeatRetained`, and `unifiedR2P2WaveSignedBeatRetained`, with matching no-physical-phase-promotion projections. This is new source-level integration, pending kernel confirmation.
