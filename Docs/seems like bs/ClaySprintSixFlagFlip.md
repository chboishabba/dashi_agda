# Clay Sprint 6 Flag-Flip Targets

This document is the reader-facing companion to:

```text
DASHI/Physics/Closure/ClaySprintSixFlagFlipReceipt.agda
```

Sprint 6 changes the live priority order.  It consumes the existing Gate3
frame-carrier, NS commutator-equivalence, and YM Balaban-continuum receipts.
It does not prove any hard bridge and does not promote Gate3, Yang-Mills,
Navier-Stokes, or Clay.

Correction note: this receipt is now superseded for the live Gate3 blocker by
`Docs/Gate3SpectralTransferOrPruning.md` and
`DASHI/Physics/Closure/Gate3SpectralTransferOrPruningReceipt.agda`.  The
carrier-side frame evidence is not enough once the SSP map enters the
continuum Hilbert space; the live Gate3 support lemma is
`SSPIsometricEmbeddingOrSpectralTransfer`, likely through weighted or pruned
spectral transfer.

## Corrected Priority

```text
1. Gate3 flag first:
   MirrorBNonDegenerate2D
   -> SSPFrameCarrierEqualsOKTensorZ3
   -> FrameSpreadTransfer
   -> PhysicalSSPSpreadBound
   -> UniformFrameLowerBound
   -> Gate3MoscoNoPollutionTransfer
   -> gate3Closed = true

2. Navier-Stokes Clay flag second:
   TransportTermEnergyCancellation
   -> HighLowEqualsCommutator
   -> CommutatorLipschitzEquivalentToPointwiseEnstrophy
   -> PointwiseEnstrophyControl
   -> NoFiniteTimeBlowup
   -> GlobalSmoothSolution
   -> clayNavierStokesPromoted = true

3. Yang-Mills Clay flag third:
   YMBalabanContinuumLimit
   -> HyperbolicShimuraToEuclideanUniversality
   -> SelfAdjointYangMillsHamiltonian
   -> MassGapSurvivesContinuumLimit
   -> OSWightmanReconstruction
   -> Nontrivial4DSU3YangMills
   -> clayYangMillsPromoted = true
```

## Gate3 Worker Lanes

Gate3 is the nearest flag flip.  Sprint 5 split the old carrier theorem:

```text
SSPFrameCarrierEqualsOKTensorZ3       -- needed for Gate3 frame/taper
SSPDepthCarrierEqualsEichlerOrder07   -- depth/YM side
```

The immediate missing field is:

```text
MirrorBNonDegenerate2D
```

The model-side values are already recorded:

```text
five of six frame fields constructed = true
sigma_frame = 0.145230
S_3D(sigma_frame) = 0.000017
```

Workers:

```text
W1:
  prove or refute MirrorBNonDegenerate2D.

W2:
  consume W1 into SSPFrameCarrierEqualsOKTensorZ3,
  PhysicalSSPSpreadBound, UniformFrameLowerBound,
  and Gate3MoscoNoPollutionTransfer.
```

## Navier-Stokes Worker Lanes

The HighLow route is now known to be Clay-equivalent, not a shortcut.

Already supported:

```text
TransportTermEnergyCancellation
HighLowEqualsCommutator
K^(-1/2) estimate retracted
```

Flag-critical theorem:

```text
PointwiseEnstrophyControl
```

Equivalently:

```text
CommutatorLipschitzControlWithoutRegularity
```

Workers:

```text
W3:
  attempt PointwiseEnstrophyControl / commutator Lipschitz control.

W4:
  audit hidden regularity input and counterfamilies; any proof that imports
  Serrin, BKM, global H118, or low-mode L-infinity is circular.
```

## Yang-Mills Worker Lanes

Sprint 6 replaces the finite 43-step induction as a proof target:

```text
43 steps = one-loop diagnostic only
```

The live theorem is:

```text
YMBalabanContinuumLimit
```

Meaning:

```text
for every sufficiently small initial cutoff a0,
find k(a0) where beta_eff crosses the strict seed and
rho_k < 1 with leakage uniformly controlled as a0 -> 0.
```

Workers:

```text
W5:
  formulate and attempt continuum-uniform Balaban transfer.

W6:
  guard the downstream constructive QFT chain:
  Shimura-flat, self-adjoint Hamiltonian, continuum mass-gap survival,
  OS/Wightman reconstruction, and nontrivial SU3.
```

## Boundary

Sprint 6 assigns the only targets that can flip flags:

```text
Gate3:
  MirrorBNonDegenerate2D + SSPFrameCarrierEqualsOKTensorZ3

NS:
  PointwiseEnstrophyControl / CommutatorLipschitzControlWithoutRegularity

YM:
  YMBalabanContinuumLimit
```

All three remain open in this receipt.  Numeric, model-side, finite-step, and
diagnostic receipts do not promote Clay.
