# Clay Promotion Flag-Flip Lemmas

This document is the reader-facing companion to:

```text
DASHI/Physics/Closure/ClayPromotionFlagFlipLemmaReceipt.agda
```

It filters the Sprint 3 shortest-path plan down to theorem targets that can
actually flip a promotion flag.  Everything numeric, model-side, finite, or
empirical remains support only.

Sprint 6 supersedes the live priority order in this document.  See:

```text
Docs/ClaySprintSixFlagFlip.md
DASHI/Physics/Closure/ClaySprintSixFlagFlipReceipt.agda
```

The main Sprint 6 corrections are: Gate3 only needs the frame-side
`MirrorBNonDegenerate2D` / `SSPFrameCarrierEqualsOKTensorZ3` path; NS
commutator control is Clay-equivalent; and YM uses
`YMBalabanContinuumLimit`, not finite 43-step induction, as the live flag
target.

## Priority Order

```text
1. Gate3:
   SSPFrameCarrierEqualsOKTensorZ3
   -> UniformFrameLowerBound
   -> Gate3MoscoNoPollutionTransfer
   -> gate3Closed = true

2. Navier-Stokes:
   CommutatorLipschitzControlWithoutRegularity
   -> CumulativeTailDissipationDominance
   -> KStarNoDrift
   -> H118Continuation
   -> clayNavierStokesPromoted = true

3. Yang-Mills:
   YMFortyThreeStepBalabanUniformity
   -> beta_eff >= 13.7
   -> Shimura-to-flat
   -> OS/Wightman
   -> mass gap survival
   -> nontrivial SU3
   -> clayYangMillsPromoted = true
```

## Six Workers

```text
W1 Gate3:
  SSPFrameCarrierEqualsOKTensorZ3

W2 Gate3:
  UniformFrameLowerBound + Gate3MoscoNoPollutionTransfer,
  conditional on W1

W3 NS:
  CommutatorLipschitzControlWithoutRegularity

W4 NS:
  equivalence/counterfamily audit for the commutator obstruction

W5 YM:
  YMFortyThreeStepBalabanUniformity + leakage summability

W6 YM/Governance:
  Shimura-flat, OS/Wightman, mass-gap, nontriviality dependency guardrails;
  no numeric/model receipt may promote Clay
```

## Gate3 Flag

Sprint 4 splits the carrier theorem:

```text
SSPFrameCarrierEqualsOKTensorZ3
SSPDepthCarrierEqualsEichlerOrder07
```

The frame/taper flag path needs the first theorem:

```text
SSPFrameCarrierEqualsOKTensorZ3
  -> PhysicalSSPSpreadBound
  -> UniformFrameLowerBound
  -> Gate3MoscoNoPollutionTransfer
```

The depth/Eichler theorem is relevant to YM/depth transport, not the immediate
Gate3 frame/taper flag.

## Navier-Stokes Flag

Already supported:

```text
TransportTermEnergyCancellation
HighLowReducesToCommutator
K^(-1/2) claim retracted
```

Flag-critical target:

```text
CommutatorLipschitzControlWithoutRegularity
```

Warning:

```text
This is not a shortcut around Clay NS.  It is the Clay regularity obstruction
in commutator form.
```

## Yang-Mills Flag

Already supported:

```text
beta_eff*c_min_BT - a_BT > log(2p)
robust sample beta_eff >= 13.7
finite target (k : Fin 43) -> rho k < 1
```

Flag-critical chain:

```text
YMFortyThreeStepBalabanUniformity
YMFortyThreeStepLeakageSummability
NonperturbativeBalabanScaleTransfer
HyperbolicShimuraToEuclideanUniversality
SelfAdjointYangMillsHamiltonian
MassGapSurvivesContinuumLimit
OSWightmanReconstruction
Nontrivial4DSU3YangMills
```

## Boundary

This receipt prioritises only theorem targets that can flip promotion flags.
It does not prove `SSPFrameCarrierEqualsOKTensorZ3`,
`CommutatorLipschitzControlWithoutRegularity`, Balaban uniformity, Gate3,
Yang-Mills, Navier-Stokes, or Clay.  All promotion flags remain false.
