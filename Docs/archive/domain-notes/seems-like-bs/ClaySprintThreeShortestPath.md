# Clay Sprint Three Shortest Path

This document is the reader-facing companion to:

```text
DASHI/Physics/Closure/ClaySprintThreeShortestPathReceipt.agda
```

It records the shortest current route from the Sprint 3 receipts to Clay
closure, using only already-supported in-repo facts and fail-closed missing
lemma lists.

## Worker Attempts

Six workers remain assigned to concrete best-effort attempts:

```text
W1 Gate3:
  prove or refute SSPCarrierEqualsOKHeckeModel

W2 Gate3:
  consume W1 conditionally into PhysicalSSPSpreadBound,
  UniformFrameLowerBound, and Gate3MoscoNoPollutionTransfer

W3 NS:
  prove or refute CommutatorLipschitzControlWithoutRegularity

W4 NS:
  search for a Leray-energy-bounded counterfamily and audit hidden inputs

W5 YM:
  prove or refute YMFortyThreeStepBalabanUniformity plus leakage summability

W6 Governance:
  keep the K^(-1/2) retraction, exact Balaban margin, O_K/SSP distinction,
  and false promotion flags aligned
```

## Shortest Support Closure

Gate3 is the closest local support stack, but it is not a Clay theorem:

```text
SSPCarrierEqualsOKHeckeModel
  -> PhysicalSSPSpreadBound
  -> UniformFrameLowerBound
  -> Gate3MoscoNoPollutionTransfer
```

Already supported:

```text
O_K model side
sigma_OK = 0.246770
S_3D(sigma_OK) = 0.190298810 < 1
```

First blocker:

```text
SSPCarrierEqualsOKHeckeModel
```

## Shortest NS Clay Route

```text
TransportTermEnergyCancellation
  -> HighLowReducesToCommutator
  -> CommutatorLipschitzControlWithoutRegularity
  -> CumulativeTailDissipationDominance
  -> DangerShellMaximumPrinciple
  -> KStarNoInertialDrift
  -> BernoulliBandGlobalH118Bound
  -> H118ContinuationCriterion
  -> ApproximationStability
  -> ClayNavierStokes
```

Already supported:

```text
TransportTermEnergyCancellation
HighLowReducesToCommutator
K^(-1/2) retraction
```

First blocker:

```text
CommutatorLipschitzControlWithoutRegularity
```

## Shortest YM Clay Route

```text
YMFortyThreeStepBalabanUniformity
  -> YMFortyThreeStepLeakageSummability
  -> YMFortyThreeStepStrictSeedReach
  -> NonperturbativeBalabanScaleTransfer
  -> HyperbolicShimuraToEuclideanUniversality
  -> SelfAdjointYangMillsHamiltonian
  -> MassGapSurvivesContinuumLimit
  -> OSWightmanReconstruction
  -> Nontrivial4DSU3YangMills
  -> ClayYangMills
```

Already supported:

```text
exact strict seed: beta_eff*c_min_BT - a_BT > log(2p)
robust sample: beta_eff >= 13.7
finite target: (k : Fin 43) -> rho k < 1
```

First blocker:

```text
YMFortyThreeStepBalabanUniformity
```

## Net Path

The shortest Clay-critical sequence from here is:

```text
NS first:
  prove CommutatorLipschitzControlWithoutRegularity

YM second:
  prove YMFortyThreeStepBalabanUniformity and leakage summability

Gate3 parallel:
  prove SSPCarrierEqualsOKHeckeModel
```

## Boundary

This receipt assigns concrete best-effort attempts and records the shortest
current path only. It does not prove `SSPCarrierEqualsOKHeckeModel`,
`CommutatorLipschitzControl`, Balaban uniformity, Gate3, Yang-Mills,
Navier-Stokes, or Clay. All promotion flags remain false.
