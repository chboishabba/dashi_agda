# Clay Sprint Seventy Five YM Temporal Entropy Quotient

Sprint 75 records the current shortest Yang-Mills proof fork in proof-safe
language.

The point is not dimensional reduction. The point is role separation:

```text
[3,1] = 3 spatial entropy directions + 1 temporal transfer direction
```

The four-dimensional theory remains four-dimensional. The temporal direction
is carried by the ordered transfer trace:

```text
Z = Tr(T ^ L_t)
```

It should not also be counted as a polymer-branching entropy direction after a
spatial-only Balaban RG step.

## Arithmetic Boundary

Sprint 74 pinned the constants:

```text
q = 0.23178189475262734
generic 4D eta = 8
spatial-transfer eta = 4

8q = 1.8542551580210187 > 1
4q = 0.9271275790105094 < 1
```

So the proof target is no longer "make q smaller." It is:

```text
justify eta = 4 structurally for the 4D transfer-matrix construction.
```

## Exact Sprint 75 Lemmas

The transfer-structure interface inputs now packaged by the receipt are:

```text
SpatialRGLeavesTimeAxisInvariant
TransferTracePreservedBySpatialRG
TemporalBoundaryPairingFromReflectionPositivity
PlanckScaleTemporalLocalityGuard
```

These are receipt-level interface closures: they record the standard lattice
transfer-matrix structure and the existing DASHI locality guard. They are not a
continuum Yang-Mills proof.

The safe downstream lemma stack is:

```text
SpatialRGLeavesTimeAxisInvariant
TransferTracePreservedBySpatialRG
TemporalBoundaryPairing
PlanckScaleTemporalLocality
TemporalSupportNonCreationForSlabs
TemporalEntropyQuotientHalvesGeneric4DCount
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
```

The quotient theorem is:

```agda
TemporalEntropyQuotientHalvesGeneric4DCount :
  SpatialRGLeavesTimeAxisInvariant ->
  TransferMatrixOrdersTemporalDirection ->
  TemporalBoundaryPairing ->
  PlanckScaleTemporalLocality ->
  TemporalSupportNonCreationForSlabs ->
  etaGeneric4D == 8 ->
  etaSpatialTransfer == 4
```

Plain reading:

```text
spatial directions branch;
time orders;
Sprint 68 locality prevents temporal polymers from re-entering the entropy count.
```

## Sprint 78 Absorption Pin

The spacetime large-field absorption floor is first available at `k_start=9`:

```text
p0(k=8) = 3.057 < floor = 3.079
p0(k=9) = 3.124 > floor = 3.079
```

The finite prefix `k=0..8` remains a live initial-condition gap unless
`NcAbsorptionFloorAuthority` is sourced from primary Balaban SU(N) authority or
a separate finite-scale argument is supplied. This does not close the quotient
theorem; it moves the live blocker to the effective-action support statement:

```text
EffectiveActionPolymersSpatialOnly
KPEntropyFromL2BlockingOrientations
TemporalEntropyQuotientHalvesGeneric4DCount
```

So the next theorem is not another absorption-floor calculation. It is proving
that, after the first spatial RG step, the residual effective-action polymer
graph has spatial support only.

## Current Roadmap

```text
TemporalSupportNonCreationForSlabs
-> LinkVariableDisjointnessForTemporalFaces
-> TemporalMeasureFactorizationWithLeakageLambdaOne
-> EffectiveActionPolymersSpatialOnly for k >= k_start, with k_start = 9
-> KPEntropyFromL2BlockingOrientations
-> ThreeOneTemporalEntropyQuotient
-> BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
-> TemporalQuotientEntropyHalvingL2
-> AnisotropicL2WeightedKPCloses
-> AllDiameterWeightedKP
-> SmallFieldBoundsSurviveAnisotropicBlocking
-> LatticeMassGapFromAnisotropicKP
-> ContinuumMassGapTransfer
-> OSWightmanReconstruction
-> MassGapSurvival
```

## Why YM First

The YM lane has a narrow structural hinge:

```text
Can spatial-only Balaban RG preserve the temporal transfer trace while using
the 3D spatial entropy count?
```

The NS lane remains useful, but its remaining gates are broader PDE bridges:

```text
DASHIToIncompressibleNS
SuitableWeakSolutionBridge
LocalEnergyInequality
RieszPressureControl
UniformCKNEpsilonBound
CKNNoBlowup
```

Those are farther from the carrier/support machinery currently owned by the
archive.

## Governance

Sprint 75 promotes no Clay result. It records:

```text
ThreeOneRoleSeparation = packaged
SpatialRGLeavesTimeAxisInvariant = packaged
TransferTracePreservedBySpatialRG = packaged
TemporalBoundaryPairingFromReflectionPositivity = packaged
PlanckScaleTemporalLocalityGuard = packaged
TemporalEntropyQuotientHalvesGeneric4DCount = open
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix = open
AllDiameterWeightedKP = open
LatticeMassGap = open
ContinuumMassGap = open
OS/Wightman = open
Clay/YM = false
```
