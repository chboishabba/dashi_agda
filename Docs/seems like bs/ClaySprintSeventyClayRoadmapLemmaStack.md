# Clay Sprint Seventy Roadmap Lemma Stack

Sprint 70 consolidates the current proof state across YM and NS.  It records
what the archive owns, what remains open, and which Clay prize is the shortest
in-repo target.

Sprint 79 override: after the 2602.0077 correction, the historical Sprint 70
stack below is superseded by two live lanes. The UV-continuum lane is:

```text
BalabanCMP98LocalOscillationBoundForQhp
  ↓
LipschitzToSquaredOscillationForQhp
  ↓
AnisotropicAssumptionA
  ↓
SquaredOscillationSummabilityForHalfPlaneBlocking
  ↓
FixedFiniteVolumeBlockedObservableContinuumLimit
```

This is the blocking-map Assumption A lane from Eriksson 2602.0077 in
half-plane/spatial DASHI form. It does not prove OS reflection positivity,
thermodynamic limit, mass gap, or Clay/YM.

Sprint 80 records the conditional arithmetic
`3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)<=3*C_local^2`, but the first two
UV sublemmas above remain false/open theorem objects.

Sprint 81 attempts the first UV sublemma and keeps it fail-closed. The repo has
W1 spatial-only blocking preservation at receipt level and has the arithmetic
shell, but it does not yet define/import:

```text
FormalOscillationSeminormForGaugeLinks
FormalQhpBlockingMapDefinition
BalabanCMP98AveragingLocalityImported
QhpPerLinkInfluenceConeLMinus2k
```

So the exact next theorem is still `BalabanCMP98LocalOscillationBoundForQhp`,
preceded by those formal-definition/import obligations.

The KP/mass-gap lane remains the residual effective-action support graph:

```text
EffectiveActionPolymersSpatialOnlyForA1
  ↓
PolymerDefinedOnBlockedLattice
  ↓
KPEntropyAtBlockedScaleL2
  ↓
TemporalEntropyQuotientHalvesGeneric4DCount
  ↓
AllDiameterWeightedKP
```

The current fork is arithmetic-sensitive:

```text
4q = 0.9271275790105094 < 1   blocked L=2 eta=4, conditional
6q = 1.390691368515764  > 1   fine-lattice spatial eta=6, blocked
8q = 1.8542551580210187 > 1   generic 4D eta=8, blocked
```

So `eta=4` has proof value only after the blocked-lattice orientation theorem
is earned. Current route decision remains `ANISOTROPIC_KP_ROUTE_BLOCKED`.

## Archive-Owned Algebra

The current structural stack is:

```text
TritInvolution
SupportNonCreation
No2Cycle
AggregateDefect contractivity
AdmissibilityEquivalence
UltrametricContraction
IdempotentKernels
TemporalSupportNonCreationForSlabs
```

The new in-repo contribution remains Sprint 68:

```text
SupportNonCreation + KernelLocality(r_K=1)
  =>
TemporalSupportNonCreationForSlabs
```

This says no admissible range-1 polymer spans both temporal faces of an
`L >= 2` slab.  It does not prove the anisotropic Balaban partition identity.

## YM Lemma Stack

The YM chain is the shortest current in-repo Clay-facing route:

```text
TemporalSupportNonCreationForSlabs
  ↓ closed
TemporalFacesDisjointForAdmissiblePolymers
  ↓ P0a
NoTemporalCrossCoupling
  ↓ P0b
ProductCutoffFactorizationWithLeakage
  ↓ P0c
WilsonActionSlabDecomposition
  ↓ P0d
MixedPlaquettesAreTransferMatrixNotCorrection
  ↓ P0d'
LinkVariableDisjointnessForTemporalFaces
  ↓ P0e
TemporalMeasureFactorizationWithLeakage
  ↓ P0f
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
  ↓ P0g
AnisotropicBalabanPartitionIdentity
  ↓ P0h
TemporalQuotientEntropyHalvingL2
  ↓ P1
AnisotropicL2WeightedKPCloses
  ↓ P2
AllDiameterWeightedKP
  ↓ P3
SmallFieldBoundsSurviveAnisotropicBlocking
  ↓ P4
TemporalTransferMatrixCompatibleWithSpatialBlocking
  ↓ P5
LatticeMassGapFromAnisotropicKP
  ↓ P6
ContinuumMassGapTransfer
  ↓ P7
OSWightmanReconstruction
  ↓ P8
MassGapSurvival
  ↓ P9
clayYangMillsPromoted
```

Historical Sprint 70/73 P0 wording: the load-bearing P0 gap was then
`BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix`, after corrected
Wilson-action bookkeeping and still-open temporal measure factorization.
Mixed spatial-temporal plaquettes touching a temporal face are transfer-matrix
face action, not residual correction. The remaining question is whether the
spatial-only Balaban partition identity is compatible with temporal
transfer-matrix factorization once Sprint 68 support non-creation forbids
cross-cut large-field polymers. Sprint 79 moves the immediate live hinge
upstream to the residual effective-action support graph and blocked-lattice KP
entropy theorem.

The arithmetic is pinned:

```text
q = 0.23178189475262734
generic eta = 8
8q = 1.8542551580210187 > 1

anisotropic eta_eff = 4
4q = 0.92712758 < 1

max leakage factor = 1.078600208471055
corrected bookkeeping lambda = 1.0
lambda * 4q = 0.9271275790105094
legacy correction-bucket leakage * 4q = 1.7130035863183526
```

The `eta_eff=4` line has no proof value until the anisotropic partition
identity, temporal measure factorization, Balaban/transfer-matrix
compatibility, and entropy transfer are proved.

## NS Lemma Stack

NS remains a live CKN route, but it is further from Clay because the remaining
gates are continuum PDE bridges:

```text
DASHIToIncompressibleNS
  ↓
CKNDiagnosticPromotedToTheorem
  ↓
SuitableWeakSolutionBridge
  ↓
RieszPressureControl
  ↓
UniformCKNEpsilonBound
  ↓
ContinuumRefinementStability
  ↓
CKNRegularity
  ↓
NoFiniteTimeBlowup
  ↓
clayNavierStokesPromoted
```

The CKN diagnostics are favorable, but diagnostic:

```text
Sprint 67B sampled hotspots/cylinders decay under zoom
no CKN epsilon theorem follows
no suitable weak solution theorem follows
no no-blowup theorem follows
```

`UniformCKNEpsilonBound` is essentially the hard NS Clay theorem.

## Prize Choice

The right current target is YM.

YM has one named P0 construction where the DASHI archive directly contributes:
turn temporal support non-creation into an anisotropic Balaban partition
identity.

NS is still valuable as a diagnostic and proof-bridge lane, but its remaining
obligations are broader continuum PDE theorems that the carrier archive does
not close directly.

## Governance

Sprint 70 promotes neither prize.  It records the roadmap and keeps the
following gates false:

```text
AnisotropicBalabanPartitionIdentity
LinkVariableDisjointnessForTemporalFaces
TemporalMeasureFactorizationWithLeakage
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
TemporalFaceFactorizationFromSupportNonCreation
TemporalQuotientEntropyHalvingL2
AnisotropicL2WeightedKPCloses
AllDiameterWeightedKP
SmallFieldBoundsSurviveAnisotropicBlocking
TemporalTransferMatrixCompatibleWithSpatialBlocking
LatticeMassGapFromAnisotropicKP
ContinuumMassGapTransfer
OSWightmanReconstruction
MassGapSurvival
DASHIToIncompressibleNS
CKNDiagnosticPromotedToTheorem
SuitableWeakSolutionBridge
RieszPressureControl
UniformCKNEpsilonBound
ContinuumRefinementStability
CKNRegularity
NoFiniteTimeBlowup
Clay/YM promotion
Clay/NS promotion
```
