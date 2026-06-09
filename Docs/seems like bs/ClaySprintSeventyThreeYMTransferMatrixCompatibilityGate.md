# Clay Sprint Seventy Three YM Transfer-Matrix Compatibility Gate

Sprint 73 packages the corrected shortest in-repo path from the Sprint 68
support theorem toward the Yang-Mills Clay endpoint.

It does not claim a Clay proof. It narrows the current bottleneck.

## Current State

Sprint 68 records the geometric input:

```text
SupportNonCreation + KernelLocality(r_K = 1)
  -> TemporalSupportNonCreationForSlabs
```

For `L = 2`, an admissible carrier has temporal range at most `1`, while a
carrier touching both temporal faces would need temporal span at least `2`.
That gives the face-separation certificate used below.

Sprint 70 and Sprint 71 corrected the action bookkeeping:

```text
mixed spatial-temporal plaquettes touching a temporal face
  = transfer-matrix face action
  != residual correction
```

So the active bookkeeping multiplier is:

```text
Lambda_bookkeeping = 1.0
Lambda_bookkeeping * 4q = 0.9271275790105094 < 1
```

The old leakage value `1.7130035863183526` remains only a legacy
correction-bucket diagnostic.

## Packageable Lemmas

Sprint 73 treats the first two requested lemmas as packageable in the current
receipt sense.

```agda
LinkVariableDisjointnessForTemporalFaces :
  KernelLocality r_K ->
  SlabThickness L ->
  r_K < L ->
  forall l -> not (InTopFaceAction l and InBottomFaceAction l)
```

Reason: with `r_K = 1 < L = 2`, any shared link variable would induce support
touching both temporal faces, contradicting `TemporalSupportNonCreationForSlabs`.

```agda
TemporalMeasureFactorizationWithLeakageLambdaOne :
  LinkVariableDisjointnessForTemporalFaces ->
  ProductHaarMeasure ->
  CorrectedTemporalFaceBookkeeping ->
  Lambda = 1.0
```

Reason: once the top, spatial, and bottom action variables are disjoint and the
link measure is a product Haar measure, Fubini/product-measure factorization
gives exact factorization at the slab bookkeeping level.

This is still a packaged local gate, not a completed constructive
Yang-Mills measure.

## Key Open Lemma

The shortest path now hinges on:

```agda
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix :
  TemporalSupportNonCreationForSlabs ->
  KernelLocality r_K ->
  r_K < L ->
  BalabanSmallFieldBoundsAtScaleK ->
  BalabanLargeFieldSuppression ->
  SpatialOnlyBlockingAtEachStep ->
  forall k ->
    TransferMatrixWellDefinedAtScaleK k
    and PartitionFunctionIdentityHolds k
    and TemporalStructurePreservedAtScaleK k
```

The intended proof shape is:

```text
1. spatial-only blocking coarsens only spatial links;
2. temporal links remain on the original time lattice at every RG scale;
3. temporal support non-creation forbids large-field cross-slab polymers;
4. the transfer-matrix trace has no temporal volume mismatch;
5. Balaban partition identity and temporal transfer matrix are compatible.
```

This is the active Sprint 73 proof fork.

## Shortest Path To Clay

The current in-repo path is:

```text
TemporalSupportNonCreationForSlabs
-> LinkVariableDisjointnessForTemporalFaces
-> TemporalMeasureFactorizationWithLeakageLambdaOne
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

Everything from `BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix`
downstream remains open in this receipt.

## External SOTA Watch

The arXiv SU(3) mass-gap claim `2506.00284v2` is not live competitive evidence:
arXiv marks it withdrawn by administration for not meeting research-content
quality standards.

The useful external input is the Eriksson large-field / Balaban-interface
paper. Its slow-field identification and interface lemma are relevant to the
Sprint 73 gate because they identify the conditional large-field suppression
that a transfer-matrix-compatible spatial Balaban step would need. In this
repo, those results are treated as external assumptions/source obligations, not
as imported proofs.

Clay still lists Yang-Mills and the mass gap among the unsolved Millennium
problems.

Tracking URLs:

```text
https://arxiv.org/abs/2506.00284v2
https://www.ai.vixra.org/pdf/2602.0056v1.pdf
https://www.claymath.org/millennium/yang-mills-the-maths-gap/
```

## Governance

Sprint 73 promotes:

```text
LinkVariableDisjointnessForTemporalFaces = packaged from Sprint 68 geometry
TemporalMeasureFactorizationWithLeakageLambdaOne = packaged from disjointness,
  product Haar measure, and corrected bookkeeping
```

Sprint 73 does not promote:

```text
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
TemporalQuotientEntropyHalvingL2
AllDiameterWeightedKP
SmallFieldBoundsSurviveAnisotropicBlocking
LatticeMassGapFromAnisotropicKP
ContinuumMassGapTransfer
OSWightmanReconstruction
Clay/YM
```
