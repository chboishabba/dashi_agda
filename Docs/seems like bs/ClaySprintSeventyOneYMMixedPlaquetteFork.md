# Clay Sprint Seventy One YM Transfer-Matrix Compatibility

Sprint 71 corrects the Sprint 70 bookkeeping fork.

The Sprint 70 audit did not discover a large physical correction term. It
exposed that the previous decomposition was charging mixed spatial-temporal
plaquettes as a residual correction when, in transfer-matrix bookkeeping, they
are part of the temporal face action itself.

## Corrected Bookkeeping

The corrected slab decomposition is:

```text
S_Wilson(B)
  = S_spatial_interior(B)
  + S_top_temporal_face(B)
  + S_bottom_temporal_face(B)
  + S_spatial_boundary(B)
  + S_residual_correction(B)
```

with the convention:

```text
S_top_temporal_face includes mixed spatial-temporal plaquettes touching top
S_bottom_temporal_face includes mixed spatial-temporal plaquettes touching bottom
```

Therefore:

```text
MixedPlaquettesAreTransferMatrixNotCorrection
S_residual_correction(B) = 0
bookkeeping_lambda = 1.0
bookkeeping_lambda * 4q = 0.9271275790105094 < 1
```

The old `35.9%` number remains useful only as a legacy diagnostic for the
wrong correction-bucket convention:

```text
legacy_total_leakage_times_4q = 1.7130035863183526
```

It is not the active proof obstruction under the temporal-face-includes-mixed
convention.

## What Does Not Follow

This is a bookkeeping closure, not a measure-theoretic proof.

Do not promote:

```text
TemporalMeasureFactorizationWithLeakage(lambda = 1)
LeakageControlledWeightedKPCloses
AnisotropicBalabanPartitionIdentity
TemporalTransferMatrixCompatibleWithSpatialBlocking
LatticeMassGapFromAnisotropicKP
Clay/YM
```

The missing analytic step is still to show that the corrected action
bookkeeping is compatible with the functional integral, the gauge-covariant
cutoffs, and Balaban's spatial-only RG identity.

## Sprint 71 Target

The next real lemma is:

```agda
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix :
  AnisotropicBalabanRGSpatialOnly L ->
  BalabanPartitionFunctionIdentity ->
  TemporalTransferMatrixFactorization ->
  TemporalSupportNonCreationForSlabs ->
  CompatibilityHolds
```

Argument sketch:

```text
1. Spatial-only Balaban blocking preserves the partition function.
2. The temporal lattice is not coarsened, so the transfer matrix remains
   defined on the original temporal ordering.
3. TemporalSupportNonCreationForSlabs forbids admissible large-field polymers
   spanning the temporal cut.
4. Mixed spatial-temporal face plaquettes are transfer-matrix terms, not
   residual correction terms.
5. Therefore the obstruction to compatibility is reduced to formal
   link-variable disjointness/cutoff factorization, not leakage arithmetic.
```

## Lemma Stack From Here

```text
1. TemporalFacesDisjointForAdmissiblePolymers
2. NoTemporalCrossCoupling
3. WilsonActionSlabDecomposition
4. MixedPlaquettesAreTransferMatrixNotCorrection
5. LinkVariableDisjointnessForTemporalFaces
6. TemporalMeasureFactorizationWithLeakage(lambda = 1)
7. BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
8. AnisotropicBalabanPartitionIdentity
9. TemporalQuotientEntropyHalvingL2
10. AnisotropicL2WeightedKPCloses
11. AllDiameterWeightedKP
12. SmallFieldBoundsSurviveAnisotropicBlocking
13. LatticeMassGapFromAnisotropicKP
14. ContinuumMassGapTransfer
15. OSWightmanReconstruction
16. MassGapSurvival
```

## Governance

Sprint 71 promotes nothing. It records:

```text
MixedPlaquettesAreTransferMatrixNotCorrection = closed by bookkeeping convention
S_residual_correction = 0 by corrected decomposition
TemporalMeasureFactorizationWithLeakage(lambda = 1) = open
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix = open
Clay/YM promotion = false
```
