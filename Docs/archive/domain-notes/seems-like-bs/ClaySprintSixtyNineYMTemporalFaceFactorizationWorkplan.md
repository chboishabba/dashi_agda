# Clay Sprint Sixty Nine YM Temporal-Face Factorization Workplan

Sprint 69 turns the Sprint 68 support result into the next proof-facing work
surface.

## Closed Input

Sprint 68 closed the support-range node:

```text
SupportNonCreation + KernelLocality(r_K = 1)
  =>
TemporalSupportNonCreationForSlabs
```

For every `L >= 2`, an admissible polymer cannot reach both temporal faces of
one spatial slab.

This is only an input.  It is not yet a functional-integral factorization
theorem.

The reusable closed support package is:

```agda
TemporalFacesDisjointForAdmissiblePolymers :
  forall Gamma B ->
    AdmissiblePolymer Gamma ->
    SpatialSlabBlock B ->
    TouchesTopTemporalFace Gamma B ->
    TouchesBottomTemporalFace Gamma B ->
    Bottom
```

## Six Worker Lanes

1. `supportNonCreationIntegrator`

   Consume Sprint 68 and keep the support non-creation result available as an
   input lemma.

2. `temporalFacePOUBuilder`

   Build the anisotropic Balaban partition of unity on temporal faces and
   spatial slabs.

3. `slabActionAdditivityAuditor`

   Check whether the gauge action decomposes cleanly enough across the slab
   boundary after support separation.

4. `entropyTransferAuditor`

   Transfer the `eta = 4` spatial-slab count into the actual weighted KP
   incompatibility sum.

5. `allDiameterWeightedKPAuditor`

   Lift the one-step entropy arithmetic to all polymer diameters with uniform
   activity and leakage constants.

6. `balabanOSMassGapBoundaryAuditor`

   Keep the downstream Balaban, transfer-matrix, OS/Wightman, and mass-gap
   gates explicit and false until actual bridge theorems exist.

## Next Theorem Target

```text
TemporalFaceFactorizationFromSupportNonCreation
```

Target statement:

```text
Admissibility
+ KernelLocality(r_K = 1)
+ TemporalSupportNonCreationForSlabs
  =>
temporal-face functional integrals factor from spatial-slab integrals
```

This is the next load-bearing YM lemma.  It must construct or cite the
anisotropic partition-of-unity identity.  Support separation alone is not
enough.

More precisely, Sprint 69 must upgrade a combinatorial support fact into an
analytic/measure-theoretic factorization:

```agda
TemporalFaceFactorizationFromSupportNonCreation :
  TemporalSupportNonCreationForSlabs ->
  SpatialOnlySlabBlocking L ->
  GaugeCovariantFaceCutoffs ->
  TemporalFaceIntegralFactors
```

Meaning:

```text
If no admissible polymer can touch both time faces, then top-face and
bottom-face large-field sectors factor independently from the spatial slab
integral.
```

The bridge decomposes into the following open gates:

```agda
NoTemporalCrossCoupling :
  TemporalFacesDisjointForAdmissiblePolymers ->
  not (CoupledBySingleAdmissiblePolymer topFace bottomFace)
```

```agda
ProductCutoffFactorizationWithLeakage :
  NoTemporalCrossCoupling ->
  GaugeCovariantFaceCutoffs ->
  exists cutoffLeakage,
    chiVolume B
      <= cutoffLeakage * chiSpatial B * chiTopTemporal B * chiBottomTemporal B
```

```agda
TemporalMeasureFactorizationWithLeakage :
  ProductCutoffFactorizationWithLeakage ->
  LocalGaugeActionDecomposition ->
  MixedPlaquettesAreTransferMatrixNotCorrection ->
  LinkVariableDisjointnessForTemporalFaces ->
  exists leakageFactor,
    TemporalIntegral B
      <= leakageFactor
       * SpatialIntegral B
       * TopTemporalIntegral B
       * BottomTemporalIntegral B
```

The last measure lemma is the analytic hinge. The corrected bookkeeping closes
the residual mixed-plaquette action term, but it does not by itself prove
functional-integral factorization.  The remaining premises are link-variable
disjointness, cutoff factorization, and compatibility with the temporal
transfer-matrix construction.

## Lemma Ladder

The exact theorem order is:

```text
1. TemporalFacesDisjointForAdmissiblePolymers
2. NoTemporalCrossCoupling
3. ProductCutoffFactorizationWithLeakage
4. LocalGaugeActionDecomposition
5. MixedPlaquettesAreTransferMatrixNotCorrection
6. LinkVariableDisjointnessForTemporalFaces
7. TemporalMeasureFactorizationWithLeakage
8. BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
9. LeakageControlledWeightedKPCloses
10. AllDiameterWeightedKP
11. SmallFieldBoundsSurviveAnisotropicBlocking
12. TemporalTransferMatrixCompatibleWithSpatialBlocking
13. LatticeMassGapFromAnisotropicKP
14. ContinuumMassGapTransfer
15. OSWightmanReconstruction
16. MassGapSurvival
```

The decisive bridge is:

```agda
TemporalQuotientEntropyHalvingL2 :
  AnisotropicBalabanPartitionIdentity ->
  Generic4DEntropy eta4 ->
  eta4 = 8 ->
  TemporalBranchFactor = 2 ->
  EffectiveSpatialEntropy etaEff ->
  etaEff = 4
```

This is what lets the `d=3` spatial-slab row control the four-dimensional
transfer-matrix problem. Without it, the `d=4` spacetime count remains the
active entropy count.

## Conditional KP Arithmetic

The arithmetic remains favorable:

```text
eta = 4
q = 0.23178189475262734
eta*q = 0.9271275790105094 < 1
```

But this arithmetic is usable for weighted KP only after temporal-face
factorization, entropy-count transfer, and the leakage bound are proved.  The
ideal weighted KP series is just the geometric tail with ratio
`eta*q = 0.9271275790105094`; it converges, but without much slack.

## Leakage Budget

The `eta=4` route has limited slack:

```text
eta_spatial * q = 0.9271275790105094
margin = 1 - eta_spatial*q
       = 0.07287242098949065

max allowed leakage factor
  = 1 / (4q)
  = 1.078600208471055

safe formal leakage target
  <= 1.0785
```

So the theorem needed is:

```agda
LeakageControlledWeightedKPCloses :
  TemporalFaceFactorizationWithLeakage ->
  etaEff = 4 ->
  leakageFactor <= 1.0785 ->
  leakageFactor * etaEff * q < 1
```

If the anisotropic partition introduces more than `7.86%` effective
entropy/activity leakage, weighted KP re-blocks.  The safe `1.0785` target is
below the exact threshold, avoiding boundary-equality ambiguity in a formal
receipt.

If leakage is spent independently across three faces, the per-face ceiling is:

```text
(1.078600208471055)^(1/3) - 1
  = 0.025542115281578237
  = 2.5542115281578237%
```

So each face has about `2.55%` multiplicative budget under a three-face
factorization model. The practical theorem target is no more than `2.5%`
leakage per independent face.

```text
(1.025)^3 * 4q = 0.998414998  passes
(1.026)^3 * 4q = 1.001340040  fails
(1.030)^3 * 4q = 1.013097338  fails
```

There is also only:

```text
0.018218105247372662
```

of q-headroom before even the `eta=4` row fails.

## Sprint 70 Plaquette Audit

Sprint 70 adds an executable boundary-correction audit:

```text
scripts/ym_sprint70_boundary_correction_plaquette_audit.py
```

It enumerates unit Wilson plaquettes in an `L=2,d=4` anisotropic slab and
writes:

```text
ym_sprint70_boundary_correction_table.csv
ym_sprint70_boundary_correction_by_category.csv
ym_sprint70_boundary_leakage_summary.json
ym_sprint70_boundary_correction_manifest.json
```

The corrected audit uses explicit transfer-matrix bookkeeping:

```text
temporal-face transfer-matrix action includes mixed spatial-temporal plaquettes
```

The old `mixed_coupling` category is retained only as a legacy diagnostic.

Default corrected `SU(3)`, `beta=16.7`, and `suN-g2` bookkeeping gives:

```text
bookkeeping_lambda = 1.0
residual_correction_action_total = 0.0
max_top_correction_ratio = 0.0
max_bottom_correction_ratio = 0.0
max_spatial_correction_ratio = 0.0
total_leakage_factor = 1.0
total_leakage_times_4q = 0.9271275790105094
route_decision = MIXED_PLAQUETTES_ABSORBED_INTO_TRANSFER_MATRIX
```

No temporal spanning counterexample appears:

```text
touches_both_temporal_faces_count = 0
temporal_faces_disjoint_for_admissible_polymers = true
```

This cleanly separates the closed Sprint 68 support fact and corrected action
bookkeeping from the still-open analytic measure-factorization lemma. The
legacy correction-bucket convention remains recorded for auditability:

```text
legacy_total_leakage_factor = 1.84764602531464
legacy_total_leakage_times_4q = 1.7130035863183526
```

That legacy value is not the active proof obstruction under the
temporal-face-includes-mixed convention.

The boundary is:

```text
L=2,d=3 spatial-slab count:
  eta = 4
  eta*q = 0.9271275790105094 < 1
  KP arithmetic closes

L=2,d=4 spacetime count:
  eta = 8
  eta*q = 1.85425516 > 1
  KP remains blocked
```

So the next theorem is not:

```text
L=2 closes KP.
```

It is:

```text
The 4D transfer-matrix construction legitimately uses the 3D spatial-slab
incompatibility count after temporal factorization.
```

## Open Gates

```text
TemporalFaceFactorization
TemporalFaceFactorizationFromSupportNonCreation
AnisotropicPartitionOfUnity
AnisotropicBalabanPartitionIdentity
TemporalFaceMeasureProduct
ProductCutoffFactorizationWithLeakage
MixedPlaquettesAreTransferMatrixNotCorrection
LinkVariableDisjointnessForTemporalFaces
TemporalMeasureFactorizationWithLeakage
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
LeakageControlledWeightedKPCloses
SlabActionAdditivity
TemporalQuotientEntropyHalvingL2
AnisotropicL2WeightedKPCloses
EntropyCountTransfer
AllDiameterWeightedKP
BalabanSmallFieldSurvival
SmallFieldBoundsSurviveAnisotropicBlocking
TransferMatrixCompatibility
TemporalTransferMatrixCompatibleWithSpatialBlocking
LatticeMassGapFromAnisotropicKP
ContinuumMassGapTransfer
OSWightmanReconstruction
MassGapSurvival
```

## Governance

Sprint 69 does not prove temporal-face factorization, anisotropic partition of
unity, product cutoff factorization with leakage, link-variable disjointness for
temporal faces, temporal measure factorization with leakage,
Balaban/transfer-matrix compatibility, temporal quotient entropy halving,
all-diameter weighted KP, small-field bound survival, lattice mass gap,
continuum mass-gap transfer, OS/Wightman reconstruction, mass gap, or Clay/YM
promotion. Later Sprint 70/71 bookkeeping records the mixed plaquettes as
transfer-matrix face action, but it does not close these analytic gates.
