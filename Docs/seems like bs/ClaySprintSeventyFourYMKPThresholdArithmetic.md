# Clay Sprint Seventy Four YM KP Threshold Arithmetic

Sprint 74 packages the arithmetic and plots behind the corrected
transfer-matrix entropy fork.

The executable artifact generator is:

```text
scripts/ym_sprint74_kp_threshold_plots.py
```

It emits:

```text
sprint72_kp_constants.csv
sprint72_kp_summary.json
sprint72_kp_manifest.json
sprint72_residual_leakage_tolerance.png
sprint72_eta_threshold.png
```

## Constants

```text
q = 0.23178189475262734
eta_spatial = 4
eta_generic_4d = 8
4q = 0.9271275790105094
8q = 1.8542551580210187
```

Therefore:

```text
AnisotropicL2WeightedKPArithmeticCloses = true
Generic4DWeightedKPFails = true
```

This is arithmetic only. The `eta = 4` count is admissible for the 4D
transfer-matrix problem only after the Balaban/transfer-matrix compatibility
gate is proved.

## Residual Fallback

If a fraction `r` of the old mixed-plaquette correction remains true leakage,
with:

```text
c = 0.3592814371257485
```

the fallback KP ratio is:

```text
(1 + r c)^2 * 4q
```

The strict threshold is:

```text
r < 0.107316402070709
```

The safe theorem target remains:

```text
r <= 0.10
```

with:

```text
10 percent residual -> 0.994944290301034 < 1
20 percent residual -> 1.065154532578283 > 1
```

## Current Proof Fork

The next live theorem is still:

```agda
BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix :
  AnisotropicBalabanRGSpatialOnly L ->
  BalabanPartitionFunctionIdentity ->
  TemporalTransferMatrixFactorization ->
  TemporalSupportNonCreationForSlabs ->
  CompatibilityHolds
```

The structural pass condition is:

```text
Can spatial-only Balaban blocking preserve the temporal transfer matrix exactly?
```

Sprint 74 does not prove that structural theorem.

## Governance

Sprint 74 records closed arithmetic:

```text
Generic4DWeightedKPFails
AnisotropicL2WeightedKPArithmeticCloses
TenPercentResidualLeakageClosesKP
```

Sprint 74 keeps open:

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
