# Physical SSP Spread Bound Attempt

This is the concrete Gate3 worker receipt for the first bounded non-Clay
support target.  The BT-metric model is closed; the physical 3D
SSP/Hecke embedding identification remains open.

## Consumed In-Repo Support

```text
Gate3NestingTaperConditionReceipt:
  p-adic Kozyrev Gram is identity
  Archimedean digit image has nested supports
  digit sigma = 0.288675
  p=3 3D taper target = 0.302511
  digit model passes with headroom
  SSP/Hecke physical taper remains open

Gate3NoSpectralPollutionConditionalProofReceipt:
  finite cutoff lower bound is recorded
  uniform infinite lower bound is blocked
  Mosco/no-pollution chain is conditional
```

## Computed Values

```text
S_1D(p=3, sigma=0.289) = 0.08094058909036041

S_3D(p=3, sigma_digit=0.2886751345948129)
  = 0.7228939450291813

S_3D(p=3, sigma_crit=0.3025113508228815)
  = 0.999999999999999
```

The BT-metric Gram itself has zero off-diagonal cross-term:

```text
A_infty = 1
mu_N = 0
```

This proves the BT-metric model frame lower bound.  It does not prove that
the physical 3D Archimedean SSP/Hecke image is the BT-metric model.

## Concrete Sublemmas

```text
1. BTMetricGramIdentity
2. BTMetricUniformFrameLowerBound
3. OneDPAWOTGResidualSeriesComputed
4. ThreeDPAWOTGDigitSeriesComputed
5. PhysicalSSPEmbedding3D
6. HeckeToArchimedeanCoordinateMap
7. SpreadFunctionalMatchesDigitModel
8. SigmaPhysicalSSPComputed
9. SigmaPhysicalSSPLt0302511
10. UniformInDepthSpreadControl
```

## First Missing Step

```text
Actual3DHeckeEmbeddingMap
```

The digit model already passes.  The missing work is proving that the actual
physical SSP/Hecke Archimedean image has the same spread control, uniformly in
depth.

No Gate3, Clay, W4, gravity, or terminal promotion follows from this BT-model
closure.
