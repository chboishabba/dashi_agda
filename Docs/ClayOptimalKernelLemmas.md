# Clay Optimal Kernel Lemmas

This is the current shortest honest path from the repo to Clay-facing claims.
It applies the T7A correction first:

```text
T7A direct counting is demoted.
Connected-animal counting is the primary YM KP route.
T7A may re-enter only as per-polymer activity suppression.
```

No item below is a promotion.  Each hard lemma remains a theorem target unless
an existing typed receipt explicitly consumes it.

## Yang-Mills: 12 Kernels

The corrected YM path starts with connected-animal entropy and then asks for a
real non-perturbative Balaban/continuum bridge.

```text
1. ConnectedAnimalKPBound
2. AnalyticContinuumKP
3. CarrierWilsonAreaLaw
4. KPUniformVolumeBalabanInduction
5. UltrametricLargeSmallFieldSplit
6. NonperturbativeBalabanScaleTransfer
7. WilsonContinuumRGTrajectory
8. HyperbolicShimuraToEuclideanUniversality
9. SelfAdjointYangMillsHamiltonian
10. MassGapSurvivesContinuumLimit
11. OSWightmanReconstruction
12. Nontrivial4DSU3YangMills
```

The live numerical ledger has three different YM thresholds and they should
not be conflated:

```text
connected-animal KP sum:
  closed form = q / (1 - p*q)^2, q = exp(-beta*c_min)
  beta* ~= 9.593637
  gap from beta_phys ~= 6: 3.593637

p=7 BT-tree convergence margin:
  beta* ~= 10.13086
  gap from beta_phys ~= 6: 4.13086

stricter p=7 KP activity-absorption margin:
  exact target: beta*c_min-a>log(2p)
  robust numeric target: beta_eff >= 13.7

direct T7A counting:
  beta* ~= 16.56
  gap from beta_phys ~= 6: 10.56
```

So the primary theorem should be stated against the exact strict inequality
`beta*c_min-a>log(2p)` when the stricter KP activity-absorption convention is
required, with `beta_eff >= 13.7` as the robust numerical target.  The
`9.593637` number is the clean connected-animal sum threshold, not a universal
replacement for every Balaban/KP margin.

The formula guard is part of the ledger: the connected-animal sum is
`sum_{d>=1} d*p^(d-1)*q^d = q/(1-p*q)^2`, not `p*q/(1-p*q)^2`.
The corrected closed form matches the direct series and yields the `9.593637`
threshold.

The optional T7A theorem is separate:

```text
T7APerPolymerActivitySuppression:
  |z(Gamma)| <=
    (T7A(d) / (d * p^(d-1))) * exp(-beta*c_min*d)
```

## Navier-Stokes: 13 Kernels

The NS path is fixed-cutoff first, then cumulative absorption, then
continuation and data transfer.

```text
1. FixedKTailFluxIdentity
2. NSFlowProjectionTransport
3. LPCommutatorDefectBound
4. CumulativeTailDissipationDominance
5. TailThetaActuality
6. TailStrictMarginAbsorption
7. DangerShellMaximumPrinciple
8. KStarNoInertialDrift
9. CarrierToStandardH118NormComparison
10. BernoulliBandGlobalH118Bound
11. H118ContinuationCriterion
12. CarrierStructuredDenseInSmoothDivergenceFree
13. ApproximationStability
```

The shortest load-bearing lemma is:

```text
CumulativeTailDissipationDominance
```

It has to dominate nonlinear injection above the danger shell without assuming
Serrin, BKM, global regularity, or the desired `H^{11/8}` estimate.  The
projection/commutator lane is the immediate companion blocker: the carrier
tail computation must shadow the actual NS flow with an absorbable defect.

## Gate3 Support: 5 Kernels

Gate3 is support infrastructure for the DASHI physics stack, not a Clay
Millennium problem by itself.

```text
1. AtomGrammarCMSplittingSeparation
2. PhysicalSSPEmbedding3D
3. PhysicalSSPSpreadBound
4. UniformFrameLowerBound
5. Gate3MoscoNoPollutionTransfer
```

The guard remains:

```text
7+7+1 = semantic atom/frame grammar
5+9+1 = literal Q(sqrt(-7)) splitting table
p71 = split, not inert, in Q(sqrt(-7))
```

The numerical support target is:

```text
sigma_physical_SSP < 0.3025
digit-expansion headroom ~= 0.0138
```

## Six Parallel Workers

```text
W1-YM-Counting-Activity-Area:
  ConnectedAnimalKPBound, T7APerPolymerActivitySuppression, and
  CarrierWilsonAreaLaw.  Own the count/activity distinction and the depth
  1-4 kill-tests.

W2-YM-Balaban-RG:
  KPUniformVolumeBalabanInduction, UltrametricLargeSmallFieldSplit,
  NonperturbativeBalabanScaleTransfer, and WilsonContinuumRGTrajectory.
  Record whether the proof needs 9.593637, 10.13086, or the exact strict
  seed inequality with robust sample 13.7.

W3-YM-Shimura-OS-Gap:
  HyperbolicShimuraToEuclideanUniversality, self-adjoint Hamiltonian
  construction, continuum mass-gap survival, OS/Wightman reconstruction, and
  nontriviality.

W4-NS-Tail-Projection:
  FixedKTailFluxIdentity, NSFlowProjectionTransport,
  LPCommutatorDefectBound, CumulativeTailDissipationDominance,
  DangerShellMaximumPrinciple, KStarNoInertialDrift, `H^{11/8}` continuation,
  and all-smooth-data transfer.

W5-Gate3-W4-GR:
  PhysicalSSPEmbedding3D, PhysicalSSPSpreadBound, UniformFrameLowerBound,
  Mosco/no-pollution transfer, W4 calibration, and GR support surfaces.

W6-Governance:
  Source-map upkeep, kill-test reproducibility, threshold normalisation,
  promotion-flag audit, TODO/status/changelog/context alignment.
```

## What This Buys

The repo now has a bounded proof attack surface:

```text
YM =
  connected-animal KP survives non-perturbative Balaban RG and the
  Shimura/hyperbolic carrier has a real Euclidean 4D continuum limit.

NS =
  fixed-K tail dissipation cumulatively dominates nonlinear injection,
  and the NS-to-carrier projection defect is absorbed non-circularly.
```

Everything else is support, reconstruction, or governance.  All Clay, Gate3,
W4, gravity, YM, NS, Schwarzschild, and terminal promotion flags remain false.
