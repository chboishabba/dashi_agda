# Clay Requisite Kernel Lemmas

This is the shortest current theorem surface for turning the repo into
Clay-facing proofs.  It is narrower than the broad proof-campaign DAG:
only terminal or immediately load-bearing lemmas are listed.

## Proved Inputs

The current computational/audit inputs are recorded as inputs, not
promotions:

```text
ymT7CoefficientPositive       : all T7A(d) > 0
ymConnectedAnimalBound        : count(d) <= d * p^(d-1)
ymBetaStarConnected           : beta* ~= 9.593637
ymBetaStarT7ADirect           : beta* ~= 16.56
nsShellFluxIdentity_numerical : shell-by-shell verified
nsDissipationDominatesFlux    : diss >> flux for synthetic spectra
```

The Clay-relevant correction is:

```text
T7A direct counting is not the YM counting improvement.
Connected-animal counting is the standard KP route.
T7A can help only through per-polymer activity suppression.
```

## Yang-Mills Required Lemmas

```text
1. ConnectedAnimalKPBound
2. T7APerPolymerActivitySuppression
3. AnalyticContinuumKP
4. BalabanConnectedAnimalBridge
5. DimensionfulMassGapConvergence
6. HyperbolicShimuraToEuclideanUniversality
7. GaugeFixedOSPositivity
8. OSWightmanReconstruction
9. UniformContinuumMassGapSurvival
10. Nontrivial4DSU3YangMills
```

The corrected T7A activity statement is:

```text
T7APerPolymerActivitySuppression:
  |z(Gamma)| <=
    (T7A(d) / (d * p^(d-1))) * exp(-beta*c_min*d)
```

The corrected Balaban target is:

```text
BalabanConnectedAnimalBridge:
  beta_phys ~= 6
  beta_eff*c_min-a > log(2p) for strict Balaban seeding
  robust numeric target beta_eff >= 13.7
```

The `9.593637` threshold remains valid for connected-animal KP convergence,
with gap `3.593637` from `beta_phys ~= 6`.  It is not enough by itself for the
Balaban block-spin induction seed.

## Navier-Stokes Required Lemmas

```text
1. CarrierToStandardH118NormComparison
2. NSFlowProjectionTransport
3. CumulativeTailDissipationDominance
4. DangerShellMaximumPrinciple
5. KStarNoInertialDrift
6. BernoulliBandGlobalH118Bound
7. H118ContinuationCriterion
8. CarrierStructuredDenseInSmoothDivergenceFree
9. ApproximationStability
```

The shortest NS hard lemma is:

```text
CumulativeTailDissipationDominance
```

The numerical shell-flux checks support the model, but the Clay theorem needs
continuous-flow projection transport and a non-circular cumulative tail
dissipation estimate.

## Gate3 Support Lemmas

Gate3 is not a Clay Millennium problem, but it remains physics-stack support.

```text
1. AtomGrammarCMSplittingSeparation
2. PhysicalSSPEmbedding3D
3. PhysicalSSPSpreadBound
4. UniformFrameLowerBound
5. Gate3MoscoNoPollutionTransfer
```

The arithmetic guard is unchanged:

```text
7+7+1 = semantic atom/frame grammar
5+9+1 = literal Q(sqrt(-7)) splitting table
p71 = split, not inert, in Q(sqrt(-7))
```

## Six Parallel Workers

```text
W1-YM-KP-Activity:
  connected-animal KP reproducibility, T7A coefficient positivity,
  T7APerPolymerActivitySuppression, and CarrierWilsonAreaLaw.

W2-YM-Balaban-RG:
  AnalyticContinuumKP, BalabanConnectedAnimalBridge,
  DimensionfulMassGapConvergence, and active KP margin selection.

W3-YM-Flat-OS-Gap:
  HyperbolicShimuraToEuclideanUniversality, GaugeFixedOSPositivity,
  OSWightmanReconstruction, UniformContinuumMassGapSurvival,
  and Nontrivial4DSU3YangMills.

W4-NS-Tail:
  NSFlowProjectionTransport, CumulativeTailDissipationDominance,
  DangerShellMaximumPrinciple, KStarNoInertialDrift,
  BernoulliBandGlobalH118Bound, continuation, and approximation stability.

W5-Gate3-Support:
  AtomGrammarCMSplittingSeparation, PhysicalSSPEmbedding3D,
  PhysicalSSPSpreadBound, UniformFrameLowerBound,
  and Gate3MoscoNoPollutionTransfer.

W6-Governance:
  threshold normalisation, source maps, kill-test preservation,
  finite-computation boundaries, and promotion-flag audit.
```

## Boundary

This receipt records required lemmas and worker assignments only.  No Clay,
Gate3, W4, gravity, Schwarzschild, Yang-Mills, Navier-Stokes, or terminal
promotion follows from the proved finite computations listed here.
