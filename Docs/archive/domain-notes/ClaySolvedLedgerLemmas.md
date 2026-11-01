# Clay Solved Ledger Lemmas

This note records the honestly inhabitable Clay-adjacent facts that can be
proved inside the repo without adding new analytic mathematics.

The corresponding Agda module is:

```text
DASHI/Physics/Closure/ClaySolvedLedgerLemmas.agda
```

The corrected connected-animal KP formula governance is recorded separately in:

```text
DASHI/Physics/Closure/ClayKPCorrectedSeriesIdentityReceipt.agda
```

## What Is Solved Here

The module proves only definitional ledger facts:

- `connectedAnimalThresholdIs959`
- `btTreeThresholdIs1013`
- `strictAbsorptionThresholdIs1364`
- `t7aDirectThresholdIs1656`
- `connectedAnimalGapIs359`
- `btTreeGapIs413`
- `strictAbsorptionGapIs764`
- `t7aDirectGapIs1056`
- `strictMinusConnectedIs405`
- `t7aMinusStrictIs292`
- `t7aDirectCountingDemoted`
- `t7aPerPolymerSuppressionOnly`
- `connectedAnimalThresholdTenThousandthsIs95936`
- `connectedAnimalSafeThresholdTenThousandthsIs95937`
- `connectedAnimalThresholdMillisIs9594`
- `strictAbsorptionExactThresholdMillionthsIs13631603`
- `strictAbsorptionSafeSampleTenthsIs137`
- `clayYangMillsPromotedIsFalse`
- `clayNavierStokesPromotedIsFalse`
- `gate3ClosedIsFalse`
- `w4ClosedIsFalse`
- `gravityPromotedIsFalse`

The formula receipt additionally records:

- `correctedClosedFormTextIsQOverOneMinusPqSquared`
- `legacyWrongClosedFormIsRejected`
- `legacyWrongClosedFormAllowedAsKPRouteIsFalse`
- `correctedFormulaProvesBalabanSeedIsFalse`
- `correctedFormulaProvesClayYangMillsIsFalse`

It also classifies the current route names:

- `ConnectedAnimalKPRoute` is the standard KP route.
- `BTTreeKPRoute` is the tighter convergence route.
- `StrictBalabanSeedRoute` is the active strict seed route.
- `T7ADirectRoute` is demoted.
- `T7ASuppressionEnvelope` is auxiliary only.

## What Remains Open

The module does not prove any Clay-grade analytic theorem.  In particular it
does not prove:

- `NonperturbativeBalabanScaleTransfer`
- `HyperbolicShimuraToEuclideanUniversality`
- `OSWightmanReconstruction`
- `MassGapSurvivesContinuumLimit`
- `Nontrivial4DSU3YangMills`
- `CumulativeTailDissipationDominance`
- `NSFlowProjectionTransport`
- `ProjectionDefectAbsorbedByTailDissipation`
- `PhysicalSSPSpreadBound`
- `UniformFrameLowerBound`

## Worker Update

The six-worker state after this receipt is:

- `W1-YM-Activity`: no new Clay inhabitant; T7A remains auxiliary only.
- `W2-YM-Balaban`: strict active seed is the exact inequality
  `beta*c_min-a>log(2p)`; `13.64` is barely safe and `13.7` is the robust
  numeric sample.
- `W3-YM-OS-Geometry`: OS/Wightman, mass-gap survival, and nontriviality remain open.
- `W4-NS`: first live targets are fixed-K tail with defect and projection-defect absorption.
- `W5-Gate3`: first live target remains `PhysicalSSPSpreadBound`.
- `W6-Governance`: ledger, route, demotion, and false-promotion facts are now inhabited.

## Boundary

This receipt buys a cleaner proof ledger and fewer ways to accidentally promote
an open theorem.  It does not solve Clay.  The shortest path from here is still
to inhabit the open analytic blockers recorded by the kernel receipts.
