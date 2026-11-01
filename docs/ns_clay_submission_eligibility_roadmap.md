# NS Clay Submission And Eligibility Roadmap

Date: 2026-07-03

## Purpose

This note records the shortest honest route from the current NS triad repo state
to:

1. a fully internalized Navier-Stokes theorem package,
2. a submission-ready paper packet,
3. external Clay eligibility after publication, the two-year clock, and broad
   mathematical acceptance.

It is a roadmap note only. It does not claim that the listed lemmas are proved.

## Current state

The live state is:

- Gate 1 uniform seam theorem: closed
- Gate 2 seam-local model: closed
- Gate 2 exact `K_N(A)` transfer: closed
- exact-operator residue / BKM frontier: open
- continuum BKM / regularity passage: open
- all-data bridge: open
- full Clay gateway theorem: open
- submission / publication / authority gates: external

The key distinction is:

- seam-local closure is an internal budget/model result;
- Clay-level progress begins only when exact PDE-level transport and the
  continuum regularity chain are proved.

## Minimal dependency ladder

The shortest valid order is:

1. Gate 1 uniform theorem
2. exact Gate 2 `K_N(A)` operator transfer
3. exact-operator frontier: `C/N`, residue scale, BKM projection, residence
4. continuum BKM / global-regularity passage
5. carrier-to-all-data bridge
6. full Clay gateway theorem
7. standard-language writeup and submission packet
8. qualifying publication
9. two-year waiting period
10. broad community acceptance
11. Clay-eligible posture

## Stage 1: Gate 1 uniform seam theorem

Controlling receipt:

- `DASHI/Physics/Closure/NSTriadKNGate1SignedDominationReceipt.agda`

Closed lemmas:

- `UniformDominationRatio`
- `SchurSignedFactorization`
- `SchurComplementPSDTheorem`
- `Gate1ConditionalTheorem`
- `UniformLeakageBound`
- `NormalizedGramToResidueTransfer`

Receipt vars that must flip:

```agda
dominationRatioUniformlyBoundedProved = true
schurSignedFactorizationProved = true
schurComplementPsdProved = true
gate1ConditionalTheoremProved = true
leakageBoundUniformInN = true
normalizedGramToResidueTransferProved = true
```

Stage 1 is now closed. The route no longer blocks on Gate 1; downstream
theorem-level progress starts from the exact-operator frontier.

## Stage 2: exact Gate 2 transfer on the true leakage operator

Controlling theorem surfaces:

- `DASHI/Physics/Closure/NSTriadKNGate2ExactKNAOperatorTransfer.agda`
- `DASHI/Physics/Closure/NSTriadKNGate2OutsideSeamAbsorption.agda`
- `DASHI/Physics/Closure/NSTriadKNGate2ANormalizedCarrierAgreementReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNGate2SeamToLeakageTransferReceipt.agda`

Required lemmas:

- `ExactCarrierEmbedding`
- `ExactRestrictionIdentity`
- `ExactSchurLinearityTransfer`
- `ExactNormalizedLeakageTransfer`
- `OutsideSeamZeroOrAbsorption`
- `ExactGate2ConditionalTheorem`

Receipt vars that must flip:

```agda
gate2aExactRestrictionIdentityObserved = true
gate2aSchurLinearityObserved = true

normalizedGramToHelicalSchurAgreementProved = true
schurCertificateTransfersToLeakageOperator = true
outsideSeamNoPollutionProved = true
gate2ConditionalTheoremProved = true

gate2ExactKNAOperatorTransferProved = true
outsideSeamNoPollutionAnalyticallyProved = true
gate2ExactTransferConditionalTheoremProved = true
```

The seam-local model booleans remain useful, but they do not count toward this
analytic stage.

## Stage 3: exact-operator frontier to BKM-residence bridge

Controlling theorem surfaces:

- `DASHI/Physics/Closure/NSTriadKNPairIncidenceOperatorReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNPairIncidenceRowColumnAuditReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNMixedTailDiagonalResidueBridgeReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNMixedTailBKMProjectionSmallnessReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNExactOperatorFrontierReceipt.agda`
- `DASHI/Physics/Closure/NSTriadKNExactOperatorRouteAuditReceipt.agda`

Required lemmas:

- `PairIncidenceCNTheorem`
  - target: `||L_FT,script^N||_op <= C / N`
- `TailDiagonalStable`
- `SchurResidueScale`
  - target: `q_gap(N) >= c_gap / N^2`
- `StructuralBKMProjectionSmallness`
- `OrthogonalityResidueSeparation`
- `ResidenceTimeExclusion`

Receipt vars that must flip:

```agda
profileIndependentTheoremClosed = true
uniformProfileIndependentBoundClosed = true
schurResidueScaleClosed = true
bkmProjectionSmallnessClosed = true
residenceTimeExclusionClosed = true
bkmResidenceBridgeClosed = true
bkmExclusionProved = true
```

This is the repo’s own exact-operator bridge from the triad leakage object to a
real BKM-facing contradiction route.

The live theorem surface inside that bridge is the weighted Schur product route
`R_N(w_N) * C_N(w_N) <= C^2 / N^2 => ||L_FT,script^N||_op <= C / N`, not a
requirement that both raw row and raw column suprema decay like `1/N`
separately.

## Stage 4: continuum BKM and global-regularity passage

Controlling theorem surfaces:

- `DASHI/Physics/Closure/NSThetaTailToBKMBridgeReceipt.agda`
- `DASHI/Physics/Closure/NSCandidateCompleteEnstrophyBKMPassageReceipt.agda`
- `DASHI/Physics/Closure/ClayMillenniumClosureTargetReceipt.agda`
- `DASHI/Physics/Closure/ClayNSProofRoadmapReceipt.agda`

Required lemmas:

- `NonCircularKStarDriftBound`
- `SobolevExponentTailControl`
- `TailToVorticityLInfinity`
- `SerrinInterpolationPassage`
- `ContinuumBKMPassage`

Receipt vars that must flip:

```agda
KStarDriftBoundProvedHere = true
sobolevExponentTailControlProvedHere = true
bkmCriterionDischarged = true
serrinCriterionDischarged = true

uniformEnstrophyControlConstructed = true
uniformVorticityLInfinityControlConstructed = true
continuumBKMRegularityPassageConstructed = true

bkmEnstrophyClosed = true
smoothGlobalRegularityProved = true
```

This is where the route stops being only a finite-shell or operator theorem and
becomes an actual continuation theorem for Navier-Stokes.

## Stage 5: carrier-to-all-data bridge

Controlling theorem surfaces:

- `DASHI/Physics/Closure/NSCarrierVsClayGapReceipt.agda`
- `DASHI/Physics/Closure/NSCarrierToAllDataReceipt.agda`

Required lemmas:

- `DensityApproximationOfCarrierData`
- `UniformityOfEstimatesUnderApproximation`
- `UniformH118BoundIndependentOfDepth`
- `AubinLionsPassage`
- `LimitSatisfiesNavierStokes`
- `AllSmoothInitialDataBridge`

Receipt vars that must flip:

```agda
densityOfCarrierDataOpen = false
uniformityOfEstimatesOpen = false
densityClosedHere = true

nsGlobalRegularityForAllH118Data != "conditional candidate"
allH118DataStatus != conditionalCandidate
```

Interpretation:

- the carrier theorem has to become an all-data theorem;
- otherwise the route remains restricted-class regularity, not Clay NS.

## Stage 6: full Clay gateway theorem

Controlling theorem surface:

- `DASHI/Physics/Closure/NSFullClayGatewayTheoremBoundaryReceipt.agda`

Primary route lemmas:

- `NonlinearDirectionalRieszSignTheorem`
- `CriticalResidualDepletion`
- `MicrolocalCommutatorGain`
- `MechanismExhaustionForFullClayNS`

Fallback route:

- `HHalfBackwardsUniqueness`

Receipt vars that must flip:

```agda
nonlinearRieszSignCondition = true
criticalResidualDepletion = true
microlocalCommutatorGain = true
mechanismExhaustionForFullClayNS = true
```

or, on the fallback branch:

```agda
hHalfBackwardsUniqueness = true
```

This is the final internal mathematical gate before any submission-facing
posture is even meaningful.

## Stage 7: writeup and submission readiness

Controlling packaging surfaces:

- `DASHI/Physics/Closure/NSClayHardWallCompletionRoadmapReceipt.agda`
- `DASHI/Physics/Closure/NSStandardPDEWriteupAssemblyBoundary.agda`
- `DASHI/Physics/Closure/NSPaperSubmissionPacketBoundary.agda`

Required non-math deliverables:

- standard-language PDE writeup
- theorem dependency audit
- internal proof-obligation map
- bibliography and classical theorem intake audit
- submission-ready packet
- authoritative Track A check

Internal state required before submission:

```text
math package closed
writeup assembled
submission packet assembled
no fail-closed theorem blockers remaining
```

## Stage 8: external path to Clay eligibility

These steps are external to the repo and must not be faked by internal booleans:

1. submit to a qualifying peer-reviewed venue
2. obtain publication
3. wait two years from publication
4. achieve broad mathematical acceptance
5. become realistically Clay-eligible

This means:

- `clayNavierStokesClosed = true` is a mathematical state,
- while Clay eligibility requires an external governance state beyond the repo.

## High-alpha execution order

From the current repo state, the order should be:

1. close the exact scripted pair-incidence `C/N` theorem
2. use that to close `SchurResidueScale`
3. close the structural BKM projection and residence-time exclusion bridge
4. discharge the continuum BKM passage
5. close the all-data bridge
6. close the full Clay gateway theorem
7. assemble standard-language writeup and submission packet
8. hand off to external review/publication/authority process

The live highest-alpha target inside Stage 3 is:

- `PairIncidenceCNTheorem`
- target: `||L_FT,script^N||_op <= C / N`
- controlling surface:
  `DASHI/Physics/Closure/NSTriadKNPairIncidenceOperatorReceipt.agda`

The kernel-formula precursor is now fixed analytically: the nonnegative Schur
kernel is the repeated-pair incidence sum over retained positive-sector triad
weights. So the first genuinely open Stage 3 item is no longer “what is the
kernel?” but “how do its profile pieces satisfy a weighted Schur product
bound?”

## Boundary

The current seam-local Gate 2 closure remains useful scaffolding, but it does
not by itself move the repo into Clay-level NS closure. The first true
post-Gate-2 theorem gap is now the exact scripted pair-incidence operator
bound `||L_FT,script^N||_op <= C / N`; only after that closes can the route
honestly advance through `SchurResidueScale`, the BKM/residence bridge, the
continuum passage, the all-data bridge, and finally the full
gateway/global-regularity route.
