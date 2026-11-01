# YM Finite Domination Candidate Audit

Route decision: `fail-closed`
Route closed: `false`

## Constants

### BW-SF-c1

- Formula: `c1 = gamma_d / 2 - C * epsilon`
- Positivity: `gamma_d / 2 - C * epsilon > 0`
- Closed: `false`
- Reason: No audited source supplies explicit uniform constants proving gamma_d > 2*C*epsilon.

### BW-LF-c2

- Formula: `c2 = large_field_Wilson_holonomy_positive_margin`
- Positivity: `c2 > 0`
- Closed: `false`
- Reason: The audit records the positivity obligation only; it does not promote a Wilson/holonomy lower-bound theorem.

## Required Blockers

- `BW-SF-c1` blocked=`true`: Prove c1 = gamma_d/2 - C*epsilon > 0 with explicit uniform gamma_d, C, and epsilon.
- `BW-LF-c2` blocked=`true`: Prove c2 > 0 from Wilson large-field action and holonomy/topological cost after leakage subtraction.
- `KB-GQ-DOMAIN` blocked=`true`: Discharge self-adjoint Killing-boundary domain preservation, quotient descent, and gauge-invariant projection obligations.
- `GQ-ZERO-MODE` blocked=`true`: Show quotienting removes gauge zero modes without creating new zero-energy modes or boundary leakage.
- `H3A-BALABAN-SEPARATION` blocked=`true`: Keep the finite domination candidate separated from H3a, Balaban, continuum transfer, no-spectral-pollution, OS/Wightman, and Clay gates.

## Promotion Guard

- `candidateAFiniteHamiltonianDominationPromoted`: `false`
- `yangMillsPromoted`: `false`
- `clayYangMillsPromoted`: `false`
- `continuumMassGapPromoted`: `false`
- `h3aBalabanPromoted`: `false`
- `terminalClayClaimPromoted`: `false`

## Evidence Buckets

- `bochner_weitzenbock`: 29 source surface(s)
- `small_field_c1`: 25 source surface(s)
- `large_field_c2`: 39 source surface(s)
- `killing_boundary`: 62 source surface(s)
- `gauge_quotient`: 34 source surface(s)
- `h3a_balaban`: 55 source surface(s)
- `promotion_guard`: 64 source surface(s)

## Fail-Closed Reasons

- DASHI/Physics/Closure/YMBochnerWeitzenbockHamiltonianDominationBoundary.agda: empty data declaration detected (L1395)
- DASHI/Physics/Closure/YMHamiltonianDominatesFiniteHodgeDefectBoundary.agda: empty data declaration detected (L1233)
- DASHI/Physics/Closure/YMKillingBoundaryFluxCancellationBoundary.agda: empty data declaration detected (L1087)
- DASHI/Physics/Closure/YMKillingBoundaryGaugeDomainPreservationBoundary.agda: empty data declaration detected (L1229)
- DASHI/Physics/Closure/YMKillingBoundaryOppositeFaceInvolutionBoundary.agda: empty data declaration detected (L1127)
- DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessCompositeBoundary.agda: empty data declaration detected (L853)
- DASHI/Physics/Closure/YMKillingBoundaryWeightPreservationBoundary.agda: empty data declaration detected (L1075)
- DASHI/Physics/Closure/YMGaugeZeroModeVacuumRigidityBoundary.agda: empty data declaration detected (L1526)
- DASHI/Physics/Closure/YMLatticeMassGapAuthority.agda: empty data declaration detected (L488)
- DASHI/Physics/Closure/YMClayUpdatedBlockerReceipt.agda: empty data declaration detected (L64)
- DASHI/Physics/Closure/AdelicWilsonLoopReceipt.agda: empty data declaration detected (L57)
- DASHI/Physics/Closure/PenguinDecayWilsonCoefficientAuthority.agda: empty data declaration detected (L655)
- DASHI/Physics/Closure/ShimuraTowerWilsonActionReceipt.agda: empty data declaration detected (L100)
- DASHI/Physics/Closure/WilsonActionOn3PlusOneLatticeReceipt.agda: empty data declaration detected (L55)
- DASHI/Physics/Closure/WilsonBetaFromCSLevelReceipt.agda: empty data declaration detected (L55)
- DASHI/Physics/Closure/YMActualP7WilsonPolymerActivityReceipt.agda: empty data declaration detected (L239)
- DASHI/Physics/Closure/BalabanRGMassGapReceiptSurface.agda: empty data declaration detected (L205)
- DASHI/Physics/Closure/BalabanRGScaleTransferFrontierReceipt.agda: empty data declaration detected (L183)
- DASHI/Physics/Closure/CarrierAreaLawBalabanSeedReceipt.agda: empty data declaration detected (L149)
- DASHI/Physics/Closure/CarrierBalabanInductiveStepReceipt.agda: empty data declaration detected (L125)
- DASHI/Physics/Closure/ClaySprintEightyOneYMBalabanCMP98QhpLocalOscillationReceipt.agda: empty data declaration detected (L143)
- DASHI/Physics/Closure/ClaySprintSeventyEightYMBalabanEndpointAfterSpatialSupportReceipt.agda: empty data declaration detected (L79)
- DASHI/Physics/Closure/ClaySprintSeventySevenYMBalabanTransferAssemblyExactLemmaReceipt.agda: empty data declaration detected (L81)
- DASHI/Physics/Closure/ClaySprintSeventySixYMBalabanTransferCompatibilityReceipt.agda: empty data declaration detected (L111)
- DASHI/Physics/Closure/ClaySprintSixtyFourYMWeightedKPBalabanPathReceipt.agda: empty data declaration detected (L102)
- DASHI/Physics/Closure/ClaySprintSixtySevenYMWeightedKPBalabanReceipt.agda: empty data declaration detected (L192)
- DASHI/Physics/Closure/YMBalabanCarrierRGContractionReceipt.agda: empty data declaration detected (L116)
- DASHI/Physics/Closure/YMBalabanContinuumLimitReceipt.agda: empty data declaration detected (L73)
- DASHI/Physics/Closure/YMBalabanMarginSplitReceipt.agda: empty data declaration detected (L103)
- DASHI/Physics/Closure/YMBalabanOptionATheoremIntakeReceipt.agda: empty data declaration detected (L10, L337)
- DASHI/Physics/Closure/YMBalabanPartitionTemporalTraceCommutation.agda: empty data declaration detected (L63)
- DASHI/Physics/Closure/YMBalabanPhysicalBetaBridgeTargetReceipt.agda: empty data declaration detected (L145)
- DASHI/Physics/Closure/YMBalabanRGInductionCandidateReceipt.agda: empty data declaration detected (L303)
- DASHI/Physics/Closure/YMBalabanRGInductiveStepProofReceipt.agda: empty data declaration detected (L108)
- DASHI/Physics/Closure/YMBalabanRGScaleTransferFrontierReceipt.agda: empty data declaration detected (L83)
- DASHI/Physics/Closure/YMBalabanTransferCompatibilityTheorem.agda: empty data declaration detected (L92)
- DASHI/Physics/Closure/YMFortyThreeStepBalabanTargetReceipt.agda: empty data declaration detected (L77)
- DASHI/Physics/Closure/YMFortyTwoStepBalabanTargetReceipt.agda: empty data declaration detected (L85)
- DASHI/Physics/Closure/YMMarginParametricBalabanReceipt.agda: empty data declaration detected (L77)
- DASHI/Physics/Closure/YMOneLoopBalaban1to3Receipt.agda: empty data declaration detected (L68)
- DASHI/Physics/Closure/YMResidualSupportBalabanAuthority.agda: empty data declaration detected (L68)
- DASHI/Physics/Closure/YMTemporalCutsStableUnderBalabanRG.agda: empty data declaration detected (L53)
- DASHI/Physics/Closure/YMH3aContinuumIntakeReceipt.agda: empty data declaration detected (L171)
- DASHI/Physics/Closure/YMH3bVacuumProjectorNoSpectralPollutionBoundaryReceipt.agda: empty data declaration detected (L158)
- Prove c1 = gamma_d/2 - C*epsilon > 0 with explicit uniform gamma_d, C, and epsilon.
- Prove c2 > 0 from Wilson large-field action and holonomy/topological cost after leakage subtraction.
- Discharge self-adjoint Killing-boundary domain preservation, quotient descent, and gauge-invariant projection obligations.
- Show quotienting removes gauge zero modes without creating new zero-energy modes or boundary leakage.
- Keep the finite domination candidate separated from H3a, Balaban, continuum transfer, no-spectral-pollution, OS/Wightman, and Clay gates.
