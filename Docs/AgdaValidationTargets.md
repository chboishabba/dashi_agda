# Agda Validation Targets

Purpose: record which Agda modules are safe for routine targeted validation and
which ones should be avoided in normal loops because they are known to be
runtime-heavy or aggregate too much of the closure surface at once.

## Timeout-Limited Clay P0 Targets

The current zero-mode/YM/core P0 modules are substantial Agda receipt surfaces
with heavy imports.  In rapid iteration loops, validate them with a hard cap:

```bash
timeout 15s agda <module>.agda
```

Exit code `124` means the module exceeded the sprint verification budget, not
that Agda found a type error.  Longer checks are still required before marking
these surfaces as fully checked:

- `DASHI/Physics/Closure/ProjectionNonlocalityDefectLaplacianZeroModeSheaf.agda`
- `DASHI/Physics/Closure/NSZeroModeSetClassificationBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianGreatCircleCriterionBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianRadialZeroModeAuthorityBoundary.agda`
- `DASHI/Physics/Closure/NSGreatCircleZeroModeTrapExclusionBoundary.agda`
- `DASHI/Physics/Closure/NSZeroModeGreatCircleGeometryTheorem.agda`
- `DASHI/Physics/Closure/NSTangentialZeroModePressureStarvationBoundary.agda`
- `DASHI/Physics/Closure/NSTrueLerayTriadicZeroModeClassificationBoundary.agda`
- `DASHI/Physics/Closure/NSAbelTriadicDefectMeasureConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSAbelTriadicStationarityConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSAbelTriadicStationarityProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSA1TypeILorentzToAbelMassRouteBoundary.agda`
- `DASHI/Physics/Closure/NSA1TypeILorentzToAbelMassRouteTheoremBoundary.agda`
- `DASHI/Physics/Closure/NSBoundedAbelMassEstimateBoundary.agda`
- `DASHI/Physics/Closure/NSQuantitativeStationarityRateBoundary.agda`
- `DASHI/Physics/Closure/NSQuantitativeStationarityRateProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSA2NearDiagonalCoifmanMeyerRouteBoundary.agda`
- `DASHI/Physics/Closure/NSA2NearDiagonalCoifmanMeyerTheoremBoundary.agda`
- `DASHI/Physics/Closure/NSTriadicShellBernsteinHolderBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianOutputSupportTransferBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianFourierOutputCouplingBoundary.agda`
- `DASHI/Physics/Closure/NSPhysicalAngularMeasureConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSLocalizedWhitneyFramePacketEstimateBoundary.agda`
- `DASHI/Physics/Closure/NSFourierOutputPushforwardBoundary.agda`
- `DASHI/Physics/Closure/NSWhitneyCouplingInequalityBoundary.agda`
- `DASHI/Physics/Closure/NSAntipodalTubeNullMassBoundary.agda`
- `DASHI/Physics/Closure/NSSardRegularValueSlicingBoundary.agda`
- `DASHI/Physics/Closure/NSWhitneyFubiniDisintegrationBoundary.agda`
- `DASHI/Physics/Closure/NSPhiJacobianLowerBoundBoundary.agda`
- `DASHI/Physics/Closure/NSA4SardFubiniCompositeBoundary.agda`
- `DASHI/Physics/Closure/NSOutputGreatCircleStripSlicingBoundary.agda`
- `DASHI/Physics/Closure/NSOutputStripPreimageMeasureEstimateBoundary.agda`
- `DASHI/Physics/Closure/NSA4ExceptionalMassCompositeBoundary.agda`
- `DASHI/Physics/Closure/NSA4NoAngularCollapseTransferCompositeBoundary.agda`
- `DASHI/Physics/Closure/NSA4CoareaStripPreimageCalculationBoundary.agda`
- `DASHI/Physics/Closure/NSA4GradientFormulaLocalChartBoundary.agda`
- `DASHI/Physics/Closure/NSA4UniformInNormalConstantsBoundary.agda`
- `DASHI/Physics/Closure/NSA4DerivativeJacobianLowerBoundCompositeBoundary.agda`
- `DASHI/Physics/Closure/NSA4EtaStripCoareaSlabEstimateBoundary.agda`
- `DASHI/Physics/Closure/NSA4UniformErrorBudgetCompositeBoundary.agda`
- `DASHI/Physics/Closure/NSA4ResidualPositiveAfterErrorsBoundary.agda`
- `DASHI/Physics/Closure/NSA4ToA6TransferLadderBoundary.agda`
- `DASHI/Physics/Closure/NSA4ResidualPositiveTheoremLadderBoundary.agda`
- `DASHI/Physics/Closure/NSA4OutputSupportCoareaResidualTheoremBoundary.agda`
- `DASHI/Physics/Closure/NSA5KappaBiasVanishingFromA4StationarityBoundary.agda`
- `DASHI/Physics/Closure/NSBonyLipschitzAngularPushforwardBoundary.agda`
- `DASHI/Physics/Closure/NSLowVorticityExceptionalMassRoutingBoundary.agda`
- `DASHI/Physics/Closure/NSBiotSavartShellLocalizationBoundary.agda`
- `DASHI/Physics/Closure/NSBiotSavartShellLocalizationProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSBonyParaproductA6RepairBoundary.agda`
- `DASHI/Physics/Closure/NSPointwiseToAbelAveragingBoundary.agda`
- `DASHI/Physics/Closure/NSDiagonalStretchingToAbelMeanBoundary.agda`
- `DASHI/Physics/Closure/NSOffDiagonalShellAbsorptionBoundary.agda`
- `DASHI/Physics/Closure/NSAbelShellMixingLLNBoundary.agda`
- `DASHI/Physics/Closure/NSLocalizationPressureCommutatorBoundary.agda`
- `DASHI/Physics/Closure/NSLocalizationPressureCommutatorProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSPressureCommutatorEstimateContractBoundary.agda`
- `DASHI/Physics/Closure/NSCutoffRieszCommutatorKernelProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSHarmonicPressureTailAbsorptionEstimateBoundary.agda`
- `DASHI/Physics/Closure/NSPressureTailAbsorptionProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSPressureLocalizationSubBudgetCompositeBoundary.agda`
- `DASHI/Physics/Closure/NSPressureLocalizationSubBudgetProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSPressureSubBudgetComponentSensitivityProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSPointwiseToAbelCompositeA6Boundary.agda`
- `DASHI/Physics/Closure/NSPointwiseToAbelAveragingProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSA6ErrorBudgetCompositeBoundary.agda`
- `DASHI/Physics/Closure/NSA6A4BiasToLeakageClosureCompositeBoundary.agda`
- `DASHI/Physics/Closure/NSA6TheoremLadderBoundary.agda`
- `DASHI/Physics/Closure/NSA7ResidualDepletionGronwallBoundary.agda`
- `DASHI/Physics/Closure/NSA8AnnularDecayClarificationBoundary.agda`
- `DASHI/Physics/Closure/NSA8FullLocalDefectMonotonicityBoundary.agda`
- `DASHI/Physics/Closure/NSA8A9MonotonicityClosureTheoremLadderBoundary.agda`
- `DASHI/Physics/Closure/NSA9SingularityContradictionRouteBoundary.agda`
- `DASHI/Physics/Closure/NSA9CKNBKMClosureBoundary.agda`
- `DASHI/Physics/Closure/NSTriadicCompensatedLeakageIdentityBoundary.agda`
- `DASHI/Physics/Closure/NSExactStrainEigenbundleHarnessBoundary.agda`
- `DASHI/Physics/Closure/NSS2BiotSavartEigenbundleCascadeDiagnosticBoundary.agda`
- `DASHI/Physics/Closure/NSSignAntisymmetryExactIdentityBoundary.agda`
- `DASHI/Physics/Closure/NSCascadeKappaArcsineLawBoundary.agda`
- `DASHI/Physics/Closure/NSCoherentStretchingExactFormulaBoundary.agda`
- `DASHI/Physics/Closure/NSFiniteCascadeStretchingNeutralityBoundary.agda`
- `DASHI/Physics/Closure/NSTransferOperatorBiasNeutralityBoundary.agda`
- `DASHI/Physics/Closure/NSBiotSavartStrainMeanSquareExactFormulaBoundary.agda`
- `DASHI/Physics/Closure/YMGaugeZeroModeVacuumRigidityBoundary.agda`
- `DASHI/Physics/Closure/YMHamiltonianDominatesFiniteHodgeDefectBoundary.agda`
- `DASHI/Physics/Closure/YMBruhatTitsToOSLatticeTransferBoundary.agda`
- `DASHI/Physics/Closure/YMAdmissibleBTBoundaryConventionBoundary.agda`
- `DASHI/Physics/Closure/YMFiniteGaugeQuotientHamiltonianPreconditionBoundary.agda`
- `DASHI/Physics/Closure/YMSelfAdjointFiniteHamiltonianBoundary.agda`
- `DASHI/Physics/Closure/YMFiniteSelfAdjointHamiltonianProxyHarnessResult.agda`
- `DASHI/Physics/Closure/YMHamiltonianDominationProxyHarnessResult.agda`
- `DASHI/Physics/Closure/YMHamiltonianDominationCompositeBoundary.agda`
- `DASHI/Physics/Closure/YMHamiltonianDominationErrorBudgetBoundary.agda`
- `DASHI/Physics/Closure/YMDominationSpectralMarginProxyHarnessResult.agda`
- `DASHI/Physics/Closure/YMSpectralMarginErrorBudgetCompositeBoundary.agda`
- `DASHI/Physics/Closure/YMSpectralMarginBoundarySensitivityProxyHarnessResult.agda`
- `DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessDomainContract.agda`
- `DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessProxyHarnessResult.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryFluxCancellationBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryOppositeFaceInvolutionBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryWeightPreservationBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryOrientationCancellationBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryOrientationSignCancellationBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryGreenIdentityBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryGaugeDomainPreservationBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessCompositeBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessTheoremBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessTheoremLadderBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundarySpectralGapExplicitBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryOppositeFaceInvolutionLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryFluxCancellationLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryGaugeQuotientDescentLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryQuotientSymmetryLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryChildProofCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMKillingBoundaryTheoremConsumerCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMSelfAdjointToDominationPreconditionCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMDominationToHolonomyPositivePartCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMHolonomyPositivePartToSpectralMarginCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMSpectralMarginToContinuumTransferCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary.agda`
- `DASHI/Physics/Closure/YMFiniteGaugeQuotientCarrierConstructionBoundary.agda`
- `DASHI/Physics/Closure/YMBochnerWeitzenbockHamiltonianDominationBoundary.agda`
- `DASHI/Physics/Closure/YMSeiler1982GapCompatibilityBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumUniformRhoBoundBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumUniformLeakageBoundBoundary.agda`
- `DASHI/Physics/Closure/YMHyperbolicShimuraToEuclideanUniversalityBoundary.agda`
- `DASHI/Physics/Closure/YMStepScalingGlobalBoundBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumBridgeCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivitySpatialTauBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityThetaBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityBoundaryPairingCompatibilityBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivitySpatialTauThetaCommutativityBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityActionSplitBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityTransferMatrixHermitianBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityOSAxiomBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityChildCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityFullTheoremAssemblyBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityBoundaryConventionBoundary.agda`
- `DASHI/Physics/Closure/YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMOSWightmanToContinuumMassGapSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumMassGapFinalAssemblyBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumMassGapToClayAuthorityBlockerCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMOnlyRemainingAuthorityBlockersBoundary.agda`
- `DASHI/Physics/Closure/YMStandardLanguageWriteupReadinessBoundary.agda`
- `DASHI/Physics/Closure/YMStandardLanguagePaperAssemblyBoundary.agda`
- `DASHI/Physics/Closure/YMPaperSubmissionPacketBoundary.agda`
- `DASHI/Physics/Closure/YMExternalAcceptanceBoundary.agda`
- `DASHI/Physics/Closure/YMFinalAuthorityPackagingCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMBTToFourDimensionalContinuumRouteBoundary.agda`
- `DASHI/Physics/Closure/YMUniformPositiveHolonomyActionBoundary.agda`
- `DASHI/Physics/Closure/YMHolonomyActionToDominationCompositeBoundary.agda`
- `DASHI/Physics/Closure/FiniteGaugeHodgeAdjointCompatibility.agda`
- `DASHI/Physics/Closure/YMWeightedBTAdjointKappaCalculation.agda`
- `DASHI/Physics/Closure/DefectFourPointParallelogramLawBoundary.agda`
- `DASHI/Physics/Closure/DefectSheafGluingFourPointParallelogramBoundary.agda`
- `DASHI/Physics/Closure/GluingResidualForcesFourPointCancellationBoundary.agda`
- `DASHI/Physics/Closure/GluingOperatorLinearityOnDefectQuotientBoundary.agda`
- `DASHI/Physics/Closure/GluingOperatorLinearityProxyHarnessResult.agda`
- `DASHI/Physics/Closure/UnificationGluingCrossTermNullClassBoundary.agda`
- `DASHI/Physics/Closure/UnificationGluingLinearityCompositeBoundary.agda`
- `DASHI/Physics/Closure/UnificationGluingQuotientAdmissibilityProxyHarnessResult.agda`
- `DASHI/Physics/Closure/UnificationQuotientFourPointStressProxyHarnessResult.agda`
- `DASHI/Physics/Closure/UnificationFourPointStressCompositeBoundary.agda`
- `DASHI/Physics/Closure/UnificationCrossTermToFourPointCompositeBoundary.agda`
- `DASHI/Physics/Closure/UnificationGluingCrossTermLinearityLiftBoundary.agda`
- `DASHI/Physics/Closure/UnificationNullClassStabilityBoundary.agda`
- `DASHI/Physics/Closure/UnificationNullToQuotientEqualityTransportBoundary.agda`
- `DASHI/Physics/Closure/UnificationGluingModuloNullLinearityCompositeBoundary.agda`
- `DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda`
- `DASHI/Physics/Closure/UnificationCrossTermNullityLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationNullClassStabilityLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationNullTransportModuloNullConsumerLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationCrossTermChildCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationHCToModuloNullLinearityCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationHCToFourPointInputCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationModuloNullLinearityRouteCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationFourPointCancellationRouteCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationFourPointToParallelogramSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationFourPointCancellationFromCrossTermNullityBoundary.agda`
- `DASHI/Physics/Closure/UnificationModuloNullLinearityFromCrossTermNullityBoundary.agda`
- `DASHI/Physics/Closure/UnificationScaleInvariantCrossTermHypothesisBoundary.agda`
- `DASHI/Physics/Closure/UnificationHierarchyConsistencyKillsFourPointDefectBoundary.agda`
- `DASHI/Physics/Closure/UnificationCrossTermNullityDiscriminantBoundary.agda`
- `DASHI/Physics/Closure/UnificationNullClassSubspaceCompleteBoundary.agda`
- `DASHI/Physics/Closure/UnificationParallelogramFromBilinearBoundary.agda`
- `DASHI/Physics/Closure/UnificationU1aHJustificationNSLaneBoundary.agda`
- `DASHI/Physics/Closure/UnificationU1aHJustificationYMLaneBoundary.agda`
- `DASHI/Physics/Closure/UnificationU1aHJustificationGlobalBoundary.agda`
- `DASHI/Physics/Closure/UnificationU1aHPerLaneCompositeBoundary.agda`
- `DASHI/Physics/Closure/UnificationCliffordSignatureTableBoundary.agda`
- `DASHI/Physics/Closure/UnificationSignatureCliffordConsumerSocketBoundary.agda`
- `DASHI/Physics/Closure/UnificationLaneJustificationAuthorityBoundary.agda`
- `DASHI/Physics/Closure/UnificationConsumerAuthorityAssemblyBoundary.agda`
- `DASHI/Physics/Closure/UnificationAuthorityReviewPacketBoundary.agda`
- `DASHI/Physics/Closure/UnificationJordanVonNeumannAdapterBoundary.agda`
- `DASHI/Physics/Closure/NSWriteupAndConstantsReadinessBoundary.agda`
- `DASHI/Physics/Closure/NSStandardPDEWriteupAssemblyBoundary.agda`
- `DASHI/Physics/Closure/NSPaperSubmissionPacketBoundary.agda`

Current frontier receipts:

- `DASHI/Physics/Closure/NSSignAntisymmetryExactIdentityBoundary.agda` is a
  finite-algebra identity receipt for the repaired NS target.  It does not
  prove output-width exclusion or PDE leakage transfer.
- `DASHI/Physics/Closure/NSCascadeKappaArcsineLawBoundary.agda`,
  `DASHI/Physics/Closure/NSCoherentStretchingExactFormulaBoundary.agda`,
  `DASHI/Physics/Closure/NSFiniteCascadeStretchingNeutralityBoundary.agda`,
  `DASHI/Physics/Closure/NSTransferOperatorBiasNeutralityBoundary.agda`,
  and
  `DASHI/Physics/Closure/NSBiotSavartStrainMeanSquareExactFormulaBoundary.agda`
  together with `DASHI/Physics/Closure/NSSignAntisymmetryExactIdentityBoundary.agda`
  record the corrected five-result finite NS normal form: true-triad sign
  antisymmetry, the kappa arcsine law, the exact stretching formula, finite
  cascade stretching neutrality, and the mean-square strain coefficient.
  `NSTransferOperatorBiasNeutralityBoundary` records conditional
  finite-statistical neutrality for the transfer operator; it does not prove
  PDE stationarity, approximate `T_NS`-stationarity, or any Clay promotion.
  The live PDE gate is `NSTypeIBlowupKappaBiasBound`, namely ruling out
  persistent positive `lambda(c)(kappa^2 - 1/2)` bias for admissible Type-I /
  self-similar Abel triadic measures.  These receipts do not prove that
  bound, the leakage identity, local defect monotonicity, CKN/BKM closure, or
  Clay NS.
  The corrected Gaussian self-similar balance currently records the analytic
  shape to be formalized in the next receipt:
  `2 int |grad omega|^2 G - 1/2 int |omega|^2 G =
  4 Bias_G Omega_G + Drift_G Omega_G`, forcing
  `1 <= 4 Bias_G + Drift_G` for any nontrivial profile after OU Poincare.
  The variational harness points to approximate `T_NS`-stationarity as the
  decisive constraint; the next named proof gap is
  `AbelTriadicDefectMeasureConstruction`, not a new finite cascade
  calculation.
- `DASHI/Physics/Closure/NSAbelTriadicStationarityConstructionBoundary.agda`
  records the A1-A4 analytic stationarity rung now sitting directly above the
  Abel measure boundary: bounded mass, observable recording, approximate
  `T_NS` stationarity with `delta_r -> 0`, and LRT output-support transfer.
  `DASHI/Physics/Closure/NSAbelTriadicStationarityProxyHarnessResult.agda`
  records only the synthetic proxy harness surface
  `scripts/ns_abel_triadic_stationarity_proxy_harness.py`.  These surfaces do
  not prove the PDE Abel measure construction, the quantitative stationarity
  rate, the Type-I kappa-bias theorem, the compensated leakage identity,
  local monotonicity, or Clay NS.
- `DASHI/Physics/Closure/NSBoundedAbelMassEstimateBoundary.agda` records A1:
  Type-I / `L^{3,infty}` control -> Littlewood-Paley shell mass -> Abel
  log-window finite-variation target.  The paired diagnostic
  `scripts/ns_bounded_abel_mass_proxy_harness.py` checks bounded proxy
  profiles and a deliberately bad profile only; neither surface proves the
  CKN-scale bounded Abel mass theorem.
- `DASHI/Physics/Closure/NSQuantitativeStationarityRateBoundary.agda` records
  the A3.3 `W_r = U_r - U_infty` energy-ODE route, Seregin/ESS rate input,
  and the still-open `delta_r -> 0` proof.  The
  `delta_r * sqrt(11/60)` bias consequence is conditional only.
- `DASHI/Physics/Closure/NSQuantitativeStationarityRateProxyHarnessResult.agda`
  records the executable proxy receipt for
  `scripts/ns_stationarity_rate_proxy_harness.py`: log-rate good profiles,
  a bad nondecaying counterprofile, and the synthetic
  `delta_r * sqrt(11/60)` bias-bound calculation.  It is not a Seregin/ESS
  proof.
- `DASHI/Physics/Closure/NSTriadicShellBernsteinHolderBoundary.agda` records
  the A2 dyadic estimate target and explicitly marks the naive `L4 x L4`
  Bernstein route as insufficient without the near-diagonal Leray/Coifman-
  Meyer shell argument.
- `DASHI/Physics/Closure/NSLeiRenTianOutputSupportTransferBoundary.agda`
  records the A4 physical-vorticity-direction to Fourier-output-direction
  support coupling target.  Whitney/frame/localization and no-angular-
  collapse transfer remain unproved.
- `DASHI/Physics/Closure/NSLeiRenTianFourierOutputCouplingBoundary.agda`
  sharpens A4 into the explicit physical angular measure -> localized
  Whitney/frame packet -> Fourier output pushforward -> no-collapse support
  lift contract.  The paired LRT Fourier-output coupling harness is
  diagnostic only.
- `DASHI/Physics/Closure/NSPhysicalAngularMeasureConstructionBoundary.agda`,
  `DASHI/Physics/Closure/NSLocalizedWhitneyFramePacketEstimateBoundary.agda`,
  `DASHI/Physics/Closure/NSFourierOutputPushforwardBoundary.agda`, and
  `DASHI/Physics/Closure/NSWhitneyCouplingInequalityBoundary.agda` split A4
  into checked child receipts.  They normalize the physical angular measure,
  localized Whitney/frame packet, `Phi(theta1,theta2)` Fourier pushforward,
  and Whitney-overlap/no-collapse coupling obligations.  Sard/Fubini
  coupling, A4, A6, NS Clay, and terminal promotion remain unproved.
- `DASHI/Physics/Closure/NSAntipodalTubeNullMassBoundary.agda`,
  `DASHI/Physics/Closure/NSSardRegularValueSlicingBoundary.agda`,
  `DASHI/Physics/Closure/NSWhitneyFubiniDisintegrationBoundary.agda`, and
  `DASHI/Physics/Closure/NSPhiJacobianLowerBoundBoundary.agda` further split
  the A4 Sard/Fubini residual into antipodal-tube discard, regular-value
  slicing, Whitney-packet disintegration, and off-antipodal Jacobian lower
  bound obligations.  These are checked receipts only; the analytic coupling
  theorem remains open.
- `DASHI/Physics/Closure/NSA4SardFubiniCompositeBoundary.agda` composes the
  four Sard/Fubini child receipts back into the Whitney coupling consumer and
  A4 output-support transfer.  `NSOutputGreatCircleStripSlicingBoundary.agda`,
  `NSBonyLipschitzAngularPushforwardBoundary.agda`, and
  `NSLowVorticityExceptionalMassRoutingBoundary.agda` record the next local
  transfer blockers: output strip slicing, Bony/Lipschitz angular stability,
  and low-vorticity/null-output exceptional routing.  The A4 theorem remains
  open.
- `DASHI/Physics/Closure/NSA4OutputSupportCoareaResidualTheoremBoundary.agda`
  is the lightweight 15s-safe A4 receipt. It records the four-part proof
  content only: local derivative, Sard/coarea density, Lei-Ren-Tian transfer,
  and residual positivity after errors. It keeps A5/A6/A7/Clay false.
- `DASHI/Physics/Closure/NSA5KappaBiasVanishingFromA4StationarityBoundary.agda`
  is the lightweight 15s-safe A5 receipt. It records the three-step route:
  bias equals half mean stretching, one-step Koopman/transfer neutrality plus
  A4 angular richness and Bony/stationarity-defect control, and the
  `O(|log r|^-1/2)` vanishing conclusion. It does not prove A5 or promote A6.
- `DASHI/Physics/Closure/NSBiotSavartShellLocalizationBoundary.agda` records
  the A6.2 theorem contract for same-shell Biot-Savart strain multiplier
  ownership, off-shell leakage decay, Calderon-Zygmund kernel control,
  Type-I `L^{3,inf}` dependence, and diagonal-to-Abel compatibility.
  `NSBiotSavartShellLocalizationProxyHarnessResult.agda` binds the paired
  finite diagnostic harness.  These do not prove the CZ localization
  estimate, A6, residual depletion, or Clay NS.
- `DASHI/Physics/Closure/NSBonyParaproductA6RepairBoundary.agda` records the
  corrected A6.2 paraproduct route after naive whole-strain same-shell
  localization failure.  It keeps the Bony, resonant, high-frequency, A6,
  residual-depletion, and Clay flags fail-closed.
- `DASHI/Physics/Closure/NSPointwiseToAbelAveragingBoundary.agda` records the
  A6 hard subtheorem: replace localized pointwise `omega . S omega` by the
  Abel/shell mean `int lambda(c)(2 kappa^2 - 1) dmu_r` with diagonal,
  off-diagonal, localization, pressure, and shell-mixing errors controlled.
  This is the current hardest NS transfer theorem and remains unproved.
- `DASHI/Physics/Closure/NSA6A4BiasToLeakageClosureCompositeBoundary.agda`
  is the lightweight A6 handoff receipt. It records the proof content for the
  localized enstrophy ODE decomposition, Bony/paraproduct correction,
  pointwise-to-Abel transfer, A5 bias absorption into dissipation, and the
  assembled inequality
  `∂t D_r + (ε0/4) c_lambda D_r <= C D_r^(1+α)`. It remains fail-closed.
- `DASHI/Physics/Closure/NSA7ResidualDepletionGronwallBoundary.agda` is the
  lightweight 15s-safe A7 receipt. It records the Gronwall substitution
  `Z = D_r^(-α)`, the linearized inequality, the smallness threshold
  `(β/C)^(1/α)`, monotone depletion below threshold, and the blowup
  contradiction. It keeps A7/A8/A9/Clay false.
- `DASHI/Physics/Closure/NSA8FullLocalDefectMonotonicityBoundary.agda` is the
  lightweight 15s-safe A8 receipt. It records annular localization control,
  the CKN annulus split, the recursion
  `D_{theta r} <= q(theta,M) D_r + C(R,M) D_r^(1+alpha)` with
  `q = (theta^2 + C M)/(1 + C M) < 1`, and the iterative
  `D_{theta^k r} -> 0` consequence. It keeps A8/A9/Clay false.
- `DASHI/Physics/Closure/NSA9CKNBKMClosureBoundary.agda` is the lightweight
  15s-safe A9 receipt. It records the closure handoff from iterated A8 decay
  to local vorticity vanishing, local harmonicity of velocity, elliptic
  regularity, and the standard CKN/BKM contradiction. It keeps A9/Clay false.
- `DASHI/Physics/Closure/NSA8A9MonotonicityClosureTheoremLadderBoundary.agda`
  is the lightweight ladder receipt tying the intended A8 -> A9 ->
  contradiction -> no-Type-I-blowup chain into one fail-closed surface.  It
  does not promote A8, A9, contradiction, NS Clay, or terminal authority.
- The A6 split now has three child boundary receipts:
  `NSDiagonalStretchingToAbelMeanBoundary.agda` for diagonal shell
  identification, `NSOffDiagonalShellAbsorptionBoundary.agda` for LP /
  Coifman-Meyer / epsilon-gradient absorption of non-diagonal terms, and
  `NSAbelShellMixingLLNBoundary.agda` for the Abel-window mixing /
  `O(N_eff^-1/2)` LLN target.  The paired diagnostic
  `scripts/ns_pointwise_to_abel_averaging_proxy_harness.py` is routed through
  the manifest and rejects a correlated positive-bias counterprofile; it is
  not a PDE proof.
- The A6 split now also has
  `NSLocalizationPressureCommutatorBoundary.agda` for cutoff, Leray pressure,
  commutator, boundary annulus, and pressure-tail controls, plus
  `NSPointwiseToAbelCompositeA6Boundary.agda` tying the four child blockers
  back to `NSPointwiseToAbelAveragingBoundary`.  The receipt
  `NSPointwiseToAbelAveragingProxyHarnessResult.agda` records the existing
  pointwise-to-Abel proxy harness.  The new diagnostic
  `scripts/ns_localization_pressure_commutator_proxy_harness.py` is routed
  through the manifest and separates refinement-decaying localized profiles
  from persistent pressure-tail/cutoff-commutator bad profiles.  These are
  diagnostics and dependency receipts only; A6, residual depletion, local
  monotonicity, and Clay NS remain unproved.
- `DASHI/Physics/Closure/NSPressureCommutatorEstimateContractBoundary.agda`
  sharpens the localization/pressure child into the explicit theorem contract
  for `[P_j, phi] R_i R_l`, local Calderon-Zygmund pressure, harmonic pressure
  tail, annular cutoff, epsilon-gradient absorption, and lower-order residual
  routing.  `DASHI/Physics/Closure/NSPressureTailAbsorptionProxyHarnessResult.agda`
  records the diagnostic split from
  `scripts/ns_pressure_tail_absorption_proxy_harness.py`.  These do not prove
  pressure-tail absorption, pressure commutator estimates, A6, residual
  depletion, or Clay NS.
- `DASHI/Physics/Closure/NSCutoffRieszCommutatorKernelProxyHarnessResult.agda`
  records the finite kernel diagnostic for
  `scripts/ns_cutoff_riesz_commutator_kernel_proxy_harness.py`: smooth
  compact, separated-annulus, and shell-recentered profiles pass, while rough
  cutoff, no-cancellation, and annulus-touching-core profiles fail.  This is
  not a cutoff/Riesz commutator theorem.
- `DASHI/Physics/Closure/NSHarmonicPressureTailAbsorptionEstimateBoundary.agda`
  records the harmonic pressure-tail theorem contract: decomposition,
  exterior annulus decay, `Q_r` mean subtraction, scale-separated absorption,
  epsilon-gradient split, pressure-tail budget routing, and no pressure sign
  claim.  `scripts/ns_harmonic_pressure_tail_decay_proxy_harness.py` is the
  paired diagnostic only.
- `DASHI/Physics/Closure/NSPressureLocalizationSubBudgetCompositeBoundary.agda`
  composes the pressure/localization sub-budget across cutoff/Riesz
  commutator, local Calderon-Zygmund core, harmonic tail, pressure tail,
  annular cutoff, epsilon-gradient absorption, and Abel recentering /
  lower-order routing.  `NSPressureLocalizationSubBudgetProxyHarnessResult`
  records the synthetic aggregate harness only.  These do not prove the
  pressure sub-budget, localization theorem, A6, residual nonpositivity, or
  Clay NS.
- `DASHI/Physics/Closure/NSPressureSubBudgetComponentSensitivityProxyHarnessResult.agda`
  records the component-sensitivity sweep for the same seven pressure /
  localization sub-budgets.  It is routed through the manifest as diagnostic
  evidence only and does not prove component sensitivity, localization, A6,
  residual depletion, or Clay NS.
- `DASHI/Physics/Closure/NSA6ErrorBudgetCompositeBoundary.agda` records the
  current aggregate A6 budget taxonomy: diagonal residual, off-diagonal
  absorption, Abel LLN variance, localization cutoff, pressure commutator,
  pressure tail, and Abel tail/recentering.  The diagnostic
  `scripts/ns_a6_error_budget_proxy_harness.py` is routed through the manifest
  and separates decaying aggregate profiles from bad single-component
  obstructions.  It is not an aggregate PDE estimate.
- `DASHI/Physics/Closure/NSA6TheoremLadderBoundary.agda` records the theorem
  ladder from A6 child estimates through aggregate budget,
  pointwise-to-Abel, compensated leakage, residual nonpositivity, local
  monotonicity, and CKN/BKM closure.  Every theorem and promotion flag remains
  false.
- `DASHI/Physics/Closure/YMAdmissibleBTBoundaryConventionBoundary.agda`
  records the finite BT boundary-convention precondition exposed by local
  calcs.  It does not prove the Hamiltonian domination, reflection positivity,
  OS transfer, or mass gap.
- `DASHI/Physics/Closure/YMFiniteGaugeQuotientHamiltonianPreconditionBoundary.agda`
  records the first YM operator-theoretic preconditions after the boundary
  convention: full-degree/Killing domain, finite gauge quotient, self-adjoint
  finite Hamiltonian, holonomy/action sector split, and the Hamiltonian
  domination inequality.  It is not a YM mass-gap proof.
- `DASHI/Physics/Closure/YMSelfAdjointFiniteHamiltonianBoundary.agda` records
  the next YM operator proof target: finite domain, symmetric form, gauge
  quotient descent, self-adjoint matrix/operator, and discrete spectrum.  It
  does not prove Hamiltonian domination, OS transfer, continuum transfer, or
  YM Clay.
- `DASHI/Physics/Closure/YMFiniteSelfAdjointHamiltonianProxyHarnessResult.agda`
  records the diagnostic for
  `scripts/ym_finite_selfadjoint_hamiltonian_proxy_harness.py`: one symmetric
  quotient-stable finite matrix proxy passes, while nonsymmetric and
  domain-unstable cases fail.  The paired finite domination diagnostic
  `scripts/ym_hamiltonian_domination_proxy_harness.py` is routed through the
  manifest and checks a good matrix inequality margin against weak-H and
  near-zero-sector failures.  Neither proves YM self-adjointness,
  Hamiltonian domination, OS transfer, continuum transfer, or Clay YM.
- `DASHI/Physics/Closure/YMHamiltonianDominationProxyHarnessResult.agda` and
  `DASHI/Physics/Closure/YMHamiltonianDominationCompositeBoundary.agda` record
  the finite domination diagnostic and dependency chain.  The chain is
  admissible boundary -> finite self-adjoint operator -> holonomy/action
  sector -> domination inequality -> reflection positivity/OS -> continuum no
  spectral pollution, all fail-closed.
- `DASHI/Physics/Closure/YMHamiltonianDominationErrorBudgetBoundary.agda`
  records the finite domination error budget: self-adjoint defect,
  quotient-domain residual, holonomy/action residuals, negative `E_d` budget,
  spectral margin, reflection-positive transfer residual, and OS/continuum
  no-spectral-pollution residual.  It does not prove Hamiltonian domination,
  reflection-positive transfer, OS/continuum transfer, or YM Clay.
- `DASHI/Physics/Closure/YMDominationSpectralMarginProxyHarnessResult.agda`
  records the finite symmetric-matrix spectral-margin diagnostic for the YM
  domination budget.  `YMSpectralMarginErrorBudgetCompositeBoundary.agda`
  imports that receipt and records the spectral margin -> domination ->
  reflection positivity -> OS/continuum -> no-spectral-pollution chain while
  keeping all theorem and promotion flags false.
- `DASHI/Physics/Closure/YMSpectralMarginBoundarySensitivityProxyHarnessResult.agda`
  records the finite boundary-sensitivity sweep around that spectral-margin
  proxy.  It varies kinetic, holonomy, `E_d`, and pollution budgets and keeps
  boundary sensitivity, spectral margin, Hamiltonian domination,
  OS/continuum transfer, YM Clay, and terminal promotion false.
- `DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessDomainContract.agda`
  records the first finite-domain theorem contract after YM boundary
  sensitivity: full-degree/Killing boundary convention, BT cell domain
  closure, boundary flux cancellation, gauge-domain invariance, quotient
  descent, symmetric finite matrix, and finite self-adjointness.  It does not
  prove Hamiltonian domination, OS transfer, continuum no-pollution, YM Clay,
  or terminal promotion.
- `DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessProxyHarnessResult.agda`
  binds the Killing/full-degree boundary diagnostic to Agda while keeping
  YM-1, Hamiltonian domination, OS/continuum transfer, no spectral pollution,
  YM Clay, and terminal promotion false.
- `DASHI/Physics/Closure/YMKillingBoundaryFluxCancellationBoundary.agda`
  records the YM-1 child obligation for full-degree/Killing boundary flux
  cancellation across finite BT faces, opposing flux pairing,
  gauge-domain preservation, induced-ball collapse exclusion, and
  self-adjointness routing.  The flux-cancellation theorem and YM-1 remain
  open.
- `DASHI/Physics/Closure/YMKillingBoundaryOppositeFaceInvolutionBoundary.agda`
  records the next YM-1 sub-obligation: construct the opposite-face
  involution, prove full-degree/Killing weight preservation, orientation-sign
  cancellation, and gauge compatibility before flux cancellation can feed
  finite self-adjointness.
- `DASHI/Physics/Closure/YMKillingBoundaryWeightPreservationBoundary.agda`
  isolates the full-degree/Killing weight equality target under the
  opposite-face involution, keeping orientation-sign cancellation and gauge
  compatibility separate from the weight formula itself.
- `DASHI/Physics/Closure/YMKillingBoundarySelfAdjointnessTheoremBoundary.agda`
  is the lightweight 15s-safe YM-1 receipt.  It records the theorem content
  only: full-degree/Killing boundary convention, opposite-face involution,
  weight/orientation/flux control, gauge-domain preservation, quotient
  descent, symmetric finite Hamiltonian, and finite self-adjointness on the
  quotient.  It keeps domination, OS transfer, YM Clay, and terminal
  promotion false.
- `DASHI/Physics/Closure/GluingResidualForcesFourPointCancellationBoundary.agda`
  records the unification gluing-residual target.  It does not prove the
  four-point law or quadratic emergence.
- `DASHI/Physics/Closure/GluingOperatorLinearityOnDefectQuotientBoundary.agda`
  records the U-1a quotient-linearity blocker: define the admissible defect
  quotient and prove the gluing operator respects zero, addition, scalars, and
  representatives before four-point cancellation can be attempted.
- `DASHI/Physics/Closure/GluingOperatorLinearityProxyHarnessResult.agda`
  records the finite diagnostic for `scripts/gluing_operator_linearity_proxy_harness.py`:
  quotient-linear proxies pass and nonlinear representative-dependent
  counterexamples fail additivity/scalar/representative/four-point checks.
  It does not prove the real quotient theorem.
- `DASHI/Physics/Closure/UnificationGluingLinearityCompositeBoundary.agda`
  records the unification first-rung dependency chain from admissible defect
  quotient and gluing-operator compatibility to four-point cancellation,
  parallelogram, quadratic emergence, and signature/Clifford consumers.  It
  does not prove any of those theorem steps.
- `scripts/unification_gluing_quotient_admissibility_proxy_harness.py` is the
  current finite proxy for quotient admissibility.  It separates a
  representative-invariant linear quotient case from representative leakage,
  nonlinear gluing, and two-homogeneous norm-like near-miss bad cases; it is
  not an Agda proof of quotient admissibility or four-point cancellation.
- `DASHI/Physics/Closure/UnificationGluingQuotientAdmissibilityProxyHarnessResult.agda`
  binds that quotient-admissibility diagnostic to Agda while keeping quotient
  admissibility, gluing linearity, four-point cancellation, parallelogram,
  quadratic emergence, and terminal promotion false.
- `DASHI/Physics/Closure/UnificationGluingCrossTermNullClassBoundary.agda`
  records the next U-1a sub-obligation: prove
  `G(s1+s2)-G(s1)-G(s2)` lies in the null class of the admissible defect
  quotient.  Four-point cancellation, parallelogram, quadratic emergence,
  signature/Clifford consumers, and terminal promotion remain blocked.
- `DASHI/Physics/Closure/UnificationCrossTermNullityLightweightBoundary.agda`
  is the lightweight 15s-safe U-1a receipt.  It records the theorem content
  only: admissible defect quotient, gluing operator `G`, actual cross-term,
  null-class target, representative invariance, null transport, and the
  modulo-null linearity consumer.  It keeps four-point cancellation,
  parallelogram, quadratic emergence, and terminal promotion false.
- `DASHI/Physics/Closure/UnificationCrossTermToFourPointCompositeBoundary.agda`
  composes cross-term-null through quotient linearity, four-point
  cancellation, parallelogram, quadratic emergence, and signature/Clifford
  consumers without promoting the unification theorem.
- `DASHI/Physics/Closure/UnificationGluingCrossTermLinearityLiftBoundary.agda`
  records the U-1a lift from cross-term-null vocabulary to modulo-null
  quotient linearity and the downstream four-point cancellation dependency.
  Representative invariance, null stability, cross-term nullity, true
  linearity, parallelogram, quadratic emergence, and terminal promotion remain
  open.
- `DASHI/Physics/Closure/UnificationNullClassStabilityBoundary.agda` records
  the null-class operation and gluing-stability prerequisites needed before
  cross-term nullity can be transported into modulo-null quotient linearity.
  Null representative relation, operation stability, `G`-stability, quotient
  equality transport, four-point cancellation, and terminal promotion remain
  open.
- `DASHI/Physics/Closure/UnificationNullToQuotientEqualityTransportBoundary.agda`
  records the transport from null cross-term evidence to quotient equality
  and modulo-null linearity.  Representative invariance, congruence under
  `G`, transport into four-point functionals, and terminal promotion remain
  open.
- `DASHI/Physics/Closure/UnificationQuotientFourPointStressProxyHarnessResult.agda`
  records the four-point stress diagnostic for representative-shift,
  nonlinear-gluing, p-norm, and asymmetric-cross-term near misses.
  `DASHI/Physics/Closure/UnificationFourPointStressCompositeBoundary.agda`
  imports that receipt and records the quotient-admissibility ->
  representative-invariance -> gluing-linearity -> four-point-cancellation ->
  parallelogram -> quadratic-emergence -> signature/Clifford chain.  It does
  not prove any theorem step.

## Safe Routine Targets

These are the preferred modules for focused validation while working on the
canonical closure spine:

- `DASHI/Geometry/CausalForcesLorentz31.agda`
- `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`
- `DASHI/Physics/Signature31IntrinsicShiftInstance.agda`
- `DASHI/Physics/Signature31FromShiftOrbitProfile.agda`
- `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
- `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
- `DASHI/Physics/CliffordEvenLiftBridge.agda`
- `DASHI/Physics/Closure/CliffordToEvenWaveLiftBridgeTheorem.agda`
- `DASHI/Physics/Closure/CanonicalContractionToCliffordBridgeTheorem.agda`
- `DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda`
- `DASHI/Physics/Closure/Canonical/LocalProgramBundle.agda`
- `DASHI/Physics/Closure/Canonical/Ladder.agda`
- `DASHI/Physics/Closure/PhysicsClosureSummary.agda`
- `DASHI/Constants/Registry.agda`
- `DASHI/Interop/CategoricalInterlinkLayer.agda`
- `DASHI/Promotion/NumericAndAuthorityObligations.agda`
- `DASHI/Promotion/ClassicalFieldObligations.agda`
- `DASHI/Promotion/QuantumQFTObligations.agda`
- `DASHI/Promotion/ChemistryBiologyObligations.agda`
- `DASHI/Promotion/Gate3ClayObligations.agda`
- `DASHI/Promotion/StandardModelTerminalObligations.agda`
- `DASHI/Promotion/NumericMeasuredAuthorityBinding.agda`
- `DASHI/Promotion/MaxwellExteriorCalculusAdapter.agda`
- `DASHI/Promotion/FiniteQuantumSchrodingerBornAdapter.agda`
- `DASHI/Promotion/ChemistryQuantitativeAdapter.agda`
- `DASHI/Promotion/EmpiricalRuntimeReplayAdapter.agda`
- `DASHI/Promotion/Gate3StandardModelClayEvidenceReducer.agda`
- `DASHI/Promotion/NumericAuthorityTokenIntake.agda`
- `DASHI/Promotion/MaxwellHodgeSourceCalibration.agda`
- `DASHI/Promotion/QuantumFiniteToGeneralBoundary.agda`
- `DASHI/Promotion/ChemistrySpectroscopyAuthorityIntake.agda`
- `DASHI/Promotion/EmpiricalReplayAcceptanceCriteria.agda`
- `DASHI/Promotion/ClayProofTranslationReducer.agda`
- `DASHI/Promotion/FiniteQuantumPhysicalScopeDecision.agda`
- `DASHI/Promotion/GRBoundaryClarification.agda`
- `DASHI/Promotion/BiologyFiniteScopeClarification.agda`
- `DASHI/Promotion/ChemistryFiniteRuleTargets.agda`
- `DASHI/Physics/Closure/YMCompletionBoundaryTightening.agda`
- `DASHI/Physics/Closure/NSMigrationInitiationThresholdConstantsReceipt.agda`
- `DASHI/Physics/Closure/YMExternalAcceptancePacketNormalization.agda`
- `DASHI/Promotion/StandardModelFiniteRepresentationNarrowing.agda`
- `DASHI/Promotion/MaxwellHodgeSourceConservationObligations.agda`
- `DASHI/Promotion/NumericMeasuredAuthorityTokenNormalization.agda`
- `DASHI/Promotion/ChemistryAuthorityBinding.agda`
- `DASHI/Promotion/DefectQuadraticClosureDependencyIndex.agda`
- `DASHI/Promotion/DownloadedNewAdditionsReferenceIndex.agda`
- `DASHI/Physics/Closure/NSSprint150SourceViscosityBalanceReceipt.agda`
- `DASHI/Promotion/ChemistryFiniteComputationSurface.agda`
- `DASHI/Promotion/StandardModelFiniteAnomalyHyperchargeCheck.agda`
- `DASHI/Promotion/StandardModelFirstPrinciplesGapIndex.agda`
- `DASHI/Promotion/StandardModelUniquenessCountermodelBoundary.agda`
- `DASHI/Promotion/StandardModelHiggsYukawaParameterFrontier.agda`
- `DASHI/Promotion/StandardModelGaugeCouplingAuthorityFrontier.agda`
- `DASHI/Promotion/StandardModelObservableAuthorityBridge.agda`
- `DASHI/Promotion/StandardModelArchiveContextBinding.agda`
- `DASHI/Promotion/StandardModelPrototypeSourceIntake.agda`
- `DASHI/Promotion/StandardModelHiggsHEPDataReceiptAdapter.agda`
- `DASHI/Promotion/StandardModelHiggsCovariantComparisonLaw.agda`
- `DASHI/Promotion/MaxwellFiniteExteriorChainStrengthening.agda`
- `DASHI/Promotion/UnificationCriticalPathReceipt.agda`
- `DASHI/Physics/Closure/DefectQuadraticParallelogramCriticalSeam.agda`
- `DASHI/Physics/Closure/DefectCriticalSeamIdentityDynamicsInstance.agda`
- `DASHI/Physics/Closure/DefectCriticalSeamIdentityQuotientHierarchy.agda`
- `DASHI/Physics/Closure/DefectCriticalSeamConcreteShiftReducer.agda`
- `DASHI/Physics/Closure/DefectCriticalSeamIdentityCompositeReceipt.agda`
- `DASHI/Physics/Closure/DefectCriticalSeamGeneralizationObstruction.agda`
- `DASHI/Physics/Closure/UnificationNextAnalyticCalculationIndex.agda`
- `DASHI/Physics/Closure/YMStrictSelectedHodgeAlgebraLaws.agda`
- `DASHI/Physics/Closure/YMStrictSelectedHodgeVariationPairing.agda`
- `DASHI/Physics/Closure/BTFiniteHodgeStarObligation.agda`
- `DASHI/Physics/Closure/BTFiniteHodgeEffectiveActionTheoremBoundary.agda`
- `DASHI/Physics/Closure/BTFiniteBuildingYMGapTransferBoundary.agda`
- `DASHI/Physics/Closure/BTNSBoundaryDefectLeakageTarget.agda`
- `DASHI/Physics/Closure/ClopenHolographicEffectiveFieldTheoryBoundary.agda`
- `DASHI/Physics/Closure/FiniteDepthBoundaryObservablePromotionPipeline.agda`
- `DASHI/Physics/Closure/NSRankOneProjectionCommutatorFormula.agda`
- `DASHI/Physics/Closure/NSSigmaNonRadialCommutatorLowerBoundTarget.agda`
- `DASHI/Physics/Closure/NSTransverseSigmaNeighborhoodGeometry.agda`
- `DASHI/Physics/Closure/NSNonRadialityQuantificationAverage.agda`
- `DASHI/Physics/Closure/NSMicrolocalDefectMassConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSTrueLerayTriadicZeroModeClassificationBoundary.agda`
- `DASHI/Physics/Closure/NSAbelTriadicDefectMeasureConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSBoundedAbelMassEstimateBoundary.agda`
- `DASHI/Physics/Closure/NSAbelShellMixingLLNBoundary.agda`
- `DASHI/Physics/Closure/NSDiagonalStretchingToAbelMeanBoundary.agda`
- `DASHI/Physics/Closure/NSOffDiagonalShellAbsorptionBoundary.agda`
- `DASHI/Physics/Closure/NSQuantitativeStationarityRateBoundary.agda`
- `DASHI/Physics/Closure/NSQuantitativeStationarityRateProxyHarnessResult.agda`
- `DASHI/Physics/Closure/NSTriadicShellBernsteinHolderBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianOutputSupportTransferBoundary.agda`
- `DASHI/Physics/Closure/NSPointwiseToAbelAveragingBoundary.agda`
- `DASHI/Physics/Closure/NSTriadicCompensatedLeakageIdentityBoundary.agda`
- `DASHI/Physics/Closure/NSSignAntisymmetryExactIdentityBoundary.agda`
- `DASHI/Physics/Closure/NSCascadeTransversalityCollapseBoundary.agda`
- `DASHI/Physics/Closure/ProjectionNonlocalityDefectLaplacianZeroModeSheaf.agda`
- `DASHI/Physics/Closure/NSZeroModeSetClassificationBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianRadialZeroModeAuthorityBoundary.agda`
- `DASHI/Physics/Closure/NSTangentialZeroModePressureStarvationBoundary.agda`
- `DASHI/Physics/Closure/NSTrueLerayTriadicDefectSymbol.agda`
- `DASHI/Physics/Closure/NSCascadeClosedZeroModeOutputWidthBoundary.agda`
- `DASHI/Physics/Closure/NSTriadicAngularDefectSheafLeakageBoundary.agda`
- `DASHI/Physics/Closure/NSTriadicLeakageSquareFunctionCoercivityBoundary.agda`
- `DASHI/Physics/Closure/FiniteGaugeHodgeAdjointCompatibility.agda`
- `DASHI/Physics/Closure/BTFiniteMetricGaugeCompatibilityKappaBoundary.agda`
- `DASHI/Physics/Closure/YMWeightedBTAdjointKappaCalculation.agda`
- `DASHI/Physics/Closure/YMSelfAdjointHamiltonianQuotientGapBoundary.agda`
- `DASHI/Physics/Closure/YMSelfAdjointFiniteHamiltonianBoundary.agda`
- `DASHI/Physics/Closure/YMHamiltonianDominatesFiniteHodgeDefectBoundary.agda`
- `DASHI/Physics/Closure/YMAdmissibleBTBoundaryConventionBoundary.agda`
- `DASHI/Physics/Closure/YMFiniteGaugeQuotientHamiltonianPreconditionBoundary.agda`
- `DASHI/Physics/Closure/GluingResidualForcesFourPointCancellationBoundary.agda`
- `DASHI/Physics/Closure/GluingOperatorLinearityOnDefectQuotientBoundary.agda`
- `DASHI/Physics/Closure/GluingOperatorLinearityProxyHarnessResult.agda`
- `DASHI/Physics/Closure/CompatibilityLeakageCoercivityTrichotomy.agda`
- `DASHI/Physics/Closure/DefectHierarchyParallelogramGeneralizationBoundary.agda`
- `DASHI/Physics/Closure/DefectFourPointParallelogramLawBoundary.agda`
- `DASHI/Physics/Closure/DNAClifford256StructuralCoincidenceReceipt.agda`
- `DASHI/Physics/Closure/P0ClayFiniteHodgeNSTopologicalStackReceipt.agda`
- `DASHI/Physics/Closure/ProjectionNonlocalityLeakagePrincipleBoundary.agda`
- `DASHI/Physics/Closure/Sprint166ProjectionNonlocalityLeakagePrincipleReceipt.agda`
- `DASHI/Physics/Closure/YMStrictSelectedBoundaryCancellationCriterion.agda`
- `DASHI/Physics/Closure/YMStrictSelectedNonzeroActionVariation.agda`
- `DASHI/Physics/Closure/YMStrictSelectedSourceCurrentCoupling.agda`
- `DASHI/Physics/Closure/YMFiniteSelectedPairingToRealCarrierBoundary.agda`
- `DASHI/Physics/Closure/YMStrictSelectedMatterCurrentAuthorityBridge.agda`
- `DASHI/Physics/Closure/YMMatterCurrentConservationAuthorityBoundary.agda`
- `DASHI/Physics/Closure/YMRealSourcedDStarFEquationBoundary.agda`
- `DASHI/Physics/Closure/YMConditionalMatterAuthorityToRealDStarF.agda`
- `DASHI/Physics/Closure/YMSourcedEquationToHamiltonianQuotientBoundary.agda`

Sprint165 P0 stack executable ledgers:

- `scripts/p0_clay_finite_hodge_ns_stack.py`
- `scripts/ns_clay_microlocal_gap_chain.py`
- `scripts/finite_hodge_variation_gap_chain.py`
- `scripts/projection_nonlocality_leakage_principle.py`
- `scripts/ns_projection_pressure_commutator_chain.py`
- `scripts/ym_bt_hodge_gauge_commutator_chain.py`

The P0 stack originally recorded `BTFiniteHodgeVariationTheorem` and
`AngularDegeneracyPressureCommutatorGain` as broad next calculations. The
current narrowed validation frontier is
`NSTrueLerayTriadicDefectSymbol`,
`NSCascadeClosedZeroModeOutputWidthBoundary`,
`NSTriadicAngularDefectSheafLeakageBoundary`, and
`NSTriadicLeakageSquareFunctionCoercivityBoundary` for the corrected NS
triadic interaction-symbol/sheaf/square-function route,
`NSMicrolocalDefectMassConstructionBoundary` for the NS LP/semiclassical
measure bootstrap, `YMSelfAdjointHamiltonianQuotientGapBoundary` for YM
transfer/OS/self-adjoint quotient work, and
`DefectHierarchyParallelogramGeneralizationBoundary` for the core hierarchy
consistency seam. Maxwell, YM/Yang-Mills, NS/Navier-Stokes, observable,
continuum, Clay, and terminal promotion flags remain false.
Sprint166 records the shared projection/nonlocality leakage frontier:
`[Pi_+, R_i R_j]` is the NS matrix/eigenbundle pressure commutator target,
`[d_A,*]F_A` is the YM/BT finite Hodge-gauge compatibility defect target, and
scalar Fourier cutoffs are explicitly not the source of the pressure gain.
The triadic correction also rejects ordinary Calderon-Zygmund/Littlewood-Paley
boundedness as a source of strict `C - c` depletion; the strict target is a
bilinear leakage square-function/coercivity estimate with a separate
Carleson/angular embedding gap.
- `DASHI/Physics/Closure/YMSelfAdjointHamiltonianQuotientRequirementNormalizer.agda`
- `DASHI/Promotion/YMStrictHodgeVariationBlockerIndex.agda`
- `DASHI/Promotion/NumericAuthorityPayloadValidator.agda`
- `DASHI/Promotion/FiniteQuantumQFTScopedClosure.agda`
- `DASHI/Promotion/ObligationIndex.agda`
- `DASHI/Unified/StellarCompositionProxyReceipt.agda`
- `DASHI/Unified/CrossScaleMatterPhysics.agda`
- `DASHI/Unified/Everything.agda`
- `DASHI/Algebra/TritTriTruthBridge.agda`
- `DASHI/Algebra/MoonshineBridge.agda`
- `DASHI/Algebra/StageQuotient.agda`
- `DASHI/Physics/TritCarrierBridge.agda`
- `DASHI/Physics/FascisticContractionInstance.agda`
- `DASHI/Physics/CRTPeriodJFixedBridge.agda`
- `DASHI/Physics/Closure/TemporalSheafProofObligations.agda`
- `DASHI/Physics/Closure/P0BlockerObligationIndex.agda`
- `DASHI/Physics/Closure/W3AcceptedAuthorityRouteNarrowing.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationRouteNarrowing.agda`
- `DASHI/Physics/Closure/P0SecondaryObligationQueue.agda`
- `DASHI/Physics/Closure/UnifiedEnergyFunctionalSurface.agda`
- `DASHI/Physics/Closure/BlockerKillConditions.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeObservable.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeUnits.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeToyFit.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeObservableIntake.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeUnitsIntake.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeToyFitAuthorityBoundary.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeObservableSourceDiagnostic.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeUnitsSourceDiagnostic.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeToyFitRealDatasetRouteDiagnostic.agda`
- `DASHI/Physics/Closure/EmpiricalCalibrationExternalReceiptRequestPack.agda`
- `DASHI/Physics/Closure/W3AcceptedAuthorityExternalReceiptRequestPack.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptRequestPack.agda`
- `DASHI/Physics/Closure/P0ProviderReceiptRequestIndex.agda`
- `DASHI/Physics/Closure/HEPDataProviderReceiptRequestPack.agda`
- `DASHI/Physics/Closure/HEPDataResidualBridgeWorkerQueue.agda`
- `DASHI/Physics/Closure/HEPDataResidualObservableClassRequest.agda`
- `DASHI/Physics/Closure/HEPDataDefectProjectionDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataResidualSourceCandidateDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataResidualProviderReceiptRequestPack.agda`
- `DASHI/Physics/Closure/HEPDataNonCollapseObservableObligation.agda`
- `DASHI/Physics/Closure/HEPDataResidualComparisonLawRequest.agda`
- `DASHI/Physics/Closure/HEPDataEmpiricalResidualBridgeCore.agda`
- `DASHI/Physics/Closure/HEPDataResidualProviderPayloadIntake.agda`
- `DASHI/Physics/Closure/HEPDataResidualBridgeAuthorityGate.agda`
- `DASHI/Physics/Closure/HEPDataExternalResidualWitnessPayload.agda`
- `DASHI/Physics/Closure/HEPDataExternalResidualWitnessCandidateDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataResidualObservableClassCandidateDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataResidualObservableClassProtoReceipt.agda`
- `DASHI/Physics/Closure/HEPDataResidualObservableClassExternalAlignment.agda`
- `DASHI/Physics/Closure/HEPDataEmpiricalAuthorityReceiptCollation.agda`
- `DASHI/Physics/Closure/HEPDataCMSSMP20003ExternalSourceAuthorityReceipt.agda`
- `DASHI/Physics/Closure/HEPDataAdapterTransformReceiptRequestDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataRatioAdapterTransformReceiptRequest.agda`
- `DASHI/Physics/Closure/HEPDataPredictionFreezeProjectionRunRequest.agda`
- `DASHI/Physics/Closure/HEPDataRatioTableArtifactRequest.agda`
- `DASHI/Physics/Closure/HEPDataRatioTableArtifactReceipt.agda`
- `DASHI/Physics/Closure/HEPDataDASHIProjectionRunnerDiscovery.agda`
- `DASHI/Physics/Closure/HEPDataPredictionFreezeIdentityDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataRatioComparisonLawIntakeRequest.agda`
- `DASHI/Physics/Closure/HEPDataT43ProjectionRunnerContract.agda`
- `DASHI/Physics/Closure/HEPDataT43ProjectionRunnerImplementationAttempt.agda`
- `DASHI/Physics/Closure/HEPDataT43PredictionAPIRouteDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataT43SudakovBaselinePredictionHook.agda`
- `DASHI/Physics/Closure/HEPDataT43DASHINativeAPIRouteDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataT43DASHINativeProjectionReceipt.agda`
- `DASHI/Physics/Closure/HEPDataT43DASHINativeProjectionRunDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataT43DASHINativeComparisonDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataT43SigmaDASHIModelGapRefinementDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataT43NeutralCurrentContinuumRefinementDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataT43PosteriorShapeResponseDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataT45HoldoutValidationDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataMassWindowGeneralPredictionLawDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataMassWindowGeneralPredictionRunDiagnostic.agda`
- `DASHI/Physics/Closure/HEPDataObservableDefinitionReceipt.agda`
- `DASHI/Physics/Closure/HEPDataPredictionFreezePolicyRequest.agda`
- `DASHI/Physics/Closure/HEPDataComparisonLawReceiptRequest.agda`
- `DASHI/Physics/Closure/W4CalibrationRatioZPeakReceiptRequestSurface.agda`
- `DASHI/Physics/Closure/W5W6PhysicsConsumerSourceInventory.agda`
- `DASHI/Physics/Closure/LilaE8RootSystemLocalSourceDiagnostic.agda`
- `DASHI/Physics/Closure/LilaE8RootSystemLatticeReceipt.agda`
- `DASHI/Physics/Closure/LilaE8InitialisationPriorNote.agda`
- `DASHI/Physics/Closure/LilaE8RootEnumeration.agda`
- `DASHI/Physics/Closure/LilaE8RootEnumerationReceiptR2.agda`
- `DASHI/Physics/Closure/LamTungE8AdapterSurface.agda`
- `DASHI/Physics/Closure/LilaE8ThetaJBridgeSurface.agda`
- `DASHI/Physics/Closure/LilaE8PhiStarProjectionReceipt.agda`
- `DASHI/Physics/Closure/SiblingEvidenceInventory.agda`
- `DASHI/Physics/Closure/SiblingEvidenceExtractionDiagnostic.agda`
- `DASHI/Physics/Closure/SiblingMathPortingMatrix.agda`
- `DASHI/Physics/Closure/CancellationPressureRetargetConsumerObligation.agda`
- `DASHI/Physics/Closure/CancellationPressureRetargetConsumerSourceDiagnostic.agda`
- `DASHI/Physics/Closure/GRQFTConsumerSourceDiagnostic.agda`
- `DASHI/Physics/Closure/GRQFTClosurePromotionReceiptRequestPack.agda`
- `DASHI/Interop/PNFResidualConsumerNextObligation.agda`
- `DASHI/Interop/PNFResidualConsumerReceiptRequestPack.agda`
- `DASHI/Physics/Closure/OriginReceiptPromotionExternalObligation.agda`
- `DASHI/Physics/Closure/OriginReceiptPromotionExternalRequestPack.agda`
- `DASHI/Physics/Closure/CancellationPressureCompatibilityNextObligation.agda`
- `DASHI/Physics/Closure/CancellationPressureRetargetConsumerAcceptanceRequestPack.agda`

Use these for routine theorem-edit loops and targeted bridge checks.

## Heavy / Certification-Only

These should not be part of normal rapid validation passes. They are closure
certification targets only:

- `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`
- `DASHI/Everything.agda`
- `DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`
- `DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda`
- `DASHI/Physics/DashiDynamicsShiftInstance.agda`
- `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda`
- `DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda`
- `DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda`
- `DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda`
- `DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda`
- `DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`

Reason:

- `PhysicsClosureValidationSummary.agda` is the known heavy aggregate closure
  summary and currently remains outside routine validation policy.
- `Everything.agda` is the authoritative top-level route, but bounded local
  checks currently time out because it eventually pulls the heavy validation
  summary path.
- The closure-recovery chain from
  `ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`
  through `KnownLimitsFullMatterGaugeTheorem.agda` and
  `AtomicPhotonuclearContactGateTheorem.agda` repeatedly drags in the expensive
  shift/observable/canonical-gauge stack and should be treated as offline-only
  unless that exact lane is the subject of the current work.
- `CanonicalP2KeyScheduleBridgeObstruction.agda` is theorem-thin logically, but
  in practice still rebuilds the same natural-charge / canonical-gauge heavy
  cone as `CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda` and
  should be treated the same way.
- `CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda` appears to
  be logically live, but it currently pulls enough of the same heavy recovery
  stack that it should stay out of routine local validation.

## Natural-Charge Heavy-Lane Rule

The current natural-charge blocker family:

- `DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda`
- `DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`

should not be run interactively without a very short cap.

Practical rule:

- if you absolutely probe one locally, use at most a `10s` timeout
- otherwise route it straight to `L2` / offline-only validation

Example:

- `timeout 10s agda -i . -l standard-library DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda`
- `timeout 10s agda -i . -l standard-library DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`

## Bounded-Only Target

- `DASHI/Physics/Closure/CanonicalStageC.agda`

This module is not banned, but it is heavy enough that bounded runs can still
time out. Use it as a checkpoint module, not as the default inner-loop target.

## Certification-Only Rule

`L2` modules are never required for:

- branch classification
- roadmap state
- theorem promotion
- staging decisions in the normal interactive loop

`L2` modules are only required for:

- closure certification
- deliberate offline coherence checks
- decomposition work on the global closure cone

Interpretation rule:

- if an `L0` or `L1` target compiles, that is enough to classify the local lane
- if an `L2` target has not been rerun recently, that does not invalidate an
  `advanced` or `blocked` lane classification
- if an `L2` target fails, that is a closure-certification event, not an excuse
  to collapse branch status back into `unknown`

## Blocker Validation Matrix

| Blocker lane | Allowed validation level | Timeout / avoidance rule |
|---|---|---|
| `W1` MDL/CR carrier | `L0/L1` targeted seam modules | Check `CanonicalToNoncanonicalMdlRetargetFinalSeamObligation.agda` when the final seam boundary changes; avoid full closure aggregates. |
| `W2` natural / `p2` / convergence | `L2` for heavy natural-charge modules, `L0/L1` for thin helper modules | Check `NaturalP2ConvergencePromotionObligation.agda` for the promotion boundary; use at most a short timeout for heavier natural-charge modules, otherwise route offline. |
| `W3` empirical adequacy | `L0/L1` targeted empirical bridge modules | Empirical sidecars do not promote theorem closure; carrier mismatch diagnostics are acceptable outputs. |
| `W4` chemistry law | `L0/L1`, except known heavy photonuclear contact dependencies | Prefer direct chemistry quotient/coupling modules; avoid `AtomicPhotonuclearContactGateTheorem` unless assigned. |
| `W5` GR/QFT consumer | `L0/L1` consumer modules, `L2` for known full matter/gauge aggregates | Check `GRQFTConsumerNextObligation.agda` when the W5 next-obligation surface changes; do not run `KnownLimitsFullMatterGaugeTheorem` as an inner-loop check. |
| `W6` ITIR/PNF consumer | `L0/L1` interop and Hecke bridge modules | Check `DASHI/Interop/PNFResidualConsumerNextObligation.agda` when the W6 receipt surface changes; no live ITIR runtime validation unless explicitly assigned. |
| `W7` claim governance | docs-only or targeted proof-obligation modules | Check `ClaimGovernancePromotionObligation.agda` when governance gates change; run `TemporalSheafProofObligations.agda` only if obligation records change. |
| `W8` origin receipt | docs-only or targeted new receipt module | Check `OriginReceiptPromotionExternalObligation.agda` when the origin promotion boundary changes; do not use `Everything.agda` as routine validation for a receipt surface. |
| `W9` cancellation-pressure seam | `L0/L1` targeted delta/arithmetic modules | Check `CancellationPressureCompatibilityNextObligation.agda`, `DeltaToQuadraticBridgeTheorem.agda`, and touched arithmetic/transport modules; avoid unrelated closure aggregates. |

Board-wide smoke target:

- `DASHI/Physics/Closure/P0BlockerObligationIndex.agda` imports the current
  W1-W9 obligation/status surfaces, including the W3/W4 route-narrowing modules
  the W5/W6/W9 secondary queue, the unified energy-functional surface, and the
  Option A/B/C empirical-calibration bridge surfaces,
  without promoting them. Use it after coordination-surface edits to confirm
  the worker-lane index still type-checks before widening to lane-specific
  checks.

Current non-promoting energy target:

- `DASHI/Physics/Closure/UnifiedEnergyFunctionalSurface.agda` records the
  shared severity/contraction/shift-energy/J-scalar Lyapunov skeleton. Check it
  directly when that coordination interface changes, then check
  `P0BlockerObligationIndex.agda`.

Current receipt-kill matrix target:

- `DASHI/Physics/Closure/BlockerKillConditions.agda` records the W1/W2/W3/W4/
  W5/W6/W8/W9 receipt-driven kill rows. Check it directly when blocker receipt
  targets or no-bypass laws change, then check `P0BlockerObligationIndex.agda`.

Current external bridge split targets:

- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeObservable.agda` records
  the Option A simple observable surface and its external measured-value /
  authority boundary.
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeUnits.agda` records the
  Option B unit/dimension-preserving calibration surface and its constructorless
  numeric-calibration authority boundary.
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeToyFit.agda` records the
  Option C finite toy-fit surface and its non-authority boundary.

Check these directly when empirical-calibration bridge interfaces change, then
check `P0BlockerObligationIndex.agda`.

Current external bridge intake targets:

- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeObservableIntake.agda`
  records the Option A measured-value / witness / authority / match-proof
  intake receipt.
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeUnitsIntake.agda` records
  the Option B unit-calibration intake receipt and consumer wiring target.
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeToyFitAuthorityBoundary.agda`
  records that Option C toy-fit adequacy is not external authority and names
  the real dataset receipt route through W3/W8.

Check these directly when intake receipt shapes change, then check
`P0BlockerObligationIndex.agda`.

Current source diagnostic / consumer-obligation targets:

- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeObservableSourceDiagnostic.agda`
  records that current sources do not provide the Option A measured-observable
  receipt fields.
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeUnitsSourceDiagnostic.agda`
  records that current sources do not provide the Option B unit-calibration
  receipt fields.
- `DASHI/Physics/Closure/EmpiricalCalibrationBridgeToyFitRealDatasetRouteDiagnostic.agda`
  records that current sources do not provide the W3/W8 real-dataset authority
  route receipts.
- `DASHI/Physics/Closure/CancellationPressureRetargetConsumerObligation.agda`
  records the downstream consumer acceptance required for the W9 pressure-
  compatible retarget receipt.
- `DASHI/Physics/Closure/EmpiricalCalibrationExternalReceiptRequestPack.agda`
  consolidates the A3/B3/C3 external receipt request fields without supplying
  the missing authority, calibration, validation, or origin receipts.
- `DASHI/Physics/Closure/GRQFTConsumerSourceDiagnostic.agda` records W5 GR/QFT
  closure-promotion source availability and keeps the constructorless authority
  gate explicit.
- `DASHI/Interop/PNFResidualConsumerReceiptRequestPack.agda` packages the W6
  runtime payload fields required before a receipt-backed PNF residual consumer
  can be built.
- `DASHI/Physics/Closure/CancellationPressureRetargetConsumerSourceDiagnostic.agda`
  records that current W9 retarget consumer interface and acceptance receipt
  sources are missing.
- `DASHI/Physics/Closure/GRQFTClosurePromotionReceiptRequestPack.agda`
  packages the W5 closure-promotion receipt payload required from an external
  provider.
- `DASHI/Physics/Closure/OriginReceiptPromotionExternalRequestPack.agda`
  packages the W8 origin-promotion external receipt payload required from an
  external provider.
- `DASHI/Physics/Closure/CancellationPressureRetargetConsumerAcceptanceRequestPack.agda`
  packages the W9 retarget consumer interface and acceptance receipt payload
  required from an external provider.
- `DASHI/Physics/Closure/W3AcceptedAuthorityExternalReceiptRequestPack.agda`
  packages the W3 accepted-authority external receipt payload required from an
  external provider.
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptRequestPack.agda`
  packages the W4 Candidate256 physical-calibration receipt payload required
  from an external provider.
- `DASHI/Physics/Closure/P0ProviderReceiptRequestIndex.agda` co-locates all
  provider-facing P0 request packs without constructing any provider receipt.
- `DASHI/Physics/Closure/W3AcceptedAuthorityProviderAttempt.agda` records the
  diagnostic-only W3 provider attempt and keeps accepted authority, B4
  promotion, origin promotion, and bridge fields external.
- `DASHI/Physics/Closure/W4PhysicalCalibrationProviderAttempt.agda` records the
  diagnostic-only W4 provider attempt and keeps calibration authority, physical
  units, factorization, and dimensional preservation external.
- `DASHI/Interop/PNFResidualConsumerRuntimeProviderAttempt.agda` records the
  diagnostic-only W6 runtime provider attempt and keeps concrete runtime PNF
  payload fields external.
- `DASHI/Physics/Closure/EmpiricalCompatibilityOptionAProviderAttempt.agda`
  records the diagnostic-only Option A measured-observable provider attempt and
  keeps measured value, authority, calibrated state, and match proof external.
- `DASHI/Physics/Closure/EmpiricalCompatibilityOptionBProviderAttempt.agda`
  records the diagnostic-only Option B unit-calibration provider attempt and
  keeps unit carrier, dimensional law, authority, and validation external.
- `DASHI/Physics/Closure/EmpiricalCompatibilityOptionCProviderAttempt.agda`
  records the diagnostic-only Option C real-dataset authority provider attempt
  and keeps W3/W8 authority and validation receipts external.
- `DASHI/Physics/Closure/HEPDataEmpiricalSourceCandidateDiagnostic.agda`
  records that local HEPData / `MeasurementSurface` source candidates are
  present while `HEPDataObservable` schema, checksums, golden conformance
  tests, projection, units, comparison law, ITIR authority adapter, and
  accepted authority receipts remain absent.
- `DASHI/Physics/Closure/HEPDataBridgeWorkerQueue.agda` records the assigned
  HEP-A through HEP-F bridge lanes without constructing receipts.
- `DASHI/Physics/Closure/HEPDataObservableSchema.agda` records the HEP-A
  observable schema/checksum request surface and its W3/W8 authority gates.
- `DASHI/Physics/Closure/HEPDataObservableSelectionDiagnostic.agda` records
  the HEP-B observable/table-column selection diagnostic and keeps concrete
  selection blocked on checksum binding and accepted authority.
- `DASHI/Physics/Closure/HEPDataUnitCalibrationRequirementDiagnostic.agda`
  records the HEP-C unit/dimension/calibration requirement diagnostic and
  keeps unit labels separate from physical-unit authority.
- `DASHI/Physics/Closure/HEPDataMeasurementSurfaceProjectionRejection.agda`
  records the HEP-D typed projection rejection for the current
  `MeasurementSurface -> DashiState` boundary.
- `DASHI/Physics/Closure/HEPDataComparisonAuthorityRouteDiagnostic.agda`
  records the HEP-E comparison-law and accepted dataset authority route
  diagnostic, blocked on HEP-B/C/D/F receipts.
- `DASHI/Physics/Closure/HEPDataITIRAuthorityAdapterDiagnostic.agda` records
  the HEP-F ITIR provenance scaffold diagnostic and missing HEPData authority
  adapter/token fields.
- `DASHI/Physics/Closure/HEPDataProviderReceiptRequestPack.agda` records the
  consolidated HEP-A..F provider request pack and keeps observable selection,
  residual/deviation class receipt, unit calibration, defect projection,
  theorem-side projection, comparison law, ITIR authority, W3 accepted
  authority, and W8 origin promotion external.
- `DASHI/Physics/Closure/HEPDataResidualBridgeWorkerQueue.agda` records the
  HEP-R1..R15 residual/deviation retarget assignments without constructing
  provider receipts.
- `DASHI/Physics/Closure/HEPDataResidualObservableClassRequest.agda` records
  that HEPData bridge payloads must target residual/deviation/anomaly /
  symmetry-breaking / defect-profile classes rather than raw collapsed values.
- `DASHI/Physics/Closure/HEPDataDefectProjectionDiagnostic.agda` records the
  theorem-side residual/deviation-to-DASHI-defect-profile diagnostic and blocks
  raw/constant projections.
- `DASHI/Physics/Closure/HEPDataResidualSourceCandidateDiagnostic.agda` records
  local residual-like artifact candidates while keeping selection, checksum,
  calibration, comparison, authority, and provider receipts absent.
- `DASHI/Physics/Closure/HEPDataResidualProviderReceiptRequestPack.agda`
  records the residual-specific first-missing provider receipt policy.
- `DASHI/Physics/Closure/HEPDataNonCollapseObservableObligation.agda` records
  the required external non-collapse witness over two observations or bins.
- `DASHI/Physics/Closure/HEPDataResidualComparisonLawRequest.agda` records
  residual-aware comparison-law modes and rejects raw value equality.
- `DASHI/Physics/Closure/HEPDataEmpiricalResidualBridgeCore.agda` records the
  generic residual observable, baseline/invariance, non-collapse witness,
  defect projection, and comparison-soundness core without constructing a
  HEPData receipt.
- `DASHI/Physics/Closure/HEPDataResidualProviderPayloadIntake.agda` records the
  residual provider payload fields and first-missing intake outcomes.
- `DASHI/Physics/Closure/HEPDataResidualBridgeAuthorityGate.agda` records the
  receipt-filter gate that rejects raw/path/unchecksumed/no-route/no-witness
  provider answers and constructs no authority token.
- `DASHI/Physics/Closure/HEPDataExternalResidualWitnessPayload.agda` records
  the external non-collapse witness payload carrier and keeps the external
  receipt constructorless.
- `Docs/W3NonCollapseRunnerReceiptHardening.md` and
  `scripts/check_w3_noncollapse_receipt.py` harden the W3 t43 runner-side
  non-collapse receipt by binding the frozen comparison JSON checksum, selected
  per-bin witness, canonical t43/t44 JSON checksums, and Agda receipt literals.
  The checker preserves `providerGradePayloadPresent = false` and cannot
  substitute for `W3AcceptedEvidenceAuthorityToken`.
- `DASHI/Physics/Closure/HEPDataExternalResidualWitnessCandidateDiagnostic.agda`
  records the `phistar_50_76` checksum-bound local candidate as an
  evidence-pointer surface only.
- `DASHI/Physics/Closure/HEPDataResidualObservableClassCandidateDiagnostic.agda`
  records the `phistar_50_76` residual observable-class candidate as a
  `fluctuationProfile` candidate only; it does not construct
  `residualObservableClassReceipt`.
- `DASHI/Physics/Closure/HEPDataResidualObservableClassProtoReceipt.agda`
  packages that candidate as an externalizable proto-receipt payload while
  preserving first-missing intake rejection and the blocked authority gate.
- `DASHI/Physics/Closure/HEPDataResidualObservableClassExternalAlignment.agda`
  aligns the internal `fluctuationProfile` candidate with adjacent-bin
  finite-difference residual / local bin-to-bin variation language without
  claiming significance or authority promotion.
- `DASHI/Physics/Closure/HEPDataEmpiricalAuthorityReceiptCollation.agda`
  records the CMS-SMP-20-003 authority collation and correction packet:
  published `phistar mass 50-76` is `ins2079374` table `t19`, covariance is
  `t20`, and raw upstream values are kept separate from the local normalized
  artifact until an adapter-transform receipt exists.
- `DASHI/Physics/Closure/HEPDataRatioTableArtifactReceipt.agda` records the
  HEP-R28 checksum-bound `t43/t44` artifact receipt: valid name-endpoint CSVs,
  local paths, SHA-256 digests, and rejected HEPData error-HTML endpoint forms,
  without constructing projection, comparison, or promotion receipts.
- `DASHI/Physics/Closure/HEPDataPredictionFreezePolicyRequest.agda` records the
  HEP-R30 clean-freeze policy sequence and clean-worktree certificate shape
  without accepting the current dirty diagnostic `HEAD`.
- `DASHI/Physics/Closure/HEPDataComparisonLawReceiptRequest.agda` records the
  HEP-R31 future comparison-law receipt shape for t43/t44: adapter receipt,
  projection artifact, t43/t44 digests, freeze hash, worktree-clean
  certificate, chi2, chi2/dof, per-bin two-sigma law, and authority DOI, while
  keeping the receipt uninhabited and W3 non-promoted.
- `DASHI/Physics/Closure/HEPDataT43SudakovBaselinePredictionHook.agda` records
  HEP-R34: the callable CSS/Sudakov baseline hook exists and can exercise the
  runner, but is not an accepted repo-native DASHI prediction API.
- `DASHI/Physics/Closure/LilaE8RootSystemLocalSourceDiagnostic.agda` and
  `DASHI/Physics/Closure/LilaE8RootSystemLatticeReceipt.agda` record LILA-R1:
  local LILA/E8 evidence pointers and remaining E8/Lam-Tung/phi-star receipt
  gaps, without physics promotion.
- `DASHI/Physics/Closure/LilaE8InitialisationPriorNote.agda` records LILA-R1a:
  SPUTNIKAI/sovereign-lila-e8 as related engineering provenance and
  AllenAI/Lila as rejected unrelated provenance.
- `DASHI/Physics/Closure/LilaE8RootEnumeration.agda`,
  `DASHI/Physics/Closure/LamTungE8AdapterSurface.agda`,
  `DASHI/Physics/Closure/LilaE8ThetaJBridgeSurface.agda`, and
  `DASHI/Physics/Closure/LilaE8PhiStarProjectionReceipt.agda` record
  LILA-R2/R3/R4/R5 request surfaces. R5 remains parked on accepted R2/R3/R4
  receipts and does not provide the HEP-R33 prediction API.
- `DASHI/Physics/Closure/SiblingEvidenceInventory.agda` records SIB-R1:
  sibling `dashifine`, `dashiQ`, `dashitest`, `DASHIg`, and `dashi_lean4`
  artifacts as useful non-promoting evidence pointers. It does not construct a
  clean freeze, accepted DASHI prediction API, projection receipt, comparison
  law, E8 carrier receipt, Lam-Tung adapter, or any W3/W4/W5/W6/W8/W9
  promotion receipt.
- `DASHI/Physics/Closure/SiblingEvidenceExtractionDiagnostic.agda` records
  SIB-R2: worker extraction findings over the sibling artifacts. It preserves
  the negative facts that no accepted `compute_dashi_ratio` shortcut,
  240-root E8 vocabulary, theta/J Lean theorem receipt, or carrier-state-bound
  Lyapunov pass certificate was found.

Check these directly when source diagnostics or retarget consumer obligations
change, then check `P0BlockerObligationIndex.agda`.

## Hygiene Script Policy

- `scripts/run_closure_hygiene.py`
- `scripts/run_closure_hygiene.sh`

These now skip learned `heavy` and `aggregator` tasks by default. Use
`--include-heavy` only for deliberate closure-certification runs with a larger
runtime budget.

## Practical Rule

Default inner loop:

1. run one or two canonical bridge modules directly
2. run `PhysicsClosureSummary.agda` if you need a broader canonical surface
3. avoid `PhysicsClosureValidationSummary.agda` unless you are explicitly doing
   a long-budget validation pass
4. treat `Everything.agda` as an occasional offline checkpoint, not a routine
   target

## Execution Stratification

Use the repo in three layers:

- `L0`: thin, interactive targets
- `L1`: bounded medium targets
- `L2`: heavy aggregate or heavy fixed-domain targets that should stay out of
  the interactive loop

Layer contract:

- `L0` / `L1` are the authoritative working surfaces for branch truth
- `L2` is the closure-certification layer
- do not mix those roles

Current policy examples:

- `L0`
  - the canonical bridge modules listed above
  - `Kernel/*.agda`
  - `Verification/*.agda`
  - `Ontology/Hecke/Layer2FiniteSearchShell.agda`
- `L1`
  - `DASHI/Physics/Closure/CanonicalStageC.agda`
  - `Ontology/Hecke/SaturatedInvariantRefinementStatus.agda`
- `L2`
  - `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`
  - `DASHI/Everything.agda`
  - the current heavy closure recovery lane:
    `DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`,
    `DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda`,
    `DASHI/Physics/DashiDynamicsShiftInstance.agda`,
    `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda`,
    `DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda`,
    `DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda`,
    `DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda`,
    `DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda`, and
    `DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`
  - the current heavy Hecke Layer 2 implementation lane:
    `Ontology/Hecke/DefectOrbitSummaryRefinement.agda`,
    `Ontology/Hecke/ForcedStableCountDecomposition.agda`,
    `Ontology/Hecke/TriadIndexedDefectOrbitSummaryRefinement.agda`,
    `Ontology/Hecke/CurrentSaturatedTriadHistogramSeparation.agda`,
    `Ontology/Hecke/CurrentSaturatedSectorHistogramComputations.agda`,
    `Ontology/Hecke/CurrentSaturatedPredictedPairComparisons.agda`,
    `Ontology/Hecke/TriadSectorCorrelationRefinement.agda`, and
    `Ontology/Hecke/Layer2FiniteSearch.agda`

Control-plane helper:

- `scripts/route_agda_by_layer.py`
- `scripts/run_agda_easy_to_hard.py`

Use it to classify one or more modules and route them as:

- interactive direct Agda runs for `L0`
- timeout-bounded Agda runs for `L1`
- queue-only or offline-certification handoff for `L2`

## Offline Closure Certification

Use exactly one aggregate target for a deliberate full closure pass:

- `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`

Run it through:

- `scripts/run_closure_full_check.sh`

Valid outcomes are only:

1. `clean`
2. `error`
3. `too_large`

Do not interpret an `L2` timeout as a branch-classification failure.

Use `scripts/run_agda_easy_to_hard.py` when the task is not “classify this one
target” but “run the current validated easiest-to-hardest sequence”.
Its default order is:

1. `Ontology/Hecke/Layer2FiniteSearchShell.agda`
2. `Kernel/Monoid.agda`
3. `Verification/Prelude.agda`
4. `DASHI/Physics/Closure/CanonicalPrimeSelectionBridge.agda`
5. `DASHI/Physics/Closure/CanonicalPrimeInvariance.agda`
6. `DASHI/Physics/Closure/CanonicalPrimeConcentration.agda`
7. `DASHI/Physics/Closure/CanonicalPrimeSelector.agda`
8. `DASHI/Physics/Closure/CanonicalPrimeIsolation.agda`

Optional flags then extend the run with:

- bounded medium targets such as
  `Ontology/Hecke/SaturatedInvariantRefinementStatus.agda`
- Layer 2 queue generation only, not heavy theorem-lane execution
