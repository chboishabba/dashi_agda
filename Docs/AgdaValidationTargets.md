# Agda Validation Targets

Purpose: record which Agda modules are safe for routine targeted validation and
which ones should be avoided in normal loops because they are known to be
runtime-heavy or aggregate too much of the closure surface at once.

## Timeout-Limited Clay P0 Targets

The current zero-mode/YM/core P0 modules are substantial Agda receipt surfaces
with heavy imports.  In rapid iteration loops, validate them with a hard cap:

```bash
timeout 10s agda <module>.agda
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
- `DASHI/Physics/Closure/YMGaugeZeroModeVacuumRigidityBoundary.agda`
- `DASHI/Physics/Closure/YMHamiltonianDominatesFiniteHodgeDefectBoundary.agda`
- `DASHI/Physics/Closure/FiniteGaugeHodgeAdjointCompatibility.agda`
- `DASHI/Physics/Closure/YMWeightedBTAdjointKappaCalculation.agda`
- `DASHI/Physics/Closure/DefectFourPointParallelogramLawBoundary.agda`

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
- `DASHI/Physics/Closure/YMHamiltonianDominatesFiniteHodgeDefectBoundary.agda`
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
