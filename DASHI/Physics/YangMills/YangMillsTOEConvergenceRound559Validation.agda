{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Validation where

------------------------------------------------------------------------
-- FOCUSED CURRENT-MASTER R559 REGRESSION
--
-- Verify source-owner identity.
-- Verify route-pruning and promotion firewalls.
-- Verify the 14-family and 7-family scheduling quotients.
-- Verify public reachability through the TOE root, Unifier, and Unified.Physics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as TOE
import DASHI.Physics.YangMills.YangMillsClayGoal1MaximumCutRound485Exact as R485
import DASHI.Physics.YangMills.YangMillsClayIrreducibleSourceFamiliesRound546Exact as R546
import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound558Exact as R558
import DASHI.EverythingTOESymmetryResolved369 as Root
import DASHI.Unified.Physics as UnifiedPhysics
import DASHI.Unifier as U

open import DASHI.Physics.YangMills.CompactLieProofLevel

rootGoal1A1MatchesOwner :
  Root.toeGoal1A1CurrentStepBetaSourceLevel
  ≡ TOE.toeGoal1A1CurrentStepBetaSourceLevel
rootGoal1A1MatchesOwner = refl

rootIrreducibleDispatchMatchesOwner :
  Root.toeIrreducibleFamilyLevel Root.a1CurrentStepVariation
  ≡ TOE.toeIrreducibleFamilyLevel TOE.a1CurrentStepVariation
rootIrreducibleDispatchMatchesOwner = refl

rootCriticalDispatchMatchesOwner :
  Root.toeCriticalFamilyLevel Root.h6MinimalWardNontriviality
  ≡ TOE.toeCriticalFamilyLevel TOE.h6MinimalWardNontriviality
rootCriticalDispatchMatchesOwner = refl

rootClayCompletionStillFalse :
  Root.toeGoal1ClayCompletionClaimed ≡ false
rootClayCompletionStillFalse = refl

------------------------------------------------------------------------
-- Goal-1 R485 -> R559 maximum-cut normalization regressions.
------------------------------------------------------------------------

goal1FiniteSymmetryAndRPMatchesR485 :
  TOE.toeGoal1FiniteSymmetryAndRPSourceLevel
  ≡ R485.aFiniteSymmetryAndRPSourceLevel
goal1FiniteSymmetryAndRPMatchesR485 = refl

goal1A1MatchesR485 :
  TOE.toeGoal1A1CurrentStepBetaSourceLevel
  ≡ R485.a1CurrentStepBetaSourceLevel
goal1A1MatchesR485 = refl

goal1A2MatchesR485 :
  TOE.toeGoal1A2GeneratedHistoryShellLevel
  ≡ R485.a2GeneratedHistoryShellIsCMP116BetaMarkLevel
goal1A2MatchesR485 = refl

goal1A3MatchesR485 :
  TOE.toeGoal1A3SourceNativeContinuumOSLevel
  ≡ R485.a3SourceNativeSameFamilyContinuumOSLevel
goal1A3MatchesR485 = refl

goal1A3RepresentationMatchesR485 :
  TOE.toeGoal1A3CountablyAdditiveRepresentationLevel
  ≡ R485.a3CountablyAdditiveRepresentationLevel
goal1A3RepresentationMatchesR485 = refl

goal1A4MatchesR485 :
  TOE.toeGoal1A4FiniteRegularityLevel
  ≡ R485.a4FiniteRegularityFromQuantitativeBoundsLevel
goal1A4MatchesR485 = refl

goal1A5MatchesR485 :
  TOE.toeGoal1A5FiniteGrowthLevel
  ≡ R485.a5FiniteGrowthFromQuantitativeBoundsLevel
goal1A5MatchesR485 = refl

goal1BWilsonShellMatchesR485 :
  TOE.toeGoal1BWilsonTwoInsertionConnectedShellLevel
  ≡ R485.bWilsonTwoInsertionConnectedShellLevel
goal1BWilsonShellMatchesR485 = refl

goal1BTwoMarkMatchesR485 :
  TOE.toeGoal1BWilsonTwoMarkExpansionLevel
  ≡ R485.bWilsonTwoMarkExpansionLevel
goal1BTwoMarkMatchesR485 = refl

goal1BWeightTailMatchesR485 :
  TOE.toeGoal1BWilsonConnectingWeightTailLevel
  ≡ R485.bWilsonConnectingWeightTailLevel
goal1BWeightTailMatchesR485 = refl

goal1BWEXTCompilerMatchesR485 :
  TOE.toeGoal1BWEXTAssemblyCompilerLevel
  ≡ R485.bWilsonWEXTAssemblyCompilerLevel
goal1BWEXTCompilerMatchesR485 = refl

goal1BSameHMatchesR485 :
  TOE.toeGoal1BSameHamiltonianTransferCoordinateLevel
  ≡ R485.bSameHamiltonianTransferCoordinateLevel
goal1BSameHMatchesR485 = refl

goal1BGeometricDecayMatchesR485 :
  TOE.toeGoal1BGeometricDecayCompilerLevel
  ≡ R485.bGeometricDecayCompilerLevel
goal1BGeometricDecayMatchesR485 = refl

goal1BSpectralTransferMatchesR485 :
  TOE.toeGoal1BStandardSpectralTransferLevel
  ≡ R485.bStandardSpectralTransferLevel
goal1BSpectralTransferMatchesR485 = refl

goal1CMatchesR485 :
  TOE.toeGoal1CSameFamilySourceInstantiationLevel
  ≡ R485.cSameFamilySourceInstantiationLevel
goal1CMatchesR485 = refl

goal1G1MatchesR485 :
  TOE.toeGoal1G1ArbitraryCompactSimpleSourceMapLevel
  ≡ R485.gArbitraryCompactSimpleSourceMapLevel
goal1G1MatchesR485 = refl

goal1G2MatchesR485 :
  TOE.toeGoal1G2SameSystemNontrivialitySemanticsLevel
  ≡ R485.gSameSystemNontrivialitySemanticsLevel
goal1G2MatchesR485 = refl

goal1MaximumCutCompilerIsChecked :
  TOE.toeGoal1MaximumCutCompilerLevel ≡ machineChecked
goal1MaximumCutCompilerIsChecked = refl

goal1NormalizationCompilerIsChecked :
  TOE.round559Goal1MaximumCutNormalizationCompilerLevel ≡ machineChecked
goal1NormalizationCompilerIsChecked = refl

goal1ProjectiveProkhorovNotMandatory :
  TOE.toeGoal1ProjectiveProkhorovMandatory ≡ false
goal1ProjectiveProkhorovNotMandatory = refl

goal1GlobalCoerciveCompactnessNotMandatory :
  TOE.toeGoal1GlobalCoerciveCompactnessMandatory ≡ false
goal1GlobalCoerciveCompactnessNotMandatory = refl

goal1PostHocMeasureWeldNotMandatory :
  TOE.toeGoal1PostHocContinuumMeasureWeldMandatory ≡ false
goal1PostHocMeasureWeldNotMandatory = refl

goal1HistoricalSelectedJNotMandatory :
  TOE.toeGoal1HistoricalSelectedJMinCutMandatory ≡ false
goal1HistoricalSelectedJNotMandatory = refl

goal1CompatibilityBRouteNotMandatory :
  TOE.toeGoal1CompatibilityBRouteMandatory ≡ false
goal1CompatibilityBRouteNotMandatory = refl

goal1ArbitraryPositiveGapTokenNotMandatory :
  TOE.toeGoal1ArbitraryPositiveGapTokenMandatory ≡ false
goal1ArbitraryPositiveGapTokenNotMandatory = refl

goal1SU2ValidationNotMandatoryForGenericG :
  TOE.toeGoal1SU2ValidationMandatoryForGenericG ≡ false
goal1SU2ValidationNotMandatoryForGenericG = refl

goal1UniformConstantsAcrossAllGroupsNotMandatory :
  TOE.toeGoal1UniformConstantsAcrossAllGroupsMandatory ≡ false
goal1UniformConstantsAcrossAllGroupsNotMandatory = refl

goal1FreshContinuumStressLimitNotMandatory :
  TOE.toeGoal1FreshContinuumStressLimitMandatory ≡ false
goal1FreshContinuumStressLimitNotMandatory = refl

goal1IndependentFourthCumulantNotMandatory :
  TOE.toeGoal1IndependentFourthCumulantMandatory ≡ false
goal1IndependentFourthCumulantNotMandatory = refl

goal1ClayCompletionStillNotClaimed :
  TOE.toeGoal1ClayCompletionClaimed ≡ false
goal1ClayCompletionStillNotClaimed = refl

------------------------------------------------------------------------
-- Goal-1 normalized facade regressions.
------------------------------------------------------------------------

unifiedPhysicsGoal1A1MatchesTOE :
  UnifiedPhysics.toeGoal1A1CurrentStepBetaSourceLevel
  ≡ TOE.toeGoal1A1CurrentStepBetaSourceLevel
unifiedPhysicsGoal1A1MatchesTOE = refl

unifiedPhysicsGoal1A3MatchesTOE :
  UnifiedPhysics.toeGoal1A3SourceNativeContinuumOSLevel
  ≡ TOE.toeGoal1A3SourceNativeContinuumOSLevel
unifiedPhysicsGoal1A3MatchesTOE = refl

unifiedPhysicsGoal1BSelectedMatchesTOE :
  UnifiedPhysics.toeGoal1BWilsonTwoInsertionConnectedShellLevel
  ≡ TOE.toeGoal1BWilsonTwoInsertionConnectedShellLevel
unifiedPhysicsGoal1BSelectedMatchesTOE = refl

unifiedPhysicsGoal1BGapMatchesTOE :
  UnifiedPhysics.toeGoal1BGeometricDecayCompilerLevel
  ≡ TOE.toeGoal1BGeometricDecayCompilerLevel
unifiedPhysicsGoal1BGapMatchesTOE = refl

unifiedPhysicsGoal1CMatchesTOE :
  UnifiedPhysics.toeGoal1CSameFamilySourceInstantiationLevel
  ≡ TOE.toeGoal1CSameFamilySourceInstantiationLevel
unifiedPhysicsGoal1CMatchesTOE = refl

unifiedPhysicsGoal1G1MatchesTOE :
  UnifiedPhysics.toeGoal1G1ArbitraryCompactSimpleSourceMapLevel
  ≡ TOE.toeGoal1G1ArbitraryCompactSimpleSourceMapLevel
unifiedPhysicsGoal1G1MatchesTOE = refl

unifiedPhysicsGoal1G2MatchesTOE :
  UnifiedPhysics.toeGoal1G2SameSystemNontrivialitySemanticsLevel
  ≡ TOE.toeGoal1G2SameSystemNontrivialitySemanticsLevel
unifiedPhysicsGoal1G2MatchesTOE = refl

unifierGoal1A1MatchesTOE :
  U.toeGoal1A1CurrentStepBetaSourceLevel
  ≡ TOE.toeGoal1A1CurrentStepBetaSourceLevel
unifierGoal1A1MatchesTOE = refl

unifierGoal1BGapMatchesTOE :
  U.toeGoal1BGeometricDecayCompilerLevel
  ≡ TOE.toeGoal1BGeometricDecayCompilerLevel
unifierGoal1BGapMatchesTOE = refl

unifierGoal1CMatchesTOE :
  U.toeGoal1CSameFamilySourceInstantiationLevel
  ≡ TOE.toeGoal1CSameFamilySourceInstantiationLevel
unifierGoal1CMatchesTOE = refl

unifierGoal1G2MatchesTOE :
  U.toeGoal1G2SameSystemNontrivialitySemanticsLevel
  ≡ TOE.toeGoal1G2SameSystemNontrivialitySemanticsLevel
unifierGoal1G2MatchesTOE = refl


------------------------------------------------------------------------
-- Full R485 inventory coverage regressions.
------------------------------------------------------------------------

goal1FiniteEuclideanAttachmentMatchesR485 :
  TOE.toeGoal1FiniteEuclideanSameObjectAttachmentLevel
  ≡ R485.aFiniteEuclideanSameObjectAttachmentLevel
goal1FiniteEuclideanAttachmentMatchesR485 = refl

goal1FiniteBosonicAttachmentMatchesR485 :
  TOE.toeGoal1FiniteBosonicSameObjectAttachmentLevel
  ≡ R485.aFiniteBosonicSameObjectAttachmentLevel
goal1FiniteBosonicAttachmentMatchesR485 = refl

goal1FiniteWilsonRPAttachmentMatchesR485 :
  TOE.toeGoal1FiniteWilsonRPSameObjectAttachmentLevel
  ≡ R485.aFiniteWilsonRPSameObjectAttachmentLevel
goal1FiniteWilsonRPAttachmentMatchesR485 = refl

goal1A3StressDensityMeasureMatchesR485 :
  TOE.toeGoal1A3StressDensityIsLiteralFiniteMeasureLevel
  ≡ R485.a3StressDensityIsLiteralFiniteMeasureLevel
goal1A3StressDensityMeasureMatchesR485 = refl

goal1A3FiniteContinuumLimitMatchesR485 :
  TOE.toeGoal1A3FiniteFamilyContinuumLimitLevel
  ≡ R485.a3FiniteFamilyContinuumLimitLevel
goal1A3FiniteContinuumLimitMatchesR485 = refl

goal1A3LiteralSchwingerMatchesR485 :
  TOE.toeGoal1A3LiteralSchwingerBelongsLevel
  ≡ R485.a3LiteralSchwingerBelongsLevel
goal1A3LiteralSchwingerMatchesR485 = refl

goal1A3SourceOSMatchesLiteralSchwingerR485 :
  TOE.toeGoal1A3SourceOSIsLiteralSchwingerLevel
  ≡ R485.a3SourceOSIsLiteralSchwingerLevel
goal1A3SourceOSMatchesLiteralSchwingerR485 = refl

goal1A3ProjectivePremeasureMatchesR485 :
  TOE.toeGoal1A3FiniteProjectiveCylinderPremeasureLevel
  ≡ R485.a3FiniteProjectiveCylinderPremeasureLevel
goal1A3ProjectivePremeasureMatchesR485 = refl

goal1A3CylinderEventSemanticsMatchesR485 :
  TOE.toeGoal1A3CylinderEventIndicatorSemanticsLevel
  ≡ R485.a3CylinderEventIndicatorSemanticsLevel
goal1A3CylinderEventSemanticsMatchesR485 = refl

goal1A3ProjectiveExpectationMatchesR485 :
  TOE.toeGoal1A3ProjectiveExpectationConsistencyLevel
  ≡ R485.a3ProjectiveEventExpectationConsistencyLevel
goal1A3ProjectiveExpectationMatchesR485 = refl

goal1A3ContinuityAtEmptyMatchesR485 :
  TOE.toeGoal1A3ContinuityAtEmptyLevel
  ≡ R485.a3ContinuityAtEmptyLevel
goal1A3ContinuityAtEmptyMatchesR485 = refl

goal1A3CaratheodoryMatchesR485 :
  TOE.toeGoal1A3CaratheodoryExtensionLevel
  ≡ R485.a3CaratheodoryExtensionLevel
goal1A3CaratheodoryMatchesR485 = refl

goal1A3CylinderIntegralMatchesR485 :
  TOE.toeGoal1A3CylinderExpectationIntegralLevel
  ≡ R485.a3CylinderExpectationIntegralIdentificationLevel
goal1A3CylinderIntegralMatchesR485 = refl

goal1A3RepresentedLiteralMatchesR485 :
  TOE.toeGoal1A3RepresentedLiteralSemanticsLevel
  ≡ R485.a3RepresentedLiteralSemanticsLevel
goal1A3RepresentedLiteralMatchesR485 = refl

goal1A45MomentMatchesR485 :
  TOE.toeGoal1A45QuantitativeMomentToFiniteOS05Level
  ≡ R485.a45QuantitativeMomentToFiniteOS05Level
goal1A45MomentMatchesR485 = refl

goal1A45ExpectationAttachmentMatchesR485 :
  TOE.toeGoal1A45QuantitativeFiniteExpectationAttachmentLevel
  ≡ R485.a45QuantitativeFiniteExpectationAttachmentLevel
goal1A45ExpectationAttachmentMatchesR485 = refl

goal1A45RepresentedOSExtensionalityMatchesR485 :
  TOE.toeGoal1A45RepresentedOSPredicateExtensionalityLevel
  ≡ R485.a45RepresentedOSPredicateExtensionalityLevel
goal1A45RepresentedOSExtensionalityMatchesR485 = refl

goal1A4RepresentedExtensionalityMatchesR485 :
  TOE.toeGoal1A4RepresentedRegularityExtensionalityLevel
  ≡ R485.a4RepresentedRegularityExtensionalityLevel
goal1A4RepresentedExtensionalityMatchesR485 = refl

goal1A5RepresentedExtensionalityMatchesR485 :
  TOE.toeGoal1A5RepresentedGrowthExtensionalityLevel
  ≡ R485.a5RepresentedGrowthExtensionalityLevel
goal1A5RepresentedExtensionalityMatchesR485 = refl

goal1BLiteralGapSemanticsMatchesR485 :
  TOE.toeGoal1BLiteralHamiltonianGapSemanticsLevel
  ≡ R485.bLiteralHamiltonianGapSemanticsLevel
goal1BLiteralGapSemanticsMatchesR485 = refl

goal1RepresentedTerminalMatchesR485 :
  TOE.toeGoal1RepresentedTerminalCompilerLevel
  ≡ R485.round485RepresentedTerminalCompilerLevel
goal1RepresentedTerminalMatchesR485 = refl

goal1TerminalContractInventoryMatchesR485 :
  TOE.toeGoal1TerminalContractSemanticInventoryLevel
  ≡ R485.terminalContractSemanticInventoryLevel
goal1TerminalContractInventoryMatchesR485 = refl

goal1PostHocSchwingerEqualityNotMandatory :
  TOE.toeGoal1PostHocSchwingerEqualityMandatory ≡ false
goal1PostHocSchwingerEqualityNotMandatory = refl

goal1CMP109PolarizationDetourNotMandatory :
  TOE.toeGoal1CMP109PolarizationDetourMandatory ≡ false
goal1CMP109PolarizationDetourNotMandatory = refl

goal1PrintedBalabanJEqualsWilsonNotMandatory :
  TOE.toeGoal1PrintedBalabanJEqualsWilsonObservableMandatory ≡ false
goal1PrintedBalabanJEqualsWilsonNotMandatory = refl


------------------------------------------------------------------------
-- R546 irreducible source-family normalization regressions.
------------------------------------------------------------------------

irreducibleA3PositiveEventMatchesR546 :
  TOE.toeIrreducibleA3PositiveEventSemanticsLevel
  ≡ R546.a3PositiveEventSemanticsLevel
irreducibleA3PositiveEventMatchesR546 = refl

irreducibleA3BooleanMatchesR546 :
  TOE.toeIrreducibleA3EventBooleanAlgebraLevel
  ≡ R546.a3EventBooleanAlgebraLevel
irreducibleA3BooleanMatchesR546 = refl

irreducibleA3ProjectiveMatchesR546 :
  TOE.toeIrreducibleA3ProjectiveConsistencyLevel
  ≡ R546.a3ProjectiveConsistencyLevel
irreducibleA3ProjectiveMatchesR546 = refl

irreducibleA3ContinuityMatchesR546 :
  TOE.toeIrreducibleA3ContinuityAtEmptyLevel
  ≡ R546.a3ContinuityAtEmptyLevel
irreducibleA3ContinuityMatchesR546 = refl

irreducibleA3IntegralMatchesR546 :
  TOE.toeIrreducibleA3ExpectationIntegralIdentificationLevel
  ≡ R546.a3ExpectationIntegralIdentificationLevel
irreducibleA3IntegralMatchesR546 = refl

irreducibleFiniteOSBosonicMatchesR546 :
  TOE.toeIrreducibleFiniteOSBosonicAttachmentLevel
  ≡ R546.finiteOSBosonicAttachmentLevel
irreducibleFiniteOSBosonicMatchesR546 = refl

irreducibleFiniteT1BundleMatchesR546 :
  TOE.toeIrreducibleFiniteT1SourceBundleLevel
  ≡ R546.finiteT1SourceBundleLevel
irreducibleFiniteT1BundleMatchesR546 = refl

irreducibleAllGroupStructuralMatchesR546 :
  TOE.toeIrreducibleAllGroupStructuralWitnessLevel
  ≡ R546.allGroupStructuralWitnessLevel
irreducibleAllGroupStructuralMatchesR546 = refl

irreducibleAllGroupAlignmentMatchesR546 :
  TOE.toeIrreducibleAllGroupActualAlignmentLevel
  ≡ R546.allGroupActualAlignmentLevel
irreducibleAllGroupAlignmentMatchesR546 = refl

irreducibleAllGroupFiveBlockMatchesR546 :
  TOE.toeIrreducibleAllGroupFiveBlockSourceLevel
  ≡ R546.allGroupFiveBlockSourceLevel
irreducibleAllGroupFiveBlockMatchesR546 = refl

irreducibleWEXTTwoMarkMatchesR546 :
  TOE.toeIrreducibleWEXTTwoMarkExpansionLevel
  ≡ R546.wextTwoMarkExpansionLevel
irreducibleWEXTTwoMarkMatchesR546 = refl

irreducibleWEXTTailMatchesR546 :
  TOE.toeIrreducibleWEXTConnectingWeightTailLevel
  ≡ R546.wextConnectingWeightTailLevel
irreducibleWEXTTailMatchesR546 = refl

irreducibleWholeMeasureEqualitiesAreGone :
  TOE.toeIrreducibleWholeMeasureRecordEqualitiesRemaining ≡ false
irreducibleWholeMeasureEqualitiesAreGone = refl

irreducibleIndependentGroupSelectionsAreGone :
  TOE.toeIrreducibleIndependentGroupSelectionsRemaining ≡ false
irreducibleIndependentGroupSelectionsAreGone = refl

irreducibleSU2PromotionIsGone :
  TOE.toeIrreducibleSU2PromotionRemaining ≡ false
irreducibleSU2PromotionIsGone = refl

irreducibleSingleCutoffExtensionIsGone :
  TOE.toeIrreducibleSingleCutoffMeasureExtensionRemaining ≡ false
irreducibleSingleCutoffExtensionIsGone = refl

irreducibleCutCompilerIsChecked :
  TOE.toeIrreducibleSourceFamilyCutCompilerLevel ≡ machineChecked
irreducibleCutCompilerIsChecked = refl

------------------------------------------------------------------------
-- R558 critical-path normalization regressions.
------------------------------------------------------------------------

criticalA3PositiveEventMatchesR558 :
  TOE.toeCriticalA3PositiveEventSemanticsLevel
  ≡ R558.a3PositiveEventSemanticsLevel
criticalA3PositiveEventMatchesR558 = refl

criticalA3BooleanMatchesR558 :
  TOE.toeCriticalA3BooleanAlgebraLevel
  ≡ R558.a3BooleanAlgebraLevel
criticalA3BooleanMatchesR558 = refl

criticalA3ProjectiveMatchesR558 :
  TOE.toeCriticalA3ProjectiveConsistencyLevel
  ≡ R558.a3ProjectiveConsistencyLevel
criticalA3ProjectiveMatchesR558 = refl

criticalA3ContinuityMatchesR558 :
  TOE.toeCriticalA3ContinuityAtEmptyLevel
  ≡ R558.a3ContinuityAtEmptyLevel
criticalA3ContinuityMatchesR558 = refl

criticalA3GeneratorRepresentationMatchesR558 :
  TOE.toeCriticalA3CylinderGeneratorRepresentationLevel
  ≡ R558.a3CylinderGeneratorRepresentationLevel
criticalA3GeneratorRepresentationMatchesR558 = refl

criticalWEXTTwoMarkMatchesR558 :
  TOE.toeCriticalWEXTTwoMarkExpansionLevel
  ≡ R558.wextTwoMarkExpansionLevel
criticalWEXTTwoMarkMatchesR558 = refl

criticalWEXTTailMatchesR558 :
  TOE.toeCriticalWEXTConnectingWeightTailLevel
  ≡ R558.wextConnectingWeightTailLevel
criticalWEXTTailMatchesR558 = refl

criticalWilsonCovarianceMatchesR558 :
  TOE.toeCriticalFiniteToContinuumWilsonCovarianceLevel
  ≡ R558.finiteToContinuumWilsonCovarianceLevel
criticalWilsonCovarianceMatchesR558 = refl

criticalMassGapCompilerMatchesR558 :
  TOE.toeCriticalMassGapCompilerLevel
  ≡ R558.massGapCompilerLevel
criticalMassGapCompilerMatchesR558 = refl

criticalMinimalH6CompilerMatchesR558 :
  TOE.toeCriticalMinimalH6CompilerLevel
  ≡ R558.minimalH6CompilerLevel
criticalMinimalH6CompilerMatchesR558 = refl

criticalPrintedJRouteNotRequired :
  TOE.toeCriticalPrintedJRouteRequired ≡ false
criticalPrintedJRouteNotRequired = refl

criticalMassGapDoesNotNeedFullC :
  TOE.toeCriticalFullCLayerRequiredForMassGap ≡ false
criticalMassGapDoesNotNeedFullC = refl

criticalMinimalH6DoesNotNeedFullC :
  TOE.toeCriticalFullCLayerRequiredForMinimalH6 ≡ false
criticalMinimalH6DoesNotNeedFullC = refl

criticalPathCompilerIsChecked :
  TOE.toeCriticalPathCompilerLevel ≡ machineChecked
criticalPathCompilerIsChecked = refl

criticalSeparateWilsonFamilyNotRequired :
  TOE.toeSeparateContinuumWilsonFamilyRequired ≡ false
criticalSeparateWilsonFamilyNotRequired = refl

criticalFiniteMoscoRouteNotRequired :
  TOE.toeFiniteHamiltonianMoscoRouteRequired ≡ false
criticalFiniteMoscoRouteNotRequired = refl

criticalConservativeClayKeepsFullC :
  TOE.toeFullCLayerRetainedForConservativeClayExistence ≡ true
criticalConservativeClayKeepsFullC = refl


------------------------------------------------------------------------
-- Canonical family-dispatch normalization regressions.
------------------------------------------------------------------------

irreducibleFamilyDispatchA1MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.a1CurrentStepVariation
  ≡ R546.familyLevel R546.a1CurrentStepVariation
irreducibleFamilyDispatchA1MatchesR546 = refl

irreducibleFamilyDispatchA2MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.a2HistoryCoordinate
  ≡ R546.familyLevel R546.a2HistoryCoordinate
irreducibleFamilyDispatchA2MatchesR546 = refl

irreducibleFamilyDispatchA3MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.a3ProjectiveRepresentation
  ≡ R546.familyLevel R546.a3ProjectiveRepresentation
irreducibleFamilyDispatchA3MatchesR546 = refl

irreducibleFamilyDispatchFiniteT1MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.finiteT1AndPublishedOS
  ≡ R546.familyLevel R546.finiteT1AndPublishedOS
irreducibleFamilyDispatchFiniteT1MatchesR546 = refl

irreducibleFamilyDispatchQuantitativeT5MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.quantitativeT5CMP119Alignment
  ≡ R546.familyLevel R546.quantitativeT5CMP119Alignment
irreducibleFamilyDispatchQuantitativeT5MatchesR546 = refl

irreducibleFamilyDispatchWEXTMatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.bWilsonWEXT
  ≡ R546.familyLevel R546.bWilsonWEXT
irreducibleFamilyDispatchWEXTMatchesR546 = refl

irreducibleFamilyDispatchSameHMatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.bSameHamiltonianEnergyDecay
  ≡ R546.familyLevel R546.bSameHamiltonianEnergyDecay
irreducibleFamilyDispatchSameHMatchesR546 = refl

irreducibleFamilyDispatchAllGroupMatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.actualGroupCompleteSource
  ≡ R546.familyLevel R546.actualGroupCompleteSource
irreducibleFamilyDispatchAllGroupMatchesR546 = refl

irreducibleFamilyDispatchDensityMeasureMatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.densityToNormalizedFiniteMeasure
  ≡ R546.familyLevel R546.densityToNormalizedFiniteMeasure
irreducibleFamilyDispatchDensityMeasureMatchesR546 = refl

irreducibleFamilyDispatchC0MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.c0WilsonLocalObservable
  ≡ R546.familyLevel R546.c0WilsonLocalObservable
irreducibleFamilyDispatchC0MatchesR546 = refl

irreducibleFamilyDispatchC1MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.c1MarkedCurvature
  ≡ R546.familyLevel R546.c1MarkedCurvature
irreducibleFamilyDispatchC1MatchesR546 = refl

irreducibleFamilyDispatchC2MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.c2PhysicalRemainderTail
  ≡ R546.familyLevel R546.c2PhysicalRemainderTail
irreducibleFamilyDispatchC2MatchesR546 = refl

irreducibleFamilyDispatchC3MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.c3AFRecurrence
  ≡ R546.familyLevel R546.c3AFRecurrence
irreducibleFamilyDispatchC3MatchesR546 = refl

irreducibleFamilyDispatchC4MatchesR546 :
  TOE.toeIrreducibleFamilyLevel TOE.c4DensityAnchoredStress
  ≡ R546.familyLevel R546.c4DensityAnchoredStress
irreducibleFamilyDispatchC4MatchesR546 = refl

criticalFamilyDispatchA3MatchesR558 :
  TOE.toeCriticalFamilyLevel TOE.a3SelectedRepresentation
  ≡ R558.criticalLevel R558.a3SelectedRepresentation
criticalFamilyDispatchA3MatchesR558 = refl

criticalFamilyDispatchT1MatchesR558 :
  TOE.toeCriticalFamilyLevel TOE.t1FiniteOSSameFamily
  ≡ R558.criticalLevel R558.t1FiniteOSSameFamily
criticalFamilyDispatchT1MatchesR558 = refl

criticalFamilyDispatchT5MatchesR558 :
  TOE.toeCriticalFamilyLevel TOE.t5QuantitativeSameFamily
  ≡ R558.criticalLevel R558.t5QuantitativeSameFamily
criticalFamilyDispatchT5MatchesR558 = refl

criticalFamilyDispatchB1MatchesR558 :
  TOE.toeCriticalFamilyLevel TOE.b1SourceFirstWilsonWEXT
  ≡ R558.criticalLevel R558.b1SourceFirstWilsonWEXT
criticalFamilyDispatchB1MatchesR558 = refl

criticalFamilyDispatchB2MatchesR558 :
  TOE.toeCriticalFamilyLevel TOE.b2SameHamiltonian
  ≡ R558.criticalLevel R558.b2SameHamiltonian
criticalFamilyDispatchB2MatchesR558 = refl

criticalFamilyDispatchG1MatchesR558 :
  TOE.toeCriticalFamilyLevel TOE.g1ActualCompactSimple
  ≡ R558.criticalLevel R558.g1ActualCompactSimple
criticalFamilyDispatchG1MatchesR558 = refl

criticalFamilyDispatchH6MatchesR558 :
  TOE.toeCriticalFamilyLevel TOE.h6MinimalWardNontriviality
  ≡ R558.criticalLevel R558.h6MinimalWardNontriviality
criticalFamilyDispatchH6MatchesR558 = refl


------------------------------------------------------------------------
-- Canonical family dispatch facade regressions.
------------------------------------------------------------------------

unifiedPhysicsIrreducibleDispatchMatchesTOE :
  UnifiedPhysics.toeIrreducibleFamilyLevel
    TOE.a1CurrentStepVariation
  ≡ TOE.toeIrreducibleFamilyLevel TOE.a1CurrentStepVariation
unifiedPhysicsIrreducibleDispatchMatchesTOE = refl

unifiedPhysicsCriticalDispatchMatchesTOE :
  UnifiedPhysics.toeCriticalFamilyLevel
    TOE.h6MinimalWardNontriviality
  ≡ TOE.toeCriticalFamilyLevel TOE.h6MinimalWardNontriviality
unifiedPhysicsCriticalDispatchMatchesTOE = refl

unifierIrreducibleDispatchMatchesTOE :
  U.toeIrreducibleFamilyLevel
    TOE.bWilsonWEXT
  ≡ TOE.toeIrreducibleFamilyLevel TOE.bWilsonWEXT
unifierIrreducibleDispatchMatchesTOE = refl

unifierCriticalDispatchMatchesTOE :
  U.toeCriticalFamilyLevel
    TOE.b2SameHamiltonian
  ≡ TOE.toeCriticalFamilyLevel TOE.b2SameHamiltonian
unifierCriticalDispatchMatchesTOE = refl


------------------------------------------------------------------------
-- Count-proof alias regressions.
------------------------------------------------------------------------

irreducibleFamilyCountProofAliasMatches :
  TOE.toeIrreducibleSourceFamilyCount ≡ 14
irreducibleFamilyCountProofAliasMatches =
  TOE.toeIrreducibleSourceFamilyCountIsFourteen

criticalFamilyCountProofAliasMatches :
  TOE.toeCriticalFamilyCount ≡ 7
criticalFamilyCountProofAliasMatches =
  TOE.toeCriticalFamilyCountIsSeven



------------------------------------------------------------------------
-- R546 firewall validation.
------------------------------------------------------------------------

opaqueEndpointPredicatesMatchR546 :
  TOE.toeOpaqueEndpointPredicatesRemaining
  ≡ R546.opaqueEndpointPredicatesRemaining
opaqueEndpointPredicatesMatchR546 = refl

opaqueEndpointPredicatesRemainFalse :
  TOE.toeOpaqueEndpointPredicatesRemaining ≡ false
opaqueEndpointPredicatesRemainFalse =
  TOE.toeOpaqueEndpointPredicatesRemainingIsFalse

constructorChoiceEqualitiesMatchR546 :
  TOE.toeConstructorChoiceEqualitiesRemaining
  ≡ R546.constructorChoiceEqualitiesRemaining
constructorChoiceEqualitiesMatchR546 = refl

constructorChoiceEqualitiesRemainFalse :
  TOE.toeConstructorChoiceEqualitiesRemaining ≡ false
constructorChoiceEqualitiesRemainFalse =
  TOE.toeConstructorChoiceEqualitiesRemainingIsFalse

allRemainingFamiliesProvedFlagMatchesR546 :
  TOE.toeAllRemainingFamiliesAlreadyProved
  ≡ R546.allRemainingFamiliesAreAlreadyProved
allRemainingFamiliesProvedFlagMatchesR546 = refl

allRemainingFamiliesAreNotAlreadyProved :
  TOE.toeAllRemainingFamiliesAlreadyProved ≡ false
allRemainingFamiliesAreNotAlreadyProved =
  TOE.toeAllRemainingFamiliesAlreadyProvedIsFalse


------------------------------------------------------------------------
-- R558 route-firewall max-cut validation.
------------------------------------------------------------------------

criticalSeparateContinuumWilsonMatchesR558 :
  TOE.toeCriticalSeparateContinuumWilsonConvergenceFamilyRequired
  ≡ R558.separateContinuumWilsonConvergenceFamilyRequired
criticalSeparateContinuumWilsonMatchesR558 = refl

criticalSeparateContinuumWilsonNotRequired :
  TOE.toeCriticalSeparateContinuumWilsonConvergenceFamilyRequired ≡ false
criticalSeparateContinuumWilsonNotRequired = refl

criticalFiniteHamiltonianMoscoMatchesR558 :
  TOE.toeCriticalFiniteHamiltonianMoscoRouteRequired
  ≡ R558.finiteHamiltonianMoscoRouteRequired
criticalFiniteHamiltonianMoscoMatchesR558 = refl

criticalFiniteHamiltonianMoscoNotRequired :
  TOE.toeCriticalFiniteHamiltonianMoscoRouteRequired ≡ false
criticalFiniteHamiltonianMoscoNotRequired = refl

criticalConservativeFullCLayerMatchesR558 :
  TOE.toeCriticalFullCLayerRetainedForConservativeClayExistence
  ≡ R558.fullCLayerRetainedForConservativeClayExistence
criticalConservativeFullCLayerMatchesR558 = refl

criticalConservativeFullCLayerRetained :
  TOE.toeCriticalFullCLayerRetainedForConservativeClayExistence ≡ true
criticalConservativeFullCLayerRetained = refl
