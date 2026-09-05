module DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityV02Everything where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityParserBatchV02Exact as Batch
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityUseUpgradeExact as Upgrade
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityResidualRefinementV02Exact as Refined
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor

------------------------------------------------------------------------
-- Exact runtime/source boundary.
------------------------------------------------------------------------

batchHasFiveSpecimens : Batch.specimenCount Batch.primaryAuthorityBatchV02 ≡ 5
batchHasFiveSpecimens = refl
batchHas197Paragraphs : Batch.paragraphCount Batch.primaryAuthorityBatchV02 ≡ 197
batchHas197Paragraphs = refl
batchHas453Sentences : Batch.sentenceCount Batch.primaryAuthorityBatchV02 ≡ 453
batchHas453Sentences = refl
batchHas22ReportingPredicates : Batch.reportingPredicateCount Batch.primaryAuthorityBatchV02 ≡ 22
batchHas22ReportingPredicates = refl

amoduRadicalUsesTextNativeProjection : Batch.projectionKind Batch.amoduRadicalTitleSpecimen ≡ Batch.textNativePdfProjection
amoduRadicalUsesTextNativeProjection = refl
amoduContinuityUsesTextNativeProjection : Batch.projectionKind Batch.amoduCessionContinuitySpecimen ≡ Batch.textNativePdfProjection
amoduContinuityUsesTextNativeProjection = refl
calderJudsonUsesOcrProjection : Batch.projectionKind Batch.calderJudsonRecognitionSpecimen ≡ Batch.ocrDerivedProjection
calderJudsonUsesOcrProjection = refl
calderHallIndependentUsesOcrProjection : Batch.projectionKind Batch.calderHallIndependentTitleSpecimen ≡ Batch.ocrDerivedProjection
calderHallIndependentUsesOcrProjection = refl
calderHallExtinguishmentUsesOcrProjection : Batch.projectionKind Batch.calderHallExtinguishmentContinuitySpecimen ≡ Batch.ocrDerivedProjection
calderHallExtinguishmentUsesOcrProjection = refl

------------------------------------------------------------------------
-- Primary proposition coordinates.
------------------------------------------------------------------------

amoduUsufructPaysRadicalTitleCoordinate : Primary.primaryCoordinate Primary.amoduUsufructBurdenProposition ≡ Factor.radicalTitleCompatibility
amoduUsufructPaysRadicalTitleCoordinate = refl
amoduCessionPaysContinuityCoordinate : Primary.primaryCoordinate Primary.amoduCessionContinuityProposition ≡ Factor.continuityAcrossSovereignty
amoduCessionPaysContinuityCoordinate = refl
hallSurvivalPaysContinuityCoordinate : Primary.primaryCoordinate Primary.hallSurvivalWithoutRecognitionProposition ≡ Factor.continuityAcrossSovereignty
hallSurvivalPaysContinuityCoordinate = refl
hallRecognitionPassageTargetsRecognitionRequirement : Primary.primaryCoordinate Primary.hallRecognitionNotPrerequisiteProposition ≡ Factor.crownRecognitionRequirement
hallRecognitionPassageTargetsRecognitionRequirement = refl
hallClearPlainPassageRemainsContinuityIndexed : Primary.primaryCoordinate Primary.hallClearPlainBurdenProposition ≡ Factor.continuityAcrossSovereignty
hallClearPlainPassageRemainsContinuityIndexed = refl

------------------------------------------------------------------------
-- Later-use / primary-text relations.
------------------------------------------------------------------------

brennanAmoduPrimarySupport : Upgrade.relation Upgrade.brennanAmoduRadicalTitleWeld ≡ Upgrade.primarySupportsLaterUse
brennanAmoduPrimarySupport = refl
brennanCalderPrimarySupport : Upgrade.relation Upgrade.brennanCalderSurvivalWeld ≡ Upgrade.primarySupportsLaterUse
brennanCalderPrimarySupport = refl
dawsonCalderHallPrimaryContrast : Upgrade.relation Upgrade.dawsonCalderRecognitionWeld ≡ Upgrade.primaryContrastsLaterUse
dawsonCalderHallPrimaryContrast = refl
dawsonAmoduPrimaryQualification : Upgrade.relation Upgrade.dawsonAmoduContinuityWeld ≡ Upgrade.primaryQualifiesLaterUse
dawsonAmoduPrimaryQualification = refl

------------------------------------------------------------------------
-- Post-v0.2 residual state.
------------------------------------------------------------------------

radicalTitleStrengthenedByTextNativePrimary : Refined.state Refined.radicalTitleAfterV02 ≡ Refined.strengthenedByPrimaryTextNative
radicalTitleStrengthenedByTextNativePrimary = refl
continuityStrengthenedByTextNativePrimary : Refined.state Refined.continuityAfterV02 ≡ Refined.strengthenedByPrimaryTextNative
continuityStrengthenedByTextNativePrimary = refl
recognitionContrastNowLocatedInPrimaryMaterial : Refined.state Refined.recognitionRequirementAfterV02 ≡ Refined.primaryInterpretiveContrastLocated
recognitionContrastNowLocatedInPrimaryMaterial = refl

continuityPlanNeedsNoFurtherParserRun : Refined.parserRerunRequired Refined.continuityV02Plan ≡ false
continuityPlanNeedsNoFurtherParserRun = refl
recognitionPlanNeedsNoFurtherParserRun : Refined.parserRerunRequired Refined.recognitionV02Plan ≡ false
recognitionPlanNeedsNoFurtherParserRun = refl
enforceabilityPlanNeedsNoFurtherParserRun : Refined.parserRerunRequired Refined.enforceabilityV02Plan ≡ false
enforceabilityPlanNeedsNoFurtherParserRun = refl

------------------------------------------------------------------------
-- Firewalls promoted at the focused-root surface.
------------------------------------------------------------------------

ocrStillNotAuthoritativeTranscription : Batch.OcrProjectionIsAuthoritativeTranscription → ⊥
ocrStillNotAuthoritativeTranscription = Batch.ocrProjectionDoesNotBecomeAuthoritativeTranscription
parserStillDoesNotResolveCoordinate : Batch.ParserCandidateCreatesLegalCoordinateResolution → ⊥
parserStillDoesNotResolveCoordinate = Batch.parserCandidateDoesNotResolveLegalCoordinate
primaryEvidenceStillDoesNotResolveCoordinate : Refined.PrimaryParserEvidenceMeansCoordinateResolved → ⊥
primaryEvidenceStillDoesNotResolveCoordinate = Refined.primaryParserEvidenceDoesNotResolveCoordinate
sameAuthorityStillDoesNotMeanSameInterpretation : Upgrade.SameAuthorityMeansSameInterpretation → ⊥
sameAuthorityStillDoesNotMeanSameInterpretation = Upgrade.sameAuthorityDoesNotMeanSameInterpretation
primaryContrastDoesNotMakeLaterJudgmentFalse : Upgrade.PrimaryContrastMakesLaterJudgmentFalse → ⊥
primaryContrastDoesNotMakeLaterJudgmentFalse = Upgrade.primaryContrastDoesNotMakeLaterJudgmentFalse
v02DoesNotCloseExactUnifiedTheory : Refined.TextNativeAmoduEvidenceResolvesExactMaboTheory → ⊥
v02DoesNotCloseExactUnifiedTheory = Refined.amoduEvidenceDoesNotResolveExactMaboTheory
