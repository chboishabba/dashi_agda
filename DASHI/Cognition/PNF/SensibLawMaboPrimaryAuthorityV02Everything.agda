module DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityV02Everything where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityParserBatchV02Exact as Batch
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityUseUpgradeExact as Upgrade
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityResidualRefinementV02Exact as Refined
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor
import DASHI.Cognition.PNF.SensibLawCalderAuthoritativeTranscriptionVerificationExact as Verify

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
-- Authoritative Calder transcription verification.
------------------------------------------------------------------------

hallIndependentTextVerified : Verify.authoritativeTranscriptionVerified Verify.hallIndependentTitleVerified ≡ true
hallIndependentTextVerified = refl
hallRecognitionTextVerified : Verify.authoritativeTranscriptionVerified Verify.hallRecognitionNotPrerequisiteVerified ≡ true
hallRecognitionTextVerified = refl
hallSurvivalTextVerified : Verify.authoritativeTranscriptionVerified Verify.hallSurvivalWithoutRecognitionVerified ≡ true
hallSurvivalTextVerified = refl
hallContinuityPresumptionTextVerified : Verify.authoritativeTranscriptionVerified Verify.hallContinuityPresumptionVerified ≡ true
hallContinuityPresumptionTextVerified = refl
hallClearPlainTextVerified : Verify.authoritativeTranscriptionVerified Verify.hallClearPlainBurdenVerified ≡ true
hallClearPlainTextVerified = refl

hallSpecificExtinguishmentIsSemanticNotVerbatimPromotion :
  Verify.verificationGrade Verify.hallSpecificExtinguishmentVerified ≡ Verify.semanticPropositionVerified
hallSpecificExtinguishmentIsSemanticNotVerbatimPromotion = refl

ocrHistoryStillRetainedAfterVerification : Batch.projectionKind Batch.calderHallIndependentTitleSpecimen ≡ Batch.ocrDerivedProjection
ocrHistoryStillRetainedAfterVerification = refl

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
-- Post-v0.2 residual state after authoritative Hall verification.
------------------------------------------------------------------------

radicalTitleStrengthenedByTextNativePrimary : Refined.state Refined.radicalTitleAfterV02 ≡ Refined.strengthenedByPrimaryTextNative
radicalTitleStrengthenedByTextNativePrimary = refl
continuityHasAuthoritativePrimaryContrast : Refined.state Refined.continuityAfterV02 ≡ Refined.authoritativePrimaryContrastVerified
continuityHasAuthoritativePrimaryContrast = refl
recognitionHasAuthoritativePrimaryContrast : Refined.state Refined.recognitionRequirementAfterV02 ≡ Refined.authoritativePrimaryContrastVerified
recognitionHasAuthoritativePrimaryContrast = refl

continuityPlanNeedsNoFurtherParserRun : Refined.parserRerunRequired Refined.continuityV02Plan ≡ false
continuityPlanNeedsNoFurtherParserRun = refl
recognitionPlanNeedsNoFurtherParserRun : Refined.parserRerunRequired Refined.recognitionV02Plan ≡ false
recognitionPlanNeedsNoFurtherParserRun = refl
enforceabilityPlanNeedsNoFurtherParserRun : Refined.parserRerunRequired Refined.enforceabilityV02Plan ≡ false
enforceabilityPlanNeedsNoFurtherParserRun = refl

continuityPlanHasNoHallVerificationResidual :
  Refined.residuals Refined.continuityV02Plan ≡
  (Refined.compareAmoduContinuityWithDawsonRecognitionUse ∷ Refined.reconcileContinuityAndRecognitionCoordinates ∷ [])
continuityPlanHasNoHallVerificationResidual = refl

recognitionPlanHasNoHallVerificationResidual :
  Refined.residuals Refined.recognitionV02Plan ≡
  (Refined.compareHallRecognitionIndependenceWithDawsonUse ∷ Refined.reconcileContinuityAndRecognitionCoordinates ∷ [])
recognitionPlanHasNoHallVerificationResidual = refl

------------------------------------------------------------------------
-- Firewalls promoted at the focused-root surface.
------------------------------------------------------------------------

ocrStillNotAuthoritativeTranscriptionByItself : Batch.OcrProjectionIsAuthoritativeTranscription → ⊥
ocrStillNotAuthoritativeTranscriptionByItself = Batch.ocrProjectionDoesNotBecomeAuthoritativeTranscription
parserStillDoesNotResolveCoordinate : Batch.ParserCandidateCreatesLegalCoordinateResolution → ⊥
parserStillDoesNotResolveCoordinate = Batch.parserCandidateDoesNotResolveLegalCoordinate
authoritativeTextStillDoesNotResolveCoordinate : Refined.AuthoritativeTranscriptionMeansCoordinateResolved → ⊥
authoritativeTextStillDoesNotResolveCoordinate = Refined.authoritativeTranscriptionDoesNotResolveCoordinate
sameAuthorityStillDoesNotMeanSameInterpretation : Upgrade.SameAuthorityMeansSameInterpretation → ⊥
sameAuthorityStillDoesNotMeanSameInterpretation = Upgrade.sameAuthorityDoesNotMeanSameInterpretation
primaryContrastDoesNotMakeLaterJudgmentFalse : Upgrade.PrimaryContrastMakesLaterJudgmentFalse → ⊥
primaryContrastDoesNotMakeLaterJudgmentFalse = Upgrade.primaryContrastDoesNotMakeLaterJudgmentFalse
hallVerificationDoesNotEraseJudsonResidual : Refined.HallVerificationEliminatesAllCalderResiduals → ⊥
hallVerificationDoesNotEraseJudsonResidual = Refined.hallVerificationDoesNotEliminateAllCalderResiduals
v02DoesNotCloseExactUnifiedTheory : Refined.TextNativeAmoduEvidenceResolvesExactMaboTheory → ⊥
v02DoesNotCloseExactUnifiedTheory = Refined.amoduEvidenceDoesNotResolveExactMaboTheory
