module DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityResidualRefinementV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityParserBatchV02Exact as Batch
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityUseUpgradeExact as Upgrade
import DASHI.Cognition.PNF.SensibLawCalderAuthoritativeTranscriptionVerificationExact as Verify

------------------------------------------------------------------------
-- Evidence grade after consuming primary-authority-parser-batch-v0.2 and
-- the independent Supreme Court of Canada transcription verification.
------------------------------------------------------------------------

data PrimaryEvidenceGrade : Set where
  sourceUnrecovered
  primaryOcrParserEvidence
  primaryTextNativeParserEvidence
  reviewedPrimaryPropositionEvidence
  authoritativeTranscriptionVerified
  : PrimaryEvidenceGrade

data RefinedCoordinateState : Set where
  coordinateUnassessed
  candidateFromReviewedUse
  strengthenedByPrimaryOcr
  strengthenedByPrimaryTextNative
  primaryInterpretiveContrastLocated
  authoritativePrimaryContrastVerified
  coordinateResolved
  : RefinedCoordinateState

record RefinedCoordinateReceipt : Set where
  constructor refinedCoordinateReceipt
  field
    coordinate : Factor.RecognitionCoordinate
    state : RefinedCoordinateState
    strongestEvidenceGrade : PrimaryEvidenceGrade
    evidenceReference : String
    parserRerunRequired : Bool
    parserRerunRequiredIsFalse : parserRerunRequired ≡ false
    finalLegalResolutionClaimed : Bool
    finalLegalResolutionClaimedIsFalse : finalLegalResolutionClaimed ≡ false
open RefinedCoordinateReceipt public

radicalTitleAfterV02 : RefinedCoordinateReceipt
radicalTitleAfterV02 = refinedCoordinateReceipt
  Factor.radicalTitleCompatibility
  strengthenedByPrimaryTextNative
  reviewedPrimaryPropositionEvidence
  "Amodu text-native parser + reviewed primary propositions: usufruct burdens radical/final title; Sovereign title may be a pure legal estate distinct from beneficial rights"
  false refl false refl

continuityAfterV02 : RefinedCoordinateReceipt
continuityAfterV02 = refinedCoordinateReceipt
  Factor.continuityAcrossSovereignty
  authoritativePrimaryContrastVerified
  authoritativeTranscriptionVerified
  "Amodu text-native continuity propositions plus Hall continuity/survival propositions independently verified against the Supreme Court of Canada Calder transcription"
  false refl false refl

enforceabilityAfterV02 : RefinedCoordinateReceipt
enforceabilityAfterV02 = refinedCoordinateReceipt
  Factor.enforceabilityAgainstCrown
  strengthenedByPrimaryTextNative
  reviewedPrimaryPropositionEvidence
  "Amodu primary propositions distinguish radical legal estate from beneficial/native usufructuary rights and deny automatic beneficial displacement on cession"
  false refl false refl

recognitionRequirementAfterV02 : RefinedCoordinateReceipt
recognitionRequirementAfterV02 = refinedCoordinateReceipt
  Factor.crownRecognitionRequirement
  authoritativePrimaryContrastVerified
  authoritativeTranscriptionVerified
  "Hall's recognition-not-prerequisite and survival-without-recognition propositions are independently verified against the official SCC Calder transcription; these verified primary propositions contrast with Dawson's reviewed Calder recognition reading"
  false refl false refl

authorityInterpretationAfterV02 : RefinedCoordinateReceipt
authorityInterpretationAfterV02 = refinedCoordinateReceipt
  Factor.authorityInterpretation
  primaryInterpretiveContrastLocated
  primaryOcrParserEvidence
  "Hall recognition-independence propositions are SCC-transcription verified, but the separate Judson recognised/unrecognised-title OCR specimen remains OCR-derived if exact Judson proposition identity is required"
  false refl false refl

------------------------------------------------------------------------
-- Query-specific residuals after authoritative Hall verification.
------------------------------------------------------------------------

data PostV02Residual : Set where
  verifyRemainingCalderJudsonOcrIfNeeded
  compareHallRecognitionIndependenceWithDawsonUse
  compareAmoduContinuityWithDawsonRecognitionUse
  reconcileContinuityAndRecognitionCoordinates
  synthesizeExactUnifiedTheory
  : PostV02Residual

data PostV02WorkKind : Set where
  verifySourceWork
  comparePropositionsWork
  synthesizeTheoryWork
  : PostV02WorkKind

record PostV02WorkPlan : Set where
  constructor postV02WorkPlan
  field
    query : Factor.RecognitionQuery
    residuals : List PostV02Residual
    workKind : PostV02WorkKind
    parserRerunRequired : Bool
    parserRerunRequiredIsFalse : parserRerunRequired ≡ false
    wholeJudgmentRescanRequired : Bool
    wholeJudgmentRescanRequiredIsFalse : wholeJudgmentRescanRequired ≡ false
    planReference : String
open PostV02WorkPlan public

postV02Plan : Factor.RecognitionQuery → PostV02WorkPlan
postV02Plan Factor.identifyContinuityRule = postV02WorkPlan
  Factor.identifyContinuityRule
  (compareAmoduContinuityWithDawsonRecognitionUse ∷ reconcileContinuityAndRecognitionCoordinates ∷ [])
  comparePropositionsWork false refl false refl
  "Hall continuity/survival text is now SCC-transcription verified; continuity work is proposition-level comparison/synthesis, not OCR recovery or parser rerun"
postV02Plan Factor.identifyCrownRecognitionRule = postV02WorkPlan
  Factor.identifyCrownRecognitionRule
  (compareHallRecognitionIndependenceWithDawsonUse ∷ reconcileContinuityAndRecognitionCoordinates ∷ [])
  comparePropositionsWork false refl false refl
  "Hall recognition-independence text is now SCC-transcription verified; the leading residual is interpretation of Hall against Dawson, not transcription recovery"
postV02Plan Factor.identifyRecognitionByConductRule = postV02WorkPlan
  Factor.identifyRecognitionByConductRule
  (compareHallRecognitionIndependenceWithDawsonUse ∷ verifyRemainingCalderJudsonOcrIfNeeded ∷ [])
  comparePropositionsWork false refl false refl
  "Hall source-quality residual is paid; exact Judson OCR verification remains conditional only if the Judson-side authority interpretation is needed to decide recognition-by-conduct"
postV02Plan Factor.identifyEnforceabilityStructure = postV02WorkPlan
  Factor.identifyEnforceabilityStructure
  (compareAmoduContinuityWithDawsonRecognitionUse ∷ [])
  comparePropositionsWork false refl false refl
  "Amodu text-native primary evidence is already available; no further parser/source retrieval is required for the current enforceability discriminator"
postV02Plan Factor.identifyExactUnifiedTheory = postV02WorkPlan
  Factor.identifyExactUnifiedTheory
  (verifyRemainingCalderJudsonOcrIfNeeded ∷ reconcileContinuityAndRecognitionCoordinates ∷ synthesizeExactUnifiedTheory ∷ [])
  synthesizeTheoryWork false refl false refl
  "Hall transcription-quality residual is closed; exact unified theory remains open because cross-coordinate jurisprudential synthesis and, if material, exact Judson verification remain separate obligations"

continuityV02Plan : PostV02WorkPlan
continuityV02Plan = postV02Plan Factor.identifyContinuityRule
recognitionV02Plan : PostV02WorkPlan
recognitionV02Plan = postV02Plan Factor.identifyCrownRecognitionRule
enforceabilityV02Plan : PostV02WorkPlan
enforceabilityV02Plan = postV02Plan Factor.identifyEnforceabilityStructure

continuityNoLongerNeedsPrimaryParserRun : parserRerunRequired continuityV02Plan ≡ false
continuityNoLongerNeedsPrimaryParserRun = refl
recognitionNoLongerNeedsPrimaryParserRun : parserRerunRequired recognitionV02Plan ≡ false
recognitionNoLongerNeedsPrimaryParserRun = refl
enforceabilityNoLongerNeedsPrimaryParserRun : parserRerunRequired enforceabilityV02Plan ≡ false
enforceabilityNoLongerNeedsPrimaryParserRun = refl

continuityNoLongerHasHallVerificationResidual :
  residuals continuityV02Plan ≡
  (compareAmoduContinuityWithDawsonRecognitionUse ∷ reconcileContinuityAndRecognitionCoordinates ∷ [])
continuityNoLongerHasHallVerificationResidual = refl

recognitionNoLongerHasHallVerificationResidual :
  residuals recognitionV02Plan ≡
  (compareHallRecognitionIndependenceWithDawsonUse ∷ reconcileContinuityAndRecognitionCoordinates ∷ [])
recognitionNoLongerHasHallVerificationResidual = refl

------------------------------------------------------------------------
-- Exact evidence-presence and source-verification witnesses.
------------------------------------------------------------------------

amoduRadicalTextNative : Batch.projectionKind Batch.amoduRadicalTitleSpecimen ≡ Batch.textNativePdfProjection
amoduRadicalTextNative = refl
amoduContinuityTextNative : Batch.projectionKind Batch.amoduCessionContinuitySpecimen ≡ Batch.textNativePdfProjection
amoduContinuityTextNative = refl
calderHallIndependentIsOcr : Batch.projectionKind Batch.calderHallIndependentTitleSpecimen ≡ Batch.ocrDerivedProjection
calderHallIndependentIsOcr = refl
calderHallExtinguishmentIsOcr : Batch.projectionKind Batch.calderHallExtinguishmentContinuitySpecimen ≡ Batch.ocrDerivedProjection
calderHallExtinguishmentIsOcr = refl

hallIndependentNowAuthoritativelyVerified : Verify.authoritativeTranscriptionVerified Verify.hallIndependentTitleVerified ≡ true
hallIndependentNowAuthoritativelyVerified = refl
hallRecognitionNowAuthoritativelyVerified : Verify.authoritativeTranscriptionVerified Verify.hallRecognitionNotPrerequisiteVerified ≡ true
hallRecognitionNowAuthoritativelyVerified = refl
hallSurvivalNowAuthoritativelyVerified : Verify.authoritativeTranscriptionVerified Verify.hallSurvivalWithoutRecognitionVerified ≡ true
hallSurvivalNowAuthoritativelyVerified = refl
hallContinuityNowAuthoritativelyVerified : Verify.authoritativeTranscriptionVerified Verify.hallContinuityPresumptionVerified ≡ true
hallContinuityNowAuthoritativelyVerified = refl
hallClearPlainNowAuthoritativelyVerified : Verify.authoritativeTranscriptionVerified Verify.hallClearPlainBurdenVerified ≡ true
hallClearPlainNowAuthoritativelyVerified = refl

calderRecognitionContrastLocated : Upgrade.relation Upgrade.dawsonCalderRecognitionWeld ≡ Upgrade.primaryContrastsLaterUse
calderRecognitionContrastLocated = refl
brennanCalderContinuitySupported : Upgrade.relation Upgrade.brennanCalderSurvivalWeld ≡ Upgrade.primarySupportsLaterUse
brennanCalderContinuitySupported = refl
brennanAmoduRadicalSupported : Upgrade.relation Upgrade.brennanAmoduRadicalTitleWeld ≡ Upgrade.primarySupportsLaterUse
brennanAmoduRadicalSupported = refl

------------------------------------------------------------------------
-- No-promotion / residual discipline.
------------------------------------------------------------------------

data PrimaryParserEvidenceMeansCoordinateResolved : Set where
data AuthoritativeTranscriptionMeansCoordinateResolved : Set where
data TextNativeAmoduEvidenceResolvesExactMaboTheory : Set where
data HallVerificationEliminatesAllCalderResiduals : Set where
data ParserRunDeterminesLaterAuthorityInterpretation : Set where

primaryParserEvidenceDoesNotResolveCoordinate : PrimaryParserEvidenceMeansCoordinateResolved → ⊥
primaryParserEvidenceDoesNotResolveCoordinate ()
authoritativeTranscriptionDoesNotResolveCoordinate : AuthoritativeTranscriptionMeansCoordinateResolved → ⊥
authoritativeTranscriptionDoesNotResolveCoordinate ()
amoduEvidenceDoesNotResolveExactMaboTheory : TextNativeAmoduEvidenceResolvesExactMaboTheory → ⊥
amoduEvidenceDoesNotResolveExactMaboTheory ()
hallVerificationDoesNotEliminateAllCalderResiduals : HallVerificationEliminatesAllCalderResiduals → ⊥
hallVerificationDoesNotEliminateAllCalderResiduals ()
parserRunDoesNotDetermineLaterInterpretation : ParserRunDeterminesLaterAuthorityInterpretation → ⊥
parserRunDoesNotDetermineLaterInterpretation ()
