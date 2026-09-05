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

------------------------------------------------------------------------
-- Evidence grade after consuming primary-authority-parser-batch-v0.2.
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
  strengthenedByPrimaryTextNative
  reviewedPrimaryPropositionEvidence
  "Amodu text-native cession/continuity propositions plus Calder Hall OCR continuity propositions; strongest source grade is the text-native Amodu primary path"
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
  primaryInterpretiveContrastLocated
  primaryOcrParserEvidence
  "Calder Hall OCR-primary propositions deny affirmative sovereign recognition as prerequisite while Dawson's reviewed Mabo use reads Calder through recognition; exact OCR/transcription verification remains open"
  false refl false refl

authorityInterpretationAfterV02 : RefinedCoordinateReceipt
authorityInterpretationAfterV02 = refinedCoordinateReceipt
  Factor.authorityInterpretation
  primaryInterpretiveContrastLocated
  primaryOcrParserEvidence
  "Judson OCR-primary recognised/unrecognised-title discussion plus Hall recognition-independence passages now permit proposition-level authority-use comparison, but OCR remains a source-quality residual"
  false refl false refl

------------------------------------------------------------------------
-- Query-specific residuals after v0.2.
------------------------------------------------------------------------

data PostV02Residual : Set where
  verifyCalderOcrAgainstAuthoritativeText
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
  (verifyCalderOcrAgainstAuthoritativeText ∷ compareAmoduContinuityWithDawsonRecognitionUse ∷ [])
  comparePropositionsWork false refl false refl
  "v0.2 already provides Amodu primary parser evidence and Calder Hall OCR; continuity work now compares propositions and verifies Calder OCR rather than retrieving/reparsing sources"
postV02Plan Factor.identifyCrownRecognitionRule = postV02WorkPlan
  Factor.identifyCrownRecognitionRule
  (verifyCalderOcrAgainstAuthoritativeText ∷ compareHallRecognitionIndependenceWithDawsonUse ∷ [])
  verifySourceWork false refl false refl
  "recognition requirement now has a located Hall-v-Dawson interpretive contrast; authoritative Calder transcription verification is the leading source residual"
postV02Plan Factor.identifyRecognitionByConductRule = postV02WorkPlan
  Factor.identifyRecognitionByConductRule
  (verifyCalderOcrAgainstAuthoritativeText ∷ compareHallRecognitionIndependenceWithDawsonUse ∷ [])
  comparePropositionsWork false refl false refl
  "recognition-by-conduct analysis can proceed from Dawson plus Calder OCR-primary material, but OCR provenance blocks exact primary proposition promotion"
postV02Plan Factor.identifyEnforceabilityStructure = postV02WorkPlan
  Factor.identifyEnforceabilityStructure
  (compareAmoduContinuityWithDawsonRecognitionUse ∷ [])
  comparePropositionsWork false refl false refl
  "Amodu text-native primary parser evidence is already available; no further parser/source retrieval is required for the current enforceability discriminator"
postV02Plan Factor.identifyExactUnifiedTheory = postV02WorkPlan
  Factor.identifyExactUnifiedTheory
  (verifyCalderOcrAgainstAuthoritativeText ∷ reconcileContinuityAndRecognitionCoordinates ∷ synthesizeExactUnifiedTheory ∷ [])
  synthesizeTheoryWork false refl false refl
  "exact unified theory remains open after v0.2; source-quality verification and cross-coordinate synthesis remain distinct obligations"

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

------------------------------------------------------------------------
-- Exact evidence-presence witnesses from the new batch.
------------------------------------------------------------------------

amoduRadicalTextNative : Batch.projectionKind Batch.amoduRadicalTitleSpecimen ≡ Batch.textNativePdfProjection
amoduRadicalTextNative = refl
amoduContinuityTextNative : Batch.projectionKind Batch.amoduCessionContinuitySpecimen ≡ Batch.textNativePdfProjection
amoduContinuityTextNative = refl
calderHallIndependentIsOcr : Batch.projectionKind Batch.calderHallIndependentTitleSpecimen ≡ Batch.ocrDerivedProjection
calderHallIndependentIsOcr = refl
calderHallExtinguishmentIsOcr : Batch.projectionKind Batch.calderHallExtinguishmentContinuitySpecimen ≡ Batch.ocrDerivedProjection
calderHallExtinguishmentIsOcr = refl

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
data OcrLocatedContrastMeansAuthoritativeTranscription : Set where
data TextNativeAmoduEvidenceResolvesExactMaboTheory : Set where
data V02EliminatesAllSourceResiduals : Set where
data ParserRunDeterminesLaterAuthorityInterpretation : Set where

primaryParserEvidenceDoesNotResolveCoordinate : PrimaryParserEvidenceMeansCoordinateResolved → ⊥
primaryParserEvidenceDoesNotResolveCoordinate ()
ocrContrastDoesNotVerifyTranscription : OcrLocatedContrastMeansAuthoritativeTranscription → ⊥
ocrContrastDoesNotVerifyTranscription ()
amoduEvidenceDoesNotResolveExactMaboTheory : TextNativeAmoduEvidenceResolvesExactMaboTheory → ⊥
amoduEvidenceDoesNotResolveExactMaboTheory ()
v02DoesNotEliminateAllResiduals : V02EliminatesAllSourceResiduals → ⊥
v02DoesNotEliminateAllResiduals ()
parserRunDoesNotDetermineLaterInterpretation : ParserRunDeterminesLaterAuthorityInterpretation → ⊥
parserRunDoesNotDetermineLaterInterpretation ()
