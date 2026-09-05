module DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityParserBatchV02Exact as Batch
import DASHI.Cognition.PNF.SensibLawMaboRecognitionBasisAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status

data PrimaryTextQuality : Set where
  textNativePrimary
  ocrPrimaryProjection
  : PrimaryTextQuality

data CoordinatePositionKind : Set where
  supportsCoordinate
  deniesDependency
  statesContinuityPresumption
  statesExtinguishmentCondition
  allocatesProofBurden
  distinguishesTitleStructure
  authorityInterpretationPosition
  : CoordinatePositionKind

record ReviewedPrimaryAuthorityProposition : Set where
  constructor reviewedPrimaryAuthorityProposition
  field
    propositionReference : String
    authorityIdentity : Authority.LegalAuthorityIdentity
    sourceSpecimenReference : String
    parserAnchorReference : String
    propositionSummary : String
    primaryCoordinate : Factor.RecognitionCoordinate
    additionalCoordinates : List Factor.RecognitionCoordinate
    positionKind : CoordinatePositionKind
    propositionStatus : Status.PropositionStatus
    truthStatus : Status.TruthStatus
    textQuality : PrimaryTextQuality
    reviewedCoordinateClassification : Bool
    reviewedCoordinateClassificationIsTrue : reviewedCoordinateClassification ≡ true
    parserAloneSelectedCoordinate : Bool
    parserAloneSelectedCoordinateIsFalse : parserAloneSelectedCoordinate ≡ false
    parserAloneCreatesHolding : Bool
    parserAloneCreatesHoldingIsFalse : parserAloneCreatesHolding ≡ false
open ReviewedPrimaryAuthorityProposition public

amoduUsufructBurdenProposition : ReviewedPrimaryAuthorityProposition
amoduUsufructBurdenProposition = reviewedPrimaryAuthorityProposition
  "proposition:amodu:usufruct-burdens-radical-title"
  Authority.amoduTijani
  (Batch.specimenId Batch.amoduRadicalTitleSpecimen)
  (Batch.anchorReference Batch.amoduUsufructRadicalAnchor)
  "reviewed primary proposition: a usual native title may take the form of a usufructuary right qualifying or burdening the Sovereign's radical/final title"
  Factor.radicalTitleCompatibility
  (Factor.enforceabilityAgainstCrown ∷ [])
  distinguishesTitleStructure
  Status.represented Status.truthUnresolved textNativePrimary
  true refl false refl false refl

amoduPureLegalEstateProposition : ReviewedPrimaryAuthorityProposition
amoduPureLegalEstateProposition = reviewedPrimaryAuthorityProposition
  "proposition:amodu:sovereign-title-pure-legal-estate"
  Authority.amoduTijani
  (Batch.specimenId Batch.amoduRadicalTitleSpecimen)
  (Batch.anchorReference Batch.amoduPureLegalEstateAnchor)
  "reviewed primary proposition: the Sovereign's title may be a pure legal estate to which beneficial rights may or may not attach"
  Factor.radicalTitleCompatibility
  (Factor.enforceabilityAgainstCrown ∷ [])
  distinguishesTitleStructure
  Status.represented Status.truthUnresolved textNativePrimary
  true refl false refl false refl

amoduCessionContinuityProposition : ReviewedPrimaryAuthorityProposition
amoduCessionContinuityProposition = reviewedPrimaryAuthorityProposition
  "proposition:amodu:cession-sovereignty-respects-inhabitant-rights"
  Authority.amoduTijani
  (Batch.specimenId Batch.amoduCessionContinuitySpecimen)
  (Batch.anchorReference Batch.amoduCessionRespectAnchor)
  "reviewed primary proposition: cession of sovereignty/radical title was treated on the footing that inhabitants' property rights were to be fully respected"
  Factor.continuityAcrossSovereignty
  (Factor.antecedentRightExistence ∷ Factor.radicalTitleCompatibility ∷ [])
  supportsCoordinate
  Status.represented Status.truthUnresolved textNativePrimary
  true refl false refl false refl

amoduNoBeneficialDisplacementProposition : ReviewedPrimaryAuthorityProposition
amoduNoBeneficialDisplacementProposition = reviewedPrimaryAuthorityProposition
  "proposition:amodu:cession-does-not-displace-presumptive-native-title"
  Authority.amoduTijani
  (Batch.specimenId Batch.amoduCessionContinuitySpecimen)
  (Batch.anchorReference Batch.amoduNoBeneficialDisplacementAnchor)
  "reviewed primary proposition: cession to the Crown does not justify treating the Crown as beneficial owner so as to displace presumptive native title"
  Factor.continuityAcrossSovereignty
  (Factor.radicalTitleCompatibility ∷ Factor.enforceabilityAgainstCrown ∷ [])
  deniesDependency
  Status.represented Status.truthUnresolved textNativePrimary
  true refl false refl false refl

hallIndependentTitleProposition : ReviewedPrimaryAuthorityProposition
hallIndependentTitleProposition = reviewedPrimaryAuthorityProposition
  "proposition:calder:hall:title-independent-of-formal-grant"
  Authority.calder
  (Batch.specimenId Batch.calderHallIndependentTitleSpecimen)
  (Batch.anchorReference Batch.hallIndependentTitleAnchor)
  "reviewed OCR-primary proposition: aboriginal Indian title does not depend on treaty, executive order or legislative enactment"
  Factor.antecedentRightExistence
  (Factor.continuityAcrossSovereignty ∷ [])
  deniesDependency
  Status.represented Status.truthUnresolved ocrPrimaryProjection
  true refl false refl false refl

hallRecognitionNotPrerequisiteProposition : ReviewedPrimaryAuthorityProposition
hallRecognitionNotPrerequisiteProposition = reviewedPrimaryAuthorityProposition
  "proposition:calder:hall:affirmative-recognition-not-prerequisite"
  Authority.calder
  (Batch.specimenId Batch.calderHallIndependentTitleSpecimen)
  (Batch.anchorReference Batch.hallRecognitionNotPrerequisiteAnchor)
  "reviewed OCR-primary proposition: affirmative governmental recognition or approval is not a prerequisite to existence of original title"
  Factor.crownRecognitionRequirement
  (Factor.antecedentRightExistence ∷ [])
  deniesDependency
  Status.represented Status.truthUnresolved ocrPrimaryProjection
  true refl false refl false refl

hallSurvivalWithoutRecognitionProposition : ReviewedPrimaryAuthorityProposition
hallSurvivalWithoutRecognitionProposition = reviewedPrimaryAuthorityProposition
  "proposition:calder:hall:survival-independent-of-sovereign-recognition"
  Authority.calder
  (Batch.specimenId Batch.calderHallIndependentTitleSpecimen)
  (Batch.anchorReference Batch.hallSurvivalWithoutRecognitionAnchor)
  "reviewed OCR-primary proposition: original Indian title based on aboriginal possession does not depend on sovereign recognition or affirmative acceptance for survival"
  Factor.continuityAcrossSovereignty
  (Factor.crownRecognitionRequirement ∷ Factor.antecedentRightExistence ∷ [])
  deniesDependency
  Status.represented Status.truthUnresolved ocrPrimaryProjection
  true refl false refl false refl

hallEnduresUntilExtinguishedProposition : ReviewedPrimaryAuthorityProposition
hallEnduresUntilExtinguishedProposition = reviewedPrimaryAuthorityProposition
  "proposition:calder:hall:title-endures-until-extinguished-or-abandoned"
  Authority.calder
  (Batch.specimenId Batch.calderHallIndependentTitleSpecimen)
  (Batch.anchorReference Batch.hallEnduresUntilExtinguishedAnchor)
  "reviewed OCR-primary proposition: once established in fact, title endures until extinguished or abandoned"
  Factor.continuityAcrossSovereignty
  (Factor.antecedentRightExistence ∷ [])
  statesContinuityPresumption
  Status.represented Status.truthUnresolved ocrPrimaryProjection
  true refl false refl false refl

hallContinuityPresumptionProposition : ReviewedPrimaryAuthorityProposition
hallContinuityPresumptionProposition = reviewedPrimaryAuthorityProposition
  "proposition:calder:hall:presumed-continuity-until-contrary-proven"
  Authority.calder
  (Batch.specimenId Batch.calderHallExtinguishmentContinuitySpecimen)
  (Batch.anchorReference Batch.hallPresumedContinuityAnchor)
  "reviewed OCR-primary proposition: once aboriginal title is established it is presumed to continue until the contrary is proven"
  Factor.continuityAcrossSovereignty
  (Factor.antecedentRightExistence ∷ [])
  statesContinuityPresumption
  Status.represented Status.truthUnresolved ocrPrimaryProjection
  true refl false refl false refl

hallSpecificExtinguishmentProposition : ReviewedPrimaryAuthorityProposition
hallSpecificExtinguishmentProposition = reviewedPrimaryAuthorityProposition
  "proposition:calder:hall:extinguishment-requires-surrender-or-specific-legislation"
  Authority.calder
  (Batch.specimenId Batch.calderHallExtinguishmentContinuitySpecimen)
  (Batch.anchorReference Batch.hallSpecificExtinguishmentAnchor)
  "reviewed OCR-primary proposition: a legal right could thereafter be extinguished by surrender or competent legislative authority, with legislation specifically directed to extinguishment"
  Factor.continuityAcrossSovereignty
  (Factor.authorityInterpretation ∷ [])
  statesExtinguishmentCondition
  Status.represented Status.truthUnresolved ocrPrimaryProjection
  true refl false refl false refl

hallClearPlainBurdenProposition : ReviewedPrimaryAuthorityProposition
hallClearPlainBurdenProposition = reviewedPrimaryAuthorityProposition
  "proposition:calder:hall:respondent-bears-clear-plain-extinguishment-onus"
  Authority.calder
  (Batch.specimenId Batch.calderHallExtinguishmentContinuitySpecimen)
  (Batch.anchorReference Batch.hallClearPlainAnchor)
  "reviewed OCR-primary proposition: the respondent bears the onus of proving sovereign intention to extinguish, and that intention must be clear and plain"
  Factor.continuityAcrossSovereignty
  (Factor.authorityInterpretation ∷ [])
  allocatesProofBurden
  Status.represented Status.truthUnresolved ocrPrimaryProjection
  true refl false refl false refl

judsonRecognizedUnrecognizedProposition : ReviewedPrimaryAuthorityProposition
judsonRecognizedUnrecognizedProposition = reviewedPrimaryAuthorityProposition
  "proposition:calder:judson:recognized-unrecognized-dichotomy-discussed"
  Authority.calder
  (Batch.specimenId Batch.calderJudsonRecognitionSpecimen)
  (Batch.anchorReference Batch.judsonRecognizedUnrecognizedAnchor)
  "reviewed OCR-primary proposition: Judson J reproduces the United States authority's rejection of a simple recognised/unrecognised title dichotomy in the compensation context"
  Factor.authorityInterpretation
  (Factor.crownRecognitionRequirement ∷ [])
  authorityInterpretationPosition
  Status.represented Status.truthUnresolved ocrPrimaryProjection
  true refl false refl false refl

record PrimaryCoordinateEvidence : Set where
  constructor primaryCoordinateEvidence
  field
    coordinate : Factor.RecognitionCoordinate
    propositions : List ReviewedPrimaryAuthorityProposition
    evidenceReference : String
    coordinateResolved : Bool
    coordinateResolvedIsFalse : coordinateResolved ≡ false
open PrimaryCoordinateEvidence public

amoduRadicalTitleEvidence : PrimaryCoordinateEvidence
amoduRadicalTitleEvidence = primaryCoordinateEvidence
  Factor.radicalTitleCompatibility
  (amoduUsufructBurdenProposition ∷ amoduPureLegalEstateProposition ∷ amoduNoBeneficialDisplacementProposition ∷ [])
  "text-native Amodu primary propositions bearing on radical-title / beneficial-ownership structure"
  false refl

amoduContinuityEvidence : PrimaryCoordinateEvidence
amoduContinuityEvidence = primaryCoordinateEvidence
  Factor.continuityAcrossSovereignty
  (amoduCessionContinuityProposition ∷ amoduNoBeneficialDisplacementProposition ∷ [])
  "text-native Amodu primary propositions bearing on continuity across cession/change of sovereignty"
  false refl

calderHallContinuityEvidence : PrimaryCoordinateEvidence
calderHallContinuityEvidence = primaryCoordinateEvidence
  Factor.continuityAcrossSovereignty
  (hallSurvivalWithoutRecognitionProposition ∷ hallEnduresUntilExtinguishedProposition ∷ hallContinuityPresumptionProposition ∷ hallSpecificExtinguishmentProposition ∷ hallClearPlainBurdenProposition ∷ [])
  "OCR-derived Hall primary propositions bearing on continuity and extinguishment; transcription still requires source verification"
  false refl

calderRecognitionEvidence : PrimaryCoordinateEvidence
calderRecognitionEvidence = primaryCoordinateEvidence
  Factor.crownRecognitionRequirement
  (hallRecognitionNotPrerequisiteProposition ∷ hallSurvivalWithoutRecognitionProposition ∷ judsonRecognizedUnrecognizedProposition ∷ [])
  "OCR-derived Calder Hall/Judson propositions bearing differently on recognition; not collapsed into one resolved doctrine"
  false refl

data ParserAnchorIsReviewedProposition : Set where
data OcrPrimaryProjectionIsAuthoritativeQuotation : Set where
data CoordinateEvidenceMeansCoordinateResolved : Set where
data OneAuthorityPropositionDeterminesMaboUse : Set where
data PrimaryPropositionMakesWorldTruth : Set where

parserAnchorDoesNotBecomeReviewedProposition : ParserAnchorIsReviewedProposition → ⊥
parserAnchorDoesNotBecomeReviewedProposition ()
ocrPrimaryProjectionDoesNotBecomeAuthoritativeQuotation : OcrPrimaryProjectionIsAuthoritativeQuotation → ⊥
ocrPrimaryProjectionDoesNotBecomeAuthoritativeQuotation ()
coordinateEvidenceDoesNotMeanResolved : CoordinateEvidenceMeansCoordinateResolved → ⊥
coordinateEvidenceDoesNotMeanResolved ()
oneAuthorityPropositionDoesNotDetermineMaboUse : OneAuthorityPropositionDeterminesMaboUse → ⊥
oneAuthorityPropositionDoesNotDetermineMaboUse ()
primaryPropositionDoesNotMakeWorldTruth : PrimaryPropositionMakesWorldTruth → ⊥
primaryPropositionDoesNotMakeWorldTruth ()
