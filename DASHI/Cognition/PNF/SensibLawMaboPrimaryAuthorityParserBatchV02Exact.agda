module DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityParserBatchV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact source boundary for primary-authority-parser-batch-v0.2.
--
-- This owner intentionally records parser observations and source provenance,
-- not judicial holdings or authoritative legal propositions.  In particular,
-- the Calder specimens are Tesseract-OCR projections of the supplied scan and
-- are therefore not promoted to authoritative transcription.
------------------------------------------------------------------------

data TextProjectionKind : Set where
  textNativePdfProjection
  ocrDerivedProjection
  : TextProjectionKind

record PrimaryAuthoritySpecimenReceipt : Set where
  constructor primaryAuthoritySpecimenReceipt
  field
    specimenId : String
    sourceReference : String
    sourcePassage : String
    reviewedContext : String
    fixtureSha256 : String
    bytes paragraphs sentences reportingPredicates : Nat
    projectionKind : TextProjectionKind
    authority : String
    parserModel : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    parserAloneAuthorizesTruth : Bool
    parserAloneAuthorizesTruthIsFalse : parserAloneAuthorizesTruth ≡ false
    parserAloneAuthorizesOccurrence : Bool
    parserAloneAuthorizesOccurrenceIsFalse : parserAloneAuthorizesOccurrence ≡ false
    governedAdmissionPresent : Bool
    governedAdmissionPresentIsFalse : governedAdmissionPresent ≡ false
open PrimaryAuthoritySpecimenReceipt public

amoduRadicalTitleSpecimen : PrimaryAuthoritySpecimenReceipt
amoduRadicalTitleSpecimen = primaryAuthoritySpecimenReceipt
  "amodu-radical-title"
  "Amodu Tijani v Secretary, Southern Nigeria [1921] 2 AC 399; supplied primary PDF"
  "[1921] 2 AC 403, radical/native-title discussion; text-native PDF projection, pp. 3-4"
  "Primary judgment excerpt. Projection uses pdftotext; no legal labels are supplied to the parser."
  "0d688a733ea19b19a4faf7a08cd855705cfe52050c93bc7f10b9c44592571160"
  4047 2 26 0 textNativePdfProjection
  "parser_observation_and_candidate_status_only" "en_core_web_sm"
  true refl false refl false refl false refl

amoduCessionContinuitySpecimen : PrimaryAuthoritySpecimenReceipt
amoduCessionContinuitySpecimen = primaryAuthoritySpecimenReceipt
  "amodu-cession-continuity"
  "Amodu Tijani v Secretary, Southern Nigeria [1921] 2 AC 399; supplied primary PDF"
  "[1921] 2 AC 403, cession/continuity discussion; text-native PDF projection, pp. 5-6"
  "Primary judgment excerpt. Projection uses pdftotext; no legal labels are supplied to the parser."
  "a1ef13b6b228cad56f8515981ac042184c8f9e4a99d99a2f315158d0ecf27646"
  2136 1 14 3 textNativePdfProjection
  "parser_observation_and_candidate_status_only" "en_core_web_sm"
  true refl false refl false refl false refl

calderJudsonRecognitionSpecimen : PrimaryAuthoritySpecimenReceipt
calderJudsonRecognitionSpecimen = primaryAuthoritySpecimenReceipt
  "calder-judson-recognition"
  "Calder v Attorney-General of British Columbia [1973] SCR 313; supplied scanned PDF"
  "Judson J reasons, PDF pp. 29-32 / reported pp. 341-344"
  "Primary judgment excerpt. Projection uses Tesseract OCR from scanned PDF pages; OCR text is not treated as authoritative transcription."
  "e0ffe05bbc1e65b9e6484f85cd38d984d2790d12f870a21102f8147d4d06cd07"
  17192 66 118 5 ocrDerivedProjection
  "parser_observation_and_candidate_status_only" "en_core_web_sm"
  true refl false refl false refl false refl

calderHallIndependentTitleSpecimen : PrimaryAuthoritySpecimenReceipt
calderHallIndependentTitleSpecimen = primaryAuthoritySpecimenReceipt
  "calder-hall-independent-title"
  "Calder v Attorney-General of British Columbia [1973] SCR 313; supplied scanned PDF"
  "Hall J reasons, PDF pp. 78-81 / reported pp. 390-393"
  "Primary judgment excerpt. Projection uses Tesseract OCR from scanned PDF pages; OCR text is not treated as authoritative transcription."
  "97ffcad633b9cf44af43bd1fbd60a0343725fe28b9d698f3a8f09f064d2eff3d"
  18829 57 171 6 ocrDerivedProjection
  "parser_observation_and_candidate_status_only" "en_core_web_sm"
  true refl false refl false refl false refl

calderHallExtinguishmentContinuitySpecimen : PrimaryAuthoritySpecimenReceipt
calderHallExtinguishmentContinuitySpecimen = primaryAuthoritySpecimenReceipt
  "calder-hall-extinguishment-continuity"
  "Calder v Attorney-General of British Columbia [1973] SCR 313; supplied scanned PDF"
  "Hall J reasons, PDF pp. 89-92 / reported pp. 401-404"
  "Primary judgment excerpt. Projection uses Tesseract OCR from scanned PDF pages; OCR text is not treated as authoritative transcription."
  "5ce03fb4493a5476ed8105cb9b9e58c7023172d4de17811cf44762e0ed8b27cc"
  18123 71 124 8 ocrDerivedProjection
  "parser_observation_and_candidate_status_only" "en_core_web_sm"
  true refl false refl false refl false refl

------------------------------------------------------------------------
-- Batch-level exact arithmetic receipt.
------------------------------------------------------------------------

record PrimaryAuthorityBatchReceipt : Set where
  constructor primaryAuthorityBatchReceipt
  field
    specimenCount paragraphCount sentenceCount reportingPredicateCount : Nat
    authority : String
    parserModel : String
    allCandidateOnly : Bool
    allCandidateOnlyIsTrue : allCandidateOnly ≡ true
    parserTruthAuthority : Bool
    parserTruthAuthorityIsFalse : parserTruthAuthority ≡ false
    parserOccurrenceAuthority : Bool
    parserOccurrenceAuthorityIsFalse : parserOccurrenceAuthority ≡ false
    admissionOrPublicationAuthority : Bool
    admissionOrPublicationAuthorityIsFalse : admissionOrPublicationAuthority ≡ false
open PrimaryAuthorityBatchReceipt public

primaryAuthorityBatchV02 : PrimaryAuthorityBatchReceipt
primaryAuthorityBatchV02 = primaryAuthorityBatchReceipt
  5 197 453 22
  "parser_observation_and_candidate_status_only"
  "en_core_web_sm"
  true refl false refl false refl false refl

------------------------------------------------------------------------
-- Exact bounded sentence anchors retained from the parser receipt.
--
-- These are parser-source coordinates, not reviewed legal conclusions.
------------------------------------------------------------------------

record ParsedSentenceAnchor (specimen : PrimaryAuthoritySpecimenReceipt) : Set where
  constructor parsedSentenceAnchor
  field
    sentenceIndex : Nat
    exactParserText : String
    anchorReference : String
    parserTextIsAuthoritativeTranscription : Bool
    parserTextIsAuthoritativeTranscriptionIsFalse : parserTextIsAuthoritativeTranscription ≡ false
open ParsedSentenceAnchor public

-- The Amodu PDF is text-native, but parser output still does not itself become
-- authoritative legal interpretation; the Boolean here concerns legal/source
-- authority of the parser text as a proposition, not whether pdftotext worked.
amoduUsufructRadicalAnchor : ParsedSentenceAnchor amoduRadicalTitleSpecimen
amoduUsufructRadicalAnchor = parsedSentenceAnchor 5
  "A very usual form of native title is that of a usufructuary right, which is a mere qualification of or burden on the radical or final title of the Sovereign where that exists."
  "primary-authority-v0.2:amodu-radical-title:sentence-5"
  false refl

amoduPureLegalEstateAnchor : ParsedSentenceAnchor amoduRadicalTitleSpecimen
amoduPureLegalEstateAnchor = parsedSentenceAnchor 6
  "In such cases the title of the Sovereign is a pure legal estate, to which beneficial rights may or may not be attached."
  "primary-authority-v0.2:amodu-radical-title:sentence-6"
  false refl

amoduCessionRespectAnchor : ParsedSentenceAnchor amoduCessionContinuitySpecimen
amoduCessionRespectAnchor = parsedSentenceAnchor 5
  "No doubt there was a cession to the British Crown, along with the sovereignty, of the radical or ultimate title to the land, in the new colony, but this cession appears to have been made on the footing that the rights of property of the inhabitants were to be fully respected."
  "primary-authority-v0.2:amodu-cession-continuity:sentence-5"
  false refl

amoduNoBeneficialDisplacementAnchor : ParsedSentenceAnchor amoduCessionContinuitySpecimen
amoduNoBeneficialDisplacementAnchor = parsedSentenceAnchor 12
  "In the light afforded by the narrative, it is not admissible to conclude that the Crown is generally speaking entitled to the beneficial ownership of the land as having so passed to the Crown as to displace any presumptive title of the natives."
  "primary-authority-v0.2:amodu-cession-continuity:sentence-12"
  false refl

judsonRecognizedUnrecognizedAnchor : ParsedSentenceAnchor calderJudsonRecognitionSpecimen
judsonRecognizedUnrecognizedAnchor = parsedSentenceAnchor 4
  "The ratio of the majority appears in the following paragraph from the reasons of Vinson C.J.: Nor do other cases in this Court lend substance to the dichotomy of recognized and unrecognized Indian title which petitioner urges."
  "primary-authority-v0.2:calder-judson-recognition:sentence-4:OCR-normalised-anchor"
  false refl

hallIndependentTitleAnchor : ParsedSentenceAnchor calderHallIndependentTitleSpecimen
hallIndependentTitleAnchor = parsedSentenceAnchor 4
  "The aboriginal Indian title does not depend on treaty, executive order or legislative enactment."
  "primary-authority-v0.2:calder-hall-independent-title:sentence-4:OCR"
  false refl

hallRecognitionNotPrerequisiteAnchor : ParsedSentenceAnchor calderHallIndependentTitleSpecimen
hallRecognitionNotPrerequisiteAnchor = parsedSentenceAnchor 121
  "To the extent that the Commission and the appellee believe that affirmative governmental recognition or approval is a prerequisite to the existence of original title, we think they err."
  "primary-authority-v0.2:calder-hall-independent-title:sentence-121:OCR"
  false refl

hallSurvivalWithoutRecognitionAnchor : ParsedSentenceAnchor calderHallIndependentTitleSpecimen
hallSurvivalWithoutRecognitionAnchor = parsedSentenceAnchor 122
  "Indian title based on aboriginal possession does not depend upon sovereign recognition or affirmative acceptance for its survival."
  "primary-authority-v0.2:calder-hall-independent-title:sentence-122:OCR"
  false refl

hallEnduresUntilExtinguishedAnchor : ParsedSentenceAnchor calderHallIndependentTitleSpecimen
hallEnduresUntilExtinguishedAnchor = parsedSentenceAnchor 123
  "Once established in fact, it endures until extinguished or abandoned."
  "primary-authority-v0.2:calder-hall-independent-title:sentence-123:OCR"
  false refl

hallPresumedContinuityAnchor : ParsedSentenceAnchor calderHallExtinguishmentContinuitySpecimen
hallPresumedContinuityAnchor = parsedSentenceAnchor 6
  "Once aboriginal title is established, it is presumed to continue until the contrary is proven."
  "primary-authority-v0.2:calder-hall-extinguishment-continuity:sentence-6:OCR"
  false refl

hallSpecificExtinguishmentAnchor : ParsedSentenceAnchor calderHallExtinguishmentContinuitySpecimen
hallSpecificExtinguishmentAnchor = parsedSentenceAnchor 32
  "It being a legal right, it could not thereafter be extinguished except by surrender to the Crown or by competent legislative authority, and then only by specific legislation."
  "primary-authority-v0.2:calder-hall-extinguishment-continuity:sentence-32:OCR"
  false refl

hallClearPlainAnchor : ParsedSentenceAnchor calderHallExtinguishmentContinuitySpecimen
hallClearPlainAnchor = parsedSentenceAnchor 97
  "It would, accordingly, appear to be beyond question that the onus of proving that the Sovereign intended to extinguish the Indian title lies on the respondent and that intention must be clear and plain."
  "primary-authority-v0.2:calder-hall-extinguishment-continuity:sentence-97:OCR"
  false refl

------------------------------------------------------------------------
-- Provenance / promotion firewalls.
------------------------------------------------------------------------

data OcrProjectionIsAuthoritativeTranscription : Set where
data ParserBatchCreatesJudicialHolding : Set where
data ParserCandidateCreatesLegalCoordinateResolution : Set where
data TextNativeProjectionCreatesWorldTruth : Set where
data FiveAuthoritySpecimensAreCorpusCoverage : Set where

ocrProjectionDoesNotBecomeAuthoritativeTranscription : OcrProjectionIsAuthoritativeTranscription → ⊥
ocrProjectionDoesNotBecomeAuthoritativeTranscription ()
parserBatchDoesNotCreateHolding : ParserBatchCreatesJudicialHolding → ⊥
parserBatchDoesNotCreateHolding ()
parserCandidateDoesNotResolveLegalCoordinate : ParserCandidateCreatesLegalCoordinateResolution → ⊥
parserCandidateDoesNotResolveLegalCoordinate ()
textNativeProjectionDoesNotCreateWorldTruth : TextNativeProjectionCreatesWorldTruth → ⊥
textNativeProjectionDoesNotCreateWorldTruth ()
fiveSpecimensDoNotClaimCorpusCoverage : FiveAuthoritySpecimensAreCorpusCoverage → ⊥
fiveSpecimensDoNotClaimCorpusCoverage ()

record PrimaryAuthorityV02Boundary : Set where
  constructor primaryAuthorityV02Boundary
  field
    exactHashesRetained : Bool
    exactHashesRetainedIsTrue : exactHashesRetained ≡ true
    allParserCandidatesOnly : Bool
    allParserCandidatesOnlyIsTrue : allParserCandidatesOnly ≡ true
    ocrIsAuthoritativeTranscription : Bool
    ocrIsAuthoritativeTranscriptionIsFalse : ocrIsAuthoritativeTranscription ≡ false
    parserCreatesHolding : Bool
    parserCreatesHoldingIsFalse : parserCreatesHolding ≡ false
    parserResolvesRecognitionCoordinate : Bool
    parserResolvesRecognitionCoordinateIsFalse : parserResolvesRecognitionCoordinate ≡ false

canonicalPrimaryAuthorityV02Boundary : PrimaryAuthorityV02Boundary
canonicalPrimaryAuthorityV02Boundary = primaryAuthorityV02Boundary true refl true refl false refl false refl false refl
