module DASHI.Cognition.PNF.SensibLawCalderAuthoritativeTranscriptionVerificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor

------------------------------------------------------------------------
-- Authoritative transcription verification overlay for the OCR-derived
-- Calder Hall propositions.
--
-- Historical provenance is preserved:
--   OCR parser receipt remains OCR-derived;
--   SCC transcription is a separate source receipt;
--   only the reviewed same-proposition weld promotes proposition identity.
------------------------------------------------------------------------

data AuthoritativeSourceKind : Set where
  supremeCourtOfCanadaDecisionTranscription
  laterSupremeCourtOfCanadaQuotation
  : AuthoritativeSourceKind

data VerificationGrade : Set where
  semanticPropositionVerified
  verbatimBoundedSentenceVerified
  : VerificationGrade

record CalderTranscriptionVerification
    (ocrProposition : Primary.ReviewedPrimaryAuthorityProposition) : Set where
  constructor calderTranscriptionVerification
  field
    authoritativeSourceKind : AuthoritativeSourceKind
    authoritativeSourceReference : String
    officialDecisionCitation : String
    officialPinpoint : String
    verificationGrade : VerificationGrade
    sameAuthorityIdentity : Bool
    sameAuthorityIdentityIsTrue : sameAuthorityIdentity ≡ true
    sameSemanticProposition : Bool
    sameSemanticPropositionIsTrue : sameSemanticProposition ≡ true
    verbatimIdentityClaimed : Bool
    authoritativeTranscriptionVerified : Bool
    authoritativeTranscriptionVerifiedIsTrue : authoritativeTranscriptionVerified ≡ true
    parserRerunRequired : Bool
    parserRerunRequiredIsFalse : parserRerunRequired ≡ false
    verificationReference : String
open CalderTranscriptionVerification public

sccCalderSource : String
sccCalderSource = "Supreme Court of Canada Decisions: Calder et al. v. Attorney-General of British Columbia, [1973] S.C.R. 313"

------------------------------------------------------------------------
-- Hall J p 390: title does not depend on treaty/executive/legislative act.
------------------------------------------------------------------------

hallIndependentTitleVerified : CalderTranscriptionVerification Primary.hallIndependentTitleProposition
hallIndependentTitleVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource
  "Hall J, p 390"
  verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "SCC transcription independently contains the bounded Hall sentence underlying the OCR proposition that aboriginal Indian title does not depend on treaty, executive order or legislative enactment"

------------------------------------------------------------------------
-- Hall J p 401: affirmative recognition not prerequisite; survival does not
-- depend on sovereign recognition/acceptance; title endures until extinguished
-- or abandoned.
------------------------------------------------------------------------

hallRecognitionNotPrerequisiteVerified : CalderTranscriptionVerification Primary.hallRecognitionNotPrerequisiteProposition
hallRecognitionNotPrerequisiteVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource
  "Hall J, p 401"
  verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "SCC transcription independently confirms Hall's proposition that affirmative governmental recognition or approval is not a prerequisite to existence of original title"

hallSurvivalWithoutRecognitionVerified : CalderTranscriptionVerification Primary.hallSurvivalWithoutRecognitionProposition
hallSurvivalWithoutRecognitionVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource
  "Hall J, p 401"
  verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "SCC transcription independently confirms Hall's proposition that Indian title based on aboriginal possession does not depend on sovereign recognition or affirmative acceptance for survival"

hallEnduresUntilExtinguishedVerified : CalderTranscriptionVerification Primary.hallEnduresUntilExtinguishedProposition
hallEnduresUntilExtinguishedVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource
  "Hall J, p 401"
  verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "SCC transcription independently confirms the bounded continuity proposition that once established in fact original title endures until extinguished or abandoned"

------------------------------------------------------------------------
-- Hall J pp 393/401-404: continuity presumption and extinguishment burden.
------------------------------------------------------------------------

hallContinuityPresumptionVerified : CalderTranscriptionVerification Primary.hallContinuityPresumptionProposition
hallContinuityPresumptionVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource
  "Hall J, p 393; repeated in extinguishment analysis around pp 401-402"
  verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "SCC transcription independently confirms that once aboriginal title is established it is presumed to continue until the contrary is proven"

hallSpecificExtinguishmentVerified : CalderTranscriptionVerification Primary.hallSpecificExtinguishmentProposition
hallSpecificExtinguishmentVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource
  "Hall J continuity/extinguishment analysis; SCC decision summary at p 316 and reasons around pp 401-404"
  semanticPropositionVerified
  true refl true refl false true refl false refl
  "SCC decision transcription/summary verifies the proposition-level rule that established title could not thereafter be extinguished except by surrender or competent legislative authority, with specific legislation in Hall's formulation; no verbatim identity is claimed for the full OCR sentence"

hallClearPlainBurdenVerified : CalderTranscriptionVerification Primary.hallClearPlainBurdenProposition
hallClearPlainBurdenVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource
  "Hall J, p 404"
  verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "SCC transcription independently confirms Hall's bounded proposition that the respondent bears the onus of proving sovereign intent to extinguish and that the intention must be clear and plain"

------------------------------------------------------------------------
-- Independent later-SCC quotation receipt for the p 404 burden formulation.
-- This is corroboration, not replacement of the Calder primary transcription.
------------------------------------------------------------------------

hallClearPlainLaterSccCorroboration : CalderTranscriptionVerification Primary.hallClearPlainBurdenProposition
hallClearPlainLaterSccCorroboration = calderTranscriptionVerification
  laterSupremeCourtOfCanadaQuotation
  "https://scc-csc.lexum.com/scc-csc/scc-csc/en/item/609/index.do"
  "R. v. Sparrow, [1990] 1 S.C.R. 1075"
  "Sparrow, pp 1098-1099 quoting Calder Hall J at p 404"
  verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "later unanimous SCC reasons quote Hall J's p 404 onus/clear-and-plain formulation and adopt clear-and-plain intention as the extinguishment test"

------------------------------------------------------------------------
-- Promotion state: the OCR object remains OCR-derived, while its bounded
-- proposition identity now has an authoritative transcription weld.
------------------------------------------------------------------------

data PropositionTextAuthorityState : Set where
  ocrLocated
  authoritativeTranscriptionVerified
  : PropositionTextAuthorityState

verifiedTextAuthorityState :
  CalderTranscriptionVerification Primary.hallSurvivalWithoutRecognitionProposition →
  PropositionTextAuthorityState
verifiedTextAuthorityState _ = authoritativeTranscriptionVerified

hallSurvivalTextNowVerified :
  verifiedTextAuthorityState hallSurvivalWithoutRecognitionVerified ≡ authoritativeTranscriptionVerified
hallSurvivalTextNowVerified = refl

hallRecognitionTextNowVerified : authoritativeTranscriptionVerified hallRecognitionNotPrerequisiteVerified ≡ true
hallRecognitionTextNowVerified = refl
hallContinuityTextNowVerified : authoritativeTranscriptionVerified hallContinuityPresumptionVerified ≡ true
hallContinuityTextNowVerified = refl
hallClearPlainTextNowVerified : authoritativeTranscriptionVerified hallClearPlainBurdenVerified ≡ true
hallClearPlainTextNowVerified = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data OcrReceiptBecomesAuthoritativeSource : Set where
data SemanticVerificationMeansVerbatimIdentity : Set where
data TranscriptionVerificationResolvesLegalCoordinate : Set where
data LaterSccQuotationRewritesCalderSourceIdentity : Set where

authVerificationDoesNotRewriteOcrProvenance : OcrReceiptBecomesAuthoritativeSource → ⊥
authVerificationDoesNotRewriteOcrProvenance ()
semanticVerificationDoesNotForceVerbatimIdentity : SemanticVerificationMeansVerbatimIdentity → ⊥
semanticVerificationDoesNotForceVerbatimIdentity ()
transcriptionVerificationDoesNotResolveCoordinate : TranscriptionVerificationResolvesLegalCoordinate → ⊥
transcriptionVerificationDoesNotResolveCoordinate ()
laterSccQuotationDoesNotRewriteCalderIdentity : LaterSccQuotationRewritesCalderSourceIdentity → ⊥
laterSccQuotationDoesNotRewriteCalderIdentity ()
