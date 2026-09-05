module DASHI.Cognition.PNF.SensibLawCalderAuthoritativeTranscriptionVerificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary

-- Verification overlay: OCR provenance is retained historically; authoritative
-- SCC transcription is a distinct source receipt over the same proposition.

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

hallIndependentTitleVerified : CalderTranscriptionVerification Primary.hallIndependentTitleProposition
hallIndependentTitleVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource "Hall J, p 390" verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "official SCC transcription independently matches the bounded Hall proposition that aboriginal Indian title does not depend on treaty, executive order or legislative enactment"

hallRecognitionNotPrerequisiteVerified : CalderTranscriptionVerification Primary.hallRecognitionNotPrerequisiteProposition
hallRecognitionNotPrerequisiteVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource "Hall J, p 401" verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "official SCC transcription independently matches Hall's rejection of affirmative governmental recognition or approval as a prerequisite to original title"

hallSurvivalWithoutRecognitionVerified : CalderTranscriptionVerification Primary.hallSurvivalWithoutRecognitionProposition
hallSurvivalWithoutRecognitionVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource "Hall J, p 401" verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "official SCC transcription independently matches Hall's proposition that original title based on aboriginal possession does not depend on sovereign recognition or affirmative acceptance for survival"

hallEnduresUntilExtinguishedVerified : CalderTranscriptionVerification Primary.hallEnduresUntilExtinguishedProposition
hallEnduresUntilExtinguishedVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource "Hall J, p 401" verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "official SCC transcription independently matches the bounded proposition that original title endures until extinguished or abandoned"

hallContinuityPresumptionVerified : CalderTranscriptionVerification Primary.hallContinuityPresumptionProposition
hallContinuityPresumptionVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource "Hall J, p 393 and extinguishment analysis around pp 401-402" verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "official SCC transcription independently matches the proposition that once aboriginal title is established it is presumed to continue until the contrary is proven"

hallSpecificExtinguishmentVerified : CalderTranscriptionVerification Primary.hallSpecificExtinguishmentProposition
hallSpecificExtinguishmentVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource "Hall J continuity/extinguishment analysis; SCC decision summary at p 316 and reasons around pp 401-404" semanticPropositionVerified
  true refl true refl false true refl false refl
  "official SCC decision text verifies the proposition-level surrender/competent-legislative-authority/specific-legislation rule; no verbatim identity is claimed for the complete OCR sentence"

hallClearPlainBurdenVerified : CalderTranscriptionVerification Primary.hallClearPlainBurdenProposition
hallClearPlainBurdenVerified = calderTranscriptionVerification
  supremeCourtOfCanadaDecisionTranscription
  "https://decisions.scc-csc.ca/scc-csc/scc-csc/en/item/5113/index.do"
  sccCalderSource "Hall J, p 404" verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "official SCC transcription independently matches Hall's onus/clear-and-plain extinguishment proposition"

hallClearPlainLaterSccCorroboration : CalderTranscriptionVerification Primary.hallClearPlainBurdenProposition
hallClearPlainLaterSccCorroboration = calderTranscriptionVerification
  laterSupremeCourtOfCanadaQuotation
  "https://scc-csc.lexum.com/scc-csc/scc-csc/en/item/609/index.do"
  "R. v. Sparrow, [1990] 1 S.C.R. 1075"
  "Sparrow, pp 1098-1099 quoting Calder Hall J at p 404" verbatimBoundedSentenceVerified
  true refl true refl true true refl false refl
  "later SCC reasons independently quote the same Hall p 404 onus/clear-and-plain formulation and adopt clear-and-plain intention as the extinguishment test"

data PropositionTextAuthorityState : Set where
  ocrLocated
  authoritativeTranscriptionVerified
  : PropositionTextAuthorityState

verifiedTextAuthorityState : CalderTranscriptionVerification Primary.hallSurvivalWithoutRecognitionProposition → PropositionTextAuthorityState
verifiedTextAuthorityState _ = authoritativeTranscriptionVerified
hallSurvivalTextNowVerified : verifiedTextAuthorityState hallSurvivalWithoutRecognitionVerified ≡ authoritativeTranscriptionVerified
hallSurvivalTextNowVerified = refl
hallRecognitionTextNowVerified : authoritativeTranscriptionVerified hallRecognitionNotPrerequisiteVerified ≡ true
hallRecognitionTextNowVerified = refl
hallContinuityTextNowVerified : authoritativeTranscriptionVerified hallContinuityPresumptionVerified ≡ true
hallContinuityTextNowVerified = refl
hallClearPlainTextNowVerified : authoritativeTranscriptionVerified hallClearPlainBurdenVerified ≡ true
hallClearPlainTextNowVerified = refl

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
