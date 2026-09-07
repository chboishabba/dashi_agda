module DASHI.Law.SensibLawCitationUsePropositionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawCitationAuthorityFollowExact as Follow

------------------------------------------------------------------------
-- PROPOSITION-LEVEL CITATION USE
--
-- A case-to-case edge is too coarse. The typed edge is between an attributed
-- proposition in the citing source and a proposition candidate in the cited
-- source, with pinpoint, speaker, segment, treatment, authority and time kept
-- separate.
------------------------------------------------------------------------

data CitationUseStatus : Set where
  citedMention : CitationUseStatus
  quotedUse : CitationUseStatus
  reliedOnUse : CitationUseStatus
  adoptedUse : CitationUseStatus
  appliedUse : CitationUseStatus
  followedUse : CitationUseStatus
  distinguishedUse : CitationUseStatus
  criticisedUse : CitationUseStatus
  rejectedUse : CitationUseStatus
  overruledUse : CitationUseStatus
  historicalBackgroundUse : CitationUseStatus
  partySubmissionUse : CitationUseStatus
  citationUseUnresolved : CitationUseStatus


data JudicialSegmentKind : Set where
  majorityReasonsSegment : JudicialSegmentKind
  pluralityReasonsSegment : JudicialSegmentKind
  concurringReasonsSegment : JudicialSegmentKind
  dissentSegment : JudicialSegmentKind
  partySubmissionSegment : JudicialSegmentKind
  factualBackgroundSegment : JudicialSegmentKind
  orderSegment : JudicialSegmentKind
  segmentUnresolved : JudicialSegmentKind


data AuthorityTreatmentStatus : Set where
  treatmentPositive : AuthorityTreatmentStatus
  treatmentNegative : AuthorityTreatmentStatus
  treatmentNeutral : AuthorityTreatmentStatus
  treatmentMixed : AuthorityTreatmentStatus
  treatmentUnresolved : AuthorityTreatmentStatus


data CurrentAuthorityStatus : Set where
  currentAuthorityUnresolved : CurrentAuthorityStatus
  currentBindingCandidate : CurrentAuthorityStatus
  currentPersuasiveCandidate : CurrentAuthorityStatus
  historicalOnlyCandidate : CurrentAuthorityStatus
  supersededCandidate : CurrentAuthorityStatus


record PropositionCitationUse : Set₁ where
  constructor propositionCitationUse
  field
    citingPropositionReference : String
    citedPropositionReference : String
    citedAuthorityReference : String
    pinpointReference : String
    speakerOrJudgeReference : String
    segment : JudicialSegmentKind
    useStatus : CitationUseStatus
    treatment : AuthorityTreatmentStatus
    currentAuthority : CurrentAuthorityStatus
    temporalReference : String
    directTextSupportReceipt : Set
    reviewedClassificationReceipt : Set
    useReference : String

open PropositionCitationUse public

record AttributedSourceVerification : Set₁ where
  constructor attributedSourceVerification
  field
    attributedPropositionReference : String
    sourcePropositionReference : String
    citationUse : PropositionCitationUse
    correspondenceReceipt : Set
    authorityFitnessReceipt : Set
    verificationReference : String

open AttributedSourceVerification public

record CitationUseFromFollow
    {candidate : Follow.CitationCandidate}
    (identity : Follow.CitationIdentity candidate) : Set₁ where
  constructor citationUseFromFollow
  field
    citationIdentity : Follow.CitationIdentity candidate
    propositionUse : PropositionCitationUse
    sameAuthorityReceipt : Set
    followDoesNotDetermineUseReceipt : Set
    weldReference : String

open CitationUseFromFollow public

------------------------------------------------------------------------
-- Source-verification obligation.
------------------------------------------------------------------------

data SourceVerificationStatus : Set where
  sourceSupportVerified : SourceVerificationStatus
  sourceSupportContradicted : SourceVerificationStatus
  sourceSupportPartial : SourceVerificationStatus
  sourceSupportUnresolved : SourceVerificationStatus


record SourceVerificationAssessment : Set₁ where
  constructor sourceVerificationAssessment
  field
    verification : AttributedSourceVerification
    status : SourceVerificationStatus
    proofPaymentStillRequiresConsumerReceipt : Bool
    proofPaymentStillRequiresConsumerReceiptIsTrue :
      proofPaymentStillRequiresConsumerReceipt ≡ true
    assessmentReference : String

open SourceVerificationAssessment public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CitationMeansAdoption : Set where
data QuotationMeansRatio : Set where
data RelianceMeansCurrentBindingAuthority : Set where
data DistinguishingMeansRejection : Set where
data LaterCitationRewritesOriginalSourceProposition : Set where
data VerifiedSourceSupportMeansConsumerProofClosed : Set where

citationDoesNotMeanAdoption : CitationMeansAdoption → ⊥
citationDoesNotMeanAdoption ()

quotationDoesNotMeanRatio : QuotationMeansRatio → ⊥
quotationDoesNotMeanRatio ()

relianceDoesNotMeanCurrentBindingAuthority : RelianceMeansCurrentBindingAuthority → ⊥
relianceDoesNotMeanCurrentBindingAuthority ()

distinguishingDoesNotMeanRejection : DistinguishingMeansRejection → ⊥
distinguishingDoesNotMeanRejection ()

laterCitationDoesNotRewriteOriginalSource : LaterCitationRewritesOriginalSourceProposition → ⊥
laterCitationDoesNotRewriteOriginalSource ()

verifiedSupportDoesNotAutoCloseConsumer : VerifiedSourceSupportMeansConsumerProofClosed → ⊥
verifiedSupportDoesNotAutoCloseConsumer ()

record CitationUseBoundary : Set where
  constructor citationUseBoundary
  field
    citationGraphIsPropositionLevel : Bool
    citationGraphIsPropositionLevelIsTrue : citationGraphIsPropositionLevel ≡ true
    citationUseRequiresReview : Bool
    citationUseRequiresReviewIsTrue : citationUseRequiresReview ≡ true
    citationEqualsAdoption : Bool
    citationEqualsAdoptionIsFalse : citationEqualsAdoption ≡ false
    sourceVerificationEqualsConsumerClosure : Bool
    sourceVerificationEqualsConsumerClosureIsFalse :
      sourceVerificationEqualsConsumerClosure ≡ false

canonicalCitationUseBoundary : CitationUseBoundary
canonicalCitationUseBoundary =
  citationUseBoundary true refl true refl false refl false refl
