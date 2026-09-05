module DASHI.Core.KnowledgeBoundaryCandidateIdentityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CANDIDATE SAME-OBJECT IDENTITY FOR KNOWLEDGE-BOUNDARY TRANSITIONS
--
-- A later public artifact can be highly compatible with an earlier unnamed
-- release/review claim without being definitionally the same object.  Identity
-- therefore has its own graded evidence object.
------------------------------------------------------------------------

data IdentityGrade : Set where
  unresolvedIdentity
  compatibleCandidate
  strongCandidate
  exactIdentity
  : IdentityGrade

data IdentitySignal : Set where
  topicOverlap
  authorOrTeamOverlap
  institutionalOverlap
  timelineCompatibility
  laterWitnessLinkage
  primaryInstitutionalIdentifierMatch
  : IdentitySignal

record CandidateObjectIdentity : Set where
  constructor candidate-object-identity
  field
    earlierObjectLabel : String
    laterObjectLabel : String
    grade : IdentityGrade
    signals : List IdentitySignal
    sourceReference : String
    boundedReading : String

open CandidateObjectIdentity public

record ExactObjectIdentity (candidate : CandidateObjectIdentity) : Set where
  constructor exact-object-identity
  field
    exactGrade : grade candidate ≡ exactIdentity
    identityReference : String

open ExactObjectIdentity public

record StrongObjectCandidate (candidate : CandidateObjectIdentity) : Set where
  constructor strong-object-candidate
  field
    strongGrade : grade candidate ≡ strongCandidate
    candidateReference : String

open StrongObjectCandidate public

record CandidateIdentityBoundary : Set where
  constructor candidate-identity-boundary
  field
    matchingTopicAndTimelineMeansExactIdentity : Bool
    matchingTopicAndTimelineMeansExactIdentityIsFalse :
      matchingTopicAndTimelineMeansExactIdentity ≡ false
    laterWitnessAttributionMeansPrimaryInstitutionalIdentity : Bool
    laterWitnessAttributionMeansPrimaryInstitutionalIdentityIsFalse :
      laterWitnessAttributionMeansPrimaryInstitutionalIdentity ≡ false
    publicArtifactAfterReviewClaimMeansSameObject : Bool
    publicArtifactAfterReviewClaimMeansSameObjectIsFalse :
      publicArtifactAfterReviewClaimMeansSameObject ≡ false
    exactIdentityRequiresIdentitySpecificReceipt : Bool
    exactIdentityRequiresIdentitySpecificReceiptIsTrue :
      exactIdentityRequiresIdentitySpecificReceipt ≡ true

canonicalCandidateIdentityBoundary : CandidateIdentityBoundary
canonicalCandidateIdentityBoundary = candidate-identity-boundary
  false refl
  false refl
  false refl
  true refl
