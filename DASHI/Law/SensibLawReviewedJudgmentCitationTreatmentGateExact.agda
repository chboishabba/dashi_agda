module DASHI.Law.SensibLawReviewedJudgmentCitationTreatmentGateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rust-led parity owner for the explicit review gate between source-located
-- citation candidates and the existing proposition reasoning graph.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "516867c503b33ea880419f9ca512307feec48e2b"

record ReviewedJudgmentCitationTreatmentGateBoundary : Set where
  constructor reviewedJudgmentCitationTreatmentGateBoundary
  field
    candidateMustRemainCandidateOnly : Bool
    candidateMustRemainCandidateOnlyIsTrue :
      candidateMustRemainCandidateOnly ≡ true

    candidateMustBePreviouslyUnreviewed : Bool
    candidateMustBePreviouslyUnreviewedIsTrue :
      candidateMustBePreviouslyUnreviewed ≡ true

    reviewedLocatorMustEqualCandidateLocator : Bool
    reviewedLocatorMustEqualCandidateLocatorIsTrue :
      reviewedLocatorMustEqualCandidateLocator ≡ true

    reviewedCitationMustEqualCandidateCitation : Bool
    reviewedCitationMustEqualCandidateCitationIsTrue :
      reviewedCitationMustEqualCandidateCitation ≡ true

    citingPropositionMustBeExplicit : Bool
    citingPropositionMustBeExplicitIsTrue : citingPropositionMustBeExplicit ≡ true

    citedDocumentMustBeExplicit : Bool
    citedDocumentMustBeExplicitIsTrue : citedDocumentMustBeExplicit ≡ true

    citedPropositionMustBeExplicit : Bool
    citedPropositionMustBeExplicitIsTrue : citedPropositionMustBeExplicit ≡ true

    citationUseMustBeExplicit : Bool
    citationUseMustBeExplicitIsTrue : citationUseMustBeExplicit ≡ true

    reasoningRoleMustBeExplicit : Bool
    reasoningRoleMustBeExplicitIsTrue : reasoningRoleMustBeExplicit ≡ true

    reviewerMustBeExplicit : Bool
    reviewerMustBeExplicitIsTrue : reviewerMustBeExplicit ≡ true

    evidenceMustBeExplicit : Bool
    evidenceMustBeExplicitIsTrue : evidenceMustBeExplicit ≡ true

    reviewedEdgeUsesCandidatePinpoint : Bool
    reviewedEdgeUsesCandidatePinpointIsTrue : reviewedEdgeUsesCandidatePinpoint ≡ true

    reviewedEdgeRemainsCandidateOnly : Bool
    reviewedEdgeRemainsCandidateOnlyIsTrue : reviewedEdgeRemainsCandidateOnly ≡ true

    lexicalHintAutomaticallyCompilesReviewedEdge : Bool
    lexicalHintAutomaticallyCompilesReviewedEdgeIsFalse :
      lexicalHintAutomaticallyCompilesReviewedEdge ≡ false

    reviewedEdgeAutomaticallyBindingAuthority : Bool
    reviewedEdgeAutomaticallyBindingAuthorityIsFalse :
      reviewedEdgeAutomaticallyBindingAuthority ≡ false

canonicalReviewedJudgmentCitationTreatmentGateBoundary :
  ReviewedJudgmentCitationTreatmentGateBoundary
canonicalReviewedJudgmentCitationTreatmentGateBoundary =
  reviewedJudgmentCitationTreatmentGateBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Fail-closed review/promotion firewalls.
------------------------------------------------------------------------

data LexicalHintAutomaticallyReviewedTreatment : Set where
data WrongLocatorAutomaticallyReviewsCandidate : Set where
data ReviewedTreatmentAutomaticallyRatio : Set where
data ReviewedTreatmentAutomaticallyCurrentAuthority : Set where

lexicalHintDoesNotBecomeReviewedTreatment :
  LexicalHintAutomaticallyReviewedTreatment → ⊥
lexicalHintDoesNotBecomeReviewedTreatment ()

wrongLocatorDoesNotReviewCandidate :
  WrongLocatorAutomaticallyReviewsCandidate → ⊥
wrongLocatorDoesNotReviewCandidate ()

reviewedTreatmentDoesNotBecomeRatio :
  ReviewedTreatmentAutomaticallyRatio → ⊥
reviewedTreatmentDoesNotBecomeRatio ()

reviewedTreatmentDoesNotBecomeCurrentAuthority :
  ReviewedTreatmentAutomaticallyCurrentAuthority → ⊥
reviewedTreatmentDoesNotBecomeCurrentAuthority ()
