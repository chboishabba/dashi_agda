module DASHI.Education.DigitalESDAdaptiveScreeningExecutionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAdaptiveScreeningExecutionExact as Exec

candidateRecommendationsCannotPromote :
  Exec.CandidateRecommendationCreatesAuthoritativeDecision → ⊥
candidateRecommendationsCannotPromote =
  Exec.candidateRecommendationDoesNotCreateAuthoritativeDecision

retrievalQueueCannotIncludeUnreviewed :
  Exec.UnreviewedMetadataEntersRetrievalResidual → ⊥
retrievalQueueCannotIncludeUnreviewed =
  Exec.unreviewedMetadataDoesNotEnterRetrievalResidual

retrievalCannotCreateReview :
  Exec.RetrievalCreatesReviewedEvidence → ⊥
retrievalCannotCreateReview =
  Exec.retrievalDoesNotCreateReviewedEvidence

parseCannotCreateAdmission :
  Exec.ParseCreatesSourceAuditAdmission → ⊥
parseCannotCreateAdmission =
  Exec.parseDoesNotCreateSourceAuditAdmission

loopPreservesDenominator :
  Exec.processingDenominatorPreserved
    Exec.canonicalAdaptiveScreeningExecutionBoundary
  ≡ true
loopPreservesDenominator = refl

loopQueuesOnlyRetained :
  Exec.retrievalResidualRequiresRetainedDecision
    Exec.canonicalAdaptiveScreeningExecutionBoundary
  ≡ true
loopQueuesOnlyRetained = refl
