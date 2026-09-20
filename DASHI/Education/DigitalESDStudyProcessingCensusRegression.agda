module DASHI.Education.DigitalESDStudyProcessingCensusRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStudyProcessingCensusExact as Census

metadataIsNotScreeningDecision :
  Census.MetadataPresenceCreatesScreeningDecision → ⊥
metadataIsNotScreeningDecision =
  Census.metadataPresenceDoesNotCreateScreeningDecision

triageStatusIsNotScreeningDecision :
  Census.TriageStatusCreatesScreeningDecision → ⊥
triageStatusIsNotScreeningDecision =
  Census.triageStatusDoesNotCreateScreeningDecision

fullTextIsNotParseReceipt :
  Census.VerifiedFullTextCreatesSLRParseReceipt → ⊥
fullTextIsNotParseReceipt =
  Census.verifiedFullTextDoesNotCreateSLRParseReceipt

parseIsNotReview :
  Census.SLRParseCreatesReviewedEvidence → ⊥
parseIsNotReview =
  Census.slrParseDoesNotCreateReviewedEvidence

reviewIsNotAdmission :
  Census.ReviewedEvidenceCreatesSourceAuditAdmission → ⊥
reviewIsNotAdmission =
  Census.reviewedEvidenceDoesNotCreateSourceAuditAdmission

stageContainmentRequired :
  Census.requiresStageContainment Census.canonicalStudyProcessingCensusBoundary
  ≡ true
stageContainmentRequired = refl

laterStageInferenceForbidden :
  Census.allowsLaterStageInference Census.canonicalStudyProcessingCensusBoundary
  ≡ false
laterStageInferenceForbidden = refl
