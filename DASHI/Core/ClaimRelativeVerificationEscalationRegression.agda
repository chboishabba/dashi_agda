module DASHI.Core.ClaimRelativeVerificationEscalationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)

import DASHI.Core.HumanReviewCore as Review
import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Core.ClaimRelativeVerificationEscalationExact as Verification

boundary : Verification.ClaimRelativeVerificationBoundary
boundary = Verification.canonicalClaimRelativeVerificationBoundary

translationVerificationSeparated :
  Verification.formalVerificationCreatesTranslationAdequacy boundary ≡ false
translationVerificationSeparated = refl

weakVerificationNotAuthority :
  Verification.weakVerificationCreatesDecisionAuthority boundary ≡ false
weakVerificationNotAuthority = refl

validatorSuccessNotConsumerSuccess :
  Verification.validatorSuccessCreatesConsumerSuccess boundary ≡ false
validatorSuccessNotConsumerSuccess = refl

boundedNarrativeNotNegativeDiscovery :
  Verification.boundedHistoryAuthorizesNegativeDiscovery boundary ≡ false
boundedNarrativeNotNegativeDiscovery = refl

abstentionBeforeIrreversibleAction :
  Verification.abstentionMayOccurBeforeIrreversibleAction boundary ≡ true
abstentionBeforeIrreversibleAction = refl

selectiveAcquisitionOnly :
  Verification.evidenceAcquisitionReopensOnlyAffectedConsumers boundary ≡ true
selectiveAcquisitionOnly = refl

reviewReceipt : Review.GenericHumanReviewReceipt
reviewReceipt = Review.generic-human-review-receipt
  "review:fixture"
  "item:fixture"
  "reviewer:fixture"
  "observation:fixture"

reviewBinding : Review.ExactReviewItemBinding
reviewBinding = Review.exact-review-item-binding
  "source:fixture"
  "pnf-batch:fixture"
  "factor:fixture"
  "consumer:fixture"
  true refl

humanEscalation : Verification.EscalationPayload Verification.humanReviewTarget
humanEscalation = Verification.humanReviewPayload reviewReceipt reviewBinding

acquisitionTarget : Acquisition.AcquisitionTarget
acquisitionTarget = Acquisition.acquisition-target
  "missing-evidence"
  "fixture targeted acquisition"
  "primary route"
  "fallback route"
  "authority fixture"

acquisitionEscalation : Verification.EscalationPayload Verification.evidenceAcquisitionTarget
acquisitionEscalation = Verification.evidenceAcquisitionPayload
  acquisitionTarget
  (Acquisition.obligationFromNotLocated acquisitionTarget)
