module DASHI.Education.DigitalESDReviewedScreeningDecisionBridgeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDReviewedScreeningDecisionBridgeExact as Bridge

candidateAssessmentCannotChangeLedger :
  Bridge.CandidateAssessmentChangesAuthoritativeLedger → ⊥
candidateAssessmentCannotChangeLedger =
  Bridge.candidateAssessmentDoesNotChangeAuthoritativeLedger

reviewPacketCannotChangeLedger :
  Bridge.ReviewPacketChangesAuthoritativeLedger → ⊥
reviewPacketCannotChangeLedger =
  Bridge.reviewPacketDoesNotChangeAuthoritativeLedger

unreviewedOverlayCannotChangeLedger :
  Bridge.UnreviewedOverlayChangesAuthoritativeLedger → ⊥
unreviewedOverlayCannotChangeLedger =
  Bridge.unreviewedOverlayDoesNotChangeAuthoritativeLedger

reviewedOverlayMayChangeLedger :
  Bridge.explicitReviewedOverlayIsOnlyAuthorityChangingStep
    Bridge.canonicalReviewedScreeningDecisionBoundary
  ≡ true
reviewedOverlayMayChangeLedger = refl

denominatorPreserved :
  Bridge.authoritativeLedgerPreservesDenominator
    Bridge.canonicalReviewedScreeningDecisionBoundary
  ≡ true
denominatorPreserved = refl
