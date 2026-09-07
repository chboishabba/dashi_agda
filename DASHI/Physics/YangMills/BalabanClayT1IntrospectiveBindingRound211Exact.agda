{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT1IntrospectiveBindingRound211Exact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.YangMills.BalabanClayT1ResidualIntrospectionRound210Exact as R210

------------------------------------------------------------------------
-- INTROSPECTIVE BINDING FOR THE LIVE T1 WALL
--
-- Round210 already identifies the residual, missing coordinate and candidate
-- producer family.  This owner adds the missing exact binding: a proposed
-- analytic producer is admissible for this introspective round only when it is
-- literally indexed by the current live residual and missing coordinate.
------------------------------------------------------------------------

record BoundT1Producer211 : Set where
  constructor bound-t1-producer-211
  field
    liveState : R210.T1IntrospectiveState210
    liveStateIsCurrent : liveState ≡ R210.currentT1IntrospectiveState210
    targetResidual : R210.T1Residual210
    targetResidualMatches : targetResidual ≡ R210.residual liveState
    targetCoordinate : R210.MissingCoordinate210
    targetCoordinateMatches : targetCoordinate ≡ R210.missingCoordinate liveState
    proposedProducer : R210.ProducerFamily210
    producerMatchesScheduledCandidate : proposedProducer ≡ R210.candidateProducer liveState
    producerPaymentEstablished : Bool
    producerPaymentEstablishedIsFalse : producerPaymentEstablished ≡ false

open BoundT1Producer211 public

currentBoundT1Producer211 : BoundT1Producer211
currentBoundT1Producer211 =
  bound-t1-producer-211
    R210.currentT1IntrospectiveState210
    refl
    R210.globalMomentToEscapeControl
    refl
    R210.selectedGlobalSublevelContainmentSemantics
    refl
    R210.directCompactContainmentTheorem
    refl
    false
    refl

currentBoundProducerTargetsLiveResidual :
  targetResidual currentBoundT1Producer211 ≡ R210.globalMomentToEscapeControl
currentBoundProducerTargetsLiveResidual = refl

currentBoundProducerTargetsLiveCoordinate :
  targetCoordinate currentBoundT1Producer211 ≡ R210.selectedGlobalSublevelContainmentSemantics
currentBoundProducerTargetsLiveCoordinate = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BoundCandidatePaysT1 : Set where
data VisualAuditPaysT1 : Set where
data AdjacentProducerPaysT1 : Set where

boundCandidateDoesNotPayT1 : BoundCandidatePaysT1 → ⊥
boundCandidateDoesNotPayT1 ()

visualAuditDoesNotPayT1 : VisualAuditPaysT1 → ⊥
visualAuditDoesNotPayT1 ()

adjacentProducerDoesNotPayT1 : AdjacentProducerPaysT1 → ⊥
adjacentProducerDoesNotPayT1 ()

round211T1Paid : Bool
round211T1Paid = false

round211T1PaidIsFalse : round211T1Paid ≡ false
round211T1PaidIsFalse = refl
