module DASHI.Foundations.ActorScopedSameObjectValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.ActorScopedSameObjectExact as Actor

sameActorRequired :
  Actor.sameActorRequired Actor.canonicalBoundary ≡ true
sameActorRequired = refl

twoSidedCarrierRecognitionRequired :
  Actor.twoSidedCarrierRecognitionRequired Actor.canonicalBoundary ≡ true
twoSidedCarrierRecognitionRequired = refl

actionIntertwiningRequired :
  Actor.actionIntertwiningRequired Actor.canonicalBoundary ≡ true
actionIntertwiningRequired = refl

cardinalityDoesNotPromote :
  Actor.cardinalitySplitPromotesToInvariantDecomposition Actor.canonicalBoundary ≡ false
cardinalityDoesNotPromote = refl

actorChangeDoesNotTransportAutomatically :
  Actor.decompositionAutomaticallySurvivesActorChange Actor.canonicalBoundary ≡ false
actorChangeDoesNotTransportAutomatically = refl
