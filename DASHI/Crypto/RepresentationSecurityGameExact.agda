module DASHI.Crypto.RepresentationSecurityGameExact where

------------------------------------------------------------------------
-- REPRESENTATION-SECURITY GAME
--
-- The value of an observation is measured by the change it induces in optimal
-- recovery work after paying acquisition cost:
--
--   V(o) = C_before - (C_acquire(o) + C_after(o)).
--
-- The blue-team representation problem is therefore minimax-shaped: choose an
-- implementation representation whose worst allowed observation value is as
-- small as possible.  This finite module gives the exact accounting carrier and
-- a regression where the faster representation has the worse observation
-- surface, so transition speed and leakage resistance are not identified.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

record ObservationValue : Set where
  constructor observationValue
  field
    recoveryBefore acquisition recoveryAfter gain : Nat
    exactValue : recoveryBefore ≡ acquisition + recoveryAfter + gain

open ObservationValue public

record RepresentationSecurityProfile : Set where
  constructor representationSecurityProfile
  field
    transitionCost : Nat
    reopenCost : Nat
    observation₀ observation₁ : ObservationValue
    worstObservationGain : Nat

open RepresentationSecurityProfile public

------------------------------------------------------------------------
-- Two finite implementation geometries.
--
-- fastLocal has smaller transition cost but one strong side observation:
--   before 30 = acquisition 2 + after 8 + gain 20.
-- conservative has slower transitions but both observations have gain 3.
------------------------------------------------------------------------

fastObs0 fastObs1 : ObservationValue
fastObs0 = observationValue 30 2 8 20 refl
fastObs1 = observationValue 30 3 24 3 refl

conservativeObs0 conservativeObs1 : ObservationValue
conservativeObs0 = observationValue 30 3 24 3 refl
conservativeObs1 = observationValue 30 4 23 3 refl

fastLocal : RepresentationSecurityProfile
fastLocal = representationSecurityProfile 5 2 fastObs0 fastObs1 20

conservative : RepresentationSecurityProfile
conservative = representationSecurityProfile 8 2 conservativeObs0 conservativeObs1 3

fastTransitionIs5 : transitionCost fastLocal ≡ 5
fastTransitionIs5 = refl

conservativeTransitionIs8 : transitionCost conservative ≡ 8
conservativeTransitionIs8 = refl

fastWorstObservationGainIs20 : worstObservationGain fastLocal ≡ 20
fastWorstObservationGainIs20 = refl

conservativeWorstObservationGainIs3 : worstObservationGain conservative ≡ 3
conservativeWorstObservationGainIs3 = refl

------------------------------------------------------------------------
-- The finite minimax winner under the observation-value objective is the
-- conservative representation even though it has slower transitions.
------------------------------------------------------------------------

data RepresentationChoice : Set where chooseFast chooseConservative : RepresentationChoice

profile : RepresentationChoice → RepresentationSecurityProfile
profile chooseFast = fastLocal
profile chooseConservative = conservative

minimaxChoice : RepresentationChoice
minimaxChoice = chooseConservative

minimaxWorstGain : worstObservationGain (profile minimaxChoice) ≡ 3
minimaxWorstGain = refl

fasterDoesNotMeanSafer :
  transitionCost fastLocal ≡ 5
  × worstObservationGain fastLocal ≡ 20
  × transitionCost conservative ≡ 8
  × worstObservationGain conservative ≡ 3
fasterDoesNotMeanSafer = refl , (refl , (refl , refl))

record RepresentationSecurityBoundary : Set where
  constructor representationSecurityBoundary
  field
    transitionOptimalImplIsAutomaticallyLeakageOptimal : Set
    observationGainEqualsInformationBits : Set

open RepresentationSecurityBoundary public

canonicalRepresentationSecurityBoundary : RepresentationSecurityBoundary
canonicalRepresentationSecurityBoundary =
  representationSecurityBoundary
    (transitionCost fastLocal ≡ transitionCost conservative)
    (worstObservationGain fastLocal ≡ worstObservationGain conservative)
