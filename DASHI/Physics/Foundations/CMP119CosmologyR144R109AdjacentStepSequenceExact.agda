{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR144R109AdjacentStepSequenceExact where

------------------------------------------------------------------------
-- B1 ADJACENT-STEP MAX-CUT.
--
-- The prior one-endpoint owner used equality of every displacement from scale
-- zero.  That is stronger than the RG source naturally wants to prove.
-- It is enough to identify the SIGNED adjacent response change at every scale:
--
--   R144(k+1)-R144(k) = R109(k+1)-R109(k),
--
-- plus one absolute endpoint.  Ordinary induction then forces equality of the
-- whole finite response sequence.
--
-- This does NOT identify Round109's present nonnegative `stressDifference`
-- with this signed adjacent difference.  It merely minimizes the same-object
-- theorem that the source layer must eventually supply.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

signedAdjacentDifference : (Nat → ℚ) → Nat → ℚ
signedAdjacentDifference response scale =
  response (suc scale) - response scale

oneEndpointAndSharedAdjacentDifferencesForceWholeSequence :
  (left right : Nat → ℚ) →
  left zero ≡ right zero →
  (∀ scale →
    signedAdjacentDifference left scale
    ≡ signedAdjacentDifference right scale) →
  ∀ scale → left scale ≡ right scale
oneEndpointAndSharedAdjacentDifferencesForceWholeSequence
    left right endpoint shared zero = endpoint
oneEndpointAndSharedAdjacentDifferencesForceWholeSequence
    left right endpoint shared (suc scale) =
  let
    inductionHypothesis : left scale ≡ right scale
    inductionHypothesis =
      oneEndpointAndSharedAdjacentDifferencesForceWholeSequence
        left right endpoint shared scale

    leftRebuild :
      left (suc scale)
      ≡ signedAdjacentDifference left scale + left scale
    leftRebuild = Ring.solve-∀ (left (suc scale)) (left scale)

    rightRebuild :
      signedAdjacentDifference right scale + right scale
      ≡ right (suc scale)
    rightRebuild = sym (Ring.solve-∀ (right (suc scale)) (right scale))
  in
  trans leftRebuild
    (trans
      (cong₂ _+_ (shared scale) inductionHypothesis)
      rightRebuild)

record AdjacentStepR144R109FiniteResponses : Set₁ where
  field
    r144FiniteResponse : Nat → ℚ
    r109FiniteResponse : Nat → ℚ

    sameSignedAdjacentStep : ∀ scale →
      signedAdjacentDifference r144FiniteResponse scale
      ≡ signedAdjacentDifference r109FiniteResponse scale

open AdjacentStepR144R109FiniteResponses public

record OneEndpointAdjacentStepCalibration
    (responses : AdjacentStepR144R109FiniteResponses) : Set where
  field
    baseEndpointExact :
      r144FiniteResponse responses zero
      ≡ r109FiniteResponse responses zero

open OneEndpointAdjacentStepCalibration public

adjacentCalibrationForcesSameFiniteSequence :
  ∀ {responses} →
  OneEndpointAdjacentStepCalibration responses →
  ∀ scale →
  r144FiniteResponse responses scale
  ≡ r109FiniteResponse responses scale
adjacentCalibrationForcesSameFiniteSequence {responses} calibration =
  oneEndpointAndSharedAdjacentDifferencesForceWholeSequence
    (r144FiniteResponse responses)
    (r109FiniteResponse responses)
    (baseEndpointExact calibration)
    (sameSignedAdjacentStep responses)

adjacentSignedStepIdentityIsSufficientWithOneEndpoint : Bool
adjacentSignedStepIdentityIsSufficientWithOneEndpoint = true

allScaleBaseDifferenceIdentityStillRequired : Bool
allScaleBaseDifferenceIdentityStillRequired = false

currentRound109NonnegativeDifferenceAlreadySuppliesSignedAdjacentStep : Bool
currentRound109NonnegativeDifferenceAlreadySuppliesSignedAdjacentStep = false

remainingB1SourceDifferenceLeafIsAdjacentSignedStepIdentity : Bool
remainingB1SourceDifferenceLeafIsAdjacentSignedStepIdentity = true
