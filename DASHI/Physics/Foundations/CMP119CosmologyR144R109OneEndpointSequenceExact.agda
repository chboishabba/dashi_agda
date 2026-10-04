{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR144R109OneEndpointSequenceExact where

------------------------------------------------------------------------
-- R144 <-> R109 SAME-SEQUENCE MAX-CUT.
--
-- Difference data determine a response sequence only up to one additive
-- constant.  Therefore, ONCE two finite response sequences are identified as
-- having the same SIGNED differences, a SINGLE absolute endpoint calibration
-- fixes the whole sequence.
--
-- Important source boundary: the present Round109 source interface exposes a
-- nonnegative `ordinaryDifference` controlled by the RG tail.  It does not yet
-- identify that scalar with the signed difference of the pinned finite
-- expectation sequence.  Thus this file does NOT claim that Round109 alone has
-- discharged `sameScaleDifferences`; that same-object interpretation remains a
-- physical/source theorem.
--
-- This is the algebraic complement to
-- `CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact`: all-scale absolute
-- calibration is redundant after signed differences match, but the signed
-- difference identification itself is not manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

responseFromBaseDifference : (Nat → ℚ) → Nat → ℚ
responseFromBaseDifference response scale =
  response scale - response zero

oneEndpointAndSharedDifferencesForceWholeSequence :
  (left right : Nat → ℚ) →
  left zero ≡ right zero →
  (∀ scale →
    responseFromBaseDifference left scale
    ≡ responseFromBaseDifference right scale) →
  ∀ scale → left scale ≡ right scale
oneEndpointAndSharedDifferencesForceWholeSequence
    left right endpoint shared scale =
  trans
    (Ring.solve-∀ (left scale) (left zero))
    (trans
      (cong (λ difference → difference + left zero) (shared scale))
      (trans
        (cong
          (λ base →
            responseFromBaseDifference right scale + base)
          endpoint)
        (sym (Ring.solve-∀ (right scale) (right zero)))))

record SameDifferenceR144R109FiniteResponses : Set₁ where
  field
    r144FiniteResponse : Nat → ℚ
    r109FiniteResponse : Nat → ℚ

    sameScaleDifferences : ∀ scale →
      responseFromBaseDifference r144FiniteResponse scale
      ≡ responseFromBaseDifference r109FiniteResponse scale

open SameDifferenceR144R109FiniteResponses public

record OneEndpointR144R109Calibration
    (responses : SameDifferenceR144R109FiniteResponses) : Set where
  field
    baseEndpointExact :
      r144FiniteResponse responses zero
      ≡ r109FiniteResponse responses zero

open OneEndpointR144R109Calibration public

calibrationForcesSameFiniteSequence :
  ∀ {responses} →
  OneEndpointR144R109Calibration responses →
  ∀ scale →
  r144FiniteResponse responses scale
  ≡ r109FiniteResponse responses scale
calibrationForcesSameFiniteSequence {responses} calibration =
  oneEndpointAndSharedDifferencesForceWholeSequence
    (r144FiniteResponse responses)
    (r109FiniteResponse responses)
    (baseEndpointExact calibration)
    (sameScaleDifferences responses)

signedDifferenceMatchLeavesOnlyOneAdditiveConstant : Bool
signedDifferenceMatchLeavesOnlyOneAdditiveConstant = true

currentRound109NonnegativeDifferenceIsAlreadySignedDifferenceIdentity : Bool
currentRound109NonnegativeDifferenceIsAlreadySignedDifferenceIdentity = false

remainingAbsoluteDebtIsOneEndpoint : Bool
remainingAbsoluteDebtIsOneEndpoint = true

allScaleAbsoluteCalibrationIsParetoRedundantOnceDifferencesMatch : Bool
allScaleAbsoluteCalibrationIsParetoRedundantOnceDifferencesMatch = true
