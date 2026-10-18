{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact where

------------------------------------------------------------------------
-- WHY ROUND109 DIFFERENCE DATA CANNOT RECOVER AN ABSOLUTE STRESS EXPECTATION.
--
-- Round109 owns a Cauchy modulus for finite-scale RESPONSE DIFFERENCES.  Such
-- data are invariant under adding one constant to every finite response.  The
-- absolute sign, however, is not invariant under that translation.
--
-- Therefore no proof may derive the absolute R144/R109 expectation anchor from
-- Round109's difference/tail interface alone.  One endpoint/same-sequence
-- identification is genuine information debt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as Ring

responseDifference : (Nat → ℚ) → Nat → Nat → ℚ
responseDifference response start count =
  response (start + count) - response start

translateResponse : ℚ → (Nat → ℚ) → Nat → ℚ
translateResponse shift response scale = shift + response scale

translationLeavesEveryDifferenceUnchanged :
  ∀ shift response start count →
  responseDifference (translateResponse shift response) start count
  ≡ responseDifference response start count
translationLeavesEveryDifferenceUnchanged shift response start count =
  Ring.solve-∀
    shift
    (response (start + count))
    (response start)

zeroResponse : Nat → ℚ
zeroResponse _ = 0ℚ

unitResponse : Nat → ℚ
unitResponse _ = 1ℚ

zeroAndUnitResponsesHaveSameDifferences :
  ∀ start count →
  responseDifference zeroResponse start count
  ≡ responseDifference unitResponse start count
zeroAndUnitResponsesHaveSameDifferences start count =
  Ring.solve []

zeroAndUnitResponsesHaveDifferentAbsoluteEndpoint :
  zeroResponse 0 ≡ 0ℚ
zeroAndUnitResponsesHaveDifferentAbsoluteEndpoint =
  Agda.Builtin.Equality.refl

unitResponseEndpointIsOne :
  unitResponse 0 ≡ 1ℚ
unitResponseEndpointIsOne =
  Agda.Builtin.Equality.refl

round109DifferenceDataFixAbsoluteAdditiveConstant : Bool
round109DifferenceDataFixAbsoluteAdditiveConstant = false

absoluteExpectationAnchorIsGenuineAdditionalInformation : Bool
absoluteExpectationAnchorIsGenuineAdditionalInformation = true

cauchyTailAloneCannotFixFiniteStressSign : Bool
cauchyTailAloneCannotFixFiniteStressSign = true
