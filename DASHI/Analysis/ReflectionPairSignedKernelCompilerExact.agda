module DASHI.Analysis.ReflectionPairSignedKernelCompilerExact where

------------------------------------------------------------------------
-- GENERIC REFLECTION-PAIR ALGEBRA
--
-- This is the Agda-owned algebraic core of the new signed off-ordinate lane.
-- If reflection preserves the even component and negates the odd component,
-- then pairing before absolute majorization removes the odd component exactly.
-- The literal identification of those components with the zeta Weil response
-- kernel is owned by the separate Lean source return.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong₂; trans)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; -_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record ReflectionPairDatum : Set where
  constructor reflection-pair-datum
  field
    even odd partnerEven partnerOdd : ℚ
    partnerEvenIsEven : partnerEven ≡ even
    partnerOddIsNegOdd : partnerOdd ≡ - odd

open ReflectionPairDatum public

leftResponse : ReflectionPairDatum → ℚ
leftResponse d = even d + odd d

rightResponse : ReflectionPairDatum → ℚ
rightResponse d = partnerEven d + partnerOdd d

reflectionPairSum : (d : ReflectionPairDatum) →
  leftResponse d + rightResponse d ≡ (+ 2 / 1) * even d
reflectionPairSum d =
  trans
    (cong₂ _+_
      refl
      (cong₂ _+_ (partnerEvenIsEven d) (partnerOddIsNegOdd d)))
    (solve (even d ∷ odd d ∷ []))

record ReflectionPairSignedKernelBoundary : Set where
  constructor reflection-pair-signed-kernel-boundary
  field
    pairBeforeAbsoluteValues : Bool
    pairBeforeAbsoluteValuesIsTrue : pairBeforeAbsoluteValues ≡ true
    oddComponentSurvivesPairing : Bool
    oddComponentSurvivesPairingIsFalse : oddComponentSurvivesPairing ≡ false

open import Agda.Builtin.Bool using (Bool; true; false)

canonicalReflectionPairSignedKernelBoundary : ReflectionPairSignedKernelBoundary
canonicalReflectionPairSignedKernelBoundary =
  reflection-pair-signed-kernel-boundary true refl false refl
