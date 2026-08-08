module DASHI.Foundations.BalancedTernaryUltrametricExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT

------------------------------------------------------------------------
-- Finite balanced-ternary addresses carry the standard prefix ultrametric
-- structure.  Rather than importing real-valued distances, we retain the exact
-- valuation depth: agreement through depth n means distance at most 3^(-n).
------------------------------------------------------------------------

data PrefixAgreement :
  Nat → List BT.BalancedDigit → List BT.BalancedDigit → Set where
  agreeZero :
    ∀ {xs ys} → PrefixAgreement 0 xs ys

  agreeNeg :
    ∀ {n xs ys} →
    PrefixAgreement n xs ys →
    PrefixAgreement (suc n) (BT.neg ∷ xs) (BT.neg ∷ ys)

  agreeOpen :
    ∀ {n xs ys} →
    PrefixAgreement n xs ys →
    PrefixAgreement (suc n)
      (BT.zeroDigit ∷ xs) (BT.zeroDigit ∷ ys)

  agreePos :
    ∀ {n xs ys} →
    PrefixAgreement n xs ys →
    PrefixAgreement (suc n) (BT.pos ∷ xs) (BT.pos ∷ ys)

prefixAgreementTransitive :
  ∀ {n xs ys zs} →
  PrefixAgreement n xs ys →
  PrefixAgreement n ys zs →
  PrefixAgreement n xs zs
prefixAgreementTransitive agreeZero agreeZero = agreeZero
prefixAgreementTransitive (agreeNeg left) (agreeNeg right) =
  agreeNeg (prefixAgreementTransitive left right)
prefixAgreementTransitive (agreeOpen left) (agreeOpen right) =
  agreeOpen (prefixAgreementTransitive left right)
prefixAgreementTransitive (agreePos left) (agreePos right) =
  agreePos (prefixAgreementTransitive left right)

prefixAgreementSymmetric :
  ∀ {n xs ys} →
  PrefixAgreement n xs ys →
  PrefixAgreement n ys xs
prefixAgreementSymmetric agreeZero = agreeZero
prefixAgreementSymmetric (agreeNeg witness) =
  agreeNeg (prefixAgreementSymmetric witness)
prefixAgreementSymmetric (agreeOpen witness) =
  agreeOpen (prefixAgreementSymmetric witness)
prefixAgreementSymmetric (agreePos witness) =
  agreePos (prefixAgreementSymmetric witness)

prefixScaleDenominator : Nat → Nat
prefixScaleDenominator depth = 3 ^ depth

prefixDepthTwoHasDenominatorNine : prefixScaleDenominator 2 ≡ 9
prefixDepthTwoHasDenominatorNine = refl

fiveDigits : List BT.BalancedDigit
fiveDigits = BT.pos ∷ BT.neg ∷ BT.neg ∷ []

sixDigits : List BT.BalancedDigit
sixDigits = BT.pos ∷ BT.neg ∷ BT.zeroDigit ∷ []

fiveSixAgreeThroughDepthTwo : PrefixAgreement 2 fiveDigits sixDigits
fiveSixAgreeThroughDepthTwo = agreePos (agreeNeg agreeZero)

fiveAddressDigitsRegression :
  BT.BalancedTernaryAddress.digitsHighToLow BT.fiveBalancedAddress
  ≡ fiveDigits
fiveAddressDigitsRegression = refl

sixAddressDigitsRegression :
  BT.BalancedTernaryAddress.digitsHighToLow BT.sixBalancedAddress
  ≡ sixDigits
sixAddressDigitsRegression = refl

record PrefixBall : Set where
  constructor prefixBall
  field
    radiusDepth : Nat
    centre point : List BT.BalancedDigit
    membership : PrefixAgreement radiusDepth centre point

open PrefixBall public

fiveCentredBallContainingSix : PrefixBall
fiveCentredBallContainingSix =
  prefixBall 2 fiveDigits sixDigits fiveSixAgreeThroughDepthTwo

record UltrametricPrefixBoundary : Set where
  constructor ultrametricPrefixBoundary
  field
    prefixBallTransitivityProved : Bool
    prefixBallTransitivityProvedIsTrue :
      prefixBallTransitivityProved ≡ true
    realValuedMetricConstructed : Bool
    realValuedMetricConstructedIsFalse :
      realValuedMetricConstructed ≡ false
    constituentSuffixesErased : Bool
    constituentSuffixesErasedIsFalse : constituentSuffixesErased ≡ false

canonicalUltrametricPrefixBoundary : UltrametricPrefixBoundary
canonicalUltrametricPrefixBoundary =
  ultrametricPrefixBoundary true refl false refl false refl
