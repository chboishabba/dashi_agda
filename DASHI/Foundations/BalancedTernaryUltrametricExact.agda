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

------------------------------------------------------------------------
-- A depth-availability witness records that a finite address actually has at
-- least the requested number of digits.
------------------------------------------------------------------------

data HasPrefixDepth : Nat → List BT.BalancedDigit → Set where
  hasDepthZero : ∀ {xs} → HasPrefixDepth 0 xs
  hasDepthNeg :
    ∀ {n xs} → HasPrefixDepth n xs →
    HasPrefixDepth (suc n) (BT.neg ∷ xs)
  hasDepthOpen :
    ∀ {n xs} → HasPrefixDepth n xs →
    HasPrefixDepth (suc n) (BT.zeroDigit ∷ xs)
  hasDepthPos :
    ∀ {n xs} → HasPrefixDepth n xs →
    HasPrefixDepth (suc n) (BT.pos ∷ xs)

prefixAgreementReflexive :
  ∀ {n xs} →
  HasPrefixDepth n xs →
  PrefixAgreement n xs xs
prefixAgreementReflexive hasDepthZero = agreeZero
prefixAgreementReflexive (hasDepthNeg witness) =
  agreeNeg (prefixAgreementReflexive witness)
prefixAgreementReflexive (hasDepthOpen witness) =
  agreeOpen (prefixAgreementReflexive witness)
prefixAgreementReflexive (hasDepthPos witness) =
  agreePos (prefixAgreementReflexive witness)

prefixAgreementWeaken :
  ∀ {n xs ys} →
  PrefixAgreement (suc n) xs ys →
  PrefixAgreement n xs ys
prefixAgreementWeaken {zero} witness = agreeZero
prefixAgreementWeaken {suc n} (agreeNeg witness) =
  agreeNeg (prefixAgreementWeaken witness)
prefixAgreementWeaken {suc n} (agreeOpen witness) =
  agreeOpen (prefixAgreementWeaken witness)
prefixAgreementWeaken {suc n} (agreePos witness) =
  agreePos (prefixAgreementWeaken witness)

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

fiveHasDepthThree : HasPrefixDepth 3 fiveDigits
fiveHasDepthThree = hasDepthPos (hasDepthNeg (hasDepthNeg hasDepthZero))

sixHasDepthThree : HasPrefixDepth 3 sixDigits
sixHasDepthThree = hasDepthPos (hasDepthNeg (hasDepthOpen hasDepthZero))

fiveReflexiveAtDepthThree : PrefixAgreement 3 fiveDigits fiveDigits
fiveReflexiveAtDepthThree = prefixAgreementReflexive fiveHasDepthThree

fiveSixAgreeThroughDepthTwo : PrefixAgreement 2 fiveDigits sixDigits
fiveSixAgreeThroughDepthTwo = agreePos (agreeNeg agreeZero)

fiveSixAgreeThroughDepthOne : PrefixAgreement 1 fiveDigits sixDigits
fiveSixAgreeThroughDepthOne =
  prefixAgreementWeaken fiveSixAgreeThroughDepthTwo

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

fiveCentredWeakerBallContainingSix : PrefixBall
fiveCentredWeakerBallContainingSix =
  prefixBall 1 fiveDigits sixDigits fiveSixAgreeThroughDepthOne

record UltrametricPrefixBoundary : Set where
  constructor ultrametricPrefixBoundary
  field
    prefixBallTransitivityProved : Bool
    prefixBallTransitivityProvedIsTrue :
      prefixBallTransitivityProved ≡ true
    transitivityWitness :
      ∀ {n xs ys zs} →
      PrefixAgreement n xs ys →
      PrefixAgreement n ys zs →
      PrefixAgreement n xs zs
    finiteDepthReflexivityProved : Bool
    finiteDepthReflexivityProvedIsTrue :
      finiteDepthReflexivityProved ≡ true
    depthWeakeningProved : Bool
    depthWeakeningProvedIsTrue : depthWeakeningProved ≡ true
    realValuedMetricConstructed : Bool
    realValuedMetricConstructedIsFalse :
      realValuedMetricConstructed ≡ false
    constituentSuffixesErased : Bool
    constituentSuffixesErasedIsFalse : constituentSuffixesErased ≡ false

canonicalUltrametricPrefixBoundary : UltrametricPrefixBoundary
canonicalUltrametricPrefixBoundary =
  ultrametricPrefixBoundary
    true refl prefixAgreementTransitive
    true refl
    true refl
    false refl
    false refl
