{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1ExplicitSmallCouplingQuarticAbsorptionRound101Exact where

------------------------------------------------------------------------
-- ROUND101: EXPLICIT SMALL-COUPLING ABSORPTION FOR THE HISTORY-UNIFORM CUT
--
-- Once the SAME current beta has a Gaussian floor b>0 and a finite nonnegative
-- history-uniform five-channel coefficient C, no fourth-root search is needed.
-- Choose
--
--        gamma* = (1/2) b / (C+b).
--
-- Then 0<=gamma*<=1/2<=1 and
--
--        C gamma*^4 <= C gamma* <= b/2.
--
-- Combined with the Round101 anti-double-count theorem, this turns the source
-- task into finite C and positive b on the same admissible generated histories.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

denominator : ℚ → ℚ → ℚ
denominator coefficient floor = coefficient + floor

floorBelowDenominator : ∀ coefficient floor →
  0ℚ ≤ coefficient → floor ≤ denominator coefficient floor
floorBelowDenominator coefficient floor coefficientNN =
  subst
    (λ right → floor ≤ right)
    (ℚRing.solve-∀ coefficient floor)
    (ℚP.+-monoʳ-≤ floor coefficientNN)

coefficientBelowDenominator : ∀ coefficient floor →
  0ℚ ≤ floor → coefficient ≤ denominator coefficient floor
coefficientBelowDenominator coefficient floor floorNN =
  subst
    (λ right → coefficient ≤ right)
    (ℚP.+-identityʳ coefficient)
    (ℚP.+-monoˡ-≤ coefficient floorNN)

denominatorPositive : ∀ coefficient floor →
  0ℚ ≤ coefficient → 0ℚ < floor →
  0ℚ < denominator coefficient floor
denominatorPositive coefficient floor coefficientNN floorPositive =
  ℚP.<-≤-trans floorPositive
    (floorBelowDenominator coefficient floor coefficientNN)

gammaStar :
  (coefficient floor : ℚ) →
  0ℚ ≤ coefficient → 0ℚ < floor → ℚ
gammaStar coefficient floor coefficientNN floorPositive =
  let
    dPositive = denominatorPositive coefficient floor coefficientNN floorPositive
  in
  Beta.half * floor
    * Quotient.positiveReciprocal
        (denominator coefficient floor) dPositive

gammaStarNonnegative :
  ∀ coefficient floor coefficientNN floorPositive →
  0ℚ ≤ gammaStar coefficient floor coefficientNN floorPositive
gammaStarNonnegative coefficient floor coefficientNN floorPositive =
  let
    d = denominator coefficient floor
    dPositive = denominatorPositive coefficient floor coefficientNN floorPositive
    reciprocal = Quotient.positiveReciprocal d dPositive
    floorNN = ℚP.<⇒≤ floorPositive
    halfTimesFloorNN =
      Norm.scaleNonnegative Beta.half
        (ℚP.nonNegative⁻¹ Beta.half) floorNN
    reciprocalNN : NonNegative reciprocal
    reciprocalNN = Quotient.positiveReciprocalNonnegative d dPositive
  in
  ℚP.*-monoʳ-≤-nonNeg reciprocalNN
    (subst (λ right → 0ℚ ≤ right) (ℚP.*-zeroˡ reciprocal)
      halfTimesFloorNN)

gammaStarBelowHalf :
  ∀ coefficient floor coefficientNN floorPositive →
  gammaStar coefficient floor coefficientNN floorPositive ≤ Beta.half
gammaStarBelowHalf coefficient floor coefficientNN floorPositive =
  let
    d = denominator coefficient floor
    dPositive = denominatorPositive coefficient floor coefficientNN floorPositive
    reciprocal = Quotient.positiveReciprocal d dPositive
    reciprocalNN : NonNegative reciprocal
    reciprocalNN = Quotient.positiveReciprocalNonnegative d dPositive
    floorBelow = floorBelowDenominator coefficient floor coefficientNN
    scaledFloor : floor * reciprocal ≤ d * reciprocal
    scaledFloor = ℚP.*-monoʳ-≤-nonNeg reciprocalNN floorBelow
    dInverse : d * reciprocal ≡ 1ℚ
    dInverse = Quotient.positiveReciprocalRightInverse d dPositive
    floorReciprocalBelowOne : floor * reciprocal ≤ 1ℚ
    floorReciprocalBelowOne =
      subst (λ right → floor * reciprocal ≤ right) dInverse scaledFloor
    scaledHalf = Norm.scaleNonnegative Beta.half
      (ℚP.nonNegative⁻¹ Beta.half) floorReciprocalBelowOne
  in
  subst
    (λ left → left ≤ Beta.half)
    (ℚRing.solve-∀ Beta.half floor reciprocal)
    (subst
      (λ right → Beta.half * (floor * reciprocal) ≤ right)
      (sym (ℚP.*-identityʳ Beta.half))
      scaledHalf)

gammaStarBelowOne :
  ∀ coefficient floor coefficientNN floorPositive →
  gammaStar coefficient floor coefficientNN floorPositive ≤ 1ℚ
gammaStarBelowOne coefficient floor coefficientNN floorPositive =
  ℚP.≤-trans
    (gammaStarBelowHalf coefficient floor coefficientNN floorPositive)
    (ℚP.nonNegative⁻¹ (1ℚ - Beta.half))
  where
    open import Data.Rational.Base using (_-_)

power4BelowSelfOnUnitInterval : ∀ gamma →
  0ℚ ≤ gamma → gamma ≤ 1ℚ → Beta.power4 gamma ≤ gamma
power4BelowSelfOnUnitInterval gamma gammaNN gammaBelowOne =
  let
    square = gamma * gamma
    squareNN = FiniteL2.squareNonnegative gamma
    squareBelowGammaRaw : gamma * gamma ≤ gamma * 1ℚ
    squareBelowGammaRaw = Norm.scaleNonnegative gamma gammaNN gammaBelowOne
    squareBelowGamma : square ≤ gamma
    squareBelowGamma = subst
      (λ right → square ≤ right)
      (ℚP.*-identityʳ gamma)
      squareBelowGammaRaw
    squareBelowOne = ℚP.≤-trans squareBelowGamma gammaBelowOne
    fourthBelowSquareRaw : square * square ≤ square * 1ℚ
    fourthBelowSquareRaw = Norm.scaleNonnegative square squareNN squareBelowOne
    fourthBelowSquare : Beta.power4 gamma ≤ square
    fourthBelowSquare = subst
      (λ right → Beta.power4 gamma ≤ right)
      (ℚP.*-identityʳ square)
      fourthBelowSquareRaw
  in
  ℚP.≤-trans fourthBelowSquare squareBelowGamma

coefficientTimesGammaStarBelowHalfFloor :
  ∀ coefficient floor coefficientNN floorPositive →
  coefficient * gammaStar coefficient floor coefficientNN floorPositive
  ≤ Beta.half * floor
coefficientTimesGammaStarBelowHalfFloor coefficient floor coefficientNN floorPositive =
  let
    d = denominator coefficient floor
    dPositive = denominatorPositive coefficient floor coefficientNN floorPositive
    reciprocal = Quotient.positiveReciprocal d dPositive
    gamma = gammaStar coefficient floor coefficientNN floorPositive
    gammaNN = gammaStarNonnegative coefficient floor coefficientNN floorPositive
    floorNN = ℚP.<⇒≤ floorPositive
    coefficientBelow = coefficientBelowDenominator coefficient floor floorNN
    scaled = Norm.scaleNonnegative gamma gammaNN coefficientBelow
    identifyRight : d * gamma ≡ Beta.half * floor
    identifyRight =
      trans
        (ℚRing.solve-∀ d Beta.half floor reciprocal)
        (trans
          (cong (Beta.half * floor *_)
            (Quotient.positiveReciprocalRightInverse d dPositive))
          (ℚP.*-identityʳ (Beta.half * floor)))
  in
  subst (λ right → coefficient * gamma ≤ right) identifyRight scaled

explicitQuarticAbsorption :
  ∀ coefficient floor coefficientNN floorPositive →
  coefficient
    * Beta.power4 (gammaStar coefficient floor coefficientNN floorPositive)
  ≤ Beta.half * floor
explicitQuarticAbsorption coefficient floor coefficientNN floorPositive =
  let
    gamma = gammaStar coefficient floor coefficientNN floorPositive
    gammaNN = gammaStarNonnegative coefficient floor coefficientNN floorPositive
    gammaBelowOne = gammaStarBelowOne coefficient floor coefficientNN floorPositive
    fourthBelowGamma = power4BelowSelfOnUnitInterval gamma gammaNN gammaBelowOne
    scaled = Norm.scaleNonnegative coefficient coefficientNN fourthBelowGamma
  in
  ℚP.≤-trans scaled
    (coefficientTimesGammaStarBelowHalfFloor
      coefficient floor coefficientNN floorPositive)

explicitSmallCouplingQuarticAbsorptionRound101Level : ProofLevel
explicitSmallCouplingQuarticAbsorptionRound101Level = machineChecked
