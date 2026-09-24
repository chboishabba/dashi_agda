{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteBoundedCovarianceExact where

------------------------------------------------------------------------
-- FINITE RATIONAL BOUNDED-COVARIANCE THEOREM
--
-- For a finite nonnegative normalized weight and pointwise bounds
--
--   |F| <= A,   |G| <= B,
--
-- prove internally
--
--   |Cov(F,G)| <= 2 A B.
--
-- This discharges the "standard bounded conditional covariance inequality"
-- used by the Heat/Doob Round102 lane on every finite rational conditional
-- probability fibre.  No probabilistic authority is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRestrictedExpectationBoundExact as Restricted
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Abs

record FiniteRationalProbability (State : Set) : Set₁ where
  field
    states : List State
    weight : State → ℚ
    weightNonnegative : ∀ state → 0ℚ ≤ weight state
    normalized :
      Sums.sumRational states weight ≡ 1ℚ

open FiniteRationalProbability public

Observable : Set → Set
Observable State = State → ℚ

expectation :
  ∀ {State} → FiniteRationalProbability State → Observable State → ℚ
expectation probability observable =
  Sums.sumRational (states probability)
    (λ state → weight probability state * observable state)

PointwiseBounded :
  ∀ {State} → Observable State → ℚ → Set
PointwiseBounded observable majorant =
  ∀ state → ∣ observable state ∣ ≤ majorant

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚP.0≤∣p∣ 1ℚ

expectationAbsoluteBound :
  ∀ {State}
    (probability : FiniteRationalProbability State)
    (observable : Observable State)
    (majorant : ℚ) →
  0ℚ ≤ majorant →
  PointwiseBounded observable majorant →
  ∣ expectation probability observable ∣ ≤ majorant
expectationAbsoluteBound probability observable majorant majorantNN bounded =
  let
    dataSet : Restricted.FiniteRestrictedExpectationData State
    dataSet = record
      { Restricted.FiniteRestrictedExpectationData.states =
          states probability
      ; Restricted.FiniteRestrictedExpectationData.weight =
          weight probability
      ; Restricted.FiniteRestrictedExpectationData.mask =
          λ _ → 1ℚ
      ; Restricted.FiniteRestrictedExpectationData.observable =
          observable
      ; Restricted.FiniteRestrictedExpectationData.majorant =
          majorant
      ; Restricted.FiniteRestrictedExpectationData.weightNonnegative =
          weightNonnegative probability
      ; Restricted.FiniteRestrictedExpectationData.maskNonnegative =
          λ _ → oneNonnegative
      ; Restricted.FiniteRestrictedExpectationData.observableBounded =
          bounded
      ; Restricted.FiniteRestrictedExpectationData.majorantNonnegative =
          majorantNN
      }

    raw :
      ∣ expectation probability observable ∣
      ≤ majorant * Restricted.restrictedMass dataSet
    raw = Restricted.restrictedExpectationBelowMass dataSet

    massIsOne : Restricted.restrictedMass dataSet ≡ 1ℚ
    massIsOne =
      trans
        (Sums.sumRationalCong
          (states probability)
          (λ state → weight probability state * 1ℚ)
          (weight probability)
          (λ state → ℚP.*-identityʳ (weight probability state)))
        (normalized probability)

    upperExact :
      majorant * Restricted.restrictedMass dataSet ≡ majorant
    upperExact =
      trans
        (cong (majorant *_) massIsOne)
        (ℚP.*-identityʳ majorant)
  in
  subst
    (λ upper → ∣ expectation probability observable ∣ ≤ upper)
    upperExact
    raw

multiplyMajorantNonnegative :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
multiplyMajorantNonnegative {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = nonNegative rightNN
      productNonnegative : NonNegative (left * right)
      productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

productPointwiseBound :
  ∀ {State}
    (left right : Observable State)
    leftMajorant rightMajorant →
  0ℚ ≤ leftMajorant →
  0ℚ ≤ rightMajorant →
  PointwiseBounded left leftMajorant →
  PointwiseBounded right rightMajorant →
  PointwiseBounded
    (λ state → left state * right state)
    (leftMajorant * rightMajorant)
productPointwiseBound left right leftMajorant rightMajorant
    leftNN rightNN leftBound rightBound state =
  Abs.absoluteProductBound
    (leftBound state)
    (rightBound state)
    leftNN rightNN

covariance :
  ∀ {State} →
  FiniteRationalProbability State →
  Observable State → Observable State → ℚ
covariance probability left right =
  expectation probability (λ state → left state * right state)
  - expectation probability left * expectation probability right

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

boundedCovariance :
  ∀ {State}
    (probability : FiniteRationalProbability State)
    (left right : Observable State)
    leftMajorant rightMajorant →
  0ℚ ≤ leftMajorant →
  0ℚ ≤ rightMajorant →
  PointwiseBounded left leftMajorant →
  PointwiseBounded right rightMajorant →
  ∣ covariance probability left right ∣
  ≤ twoℚ * (leftMajorant * rightMajorant)
boundedCovariance probability left right
    leftMajorant rightMajorant
    leftNN rightNN leftBound rightBound =
  let
    productMajorant = leftMajorant * rightMajorant
    productNN = multiplyMajorantNonnegative leftNN rightNN

    productExpectationBound :
      ∣ expectation probability
          (λ state → left state * right state) ∣
      ≤ productMajorant
    productExpectationBound =
      expectationAbsoluteBound
        probability
        (λ state → left state * right state)
        productMajorant
        productNN
        (productPointwiseBound
          left right leftMajorant rightMajorant
          leftNN rightNN leftBound rightBound)

    leftExpectationBound :
      ∣ expectation probability left ∣ ≤ leftMajorant
    leftExpectationBound =
      expectationAbsoluteBound
        probability left leftMajorant leftNN leftBound

    rightExpectationBound :
      ∣ expectation probability right ∣ ≤ rightMajorant
    rightExpectationBound =
      expectationAbsoluteBound
        probability right rightMajorant rightNN rightBound

    meansProductBound :
      ∣ expectation probability left * expectation probability right ∣
      ≤ productMajorant
    meansProductBound =
      Abs.absoluteProductBound
        leftExpectationBound rightExpectationBound leftNN rightNN

    triangle :
      ∣ covariance probability left right ∣
      ≤ ∣ expectation probability
            (λ state → left state * right state) ∣
        + ∣ expectation probability left * expectation probability right ∣
    triangle =
      ℚP.∣p-q∣≤∣p∣+∣q∣
        (expectation probability (λ state → left state * right state))
        (expectation probability left * expectation probability right)

    summed :
      ∣ expectation probability
          (λ state → left state * right state) ∣
        + ∣ expectation probability left * expectation probability right ∣
      ≤ productMajorant + productMajorant
    summed =
      ℚP.+-mono-≤ productExpectationBound meansProductBound

    twiceExact :
      productMajorant + productMajorant
      ≡ twoℚ * productMajorant
    twiceExact = ℚRing.solve-∀ productMajorant
  in
  ℚP.≤-trans triangle
    (subst
      (λ upper →
        ∣ expectation probability
            (λ state → left state * right state) ∣
          + ∣ expectation probability left * expectation probability right ∣
        ≤ upper)
      twiceExact
      summed)

unitBoundedCovariance :
  ∀ {State}
    (probability : FiniteRationalProbability State)
    (left right : Observable State) →
  PointwiseBounded left 1ℚ →
  PointwiseBounded right 1ℚ →
  ∣ covariance probability left right ∣ ≤ twoℚ
unitBoundedCovariance probability left right leftBound rightBound =
  subst
    (λ upper → ∣ covariance probability left right ∣ ≤ upper)
    (ℚRing.solve [] : twoℚ * (1ℚ * 1ℚ) ≡ twoℚ)
    (boundedCovariance
      probability left right 1ℚ 1ℚ
      oneNonnegative oneNonnegative leftBound rightBound)

finiteRationalBoundedCovarianceLevel : ProofLevel
finiteRationalBoundedCovarianceLevel = machineChecked
