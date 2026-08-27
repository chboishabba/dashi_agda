module DASHI.Analysis.RiemannG21OddTaylorNormalizedRadiusGateExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

oddMarginQ : ℚ → ℚ → ℚ → ℚ → ℚ
oddMarginQ n1a n1p qa qp =
  n1a * (n1p * qp) - (n1a * qa) * n1p

oddMarginRatioFactorization :
  (n1a n1p qa qp : ℚ) →
  oddMarginQ n1a n1p qa qp
  ≡ n1a * n1p * (qp - qa)
oddMarginRatioFactorization n1a n1p qa qp =
  solve (n1a ∷ n1p ∷ qa ∷ qp ∷ [])

trunc1RatioQ : ℚ → ℚ
trunc1RatioQ q = 6 + q

trunc2RatioQ : ℚ → ℚ
trunc2RatioQ q = 12 + 8 * q

normalizedErrorPolynomialQ : ℚ → ℚ → ℚ → ℚ → ℚ
normalizedErrorPolynomialQ qa qp ca cp =
    32 * trunc1RatioQ qa * cp
  + ca * trunc2RatioQ qp
  + trunc2RatioQ qa * cp
  + 32 * ca * trunc1RatioQ qp
  + 64 * ca * cp

normalizedErrorPolynomialExpanded :
  (qa qp ca cp : ℚ) →
  normalizedErrorPolynomialQ qa qp ca cp
  ≡
    204 * (ca + cp)
    + 40 * (qa * cp + qp * ca)
    + 64 * ca * cp
normalizedErrorPolynomialExpanded qa qp ca cp =
  solve (qa ∷ qp ∷ ca ∷ cp ∷ [])

fullErrorCoefficientQ :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
fullErrorCoefficientQ n1a n1p qa qp ca cp =
    32 * (n1a * trunc1RatioQ qa) * (n1p * cp)
  + (n1a * ca) * (n1p * trunc2RatioQ qp)
  + (n1a * trunc2RatioQ qa) * (n1p * cp)
  + 32 * (n1a * ca) * (n1p * trunc1RatioQ qp)
  + 64 * (n1a * ca) * (n1p * cp)

errorCoefficientMassFactorization :
  (n1a n1p qa qp ca cp : ℚ) →
  fullErrorCoefficientQ n1a n1p qa qp ca cp
  ≡
  (n1a * n1p) * normalizedErrorPolynomialQ qa qp ca cp
errorCoefficientMassFactorization n1a n1p qa qp ca cp =
  solve (n1a ∷ n1p ∷ qa ∷ qp ∷ ca ∷ cp ∷ [])

squareQ : ℚ → ℚ
squareQ x = x * x

fourthQ : ℚ → ℚ
fourthQ x = squareQ x * squareQ x

sixthQ : ℚ → ℚ
sixthQ x = fourthQ x * squareQ x

eighthQ : ℚ → ℚ
eighthQ x = fourthQ x * fourthQ x

supportPolynomial25Q : ℚ → ℚ
supportPolynomial25Q r =
  510 * fourthQ r + 100 * sixthQ r + 4 * eighthQ r

------------------------------------------------------------------------
-- Exact saturation certificate without division.
--
-- If c is the saturated coefficient R^4/20, encoded by 20c=R^4, the first
-- factor below vanishes.  We deliberately expose only the ring factorization
-- here; turning 20c=R^4 into the final equality is a tiny ordered/ring consumer
-- step and is not worth a brittle hand-built equality proof in this owner.
------------------------------------------------------------------------

supportSaturationDifferenceFactorization :
  (r c : ℚ) →
  25 * normalizedErrorPolynomialQ (squareQ r) (squareQ r) c c
    - supportPolynomial25Q r
  ≡
  2 * (20 * c - fourthQ r)
    * (2 * fourthQ r + 50 * squareQ r + 40 * c + 255)
supportSaturationDifferenceFactorization r c =
  solve (r ∷ c ∷ [])

record SupportNormalizedErrorMajorant : Set₁ where
  field
    Scalar : Set
    supportRadius errorPolynomial supportPolynomial : Scalar
    multiply : Scalar → Scalar → Scalar
    times25 : Scalar → Scalar
    LessOrEqual : Scalar → Scalar → Set
    supportMomentBounds : Set
    errorPolynomialMajorized :
      LessOrEqual (times25 errorPolynomial) supportPolynomial
    reading : String

record NormalizedOddRadiusGate : Set₁ where
  field
    Scalar : Set
    qa qp ca cp radiusSquared : Scalar
    errorPolynomial ratioGap : Scalar
    multiply : Scalar → Scalar → Scalar
    times36 : Scalar → Scalar
    StrictBelow : Scalar → Scalar → Set
    errorPolynomialFormula : Set
    ratioGapFormula : Set
    normalizedSmallRadiusGate :
      StrictBelow
        (multiply errorPolynomial radiusSquared)
        (times36 ratioGap)
    reading : String

record SupportOnlyOddRadiusGate : Set₁ where
  field
    Scalar : Set
    supportPolynomial radiusSquared ratioGap : Scalar
    multiply : Scalar → Scalar → Scalar
    times900 : Scalar → Scalar
    StrictBelow : Scalar → Scalar → Set
    sufficientGate :
      StrictBelow
        (multiply supportPolynomial radiusSquared)
        (times900 ratioGap)
    reading : String

record NormalizedRadiusGateBoundary : Set where
  constructor normalizedRadiusGateBoundary
  field
    oddMarginMassFactorizationDerived : Bool
    oddMarginMassFactorizationDerivedIsTrue :
      oddMarginMassFactorizationDerived ≡ true
    errorCoefficientMassFactorizationDerived : Bool
    errorCoefficientMassFactorizationDerivedIsTrue :
      errorCoefficientMassFactorizationDerived ≡ true
    normalizedErrorPolynomialExpansionDerived : Bool
    normalizedErrorPolynomialExpansionDerivedIsTrue :
      normalizedErrorPolynomialExpansionDerived ≡ true
    supportSaturationFactorizationDerived : Bool
    supportSaturationFactorizationDerivedIsTrue :
      supportSaturationFactorizationDerived ≡ true
    supportOnlyPolynomialConstructed : Bool
    supportOnlyPolynomialConstructedIsTrue : supportOnlyPolynomialConstructed ≡ true
    massFreeRadiusGateConstructed : Bool
    massFreeRadiusGateConstructedIsTrue : massFreeRadiusGateConstructed ≡ true
    positiveMassCancellationDerivedInAgda : Bool
    positiveMassCancellationDerivedInAgdaIsFalse :
      positiveMassCancellationDerivedInAgda ≡ false
    supportPolynomialMajorantDerivedInAgda : Bool
    supportPolynomialMajorantDerivedInAgdaIsFalse :
      supportPolynomialMajorantDerivedInAgda ≡ false
    actualNormalizedRadiusGateInhabited : Bool
    actualNormalizedRadiusGateInhabitedIsFalse :
      actualNormalizedRadiusGateInhabited ≡ false

canonicalNormalizedRadiusGateBoundary : NormalizedRadiusGateBoundary
canonicalNormalizedRadiusGateBoundary =
  normalizedRadiusGateBoundary
    true refl true refl true refl true refl true refl true refl
    false refl false refl false refl
