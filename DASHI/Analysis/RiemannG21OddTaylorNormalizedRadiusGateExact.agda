module DASHI.Analysis.RiemannG21OddTaylorNormalizedRadiusGateExact where

------------------------------------------------------------------------
-- Normalize the odd Taylor sign gate by the common N1(a)N1(p) mass.
--
-- Assume
--
--   N3(a) = N1(a) q_a,
--   N3(p) = N1(p) q_p,
--   C_a   = N1(a) c_a,
--   C_p   = N1(p) c_p,
--
-- where C_a,C_p are the six-scaled fifth-order response-remainder
-- coefficients.  Then both the strict odd signal margin and the constructed
-- determinant-error coefficient factor through N1(a)N1(p).
--
-- This reduces the eventual radius condition from
--
--   C_det r^2 < 36 Delta_odd
--
-- to the mass-free comparison
--
--   P(q_a,q_p,c_a,c_p) r^2 < 36 (q_p-q_a),
--
-- once positivity permits cancellation of N1(a)N1(p).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
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

------------------------------------------------------------------------
-- Division-free normalized gate interface.
------------------------------------------------------------------------

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

    reading : Agda.Builtin.String.String

record NormalizedRadiusGateBoundary : Set where
  constructor normalizedRadiusGateBoundary
  field
    oddMarginMassFactorizationDerived : Bool
    oddMarginMassFactorizationDerivedIsTrue :
      oddMarginMassFactorizationDerived ≡ true
    errorCoefficientMassFactorizationDerived : Bool
    errorCoefficientMassFactorizationDerivedIsTrue :
      errorCoefficientMassFactorizationDerived ≡ true
    massFreeRadiusGateConstructed : Bool
    massFreeRadiusGateConstructedIsTrue : massFreeRadiusGateConstructed ≡ true
    positiveMassCancellationDerivedInAgda : Bool
    positiveMassCancellationDerivedInAgdaIsFalse :
      positiveMassCancellationDerivedInAgda ≡ false
    actualNormalizedRadiusGateInhabited : Bool
    actualNormalizedRadiusGateInhabitedIsFalse :
      actualNormalizedRadiusGateInhabited ≡ false

canonicalNormalizedRadiusGateBoundary : NormalizedRadiusGateBoundary
canonicalNormalizedRadiusGateBoundary =
  normalizedRadiusGateBoundary true refl true refl true refl false refl false refl
