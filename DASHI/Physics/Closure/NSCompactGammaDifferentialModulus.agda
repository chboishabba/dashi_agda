module DASHI.Physics.Closure.NSCompactGammaDifferentialModulus where

open import Agda.Primitive using (Set₁)

------------------------------------------------------------------------
-- Division-free differential-modulus reduction.
--
-- For Gamma = Q / S on the strict positive-transfer branch, the analytic
-- quotient rule can be written without division as
--
--   |D Gamma[h]| S² <= |DQ[h]| S + Q |DS[h]|.
--
-- If the numerator variation is bounded by
--
--   L_Gamma ||h|| S²,
--
-- positivity of S² allows cancellation and yields
--
--   |D Gamma[h]| <= L_Gamma ||h||.
--
-- Likewise, for positive escape E,
--
--   |D log E[h]| E <= |DE[h]|
--
-- and a bound |DE[h]| <= L_logE ||h|| E yields the desired logarithmic
-- modulus.  This module proves those two reductions abstractly.  It does not
-- construct the PDE estimates, prove denominator positivity, or supply
-- cutoff-uniform constants.
------------------------------------------------------------------------

record DifferentialArithmetic : Set₁ where
  field
    Scalar : Set
    _≤_ : Scalar → Scalar → Set
    _*_ : Scalar → Scalar → Scalar
    Positive : Scalar → Set

    ≤-trans :
      {a b c : Scalar} → _≤_ a b → _≤_ b c → _≤_ a c

    multiplyMonotoneRight :
      {a b c : Scalar} →
      _≤_ a b →
      _≤_ (_*_ a c) (_*_ b c)

    cancelPositiveRight :
      {a b c : Scalar} →
      Positive c →
      _≤_ (_*_ a c) (_*_ b c) →
      _≤_ a b

open DifferentialArithmetic public

record ScaledDifferentialModulusInputs
    (A : DifferentialArithmetic) : Set₁ where
  field
    absoluteDerivative : Scalar A
    modulusConstant : Scalar A
    tangentNorm : Scalar A
    positiveScale : Scalar A
    numeratorVariation : Scalar A

    scalePositive : Positive A positiveScale

    scaledDerivativeControlled :
      _≤_ A
        (_*_ A absoluteDerivative positiveScale)
        numeratorVariation

    numeratorVariationControlled :
      _≤_ A
        numeratorVariation
        (_*_ A
          (_*_ A modulusConstant tangentNorm)
          positiveScale)

open ScaledDifferentialModulusInputs public

scaledDifferentialModulus :
  (A : DifferentialArithmetic) →
  (I : ScaledDifferentialModulusInputs A) →
  _≤_ A
    (absoluteDerivative I)
    (_*_ A (modulusConstant I) (tangentNorm I))
scaledDifferentialModulus A I =
  cancelPositiveRight A
    (scalePositive I)
    (≤-trans A
      (scaledDerivativeControlled I)
      (numeratorVariationControlled I))

------------------------------------------------------------------------
-- Compact-Gamma and logarithmic-escape pair.
------------------------------------------------------------------------

record CompactGammaDifferentialInputs
    (A : DifferentialArithmetic) : Set₁ where
  field
    gammaInputs : ScaledDifferentialModulusInputs A
    logEscapeInputs : ScaledDifferentialModulusInputs A

open CompactGammaDifferentialInputs public

gammaDifferentialModulus :
  (A : DifferentialArithmetic) →
  (I : CompactGammaDifferentialInputs A) →
  _≤_ A
    (absoluteDerivative (gammaInputs I))
    (_*_ A
      (modulusConstant (gammaInputs I))
      (tangentNorm (gammaInputs I)))
gammaDifferentialModulus A I =
  scaledDifferentialModulus A (gammaInputs I)

logEscapeDifferentialModulus :
  (A : DifferentialArithmetic) →
  (I : CompactGammaDifferentialInputs A) →
  _≤_ A
    (absoluteDerivative (logEscapeInputs I))
    (_*_ A
      (modulusConstant (logEscapeInputs I))
      (tangentNorm (logEscapeInputs I)))
logEscapeDifferentialModulus A I =
  scaledDifferentialModulus A (logEscapeInputs I)
