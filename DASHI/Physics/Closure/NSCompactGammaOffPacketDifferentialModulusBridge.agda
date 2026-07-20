module DASHI.Physics.Closure.NSCompactGammaOffPacketDifferentialModulusBridge where

open import Agda.Primitive using (Set₁)

import DASHI.Physics.Closure.NSCompactGammaDifferentialModulus as Differential
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaOffPacketSchurSplit

------------------------------------------------------------------------
-- Direct consumer for the already-landed division-free D log E theorem.
--
-- `OffPacketLogNumeratorInputs` proves that the complete logarithmic numerator
-- is below a declared total budget.  This module equips the same scalar/order
-- carrier with multiplication and positive cancellation, factors that total
-- budget as
--
--   (L_logE * ||h||) * E,
--
-- and constructs `ScaledDifferentialModulusInputs` without another opaque
-- theorem socket.  Once near majorization, Schur control, and tail absorption
-- provide the total budget, the final D log E step is therefore composition.
------------------------------------------------------------------------

record DifferentialAbsorptionArithmetic : Set₁ where
  field
    absorption : AbsorptionArithmetic

    multiply :
      Scalar absorption → Scalar absorption → Scalar absorption

    Positive : Scalar absorption → Set

    multiplyMonotoneRight :
      {a b c : Scalar absorption} →
      _≤_ absorption a b →
      _≤_ absorption
        (multiply a c)
        (multiply b c)

    cancelPositiveRight :
      {a b c : Scalar absorption} →
      Positive c →
      _≤_ absorption
        (multiply a c)
        (multiply b c) →
      _≤_ absorption a b

open DifferentialAbsorptionArithmetic public

asDifferentialArithmetic :
  DifferentialAbsorptionArithmetic →
  Differential.DifferentialArithmetic
asDifferentialArithmetic C = record
  { Scalar = Scalar (absorption C)
  ; _≤_ = _≤_ (absorption C)
  ; _*_ = multiply C
  ; Positive = Positive C
  ; ≤-trans = ≤-trans (absorption C)
  ; multiplyMonotoneRight = multiplyMonotoneRight C
  ; cancelPositiveRight = cancelPositiveRight C
  }

record OffPacketLogDifferentialInputs
    (C : DifferentialAbsorptionArithmetic) : Set₁ where
  field
    numeratorInputs :
      OffPacketLogNumeratorInputs (absorption C)

    absoluteLogDerivative : Scalar (absorption C)
    modulusConstant : Scalar (absorption C)
    tangentNorm : Scalar (absorption C)
    positiveEscape : Scalar (absorption C)

    escapePositive : Positive C positiveEscape

    scaledDerivativeBelowNumerator :
      _≤_ (absorption C)
        (multiply C absoluteLogDerivative positiveEscape)
        (logarithmicNumerator numeratorInputs)

    totalBudgetBelowModulusScale :
      _≤_ (absorption C)
        (totalNumeratorBudget numeratorInputs)
        (multiply C
          (multiply C modulusConstant tangentNorm)
          positiveEscape)

open OffPacketLogDifferentialInputs public

logNumeratorBelowModulusScale :
  (C : DifferentialAbsorptionArithmetic) →
  (I : OffPacketLogDifferentialInputs C) →
  _≤_ (absorption C)
    (logarithmicNumerator (numeratorInputs I))
    (multiply C
      (multiply C (modulusConstant I) (tangentNorm I))
      (positiveEscape I))
logNumeratorBelowModulusScale C I =
  ≤-trans (absorption C)
    (offPacketSchurSplitBoundsLogNumerator
      (absorption C)
      (numeratorInputs I))
    (totalBudgetBelowModulusScale I)

asLogScaledDifferentialInputs :
  (C : DifferentialAbsorptionArithmetic) →
  OffPacketLogDifferentialInputs C →
  Differential.ScaledDifferentialModulusInputs
    (asDifferentialArithmetic C)
asLogScaledDifferentialInputs C I = record
  { absoluteDerivative = absoluteLogDerivative I
  ; modulusConstant = modulusConstant I
  ; tangentNorm = tangentNorm I
  ; positiveScale = positiveEscape I
  ; numeratorVariation =
      logarithmicNumerator (numeratorInputs I)
  ; scalePositive = escapePositive I
  ; scaledDerivativeControlled =
      scaledDerivativeBelowNumerator I
  ; numeratorVariationControlled =
      logNumeratorBelowModulusScale C I
  }

offPacketLogDifferentialModulus :
  (C : DifferentialAbsorptionArithmetic) →
  (I : OffPacketLogDifferentialInputs C) →
  _≤_ (absorption C)
    (absoluteLogDerivative I)
    (multiply C (modulusConstant I) (tangentNorm I))
offPacketLogDifferentialModulus C I =
  Differential.scaledDifferentialModulus
    (asDifferentialArithmetic C)
    (asLogScaledDifferentialInputs C I)

------------------------------------------------------------------------
-- Pair with an independently supplied compact-Gamma quotient input.  This is
-- the exact consumer expected by `CompactGammaDifferentialInputs`.
------------------------------------------------------------------------

record OffPacketCompactGammaDifferentialInputs
    (C : DifferentialAbsorptionArithmetic) : Set₁ where
  field
    gammaScaledInputs :
      Differential.ScaledDifferentialModulusInputs
        (asDifferentialArithmetic C)

    offPacketLogInputs : OffPacketLogDifferentialInputs C

open OffPacketCompactGammaDifferentialInputs public

toCompactGammaDifferentialInputs :
  (C : DifferentialAbsorptionArithmetic) →
  OffPacketCompactGammaDifferentialInputs C →
  Differential.CompactGammaDifferentialInputs
    (asDifferentialArithmetic C)
toCompactGammaDifferentialInputs C I = record
  { gammaInputs = gammaScaledInputs I
  ; logEscapeInputs =
      asLogScaledDifferentialInputs C (offPacketLogInputs I)
  }
