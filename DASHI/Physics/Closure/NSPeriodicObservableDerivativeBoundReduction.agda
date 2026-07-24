module DASHI.Physics.Closure.NSPeriodicObservableDerivativeBoundReduction where

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicUniformChartScoreModulus as Score
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Uniform quotient-derivative bound.
--
-- For q = n/d the magnitude estimate has the standard form
--
--   |q'| <= (|n'| |d| + |n| |d'|) |d|^{-2}.
--
-- This module proves that uniform numerator, denominator, derivative and inverse
-- square bounds produce a cutoff-independent q' bound.  Applying it to Gamma,
-- normalized packet fraction and off-packet ratio leaves only literal energy and
-- triad derivative estimates, rather than four opaque score-modulus constants.
------------------------------------------------------------------------

record OrderedProductArithmetic
    (A : AbsorptionArithmetic) : Set₁ where
  field
    multiply : Scalar A → Scalar A → Scalar A

    orderReflexive : ∀ x → _≤_ A x x

    multiplyMonotone : ∀ {a b c d} →
      _≤_ A a b →
      _≤_ A c d →
      _≤_ A (multiply a c) (multiply b d)

open OrderedProductArithmetic public

additionMonotone :
  ∀ {A : AbsorptionArithmetic} {a b c d} →
  _≤_ A a b → _≤_ A c d →
  _≤_ A (_+_ A a c) (_+_ A b d)
additionMonotone {A = A} left right =
  ≤-trans A
    (additionMonotoneRight A left)
    (additionMonotoneLeft A right)

record QuotientDerivativeMagnitudeInputs
    (A : AbsorptionArithmetic)
    (P : OrderedProductArithmetic A) : Set₁ where
  field
    numeratorMagnitude denominatorMagnitude : Scalar A
    numeratorDerivativeMagnitude denominatorDerivativeMagnitude : Scalar A
    quotientDerivativeMagnitude : Scalar A

    numeratorBound denominatorBound : Scalar A
    numeratorDerivativeBound denominatorDerivativeBound : Scalar A
    inverseDenominatorSquareBound : Scalar A

    quotientDerivativeBelowFormula :
      _≤_ A quotientDerivativeMagnitude
        (multiply P
          (_+_ A
            (multiply P numeratorDerivativeMagnitude denominatorMagnitude)
            (multiply P numeratorMagnitude denominatorDerivativeMagnitude))
          inverseDenominatorSquareBound)

    numeratorUniform : _≤_ A numeratorMagnitude numeratorBound
    denominatorUniform : _≤_ A denominatorMagnitude denominatorBound
    numeratorDerivativeUniform :
      _≤_ A numeratorDerivativeMagnitude numeratorDerivativeBound
    denominatorDerivativeUniform :
      _≤_ A denominatorDerivativeMagnitude denominatorDerivativeBound

open QuotientDerivativeMagnitudeInputs public

quotientDerivativeUniformConstant :
  ∀ {A : AbsorptionArithmetic} {P : OrderedProductArithmetic A} →
  QuotientDerivativeMagnitudeInputs A P → Scalar A
quotientDerivativeUniformConstant {A = A} {P = P} Q =
  multiply P
    (_+_ A
      (multiply P
        (numeratorDerivativeBound Q)
        (denominatorBound Q))
      (multiply P
        (numeratorBound Q)
        (denominatorDerivativeBound Q)))
    (inverseDenominatorSquareBound Q)

quotientFormulaBelowUniformConstant :
  ∀ {A : AbsorptionArithmetic} {P : OrderedProductArithmetic A} →
  (Q : QuotientDerivativeMagnitudeInputs A P) →
  _≤_ A
    (multiply P
      (_+_ A
        (multiply P
          (numeratorDerivativeMagnitude Q)
          (denominatorMagnitude Q))
        (multiply P
          (numeratorMagnitude Q)
          (denominatorDerivativeMagnitude Q)))
      (inverseDenominatorSquareBound Q))
    (quotientDerivativeUniformConstant Q)
quotientFormulaBelowUniformConstant {A = A} {P = P} Q =
  multiplyMonotone P summedProducts
    (orderReflexive P (inverseDenominatorSquareBound Q))
  where
  firstProduct :
    _≤_ A
      (multiply P
        (numeratorDerivativeMagnitude Q)
        (denominatorMagnitude Q))
      (multiply P
        (numeratorDerivativeBound Q)
        (denominatorBound Q))
  firstProduct = multiplyMonotone P
    (numeratorDerivativeUniform Q)
    (denominatorUniform Q)

  secondProduct :
    _≤_ A
      (multiply P
        (numeratorMagnitude Q)
        (denominatorDerivativeMagnitude Q))
      (multiply P
        (numeratorBound Q)
        (denominatorDerivativeBound Q))
  secondProduct = multiplyMonotone P
    (numeratorUniform Q)
    (denominatorDerivativeUniform Q)

  summedProducts :
    _≤_ A
      (_+_ A
        (multiply P
          (numeratorDerivativeMagnitude Q)
          (denominatorMagnitude Q))
        (multiply P
          (numeratorMagnitude Q)
          (denominatorDerivativeMagnitude Q)))
      (_+_ A
        (multiply P
          (numeratorDerivativeBound Q)
          (denominatorBound Q))
        (multiply P
          (numeratorBound Q)
          (denominatorDerivativeBound Q)))
  summedProducts = additionMonotone firstProduct secondProduct

quotientDerivativeUniform :
  ∀ {A : AbsorptionArithmetic} {P : OrderedProductArithmetic A} →
  (Q : QuotientDerivativeMagnitudeInputs A P) →
  _≤_ A
    (quotientDerivativeMagnitude Q)
    (quotientDerivativeUniformConstant Q)
quotientDerivativeUniform {A = A} Q =
  ≤-trans A
    (quotientDerivativeBelowFormula Q)
    (quotientFormulaBelowUniformConstant Q)

------------------------------------------------------------------------
-- Three quotient observables plus the direct size derivative produce exactly
-- the four component inputs consumed by the chart-score modulus theorem.
------------------------------------------------------------------------

record PeriodicObservableDerivativeBoundInputs
    (A : AbsorptionArithmetic)
    (P : OrderedProductArithmetic A) : Set₁ where
  field
    gammaQuotient : QuotientDerivativeMagnitudeInputs A P
    packetFractionQuotient : QuotientDerivativeMagnitudeInputs A P
    offPacketQuotient : QuotientDerivativeMagnitudeInputs A P

    sizeDerivativeMagnitude sizeDerivativeBound : Scalar A
    sizeDerivativeUniform :
      _≤_ A sizeDerivativeMagnitude sizeDerivativeBound

    scoreDerivativeMagnitude : Scalar A
    scoreDerivativeBelowComponents :
      _≤_ A scoreDerivativeMagnitude
        (_+_ A
          (quotientDerivativeMagnitude gammaQuotient)
          (_+_ A
            (quotientDerivativeMagnitude packetFractionQuotient)
            (_+_ A
              (quotientDerivativeMagnitude offPacketQuotient)
              sizeDerivativeMagnitude)))

open PeriodicObservableDerivativeBoundInputs public

observableBoundsToScoreDerivativeInputs :
  ∀ {A : AbsorptionArithmetic} {P : OrderedProductArithmetic A} →
  PeriodicObservableDerivativeBoundInputs A P →
  Score.UniformScoreDerivativeInputs A
observableBoundsToScoreDerivativeInputs I = record
  { gammaDerivativeMagnitude =
      quotientDerivativeMagnitude (gammaQuotient I)
  ; packetDerivativeMagnitude =
      quotientDerivativeMagnitude (packetFractionQuotient I)
  ; ratioDerivativeMagnitude =
      quotientDerivativeMagnitude (offPacketQuotient I)
  ; sizeDerivativeMagnitude = sizeDerivativeMagnitude I
  ; gammaDerivativeBound =
      quotientDerivativeUniformConstant (gammaQuotient I)
  ; packetDerivativeBound =
      quotientDerivativeUniformConstant (packetFractionQuotient I)
  ; ratioDerivativeBound =
      quotientDerivativeUniformConstant (offPacketQuotient I)
  ; sizeDerivativeBound = sizeDerivativeBound I
  ; scoreDerivativeMagnitude = scoreDerivativeMagnitude I
  ; scoreDerivativeBelowComponents = scoreDerivativeBelowComponents I
  ; gammaDerivativeUniform = quotientDerivativeUniform (gammaQuotient I)
  ; packetDerivativeUniform =
      quotientDerivativeUniform (packetFractionQuotient I)
  ; ratioDerivativeUniform = quotientDerivativeUniform (offPacketQuotient I)
  ; sizeDerivativeUniform = sizeDerivativeUniform I
  }

periodicScoreDerivativeUniformBound :
  ∀ {A : AbsorptionArithmetic} {P : OrderedProductArithmetic A} →
  (I : PeriodicObservableDerivativeBoundInputs A P) →
  _≤_ A
    (scoreDerivativeMagnitude I)
    (Score.uniformScoreLipschitzConstant
      (observableBoundsToScoreDerivativeInputs I))
periodicScoreDerivativeUniformBound I =
  Score.uniformScoreDerivativeBound
    (observableBoundsToScoreDerivativeInputs I)

------------------------------------------------------------------------
-- Status: Gamma, packet-fraction and off-packet derivative constants are no
-- longer independent assumptions.  They are derived from uniform bounds on the
-- corresponding energies, energy derivatives and denominator floors.  The size
-- derivative remains a direct energy estimate.
------------------------------------------------------------------------

observableDerivativeBoundReductionLevel : ProofLevel
observableDerivativeBoundReductionLevel = machineChecked
