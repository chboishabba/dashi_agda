module DASHI.Empirical.DarkDimensionPredictionQuantityAdapterExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.GRQuantumObservableCalibration as Observable
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- DARK-DIMENSION PREDICTION-QUANTITY ADAPTER
--
-- The canonical SI carrier represents micrometres by a signed decimal scale.
-- GRQuantumPredictionProtocol.ScaledQuantity instead carries a natural-valued
-- decimalExponent whose sign semantics are not independently specified.
--
-- For this Dark-Dimension seam we do not guess that convention.  A positive
-- micrometre magnitude n is embedded exactly as the rational metre quantity
--
--                       n / 1,000,000 metre
--
-- with decimalExponent = 0.  This is enough to carry the source-supported
-- 1-30 micrometre interval into the prediction surface without inventing a
-- general SI <-> prediction conversion law.
------------------------------------------------------------------------

predictionMetreUnit : Observable.PhysicalUnit
predictionMetreUnit =
  Observable.physical-unit
    "metre"
    "m"
    Observable.lengthDimension
    1
    (Observable.positive 0)
    "SI metre; scale numerator/denominator = 1/1"
    "DASHI.Physics.Units.SI / BIPM SI"

millionPositive : Observable.PositiveNat
millionPositive = Observable.positive 999999

micrometreMagnitudeToPredictionQuantity : Nat → Prediction.ScaledQuantity
micrometreMagnitudeToPredictionQuantity n =
  Prediction.scaled-quantity
    n
    millionPositive
    zero
    predictionMetreUnit

oneMicrometreAsPredictionQuantity : Prediction.ScaledQuantity
oneMicrometreAsPredictionQuantity =
  micrometreMagnitudeToPredictionQuantity 1

thirtyMicrometresAsPredictionQuantity : Prediction.ScaledQuantity
thirtyMicrometresAsPredictionQuantity =
  micrometreMagnitudeToPredictionQuantity 30

------------------------------------------------------------------------
-- Exact bridge receipts retain both carriers.
------------------------------------------------------------------------

record ExactMicrometrePredictionBridge (n : Nat) : Set where
  constructor exactMicrometrePredictionBridge
  field
    sourceSI : SI.Quantity SI.Length SI.microScale
    sourceMagnitude : SI.Quantity.magnitude sourceSI ≡ n
    targetPrediction : Prediction.ScaledQuantity
    targetIsExactRationalMetres :
      targetPrediction ≡ micrometreMagnitudeToPredictionQuantity n

open ExactMicrometrePredictionBridge public

microRadiusLowerBridge : ExactMicrometrePredictionBridge 1
microRadiusLowerBridge =
  exactMicrometrePredictionBridge
    (SI.posQ 1)
    refl
    oneMicrometreAsPredictionQuantity
    refl

microRadiusUpperBridge : ExactMicrometrePredictionBridge 30
microRadiusUpperBridge =
  exactMicrometrePredictionBridge
    (SI.posQ 30)
    refl
    thirtyMicrometresAsPredictionQuantity
    refl

------------------------------------------------------------------------
-- Boundary: this exact local encoding avoids the unresolved exponent-sign
-- convention; it does not define a total SI conversion API or lock a forecast.
------------------------------------------------------------------------

data ExponentSignGuessRequired : Set where

data QuantityBridgeLocksModelSeparation : Set where

exactRationalMetreEncodingAvoidsExponentSignAmbiguity :
  ExponentSignGuessRequired → ⊥
exactRationalMetreEncodingAvoidsExponentSignAmbiguity ()

quantityBridgeDoesNotLockModelSeparation :
  QuantityBridgeLocksModelSeparation → ⊥
quantityBridgeDoesNotLockModelSeparation ()

predictionStillNotDerived :
  Prediction.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
predictionStillNotDerived =
  Prediction.quantitativePredictionDerivedIsFalse
    Prediction.canonicalPredictionBoundary
