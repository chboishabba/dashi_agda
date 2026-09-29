{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityTraceEnergyThresholdExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- SHARP TRACE / ENERGY THRESHOLD FOR NEGATIVE ACTIVE STRESS
--
-- Let
--
--   Theta = -rho + p_x + p_y + p_z
--   A     =  rho + p_x + p_y + p_z.
--
-- Then A = Theta + 2 rho.  Therefore the anomaly route has one exact scalar
-- decision boundary:
--
--   A < 0    iff    2 rho < -Theta.
--
-- The forward/reverse implications below are stated division-free, so no sign
-- assumption on rho or Theta is needed.
------------------------------------------------------------------------

tracePlusTwiceEnergy :
  ℚ → ℚ → ℚ
tracePlusTwiceEnergy trace energy =
  trace + ((1ℚ + 1ℚ) * energy)

negativeActiveFromEnergyBelowTraceMagnitude :
  ∀ trace energy →
  ((1ℚ + 1ℚ) * energy) < - trace →
  tracePlusTwiceEnergy trace energy < 0ℚ
negativeActiveFromEnergyBelowTraceMagnitude trace energy h =
  let
    shifted :
      trace + ((1ℚ + 1ℚ) * energy)
      < trace + (- trace)
    shifted =
      ℚP.+-monoˡ-< trace h

    cancel :
      trace + (- trace) ≡ 0ℚ
    cancel = ℚRing.solve-∀ trace
  in
  subst
    (λ value → tracePlusTwiceEnergy trace energy < value)
    cancel
    shifted

energyAtLeastTraceMagnitudeBlocksNegativeActive :
  ∀ trace energy →
  (- trace) ≤ ((1ℚ + 1ℚ) * energy) →
  0ℚ ≤ tracePlusTwiceEnergy trace energy
energyAtLeastTraceMagnitudeBlocksNegativeActive trace energy h =
  let
    shifted :
      trace + (- trace)
      ≤ trace + ((1ℚ + 1ℚ) * energy)
    shifted =
      ℚP.+-monoˡ-≤ trace h

    cancel :
      trace + (- trace) ≡ 0ℚ
    cancel = ℚRing.solve-∀ trace
  in
  subst
    (λ value → value ≤ tracePlusTwiceEnergy trace energy)
    cancel
    shifted

record TraceAnomalyRepulsionThreshold : Set where
  field
    trace energyDensity : ℚ

    traceNegative :
      trace < 0ℚ

    twiceEnergyBelowTraceMagnitude :
      ((1ℚ + 1ℚ) * energyDensity) < - trace

open TraceAnomalyRepulsionThreshold public

thresholdClosesNegativeActiveStress :
  (input : TraceAnomalyRepulsionThreshold) →
  tracePlusTwiceEnergy
    (trace input)
    (energyDensity input)
  < 0ℚ
thresholdClosesNegativeActiveStress input =
  negativeActiveFromEnergyBelowTraceMagnitude
    (trace input)
    (energyDensity input)
    (twiceEnergyBelowTraceMagnitude input)

record TraceAnomalyRepulsionNoGoThreshold : Set where
  field
    trace energyDensity : ℚ

    twiceEnergyAtLeastTraceMagnitude :
      (- trace) ≤ ((1ℚ + 1ℚ) * energyDensity)

open TraceAnomalyRepulsionNoGoThreshold public

thresholdBlocksNegativeActiveStress :
  (input : TraceAnomalyRepulsionNoGoThreshold) →
  0ℚ ≤
  tracePlusTwiceEnergy
    (TraceAnomalyRepulsionNoGoThreshold.trace input)
    (TraceAnomalyRepulsionNoGoThreshold.energyDensity input)
thresholdBlocksNegativeActiveStress input =
  energyAtLeastTraceMagnitudeBlocksNegativeActive
    (TraceAnomalyRepulsionNoGoThreshold.trace input)
    (TraceAnomalyRepulsionNoGoThreshold.energyDensity input)
    (twiceEnergyAtLeastTraceMagnitude input)
