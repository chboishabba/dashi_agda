{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityTraceVsActiveStressFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _<_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

------------------------------------------------------------------------
-- TRACE != ACTIVE STRESS
--
-- In a local Lorentzian orthonormal rest frame:
--
--   trace(T)  = -rho + px + py + pz
--   active(T) =  rho + px + py + pz
--
-- Hence:
--
--   active(T) = trace(T) + 2 rho.
--
-- The four-diagonal Euclidean trace sum in the CMP119 anomaly lane therefore
-- does not, by itself, establish the Lorentzian Raychaudhuri/static active
-- contraction.  The missing physics is control of the timelike energy-density
-- contribution on the SAME stress tensor.
------------------------------------------------------------------------

lorentzianTrace :
  ℚ → ℚ → ℚ → ℚ → ℚ
lorentzianTrace rho px py pz =
  - rho + px + py + pz

lorentzianActiveStress :
  ℚ → ℚ → ℚ → ℚ → ℚ
lorentzianActiveStress rho px py pz =
  rho + px + py + pz

activeStressIsTracePlusTwiceEnergyDensity :
  ∀ rho px py pz →
  lorentzianActiveStress rho px py pz
  ≡
  lorentzianTrace rho px py pz + ((1 ℚ.+ 1) * rho)
activeStressIsTracePlusTwiceEnergyDensity rho px py pz =
  ℚRing.solve-∀ rho px py pz

record TraceToActiveStressClosure : Set where
  field
    rho px py pz : ℚ

    traceNegative :
      lorentzianTrace rho px py pz < 0ℚ

    -- This is the actual additional inequality required after the anomaly:
    -- trace(T) + 2 rho < 0.
    tracePlusTwiceEnergyDensityNegative :
      lorentzianTrace rho px py pz + ((1 ℚ.+ 1) * rho) < 0ℚ

open TraceToActiveStressClosure public

tracePlusEnergyControlClosesNegativeActiveStress :
  (input : TraceToActiveStressClosure) →
  lorentzianActiveStress
    (rho input) (px input) (py input) (pz input)
  < 0ℚ
tracePlusEnergyControlClosesNegativeActiveStress input
  rewrite activeStressIsTracePlusTwiceEnergyDensity
    (rho input) (px input) (py input) (pz input) =
  tracePlusTwiceEnergyDensityNegative input

negativeTraceAloneClosesNegativeActiveStress : Bool
negativeTraceAloneClosesNegativeActiveStress = false

negativeTraceAloneClosesNegativeActiveStressIsFalse :
  negativeTraceAloneClosesNegativeActiveStress ≡ false
negativeTraceAloneClosesNegativeActiveStressIsFalse = refl

traceAnomalyAloneClosesRepulsionSource : Bool
traceAnomalyAloneClosesRepulsionSource = false

traceAnomalyAloneClosesRepulsionSourceIsFalse :
  traceAnomalyAloneClosesRepulsionSource ≡ false
traceAnomalyAloneClosesRepulsionSourceIsFalse = refl

timelikeEnergyDensityControlStillRequired : Bool
timelikeEnergyDensityControlStillRequired = true

timelikeEnergyDensityControlStillRequiredIsTrue :
  timelikeEnergyDensityControlStillRequired ≡ true
timelikeEnergyDensityControlStillRequiredIsTrue = refl
