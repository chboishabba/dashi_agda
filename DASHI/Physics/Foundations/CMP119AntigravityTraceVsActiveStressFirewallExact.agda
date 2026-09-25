{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityTraceVsActiveStressFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _<_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- TRACE != ACTIVE STRESS
--
-- In a local Lorentzian orthonormal rest frame:
--
--   trace(T)  = -rho + px + py + pz
--   active(T) =  rho + px + py + pz
--
-- hence
--
--   active(T) = trace(T) + 2 rho.
--
-- The Euclidean four-diagonal sum selected by the existing CMP119 trace lane
-- analytically continues to the Lorentzian trace contraction.  It is not, by
-- itself, the Raychaudhuri/static active-stress combination.
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
  lorentzianTrace rho px py pz + (2ℚ * rho)
activeStressIsTracePlusTwiceEnergyDensity rho px py pz =
  ℚRing.solve-∀ rho px py pz

------------------------------------------------------------------------
-- Exact counterexample carried by the explicit finite-thickness geometry.
--
-- rho = 1, pr = 0, pt = -33/380:
--
--   trace  = -223/190 < 0
--   active =  157/190 > 0.
------------------------------------------------------------------------

counterexampleRho : ℚ
counterexampleRho = 1ℚ

counterexamplePR : ℚ
counterexamplePR = 0ℚ

counterexamplePT : ℚ
counterexamplePT = - (33 ℚ./ 380)

counterexampleTrace :
  lorentzianTrace
    counterexampleRho
    counterexamplePR
    counterexamplePT
    counterexamplePT
  ≡ - (223 ℚ./ 190)
counterexampleTrace = refl

counterexampleTraceNegative :
  lorentzianTrace
    counterexampleRho
    counterexamplePR
    counterexamplePT
    counterexamplePT
  < 0ℚ
counterexampleTraceNegative = by
  norm_num

counterexampleActive :
  lorentzianActiveStress
    counterexampleRho
    counterexamplePR
    counterexamplePT
    counterexamplePT
  ≡ (157 ℚ./ 190)
counterexampleActive = refl

counterexampleActivePositive :
  0ℚ
  <
  lorentzianActiveStress
    counterexampleRho
    counterexamplePR
    counterexamplePT
    counterexamplePT
counterexampleActivePositive = by
  norm_num

negativeTraceImpliesNegativeActiveStress : Bool
negativeTraceImpliesNegativeActiveStress = false

negativeTraceImpliesNegativeActiveStressIsFalse :
  negativeTraceImpliesNegativeActiveStress ≡ false
negativeTraceImpliesNegativeActiveStressIsFalse = refl

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
