{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkH2EquationOfStateUnderdeterminationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; -_)

import DASHI.Quantum.QuantumBirthmarkHistoryHorizonScalingExact as Scaling

------------------------------------------------------------------------
-- H^2 TRACKING DOES NOT BY ITSELF DETERMINE w(a)
--
-- If H^2 is constant, rho_H proportional H^2 is constant and the standard
-- continuity scaling gives n=0 -> w=-1.  If instead H^2 scales as a^-1, the
-- same rho_H proportional H^2 carrier has n=1 -> w=-2/3.  Therefore the H^2
-- relation alone does not choose a CPL/equation-of-state history.
------------------------------------------------------------------------

constantH2ScalingExponent : ℚ
constantH2ScalingExponent = 0ℚ

unitScalingH2Exponent : ℚ
unitScalingH2Exponent = 1ℚ

constantH2GivesVacuumW :
  Scaling.wFromScalingExponent constantH2ScalingExponent
  ≡ - 1ℚ
constantH2GivesVacuumW = Scaling.constantDensityGivesVacuumW

unitScalingH2GivesMinusTwoThirds :
  Scaling.wFromScalingExponent unitScalingH2Exponent
  ≡ - (Int.+ 2 / 3)
unitScalingH2GivesMinusTwoThirds = Scaling.unitExponentGivesMinusTwoThirds

hubbleSquaredTrackingDoesNotFixEquationOfState : Bool
hubbleSquaredTrackingDoesNotFixEquationOfState = true

cplParametersFollowFromH2AlgebraAlone : Bool
cplParametersFollowFromH2AlgebraAlone = false

microscopicExpansionHistoryStillRequired : Bool
microscopicExpansionHistoryStillRequired = true
