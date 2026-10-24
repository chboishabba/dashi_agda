{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkDeSitterCoreLocalRegularityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction

------------------------------------------------------------------------
-- LOCAL REGULARITY OF THE DE-SITTER-LIKE CORE CARRIER
--
-- f_in(r)=1-Lambda r^2/3 is polynomial at r=0.  In particular the selected
-- interior fixture has finite unit lapse and zero first radial derivative at
-- the center.  This removes the Schwarzschild M/r singular term from the core
-- branch by construction.
--
-- This does not by itself prove bounded curvature invariants, geodesic
-- completeness, or a maximally extended regular black-hole spacetime.
------------------------------------------------------------------------

coreCenterRadius : ℚ
coreCenterRadius = 0ℚ

coreCenterLapse :
  Junction.fInterior coreCenterRadius Junction.lambdaIn ≡ 1ℚ
coreCenterLapse = solve []

coreCenterFirstDerivative :
  Junction.fInteriorPrime coreCenterRadius Junction.lambdaIn ≡ 0ℚ
coreCenterFirstDerivative = solve []

coreCenterHasNoExteriorMassOverRadiusTerm : Bool
coreCenterHasNoExteriorMassOverRadiusTerm = true

localCoreLapseRegularityOwned : Bool
localCoreLapseRegularityOwned = true

localCoreFirstDerivativeRegularityOwned : Bool
localCoreFirstDerivativeRegularityOwned = true

boundedCurvatureInvariantsDerived : Bool
boundedCurvatureInvariantsDerived = false

globalGeodesicCompletenessDerived : Bool
globalGeodesicCompletenessDerived = false

maximalHorizonExtensionDerived : Bool
maximalHorizonExtensionDerived = false
