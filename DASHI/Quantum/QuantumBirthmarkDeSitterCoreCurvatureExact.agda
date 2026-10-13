{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkDeSitterCoreCurvatureExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([])
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction

------------------------------------------------------------------------
-- CONSTANT-CURVATURE DE-SITTER CORE INVARIANTS
--
-- Standard 4D de-Sitter identities:
--   R                  = 4 Lambda
--   R_ab R^ab          = 4 Lambda^2
--   R_abcd R^abcd      = (8/3) Lambda^2
--
-- The repo's selected interior has Lambda_in = 3/8.  This module evaluates
-- those standard constant-curvature formulas exactly on that SAME fixture.
-- It does not construct the Riemann tensor internally from the metric.
------------------------------------------------------------------------

coreRicciScalar : ℚ
coreRicciScalar = (Int.+ 4 / 1) * Junction.lambdaIn

coreRicciSquare : ℚ
coreRicciSquare =
  (Int.+ 4 / 1) * Junction.lambdaIn * Junction.lambdaIn

coreKretschmann : ℚ
coreKretschmann =
  (Int.+ 8 / 3) * Junction.lambdaIn * Junction.lambdaIn

coreRicciScalarIsThreeHalves :
  coreRicciScalar ≡ Int.+ 3 / 2
coreRicciScalarIsThreeHalves = solve []

coreRicciSquareIsNineSixteenths :
  coreRicciSquare ≡ Int.+ 9 / 16
coreRicciSquareIsNineSixteenths = solve []

coreKretschmannIsThreeEighths :
  coreKretschmann ≡ Int.+ 3 / 8
coreKretschmannIsThreeEighths = solve []

constantCurvatureInvariantFormulaImported : Bool
constantCurvatureInvariantFormulaImported = true

selectedCoreInvariantValuesFinite : Bool
selectedCoreInvariantValuesFinite = true

boundedCoreCurvatureInvariantsOwned : Bool
boundedCoreCurvatureInvariantsOwned = true

riemannTensorDerivedFromMetricInsideThisModule : Bool
riemannTensorDerivedFromMetricInsideThisModule = false

globalGeodesicCompletenessDerived : Bool
globalGeodesicCompletenessDerived = false

maximalHorizonExtensionDerived : Bool
maximalHorizonExtensionDerived = false
