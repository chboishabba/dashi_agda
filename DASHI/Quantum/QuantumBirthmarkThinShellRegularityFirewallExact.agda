{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkThinShellRegularityFirewallExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Quantum.QuantumBirthmarkDeSitterCoreCurvatureExact as Core
import DASHI.Quantum.QuantumBirthmarkKottlerHorizonLeanBoundaryExact as Horizons
import DASHI.Physics.Foundations.GRQFTNambuGotoSurfaceActionExact as Surface

------------------------------------------------------------------------
-- REGULARITY FIREWALL
--
-- The exact current repulsive-bubble construction is an Israel/Nambu-Goto thin
-- shell.  Finite smooth-region curvature invariants plus horizon existence do
-- not make the whole joined metric C^2 across the shell: the shell is precisely
-- a distributional surface stress source.  Therefore "regular black hole" must
-- specify whether distributional thin-shell regularity is accepted, or replace
-- the shell by a finite-thickness smooth wall and prove global regularity there.
------------------------------------------------------------------------

interiorCurvatureInvariantsFinite : Bool
interiorCurvatureInvariantsFinite = Core.boundedCoreCurvatureInvariantsOwned

positiveHorizonExistenceSourceWritten : Bool
positiveHorizonExistenceSourceWritten =
  Horizons.innerPositiveHorizonExistenceSourceWritten

israelShellCarriesDistributionalStress : Bool
israelShellCarriesDistributionalStress = true

thinShellIsNotSmoothFiniteThicknessWall : Bool
thinShellIsNotSmoothFiniteThicknessWall = true

nambuGotoSurfaceSourceOwned : Bool
nambuGotoSurfaceSourceOwned = true

globalSmoothRegularBlackHoleNotPromoted : Bool
globalSmoothRegularBlackHoleNotPromoted = true

finiteThicknessOrDistributionalRegularityTheoremRequired : Bool
finiteThicknessOrDistributionalRegularityTheoremRequired = true

maximalExtensionStillRequired : Bool
maximalExtensionStillRequired = true

regularityReading : String
regularityReading =
  "The de-Sitter core is locally finite-curvature and the selected Kottler horizons exist, but the exact junction is a thin distributional surface. A globally smooth regular-black-hole claim therefore requires a finite-thickness wall plus smooth maximal extension/geodesic completeness, or an explicitly distributional notion of regularity with its own theorem."
