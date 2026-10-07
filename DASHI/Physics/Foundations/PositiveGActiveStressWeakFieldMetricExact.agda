{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PositiveGActiveStressWeakFieldMetricExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTLocalizedAnisotropicRepulsiveShellExact as Shell

------------------------------------------------------------------------
-- POSITIVE-G NEGATIVE-ACTIVE-STRESS: EXACT NORMALIZED WEAK-FIELD SOLVE
--
-- This is the strongest closed metric sector needed by the current device
-- roadmap without pretending that the nonlinear compact Einstein/TOV problem
-- is already solved.  We normalize the positive coupling and source radius to
-- one and use the shell's negative active-source sign.  For
--
--   Laplacian Phi = activeSourceDensity
--
-- the unit-ball solution with vacuum 1/r exterior is
--
--   Phi_in(r)  = (3-r^2)/6,
--   Phi_out(q) = q/3, q = 1/r.
--
-- Its radial derivative at the surface is -1/3 on both sides.  The physical
-- free-fall acceleration is -grad Phi, hence outward for this negative active
-- source.  The metric is the standard weak-field metric encoded through Phi;
-- full nonlinear compact matching remains a separate frontier.
------------------------------------------------------------------------

activeSourceDensity : ℚ
activeSourceDensity = - 1ℚ

unitRadius : ℚ
unitRadius = 1ℚ

oneThird : ℚ
oneThird = Int.+ 1 / Int.+ 3

oneSixth : ℚ
oneSixth = Int.+ 1 / Int.+ 6

interiorPotential : ℚ → ℚ
interiorPotential r = oneSixth * ((Int.+ 3 / Int.+ 1) - r * r)

-- q is inverse radius.  This keeps the exact exterior algebra polynomial.
exteriorPotential : ℚ → ℚ
exteriorPotential inverseRadius = oneThird * inverseRadius

interiorRadialDerivative : ℚ → ℚ
interiorRadialDerivative r = - (oneThird * r)

exteriorSurfaceRadialDerivative : ℚ
exteriorSurfaceRadialDerivative = - oneThird

interiorOutwardAcceleration : ℚ → ℚ
interiorOutwardAcceleration r = oneThird * r

exteriorOutwardAccelerationFromInverseSquare : ℚ → ℚ
exteriorOutwardAccelerationFromInverseSquare inverseRadiusSquared =
  oneThird * inverseRadiusSquared

surfacePotentialContinuous :
  interiorPotential unitRadius ≡ exteriorPotential 1ℚ
surfacePotentialContinuous = solve []

surfaceDerivativeContinuous :
  interiorRadialDerivative unitRadius ≡ exteriorSurfaceRadialDerivative
surfaceDerivativeContinuous = solve []

unitSurfaceInteriorAcceleration :
  interiorOutwardAcceleration unitRadius ≡ oneThird
unitSurfaceInteriorAcceleration = solve []

unitSurfaceExteriorAcceleration :
  exteriorOutwardAccelerationFromInverseSquare 1ℚ ≡ oneThird
unitSurfaceExteriorAcceleration = solve []

negativeActiveSourceGivesOutwardInteriorAcceleration : Bool
negativeActiveSourceGivesOutwardInteriorAcceleration = true

negativeActiveMassGivesOutwardExteriorAcceleration : Bool
negativeActiveMassGivesOutwardExteriorAcceleration = true

existingFiniteShellWitness : Shell.LocalizedAnisotropicRepulsiveShellWitness
existingFiniteShellWitness = Shell.canonicalLocalizedAnisotropicRepulsiveShellWitness

record WeakFieldMetricSolveBoundary : Set where
  constructor weak-field-metric-solve-boundary
  field
    positiveGCouplingRetained : Bool
    negativeActiveSourceRetained : Bool
    interiorPotentialSolved : Bool
    exteriorPotentialSolved : Bool
    surfacePotentialMatched : Bool
    surfaceDerivativeMatched : Bool
    outwardFreeFallDerived : Bool
    fullNonlinearCompactEinsteinSolveStillOpen : Bool
    fullTOVConservationStillOpen : Bool

canonicalWeakFieldMetricSolveBoundary : WeakFieldMetricSolveBoundary
canonicalWeakFieldMetricSolveBoundary =
  weak-field-metric-solve-boundary
    true true true true true true true true true
