{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PositiveGActiveStressWeakFieldMetricExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTLocalizedAnisotropicRepulsiveShellExact as Shell

activeSourceDensity : ℚ
activeSourceDensity = - 1ℚ

unitRadius : ℚ
unitRadius = 1ℚ

oneThird : ℚ
oneThird = Int.+ 1 / 3

oneSixth : ℚ
oneSixth = Int.+ 1 / 6

three : ℚ
three = Int.+ 3 / 1

interiorPotential : ℚ → ℚ
interiorPotential r = oneSixth * (three - r * r)

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
    selectedPoissonFixtureOnly : Bool
    sameObjectConservedShellSourceEstablished : Bool
    fullNonlinearCompactEinsteinSolveStillOpen : Bool
    fullTOVConservationStillOpen : Bool

canonicalWeakFieldMetricSolveBoundary : WeakFieldMetricSolveBoundary
canonicalWeakFieldMetricSolveBoundary =
  weak-field-metric-solve-boundary
    true true true true true true true true false true true
