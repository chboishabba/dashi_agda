{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PositiveGLocalRepulsiveInteriorFamilyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve; solve-∀)

import DASHI.Physics.Foundations.PositiveGConservedAnisotropicProfileCompilerExact as Conservation
import DASHI.Physics.Foundations.PositiveGSphericalInteriorRepulsionBoundaryExact as Boundary

------------------------------------------------------------------------
-- EXACT LOCAL REPULSIVE INTERIOR FAMILY
--
-- Choose, on the normalized unit ball,
--
--   m(r)   = a r^3,
--   nu'(r) = -b r,
--
-- with selected positive a=b=1/4.  Then the selected fixture stays on the
-- outside-horizon branch on the unit interval, while -nu' points outward.
-- Einstein's radial equation determines the pressure contribution:
--
--   m + P_r = nu' r (r - 2m)
--
-- and conservation determines p_t from rho,p_r,p_r',nu'.  At r=1 the radial
-- pressure contribution is -3/8, so this local outward interior cannot be
-- smoothly matched directly to a zero-pressure positive-mass vacuum boundary.
------------------------------------------------------------------------

oneQuarter : ℚ
oneQuarter = Int.+ 1 / 4

threeEighths : ℚ
threeEighths = Int.+ 3 / 8

massFunction : ℚ → ℚ
massFunction r = oneQuarter * r * r * r

nuPrime : ℚ → ℚ
nuPrime r = - (oneQuarter * r)

outwardStaticAcceleration : ℚ → ℚ
outwardStaticAcceleration r = oneQuarter * r

radialPressureContribution : ℚ → ℚ
radialPressureContribution r =
  - (r * r * r
     * (oneQuarter + oneQuarter * (1ℚ - (oneQuarter + oneQuarter) * r * r)))

radialEinsteinEquationPaid :
  ∀ r →
  Boundary.radialEinsteinNumerator
    (massFunction r)
    (radialPressureContribution r)
  ≡ nuPrime r * r * (r - (massFunction r + massFunction r))
radialEinsteinEquationPaid = solve-∀

unitBoundaryMass : massFunction 1ℚ ≡ oneQuarter
unitBoundaryMass = solve []

unitBoundaryNuPrime : nuPrime 1ℚ ≡ - oneQuarter
unitBoundaryNuPrime = solve []

unitBoundaryOutwardAcceleration : outwardStaticAcceleration 1ℚ ≡ oneQuarter
unitBoundaryOutwardAcceleration = solve []

unitBoundaryRadialPressureContribution :
  radialPressureContribution 1ℚ ≡ - threeEighths
unitBoundaryRadialPressureContribution = solve []

-- Exact reuse of the existing conservation compiler.  Radius is the final
-- argument in that owner.
tangentialPressureFromConservation :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
tangentialPressureFromConservation rho pr prPrime localNuPrime radius =
  Conservation.tangentialPressureFromConservation
    rho pr prPrime localNuPrime radius

record LocalRepulsiveInteriorBoundary : Set where
  constructor local-repulsive-interior-boundary
  field
    positiveMassInteriorConstructed : Bool
    outsideHorizonSelectedFixture : Bool
    outwardInteriorAccelerationConstructed : Bool
    radialEinsteinEquationPaidExactly : Bool
    tangentialStressCompiledFromConservation : Bool
    zeroPressureSmoothVacuumBoundarySatisfied : Bool
    nonzeroBoundaryStressOrTransitionLayerRequired : Bool
    repulsiveAsymptoticVacuumExteriorClaimed : Bool

canonicalLocalRepulsiveInteriorBoundary : LocalRepulsiveInteriorBoundary
canonicalLocalRepulsiveInteriorBoundary =
  local-repulsive-interior-boundary
    true true true true true false true false
