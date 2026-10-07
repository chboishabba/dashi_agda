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
-- with selected positive a=b=1/4.  Then 2m/r = 2 a r^2 <= 1/2 on the
-- unit interval, so the selected fixture is on the outside-horizon branch.
-- Static test-particle acceleration has sign -nu' = +b r: outward.
--
-- Einstein's radial equation determines the pressure contribution rather than
-- allowing it to be chosen independently:
--
--   m + P_r = nu' r (r - 2m)
--
-- hence
--
--   P_r(r) = -r^3 [ a + b (1 - 2 a r^2) ].
--
-- Conservation then determines p_t from rho,p_r,nu'.  Thus this is a genuine
-- reduction of the source search.  At r=1 the required radial pressure term is
-- nonzero (-3/8 for a=b=1/4), proving that this outward interior cannot be
-- smoothly matched to a zero-pressure positive-mass vacuum boundary without a
-- transition/surface layer.
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

-- Generic tangential-pressure compiler.  The normalization of rho/pr is left
-- to the concrete Einstein-unit realization; conservation itself is exact.
tangentialPressureFromConservation :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
tangentialPressureFromConservation radius rho pr prPrime localNuPrime =
  Conservation.compileTangentialPressure
    radius rho pr prPrime localNuPrime

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
