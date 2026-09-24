{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTUnequalVacuumStaticWallNoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _-_; -_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Foundations.GRQFTNambuGotoTwoVacuumPotentialExact as Potential

------------------------------------------------------------------------
-- STATIC FLAT-WALL FIRST-INTEGRAL NO-GO
--
-- For a canonical one-dimensional static scalar profile in flat spacetime,
--
--   E_wall = (1/2)(phi')^2 - V(phi)
--
-- is constant along the profile.
--
-- At an asymptotic stationary vacuum, phi' -> 0, so the conserved value is
--
--   E_wall = -V_vacuum.
--
-- Therefore a static wall that approaches stationary vacua at BOTH ends
-- requires the two vacuum energies to be equal.
------------------------------------------------------------------------

staticVacuumFirstIntegral :
  ℚ → ℚ
staticVacuumFirstIntegral vacuumEnergy =
  - vacuumEnergy

stationaryEndpointFirstIntegralEqualityForcesEqualVacua :
  (leftVacuum rightVacuum : ℚ) →
  staticVacuumFirstIntegral leftVacuum
    ≡ staticVacuumFirstIntegral rightVacuum →
  leftVacuum ≡ rightVacuum
stationaryEndpointFirstIntegralEqualityForcesEqualVacua left right equality =
  trans
    (sym (ℚP.neg-involutive left))
    (trans
      (cong -_ equality)
      (ℚP.neg-involutive right))

------------------------------------------------------------------------
-- NAMBU VACUA ARE UNEQUAL
------------------------------------------------------------------------

nambuInteriorVacuum : ℚ
nambuInteriorVacuum = Int.+ 21 / 64

nambuExteriorVacuum : ℚ
nambuExteriorVacuum = Int.+ 19 / 48

nambuVacuumEnergyDifference :
  nambuExteriorVacuum - nambuInteriorVacuum
    ≡ Int.+ 13 / 192
nambuVacuumEnergyDifference = refl

nambuVacuaCannotBeEqual :
  nambuInteriorVacuum ≡ nambuExteriorVacuum → ⊥
nambuVacuaCannotBeEqual ()

nambuStationaryEndpointFirstIntegralsCannotMatch :
  staticVacuumFirstIntegral nambuInteriorVacuum
    ≡ staticVacuumFirstIntegral nambuExteriorVacuum →
  ⊥
nambuStationaryEndpointFirstIntegralsCannotMatch equality =
  nambuVacuaCannotBeEqual
    (stationaryEndpointFirstIntegralEqualityForcesEqualVacua
      nambuInteriorVacuum
      nambuExteriorVacuum
      equality)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The explicit asymmetric potential can have two local minima, but those
-- unequal minima cannot be connected by a globally static canonical flat kink
-- with vanishing derivative at both asymptotic ends.
--
-- At least one assumption must change:
--   * include gravitational backreaction / junction geometry,
--   * allow wall motion / acceleration,
--   * allow noncanonical field dynamics,
--   * or add additional stress sectors.
------------------------------------------------------------------------

data UnequalVacuumWallEscapeRoute : Set where
  gravitatingWall : UnequalVacuumWallEscapeRoute
  acceleratingWall : UnequalVacuumWallEscapeRoute
  noncanonicalFieldDynamics : UnequalVacuumWallEscapeRoute
  additionalStressSector : UnequalVacuumWallEscapeRoute

record UnequalVacuumStaticWallNoGoBoundary : Set where
  constructor unequal-vacuum-static-wall-no-go-boundary
  field
    unequalVacuaConstructed : Bool
    flatCanonicalStaticWallWithRestVacuaPossible : Bool
    gravitatingJunctionIsLegitimateEscape : Bool
    wallMotionIsLegitimateEscape : Bool
    noGoClaimsNoDomainWallOfAnyKind : Bool

canonicalUnequalVacuumStaticWallNoGoBoundary :
  UnequalVacuumStaticWallNoGoBoundary
canonicalUnequalVacuumStaticWallNoGoBoundary =
  unequal-vacuum-static-wall-no-go-boundary
    true false true true false
