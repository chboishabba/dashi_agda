module DASHI.Mathematics.Topology.AlexanderHornedC3SatellitePlacementExact where

------------------------------------------------------------------------
-- EXPLICIT RATIONAL-COORDINATE THREEFOLD PLACEMENT, NATURAL GRID.
--
-- The centers of the three satellite construction balls are
-- 9 e_x, 9 e_y and 9 e_z; the central ball is at the origin.
-- Coordinate cycling (x,y,z) -> (z,x,y) moves each satellite to
-- the next one and fixes the center. Squared distances are exactly
-- 81 from the center and 162 between distinct satellites.
--
-- Source/classification: these are new finite coordinate calculations.
-- They are NOT a construction of a wild sphere, smooth collars,
-- or a proof of topological separation of the complement.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Ambient

difference : Nat → Nat → Nat
difference a b = (a - b) + (b - a)

square : Nat → Nat
square n = n * n

squareDistance : Ambient.Triple Nat → Ambient.Triple Nat → Nat
squareDistance (Ambient.xyz a b c) (Ambient.xyz x y z) =
  square (difference a x) +
  (square (difference b y) + square (difference c z))

center : Ambient.Triple Nat
center = Ambient.xyz 0 0 0

satelliteCenter : C3.C3 → Ambient.Triple Nat
satelliteCenter C3.c0 = Ambient.xyz 9 0 0
satelliteCenter C3.c1 = Ambient.xyz 0 9 0
satelliteCenter C3.c2 = Ambient.xyz 0 0 9

centerRotationFixed : Ambient.rotateXYZ center ≡ center
centerRotationFixed = refl

satelliteRotation : ∀ c →
  Ambient.rotateXYZ (satelliteCenter c)
    ≡ satelliteCenter (C3.act C3.c1 c)
satelliteRotation C3.c0 = refl
satelliteRotation C3.c1 = refl
satelliteRotation C3.c2 = refl

eachSatelliteNineAwaySquared : ∀ c →
  squareDistance center (satelliteCenter c) ≡ 81
eachSatelliteNineAwaySquared C3.c0 = refl
eachSatelliteNineAwaySquared C3.c1 = refl
eachSatelliteNineAwaySquared C3.c2 = refl

betweenSatellite01 : squareDistance
  (satelliteCenter C3.c0) (satelliteCenter C3.c1) ≡ 162
betweenSatellite01 = refl

betweenSatellite12 : squareDistance
  (satelliteCenter C3.c1) (satelliteCenter C3.c2) ≡ 162
betweenSatellite12 = refl

betweenSatellite20 : squareDistance
  (satelliteCenter C3.c2) (satelliteCenter C3.c0) ≡ 162
betweenSatellite20 = refl

-- A radius-one closed Euclidean ball around a satellite center is
-- disjoint from the radius-one central ball (81 > (1+1)^2 = 4).
-- Distinct radius-one satellite balls are disjoint as 162 > 4.
-- The Euclidean ball disjointness theorem itself still belongs to
-- the metric/topology library, not to these arithmetic equalities.
criticalTwiceRadiusSquared : Nat
criticalTwiceRadiusSquared = 4

centerSeparationMargin : squareDistance center
  (satelliteCenter C3.c0) - criticalTwiceRadiusSquared ≡ 77
centerSeparationMargin = refl

sectorSeparationMargin : squareDistance
  (satelliteCenter C3.c0) (satelliteCenter C3.c1)
  - criticalTwiceRadiusSquared ≡ 158
sectorSeparationMargin = refl

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

satellites01Different :
  satelliteCenter C3.c0 ≢ satelliteCenter C3.c1
satellites01Different ()
