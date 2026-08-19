module DASHI.Moonshine.DuncanSwisherMonsterExponentGeometryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Theorem 1.2 and equations (1.4)--(1.5).
--
-- CROSS-CHECK SOURCES
--
-- John Voight, "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 42 DOI: 10.1007/978-3-030-56694-4_42.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the three Duncan--Swisher regimes on structurally different
-- primes and compare the geometric exponent with the existing authoritative
-- Monster exponent owner.  The non-Ogg controls p=37,43 use TWO elements in
-- S_p^2 for one Frobenius-conjugate pair; pair count and |S_p^2| are not
-- silently identified.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Moonshine.DuncanSwisherSupersingularExponentDatumExact as DS
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as P11

------------------------------------------------------------------------
-- Small inequality witnesses for the published p>3 scope.
------------------------------------------------------------------------

fourLeFive : 4 ≤ 5
fourLeFive = s≤s (s≤s (s≤s (s≤s z≤n)))

fourLeSeven : 4 ≤ 7
fourLeSeven = s≤s (s≤s (s≤s (s≤s z≤n)))

fourLeEleven : 4 ≤ 11
fourLeEleven = s≤s (s≤s (s≤s (s≤s z≤n)))

fourLeThirteen : 4 ≤ 13
fourLeThirteen = s≤s (s≤s (s≤s (s≤s z≤n)))

------------------------------------------------------------------------
-- Source regimes and minimum FULL automorphism orders.
------------------------------------------------------------------------

p5Geometry : DS.SupersingularExponentGeometry
p5Geometry = DS.supersingular-exponent-geometry
  5 1 0 6 DS.singletonRationalNoQuadratic
  (DS.singletonEvidence refl refl)

p7Geometry : DS.SupersingularExponentGeometry
p7Geometry = DS.supersingular-exponent-geometry
  7 1 0 4 DS.singletonRationalNoQuadratic
  (DS.singletonEvidence refl refl)

p11Geometry : DS.SupersingularExponentGeometry
p11Geometry = DS.supersingular-exponent-geometry
  11 2 0 4 DS.multipleRationalNoQuadratic
  (DS.multipleEvidence (s≤s (s≤s z≤n)) refl)

p13Geometry : DS.SupersingularExponentGeometry
p13Geometry = DS.supersingular-exponent-geometry
  13 1 0 2 DS.singletonRationalNoQuadratic
  (DS.singletonEvidence refl refl)

-- One quadratic Frobenius pair means TWO elements of S_p^2.
p37Geometry : DS.SupersingularExponentGeometry
p37Geometry = DS.supersingular-exponent-geometry
  37 1 2 2 DS.quadraticLocusPresent
  (DS.quadraticEvidence (s≤s z≤n))

p43Geometry : DS.SupersingularExponentGeometry
p43Geometry = DS.supersingular-exponent-geometry
  43 2 2 2 DS.quadraticLocusPresent
  (DS.quadraticEvidence (s≤s z≤n))

------------------------------------------------------------------------
-- Theorem 1.2, denominator-cleared, reproduces the Monster exponents.
------------------------------------------------------------------------

p5DoubledExponent :
  2 * Monster.monsterOrderExponent Lane.p5
  ≡ DS.doubledGeometricExponent p5Geometry
p5DoubledExponent = refl

p7DoubledExponent :
  2 * Monster.monsterOrderExponent Lane.p7
  ≡ DS.doubledGeometricExponent p7Geometry
p7DoubledExponent = refl

p11DoubledExponent :
  2 * Monster.monsterOrderExponent Lane.p11
  ≡ DS.doubledGeometricExponent p11Geometry
p11DoubledExponent = refl

p13DoubledExponent :
  2 * Monster.monsterOrderExponent Lane.p13
  ≡ DS.doubledGeometricExponent p13Geometry
p13DoubledExponent = refl

p37GeometricExponentZero : DS.doubledGeometricExponent p37Geometry ≡ 0
p37GeometricExponentZero = refl

p43GeometricExponentZero : DS.doubledGeometricExponent p43Geometry ≡ 0
p43GeometricExponentZero = refl

------------------------------------------------------------------------
-- p=11 convention bridge to the earlier Brandt lane.
--
-- Voight gives reduced orders 3 and 2.  Full automorphism orders are therefore
-- 6 and 4; Duncan--Swisher m_11 is the minimum FULL order 4.
------------------------------------------------------------------------

p11FullAutomorphismOrder : P11.P11SupersingularJ → Nat
p11FullAutomorphismOrder j = 2 * P11.reducedAutomorphismOrder j

p11JZeroFullAutIsSix : p11FullAutomorphismOrder P11.jZeroSS ≡ 6
p11JZeroFullAutIsSix = refl

p11J1728FullAutIsFour : p11FullAutomorphismOrder P11.j1728SS ≡ 4
p11J1728FullAutIsFour = refl

p11EveryFullAutAtLeastFour :
  (j : P11.P11SupersingularJ) → 4 ≤ p11FullAutomorphismOrder j
p11EveryFullAutAtLeastFour P11.jZeroSS =
  s≤s (s≤s (s≤s (s≤s z≤n)))
p11EveryFullAutAtLeastFour P11.j1728SS =
  s≤s (s≤s (s≤s (s≤s z≤n)))

p11MinimumFullAutOrderIsFour : DS.minFullAutomorphismOrder p11Geometry ≡ 4
p11MinimumFullAutOrderIsFour = refl

p11MpIsTwiceMinimumReducedOrder :
  DS.minFullAutomorphismOrder p11Geometry
  ≡ 2 * P11.reducedAutomorphismOrder P11.j1728SS
p11MpIsTwiceMinimumReducedOrder = refl

------------------------------------------------------------------------
-- Published-law packages for the four positive-exponent probes.
------------------------------------------------------------------------

p5Law : DS.DuncanSwisherExponentLaw p5Geometry (Monster.monsterOrderExponent Lane.p5)
p5Law = record
  { DS.characteristicGreaterThanThree = fourLeFive
  ; DS.doubledExponentExact = p5DoubledExponent
  }

p7Law : DS.DuncanSwisherExponentLaw p7Geometry (Monster.monsterOrderExponent Lane.p7)
p7Law = record
  { DS.characteristicGreaterThanThree = fourLeSeven
  ; DS.doubledExponentExact = p7DoubledExponent
  }

p11Law : DS.DuncanSwisherExponentLaw p11Geometry (Monster.monsterOrderExponent Lane.p11)
p11Law = record
  { DS.characteristicGreaterThanThree = fourLeEleven
  ; DS.doubledExponentExact = p11DoubledExponent
  }

p13Law : DS.DuncanSwisherExponentLaw p13Geometry (Monster.monsterOrderExponent Lane.p13)
p13Law = record
  { DS.characteristicGreaterThanThree = fourLeThirteen
  ; DS.doubledExponentExact = p13DoubledExponent
  }

record DuncanSwisherMonsterExponentGeometryBoundary : Set where
  field
    p5p7p11p13PositiveExponentRegimesConstructed : Bool
    p37p43QuadraticZeroControlsConstructed : Bool
    p11FullVsReducedAutomorphismConventionBridged : Bool
    reciprocalStackSheetsUsedAsMp : Bool
    monsterExponentOwnerReused : Bool

canonicalDuncanSwisherMonsterExponentGeometryBoundary :
  DuncanSwisherMonsterExponentGeometryBoundary
canonicalDuncanSwisherMonsterExponentGeometryBoundary = record
  { p5p7p11p13PositiveExponentRegimesConstructed = true
  ; p37p43QuadraticZeroControlsConstructed = true
  ; p11FullVsReducedAutomorphismConventionBridged = true
  ; reciprocalStackSheetsUsedAsMp = false
  ; monsterExponentOwnerReused = true
  }
