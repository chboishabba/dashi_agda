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
-- Do NOT introduce a second generic Duncan--Swisher theorem owner.  Reuse
-- DuncanSwisherTheorem12Exact and instantiate its exact case type on a small set
-- of structurally different primes:
--
--   5,7,13 : singleton rational locus, different m_p and exponents;
--   11     : multiple rational locus, m_11 = 4;
--   37,43  : non-rational locus present, valuation zero.
--
-- The p=11 instance additionally bridges Duncan--Swisher's FULL automorphism
-- convention back to the earlier Brandt lane: reduced orders 3,2 become full
-- orders 6,4, so m_11=4.  Reciprocal stack sheets 2,3 are not m_11.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Moonshine.DuncanSwisherTheorem12Exact as DS
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as P11

------------------------------------------------------------------------
-- Exact source-shaped cases.
------------------------------------------------------------------------

p5Case :
  DS.DuncanSwisherTheorem12Case
    1 0 6 (Monster.monsterOrderExponent Lane.p5)
p5Case = DS.oneRationalNoQuadratic
  refl refl (s≤s z≤n) refl

p7Case :
  DS.DuncanSwisherTheorem12Case
    1 0 4 (Monster.monsterOrderExponent Lane.p7)
p7Case = DS.oneRationalNoQuadratic
  refl refl (s≤s z≤n) refl

p11Case :
  DS.DuncanSwisherTheorem12Case
    2 0 4 (Monster.monsterOrderExponent Lane.p11)
p11Case = DS.manyRationalNoQuadratic
  (s≤s (s≤s z≤n)) refl (s≤s z≤n) refl

p13Case :
  DS.DuncanSwisherTheorem12Case
    1 0 2 (Monster.monsterOrderExponent Lane.p13)
p13Case = DS.oneRationalNoQuadratic
  refl refl (s≤s z≤n) refl

-- |S_p^2| counts individual non-rational j-points.  One Frobenius pair
-- therefore contributes TWO source points.
p37Case : DS.DuncanSwisherTheorem12Case 1 2 2 0
p37Case = DS.hasNonRationalSupersingular (s≤s z≤n) refl

p43Case : DS.DuncanSwisherTheorem12Case 2 2 2 0
p43Case = DS.hasNonRationalSupersingular (s≤s z≤n) refl

------------------------------------------------------------------------
-- Denominator-cleared exponent equations are exact against the existing owner.
------------------------------------------------------------------------

p5DoubledExponent :
  2 * Monster.monsterOrderExponent Lane.p5 ≡ 3 * 6
p5DoubledExponent = refl

p7DoubledExponent :
  2 * Monster.monsterOrderExponent Lane.p7 ≡ 3 * 4
p7DoubledExponent = refl

p11DoubledExponent :
  2 * Monster.monsterOrderExponent Lane.p11 ≡ 4
p11DoubledExponent = refl

p13DoubledExponent :
  2 * Monster.monsterOrderExponent Lane.p13 ≡ 3 * 2
p13DoubledExponent = refl

p37DoubledExponent : 2 * 0 ≡ 0
p37DoubledExponent = refl

p43DoubledExponent : 2 * 0 ≡ 0
p43DoubledExponent = refl

------------------------------------------------------------------------
-- p=11 convention bridge to #567's source-native automorphism carrier.
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

p11MinimumFullAutOrderAttained :
  p11FullAutomorphismOrder P11.j1728SS ≡ 4
p11MinimumFullAutOrderAttained = refl

p11MpIsTwiceMinimumReducedOrder :
  4 ≡ 2 * P11.reducedAutomorphismOrder P11.j1728SS
p11MpIsTwiceMinimumReducedOrder = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DuncanSwisherMonsterExponentGeometryBoundary : Set where
  field
    canonicalTheorem12OwnerReused : Bool
    p5p7p11p13PositiveExponentCasesConstructed : Bool
    p37p43QuadraticZeroControlsConstructed : Bool
    sourceQuadraticPointCountKeptDistinctFromPairCount : Bool
    p11FullVsReducedAutomorphismConventionBridged : Bool
    reciprocalStackSheetsUsedAsMp : Bool
    monsterExponentOwnerReused : Bool

canonicalDuncanSwisherMonsterExponentGeometryBoundary :
  DuncanSwisherMonsterExponentGeometryBoundary
canonicalDuncanSwisherMonsterExponentGeometryBoundary = record
  { canonicalTheorem12OwnerReused = true
  ; p5p7p11p13PositiveExponentCasesConstructed = true
  ; p37p43QuadraticZeroControlsConstructed = true
  ; sourceQuadraticPointCountKeptDistinctFromPairCount = true
  ; p11FullVsReducedAutomorphismConventionBridged = true
  ; reciprocalStackSheetsUsedAsMp = false
  ; monsterExponentOwnerReused = true
  }
