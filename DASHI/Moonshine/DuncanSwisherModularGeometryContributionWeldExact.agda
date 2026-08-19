module DASHI.Moonshine.DuncanSwisherModularGeometryContributionWeldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Theorem 1.1 expresses v_p(|M|) as the sum of three modular-function
-- valuations at levels p+, p and p^2.  Theorem 1.2 expresses the SAME exponent
-- through supersingular rationality and the minimum full automorphism order.
--
-- DASHI CONTRIBUTION
--
-- Reuse the pre-existing MonsterOrderExponentCorrectionExact owner for the
-- Theorem-1.1 contribution triples and the new geometric Theorem-1.2 carrier,
-- then prove they meet at one exponent.  No new Monster valuation table is
-- introduced.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Moonshine.DuncanSwisherSupersingularExponentDatumExact as DS
import DASHI.Moonshine.DuncanSwisherMonsterExponentGeometryExact as Geo
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Existing modular-function contribution total.
------------------------------------------------------------------------

modularContributionTotal :
  (prime : Lane.MonsterPrimeLane) →
  (above : Monster.PrimeAboveThree prime) → Nat
modularContributionTotal prime above =
  let C = Monster.modularContribution prime above
  in Monster.frickeLevel C + Monster.primeLevel C + Monster.squareLevel C

modularContributionRecoversExponent :
  (prime : Lane.MonsterPrimeLane) →
  (above : Monster.PrimeAboveThree prime) →
  modularContributionTotal prime above ≡ Monster.monsterOrderExponent prime
modularContributionRecoversExponent prime above =
  Monster.reconstructsExponent (Monster.modularContribution prime above)

------------------------------------------------------------------------
-- Four geometrically distinct positive-exponent probes.
------------------------------------------------------------------------

p5ModularEqualsExponent :
  modularContributionTotal Lane.p5 Monster.p5AboveThree
  ≡ Monster.monsterOrderExponent Lane.p5
p5ModularEqualsExponent = refl

p7ModularEqualsExponent :
  modularContributionTotal Lane.p7 Monster.p7AboveThree
  ≡ Monster.monsterOrderExponent Lane.p7
p7ModularEqualsExponent = refl

p11ModularEqualsExponent :
  modularContributionTotal Lane.p11 Monster.p11AboveThree
  ≡ Monster.monsterOrderExponent Lane.p11
p11ModularEqualsExponent = refl

p13ModularEqualsExponent :
  modularContributionTotal Lane.p13 Monster.p13AboveThree
  ≡ Monster.monsterOrderExponent Lane.p13
p13ModularEqualsExponent = refl

------------------------------------------------------------------------
-- Denominator-cleared geometric formula meets the same exponent.
------------------------------------------------------------------------

p5ModularGeometryMeet :
  2 * modularContributionTotal Lane.p5 Monster.p5AboveThree
  ≡ DS.doubledGeometricExponent Geo.p5Geometry
p5ModularGeometryMeet = refl

p7ModularGeometryMeet :
  2 * modularContributionTotal Lane.p7 Monster.p7AboveThree
  ≡ DS.doubledGeometricExponent Geo.p7Geometry
p7ModularGeometryMeet = refl

p11ModularGeometryMeet :
  2 * modularContributionTotal Lane.p11 Monster.p11AboveThree
  ≡ DS.doubledGeometricExponent Geo.p11Geometry
p11ModularGeometryMeet = refl

p13ModularGeometryMeet :
  2 * modularContributionTotal Lane.p13 Monster.p13AboveThree
  ≡ DS.doubledGeometricExponent Geo.p13Geometry
p13ModularGeometryMeet = refl

------------------------------------------------------------------------
-- Concrete triples expose why equal Ogg support can still have unequal
-- Monster multiplicity.
------------------------------------------------------------------------

p5ContributionTriple :
  ( Monster.frickeLevel (Monster.modularContribution Lane.p5 Monster.p5AboveThree)
  , Monster.primeLevel (Monster.modularContribution Lane.p5 Monster.p5AboveThree)
  , Monster.squareLevel (Monster.modularContribution Lane.p5 Monster.p5AboveThree))
  ≡ (3 , 5 , 1)
p5ContributionTriple = refl

p7ContributionTriple :
  ( Monster.frickeLevel (Monster.modularContribution Lane.p7 Monster.p7AboveThree)
  , Monster.primeLevel (Monster.modularContribution Lane.p7 Monster.p7AboveThree)
  , Monster.squareLevel (Monster.modularContribution Lane.p7 Monster.p7AboveThree))
  ≡ (2 , 4 , 0)
p7ContributionTriple = refl

p11ContributionTriple :
  ( Monster.frickeLevel (Monster.modularContribution Lane.p11 Monster.p11AboveThree)
  , Monster.primeLevel (Monster.modularContribution Lane.p11 Monster.p11AboveThree)
  , Monster.squareLevel (Monster.modularContribution Lane.p11 Monster.p11AboveThree))
  ≡ (2 , 0 , 0)
p11ContributionTriple = refl

p13ContributionTriple :
  ( Monster.frickeLevel (Monster.modularContribution Lane.p13 Monster.p13AboveThree)
  , Monster.primeLevel (Monster.modularContribution Lane.p13 Monster.p13AboveThree)
  , Monster.squareLevel (Monster.modularContribution Lane.p13 Monster.p13AboveThree))
  ≡ (1 , 2 , 0)
p13ContributionTriple = refl

record DuncanSwisherModularGeometryContributionWeldBoundary : Set where
  field
    existingMonsterExponentOwnerReused : Bool
    theorem11ContributionOwnerReused : Bool
    theorem12GeometryOwnerReused : Bool
    p5p7p11p13BothDescriptionsMeet : Bool
    supportOnlySufficientForMultiplicity : Bool

canonicalDuncanSwisherModularGeometryContributionWeldBoundary :
  DuncanSwisherModularGeometryContributionWeldBoundary
canonicalDuncanSwisherModularGeometryContributionWeldBoundary = record
  { existingMonsterExponentOwnerReused = true
  ; theorem11ContributionOwnerReused = true
  ; theorem12GeometryOwnerReused = true
  ; p5p7p11p13BothDescriptionsMeet = true
  ; supportOnlySufficientForMultiplicity = false
  }
