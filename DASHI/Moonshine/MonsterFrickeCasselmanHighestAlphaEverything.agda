module DASHI.Moonshine.MonsterFrickeCasselmanHighestAlphaEverything where

------------------------------------------------------------------------
-- Current highest-alpha convergence root.
--
-- GLOBAL PRIME-SET SIDE -- CLOSED AT EXPLICIT PUBLISHED AUTHORITY BOUNDARIES
--
--   actual Monster order divisibility
--     <=> Duncan--Ono/Ogg coarse supersingular rationality
--     <=> Deligne--Rapoport/Fricke coarse Frobenius fully fixed
--     <=> g(X_0^+(p)) = 0
--
-- for primes p >= 5 covered by the prime-level geometric authority.
-- No MonsterPrimeLane / SSP15 finite table participates in that chain.
--
-- LOCAL p11 SIDE -- ONE CONCRETE PRODUCER REMAINS
--
-- Casselman/Schmidt gives the source-native K_0(4)=K_2(2) fixed-vector model
-- with three compact double-coset cells.  Full level 2 gives the distinct
-- principal-congruence marked model P^1(F_2), also of size three.
--
-- Good-prime Hecke cannot select their alignment; compact averaging drops
-- rank; a 2-isogeny cannot transport a full level-2 frame; and the internal
-- positive marked R2 is not the classical U2 under common coordinates.
--
-- Remaining producer:
--   construct the actual local GL_2(Q_2) / Casselman test-vector transform
--   between the three K_0(4) double-coset cells and the three marked
--   principal-level-2 branches, inside the same p11 automorphic representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as Global
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.CasselmanUnramifiedPGL2FixedVectorTowerExact as Casselman
import DASHI.Moonshine.P11CasselmanLevel4DoubleCosetBasisExact as LocalBasis

monsterPrimeGenusZeroRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
monsterPrimeGenusZeroRegression = Global.monsterPrimeIffFrickeGenusZero

casselmanLevelFourDimensionRegression :
  Casselman.fixedDimension Casselman.publishedP11LocalUnramifiedTower 2 ≡ 3
casselmanLevelFourDimensionRegression = Casselman.level4FixedDimensionIsThree

localComparisonStillOpenRegression :
  LocalBasis.twoAdicTestVectorTransformStillRequired
    LocalBasis.canonicalP11CasselmanLevel4DoubleCosetBasisBoundary ≡ true
localComparisonStillOpenRegression = refl

finiteMonsterLaneTableStillUnusedRegression :
  Global.MonsterPrimeLaneTableUsed
    Global.canonicalPublishedMonsterFrickeGenusZeroBoundary ≡ false
finiteMonsterLaneTableStillUnusedRegression = refl
