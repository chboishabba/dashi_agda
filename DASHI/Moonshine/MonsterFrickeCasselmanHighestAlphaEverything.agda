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
-- LOCAL p11 SIDE -- NOW ONE TRANSVERSE COORDINATE
--
-- Casselman/Schmidt gives the K_0(4)=K_2(2) fixed-vector model with three
-- compact double-coset cells.  Full level 2 gives the distinct principal
-- K(2)-fixed P^1(F_2) model, also three-dimensional.
--
-- The exact common compact quotient B(Z/4)\GL_2(Z/4) shows these are DISTINCT
-- 3-spaces with a two-coordinate intersection.  Each admits a lossless split
--
--   Common2 + one transverse defect.
--
-- Two different integral alignments already fix Common2 pointwise and differ
-- only by the sign of the transverse coordinate.  Thus equal dimension,
-- common ambient representation, common intersection and good-prime Hecke
-- agreement still do not select the final alignment.
--
-- Remaining producer:
--   one source-native local operator / Whittaker-test-vector normalization that
--   orients or normalizes the transverse line.
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
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection
import DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact as Transverse

monsterPrimeGenusZeroRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
monsterPrimeGenusZeroRegression = Global.monsterPrimeIffFrickeGenusZero

casselmanLevelFourDimensionRegression :
  Casselman.fixedDimension Casselman.publishedP11LocalUnramifiedTower 2 ≡ 3
casselmanLevelFourDimensionRegression = Casselman.level4FixedDimensionIsThree

commonIntersectionHasTwoCoordinatesRegression :
  Intersection.commonIntersectionCoordinates
    Intersection.canonicalP11Level44TwoAdicFixedSpaceIntersectionBoundary ≡ 2
commonIntersectionHasTwoCoordinatesRegression = refl

fixedSpacesAreNotIdenticalRegression :
  Intersection.fixedSpacesDefinitionallyIdentical
    Intersection.canonicalP11Level44TwoAdicFixedSpaceIntersectionBoundary ≡ false
fixedSpacesAreNotIdenticalRegression = refl

transverseCoordinateCountRegression :
  Transverse.transverseCoordinates
    Transverse.canonicalP11Level44TwoAdicTransverseAlignmentBoundary ≡ 1
transverseCoordinateCountRegression = refl

commonPlaneDoesNotDetermineAlignmentRegression :
  Transverse.commonPlaneDeterminesFullAlignment
    Transverse.canonicalP11Level44TwoAdicTransverseAlignmentBoundary ≡ false
commonPlaneDoesNotDetermineAlignmentRegression = refl

sourceNativeTransverseSelectorStillRequiredRegression :
  Transverse.sourceNativeTransverseSelectorStillRequired
    Transverse.canonicalP11Level44TwoAdicTransverseAlignmentBoundary ≡ true
sourceNativeTransverseSelectorStillRequiredRegression = refl

finiteMonsterLaneTableStillUnusedRegression :
  Global.MonsterPrimeLaneTableUsed
    Global.canonicalPublishedMonsterFrickeGenusZeroBoundary ≡ false
finiteMonsterLaneTableStillUnusedRegression = refl
