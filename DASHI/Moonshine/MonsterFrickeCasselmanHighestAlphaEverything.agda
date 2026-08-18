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
-- LOCAL p11 SIDE -- RESOLVED AT THE CORRECT REPRESENTATION LEVEL
--
-- Jacquet--Langlands identifies the p11 quaternionic/Brandt automorphic
-- representation with the unique classical weight-2 level-11 representation.
-- Hence their local components at 2 are the same unramified pi_2.
--
-- Casselman/Schmidt and the finite compact model then show that the two compact
-- opens used by the programme cut out DIFFERENT three-dimensional subspaces of
-- that same pi_2:
--
--   V^{K(2)}       principal full-level-2 marked model,
--   V^{K_0(4)}     classical oldvector model.
--
-- Their intersection has exactly two coordinates.  The remaining transverse
-- line admits at least two alignments fixing the common plane, so no canonical
-- 3D fixed-space map follows from JL.  Martin's noncanonical JL discipline is
-- therefore essential, not a missing implementation detail.
--
-- An extra Whittaker/test-vector normalization may still be studied as an
-- OPTIONAL coordinate choice, but it no longer blocks the same-object theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as Global
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.CasselmanUnramifiedPGL2FixedVectorTowerExact as Casselman
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection
import DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact as Transverse
import DASHI.Moonshine.P11JacquetLanglandsRepresentationStandardAuthorityExact as JL
import DASHI.Moonshine.P11JacquetLanglandsFixedSpaceResolutionExact as JLResolution

monsterPrimeGenusZeroRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
monsterPrimeGenusZeroRegression = Global.monsterPrimeIffFrickeGenusZero

casselmanLevelFourDimensionRegression :
  Casselman.fixedDimension Casselman.publishedP11LocalUnramifiedTower 2 ≡ 3
casselmanLevelFourDimensionRegression = Casselman.level4FixedDimensionIsThree

sameP11LocalRepresentationAtTwoRegression :
  JL.localAtTwo JL.p11QuaternionBrandtRepresentation
  ≡ JL.localAtTwo JL.p11ClassicalNewformRepresentation
sameP11LocalRepresentationAtTwoRegression = JLResolution.sameP11LocalRepresentationAtTwo

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

canonicalFixedSpaceMapNotRequiredRegression :
  JLResolution.canonicalFixedSpaceMapRequiredForJL
    JLResolution.canonicalP11JacquetLanglandsFixedSpaceResolutionBoundary ≡ false
canonicalFixedSpaceMapNotRequiredRegression = refl

localSameObjectSeamResolvedRegression :
  JLResolution.localSameObjectSeamResolvedAtCorrectLevel
    JLResolution.canonicalP11JacquetLanglandsFixedSpaceResolutionBoundary ≡ true
localSameObjectSeamResolvedRegression = refl

finiteMonsterLaneTableStillUnusedRegression :
  Global.MonsterPrimeLaneTableUsed
    Global.canonicalPublishedMonsterFrickeGenusZeroBoundary ≡ false
finiteMonsterLaneTableStillUnusedRegression = refl
