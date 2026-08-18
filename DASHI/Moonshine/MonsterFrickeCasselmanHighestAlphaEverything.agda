module DASHI.Moonshine.MonsterFrickeCasselmanHighestAlphaEverything where

------------------------------------------------------------------------
-- Current highest-alpha convergence root.
--
-- GLOBAL PRIME-SET SIDE -- ALL-PRIME THEOREM WITH TWO MODERN MECHANISMS
--
--   FORWARD:
--     p | |M|
--       -> Conway--Norton/Borcherds prime-order moonshine class
--       -> moonshine group Gamma_0(p)^+ is genus zero
--       -> g(X_0^+(p)) = 0.
--
--   CONVERSE:
--     g(X_0^+(p)) = 0
--       -> zero coarse Frobenius-pair defect
--       -> Duncan--Swisher Theorem 1.2 exponent support (p>3)
--       -> p | |M|,
--
-- with p=2,3 handled by the separate exact low-level lane.
--
-- The older Duncan--Ono/Ogg supersingular SUPPORT equivalence is no longer
-- imported by the primary arbitrary-prime theorem.  It remains an independent
-- historical cross-check.  The next global frontier is to lower the stronger
-- Duncan--Swisher exponent theorem itself into explicit modular-function
-- operators rather than consuming only its support corollary.
--
-- No MonsterPrimeLane / SSP15 finite table and no finite under-72 Fricke table
-- participates in the arbitrary-prime theorem.
--
-- LOCAL p11 SIDE -- RESOLVED AT THE CORRECT REPRESENTATION LEVEL
--
-- Jacquet--Langlands identifies the p11 quaternionic/Brandt automorphic
-- representation with the unique classical weight-2 level-11 representation.
-- Hence their local components at 2 are the same unramified pi_2.
--
-- Casselman/Schmidt and the finite compact model show that the programme's two
-- compact opens cut out DISTINCT three-dimensional subspaces of that same pi_2:
--
--   V^{K(2)}       principal full-level-2 marked model,
--   V^{K_0(4)}     classical oldvector model.
--
-- Their intersection has exactly two coordinates.  The remaining transverse
-- line admits two integral alignments fixing that common plane.
--
-- LOCAL NON-CANONICITY AUDIT
--
-- The classical degeneracy basis is tied to Schmidt's n=2 Casselman cells in
-- the source-backed order
--
--   (wide,left,right) = (valuation0,terminal2,valuation1),
--
-- so the actual classical bad-prime operator is
--
--   U2(w,l,r) = (-2w+r, 0, -2w+l).
--
-- On analytic Old3 it satisfies
--
--   U2 (U2^2 + 2 U2 + 2 I) = 0,
--   ker(U2) = Z * (1,2,2).
--
-- The internally discovered positive marked R2 has trivial kernel and cannot
-- be conjugate to analytic U2 under ANY invertible zero-preserving coordinate
-- change.
--
-- Transporting the correct U2 through the two transverse alignments produces
-- distinct principal-side operators P+ and P-, but their COMPLETE Satake
-- residual maps coincide pointwise:
--
--   (P+^2+2P++2I)(x,y,z)
--     = (z,z,2z)
--     = (P-^2+2P-+2I)(x,y,z).
--
-- They also share the same kernel generator (1,1,2).  Therefore even
--
--   same pi_2 + common plane + a2 + Satake cubic + residual map + kernel line
--
-- does NOT canonically select a fixed-space coordinate alignment.
--
-- A Whittaker/test-vector normalization may select a preferred chart for a
-- downstream consumer, but it is OPTIONAL extra coordinate structure and is
-- not required by the representation-level Jacquet--Langlands theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as HistoricalGe5
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as GlobalAll
import DASHI.Moonshine.MonsterFrickeModernDirectionalMechanismExact as Modern
import DASHI.Moonshine.DuncanSwisherMonsterFrickeAllPrimesExact as DSAll
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.CasselmanUnramifiedPGL2FixedVectorTowerExact as Casselman
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection
import DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact as Transverse
import DASHI.Moonshine.P11JacquetLanglandsRepresentationStandardAuthorityExact as JL
import DASHI.Moonshine.P11JacquetLanglandsFixedSpaceResolutionExact as JLResolution
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal
import DASHI.Moonshine.P11Level44BadPrimeOperatorSeparationExact as Bad
import DASHI.Moonshine.P11Level44BadPrimeConjugacyNoGoExact as R2NoGo
import DASHI.Moonshine.P11Level44AnalyticU2SatakePolynomialExact as AnalyticSatake
import DASHI.Moonshine.P11CasselmanBruhatDegeneracyChartExact as BruhatChart
import DASHI.Moonshine.P11Level44TransverseSatakeNonUniquenessExact as TransverseSatake
import DASHI.Moonshine.P11JacquetLanglandsCoordinateNonCanonicityExact as CoordinateNoGo

------------------------------------------------------------------------
-- Global Monster / Fricke regressions.
------------------------------------------------------------------------

monsterPrimeGenusZeroGe5HistoricalRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
monsterPrimeGenusZeroGe5HistoricalRegression =
  HistoricalGe5.monsterPrimeIffFrickeGenusZero

monsterPrimeGenusZeroAllPrimesRegression :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ GlobalAll.primeFrickeGenus p prime ≡ 0
monsterPrimeGenusZeroAllPrimesRegression =
  Modern.monsterPrimeIffFrickeGenusZeroModern

moonshineForwardRegression :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  GlobalAll.primeFrickeGenus p prime ≡ 0
moonshineForwardRegression =
  Modern.monsterPrimeImpliesFrickeGenusZeroByMoonshine

exponentSupportConverseRegression :
  (p : Nat) → (prime : Prime p) →
  GlobalAll.primeFrickeGenus p prime ≡ 0 →
  Monster.PrimeDividesMonsterOrder p
exponentSupportConverseRegression =
  Modern.frickeGenusZeroImpliesMonsterPrimeByExponentSupport

primaryAllPrimeProofUsesDuncanOnoSupportRegression :
  Modern.DuncanOnoSupportEquivalenceImported
    Modern.canonicalMonsterFrickeModernDirectionalBoundary ≡ false
primaryAllPrimeProofUsesDuncanOnoSupportRegression = refl

duncanSwisherAllPrimeSupportRegression :
  DSAll.arbitraryPrimeSupportEquivalenceDerived
    DSAll.canonicalDuncanSwisherMonsterFrickeAllPrimesBoundary ≡ true
duncanSwisherAllPrimeSupportRegression = refl

primeCaseExhaustionRegression :
  GlobalAll.arbitraryPrimeCaseExhaustionDerivedInternally
    GlobalAll.canonicalPublishedMonsterFrickeAllSupportedPrimesBoundary ≡ true
primeCaseExhaustionRegression = refl

lowPrimeMonsterLaneStillUnusedRegression :
  GlobalAll.MonsterPrimeLaneImported
    GlobalAll.canonicalPublishedMonsterFrickeAllSupportedPrimesBoundary ≡ false
lowPrimeMonsterLaneStillUnusedRegression = refl

lowPrimeFiniteFrickeTableStillUnusedRegression :
  GlobalAll.finiteUnder72FrickeTableImported
    GlobalAll.canonicalPublishedMonsterFrickeAllSupportedPrimesBoundary ≡ false
lowPrimeFiniteFrickeTableStillUnusedRegression = refl

------------------------------------------------------------------------
-- Local p11 representation / coordinate regressions.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Local bad-prime / Satake regressions.
------------------------------------------------------------------------

internalR2CannotBeRecoveredByConjugacyRegression :
  R2NoGo.arbitraryInvertibleU2R2IntertwinerPossible
    R2NoGo.canonicalP11Level44BadPrimeConjugacyNoGoBoundary ≡ false
internalR2CannotBeRecoveredByConjugacyRegression = refl

analyticU2CubicRegression :
  (v : Principal.Old3) →
  Bad.analyticU2 (AnalyticSatake.satakeQuadraticU2 v) ≡ Bad.zeroOld3
analyticU2CubicRegression = AnalyticSatake.satakeQuadraticLandsInKernel

casselmanBruhatOrderRegression :
  BruhatChart.bruhatOrderValuation0Terminal2Valuation1
    BruhatChart.canonicalP11CasselmanBruhatDegeneracyChartBoundary ≡ true
casselmanBruhatOrderRegression = refl

transverseSatakeResidualCollisionRegression :
  (v : Principal.Old3) →
  TransverseSatake.plusSatakeQuadratic v
  ≡ TransverseSatake.minusSatakeQuadratic v
transverseSatakeResidualCollisionRegression =
  TransverseSatake.satakeResidualsIdentical

satakeCannotSelectTransverseSignRegression :
  TransverseSatake.satakePolynomialSelectsTransverseSign
    TransverseSatake.canonicalP11Level44TransverseSatakeNonUniquenessBoundary ≡ false
satakeCannotSelectTransverseSignRegression = refl

coordinateAlignmentStillNoncanonicalRegression :
  CoordinateNoGo.coordinateAlignmentDeterminedByDeclaredData
    CoordinateNoGo.canonicalP11JacquetLanglandsCoordinateNonCanonicityBoundary ≡ false
coordinateAlignmentStillNoncanonicalRegression = refl

whittakerNotRequiredForJLRegression :
  CoordinateNoGo.whittakerNormalizationRequiredForJLTheorem
    CoordinateNoGo.canonicalP11JacquetLanglandsCoordinateNonCanonicityBoundary ≡ false
whittakerNotRequiredForJLRegression = refl

whittakerOptionalForPreferredCoordinatesRegression :
  CoordinateNoGo.whittakerNormalizationOptionalForPreferredCoordinates
    CoordinateNoGo.canonicalP11JacquetLanglandsCoordinateNonCanonicityBoundary ≡ true
whittakerOptionalForPreferredCoordinatesRegression = refl
