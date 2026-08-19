module DASHI.Moonshine.MonsterFrickeCasselmanHighestAlphaEverything where

------------------------------------------------------------------------
-- Current highest-alpha convergence root.
--
-- GLOBAL PRIME SUPPORT -- ALL-PRIME THEOREM WITH TWO MODERN MECHANISMS
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
-- with p=2,3 handled by the separate exact low-level support lane.
--
-- GLOBAL EXPONENT DEPTH -- ABOVE SUPPORT
--
-- The branch retains the full Duncan--Swisher p>3 multiplicity theorem, not
-- only its Boolean support corollary. The same Monster valuation is computed
-- from two source-natural observers:
--
--   supersingular stratum + m_p
--   modular-function p-adic valuation triple.
--
-- Their outputs agree at the declared consumer 2*v_p(|M|), while their carrier
-- types are not identified. Ogg support is a further coarse projection.
--
-- LOW PRIME STRUCTURE
--
-- Duncan--Swisher's two RHS values agree at p=2,3 but give 36 and 18, versus
-- actual Monster exponents 46 and 20. The branch now independently reconstructs
-- those FULL depths from standard Monster local subgroup structure:
--
--   2^{1+24}.Co_1 : 25 + 21 = 46,
--   3^{1+12}.2Suz.2 : 13 + 7 = 20.
--
-- Separately, the two special elliptic J_1 residue roles used with distinct
-- p>3 sharpness weights collide in characteristics 2 and 3; their separation is
-- 1728 = 2^6*3^3. The remaining low-prime theorem is the causal/analytic bridge
-- from this changed low-characteristic geometry to the residual depth 10/2,
-- not recovery of the final Monster exponents themselves.
--
-- For p>3 the next explanatory frontier is below the valuation identities:
-- explicit modular-function / U_p / level-lowering / p-adic rigidity machinery.
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
-- Their intersection has exactly two coordinates. The remaining transverse
-- line admits two integral alignments fixing that common plane.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as HistoricalGe5
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as GlobalAll
import DASHI.Moonshine.MonsterFrickeModernDirectionalMechanismExact as Modern
import DASHI.Moonshine.DuncanSwisherMonsterFrickeAllPrimesExact as DSAll
import DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything as Depth
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
moonshineForwardRegression = Modern.monsterPrimeImpliesFrickeGenusZeroByMoonshine

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
-- Quantitative Monster exponent regressions.
------------------------------------------------------------------------

fullExponentDepthRetainedRegression :
  Depth.fullExponentDepthNowRetained
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
fullExponentDepthRetainedRegression = refl

geometricAndModularDepthShareConsumerRegression :
  Depth.geometricAndModularObserversShareConsumer
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
geometricAndModularDepthShareConsumerRegression = refl

supportStrictlyCoarserThanDepthRegression :
  Depth.supportExposedAsCoarserProjection
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
supportStrictlyCoarserThanDepthRegression = refl

p2p3ResidualsExplicitRegression :
  Depth.p2p3ResidualsIsolated
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
p2p3ResidualsExplicitRegression = refl

lowPrimeFullDepthRecoveredLocallyRegression :
  Depth.lowPrimeFullExponentRecoveredFromLocalSubgroupStructure
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
lowPrimeFullDepthRecoveredLocallyRegression = refl

lowPrimeEllipticCollisionExposedRegression :
  Depth.lowPrimeEllipticStratumCollisionExposed
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
lowPrimeEllipticCollisionExposedRegression = refl

lowPrimeCausalBridgeStillOpenRegression :
  Depth.causalBridgeFromEllipticCollisionToResidualProved
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ false
lowPrimeCausalBridgeStillOpenRegression = refl

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
transverseSatakeResidualCollisionRegression = TransverseSatake.satakeResidualsIdentical

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
