module DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused highest-alpha root for the post-support Monster exponent problem.
--
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- LOCAL GROUP SOURCE CALIBRATION
--
-- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker,
-- Robert A. Wilson, "Atlas of Finite Groups", Oxford University Press, 1985.
-- ISBN 0-19-853199-0; no DOI asserted.
--
-- This root deliberately sits ABOVE the already-closed prime-support theorem.
-- It asks what the EXPONENT v_p(|M|) remembers once
--
--   p | |M| <=> g(X_0^+(p)) = 0
--
-- is already known.
--
-- For p>3 the answer now retained is:
--
--   positive Fricke genus
--     -> valuation 0 and m_p = 2;
--
--   genus zero, multiple rational supersingular points
--     -> 2 valuation = m_p and no non-Fricke modular residual;
--
--   genus zero, singleton supersingular locus
--     -> 2 valuation = 3 m_p and the p,p^2 modular residual = m_p.
--
-- The same doubled Monster valuation is explicitly exposed as a consumer of
-- TWO source-natural observers: supersingular geometry and the three modular
-- valuation contributions. Support is a further coarse projection.
--
-- LOW CHARACTERISTICS
--
-- Duncan--Swisher's two right-hand sides agree at p=2,3 but give 36 and 18,
-- while the actual Monster exponents are 46 and 20.  We now retain TWO exact
-- structural facts around that discrepancy:
--
--   * standard Monster local subgroup shapes carry the FULL low-prime depths:
--       2^{1+24}.Co_1 -> 25 + 21 = 46,
--       3^{1+12}.2Suz.2 -> 13 + 7 = 20;
--
--   * the two special elliptic J_1 residue roles used with different p>3
--     sharpness weights collapse in characteristics 2 and 3 because their
--     separation is 1728 = 2^6*3^3.
--
-- The missing theorem is therefore considerably narrower: explain how the
-- low-characteristic analytic/geometric mechanism bridges from its common
-- RHS to the full local-group depth.  We do NOT identify the residuals 10,2
-- with particular Co_1/Suz factors merely from the arithmetic.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as Exponent
import DASHI.Moonshine.DuncanSwisherExponentFrickeGenusRefinementExact as Genus
import DASHI.Moonshine.DuncanSwisherModularValuationDepthMechanismExact as Modular
import DASHI.Moonshine.DuncanSwisherExponentObserverFactorizationExact as Observers
import DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact as LowPrime
import DASHI.Moonshine.MonsterLowPrimeLocalSubgroupDepthExact as LocalDepth
import DASHI.Moonshine.DuncanSwisherLowPrimeEllipticCollisionExact as Elliptic
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- Full depth authority is same-carrier with the Fricke selector.
------------------------------------------------------------------------

exactFrickeCarrierReusedRegression :
  Exponent.exactFrickeFrobeniusCarrierReused
    Exponent.canonicalDuncanSwisherExponentFormulaBoundary ≡ true
exactFrickeCarrierReusedRegression = refl

duplicateGeometryAuthorityAbsentRegression :
  Exponent.duplicateSupersingularGeometryAuthorityIntroduced
    Exponent.canonicalDuncanSwisherExponentFormulaBoundary ≡ false
duplicateGeometryAuthorityAbsentRegression = refl

------------------------------------------------------------------------
-- Support is recovered from depth, not used as its premise.
------------------------------------------------------------------------

valuationZeroIffPositiveGenusRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
  in
  Exponent.monsterValuation E ≡ 0
  ↔ 1 ≤ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5)
valuationZeroIffPositiveGenusRegression = Genus.valuationZeroIffFrickeGenusPositive

------------------------------------------------------------------------
-- The exact Theorem 1.2 branch induces the full modular residual
-- classification from Theorem 1.1 + equation (1.8).
------------------------------------------------------------------------

modularResidualDepthRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let
    E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
    M = Modular.publishedDuncanSwisherModularValuationAuthority p prime ge5
  in
  Modular.modularResidualByExponentCase E M (Exponent.theorem12 E)
modularResidualDepthRegression p prime ge5 =
  let
    E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
    M = Modular.publishedDuncanSwisherModularValuationAuthority p prime ge5
  in
  Modular.modularResidualClassification E M (Exponent.theorem12 E)

------------------------------------------------------------------------
-- Positive genus gives the complete zero-exponent collapse, including m_p=2.
------------------------------------------------------------------------

positiveGenusDepthCollapseRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  1 ≤ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) →
  let E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
  in
  Genus.PositiveGenusExponentCollapse
    (DR.pairedCount (Exponent.sharedGeometry p prime ge5))
    (Exponent.monsterValuation E)
    (Exponent.minimumAutomorphismOrder E)
positiveGenusDepthCollapseRegression = Genus.positiveGenusExponentCollapse

------------------------------------------------------------------------
-- Top-down observer result: geometric and modular carriers compute one consumer
-- without being identified with each other.
------------------------------------------------------------------------

geometricAndModularConsumerAgreementRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let S = Observers.publishedExponentMechanismState p prime ge5
  in
  Observers.depthFromGeometry (Observers.geometricObserver S)
  ≡ Observers.depthFromModular (Observers.modularObserver S)
geometricAndModularConsumerAgreementRegression p prime ge5 =
  Observers.geometricAndModularDepthAgree
    (Observers.publishedExponentMechanismState p prime ge5)

supportIsCoarseProjectionOfGeometryRegression :
  Observers.supportFactorsThroughGeometry
    Observers.canonicalDuncanSwisherExponentObserverBoundary ≡ true
supportIsCoarseProjectionOfGeometryRegression = refl

observerCarriersNotIdentifiedRegression :
  Observers.observerCarriersIdentified
    Observers.canonicalDuncanSwisherExponentObserverBoundary ≡ false
observerCarriersNotIdentifiedRegression = refl

------------------------------------------------------------------------
-- Low-prime quantitative residual and independent local-group realization.
------------------------------------------------------------------------

p2ResidualRegression : LowPrime.lowPrimeResidual LowPrime.low2 ≡ 10
p2ResidualRegression = LowPrime.p2ResidualIsTen

p3ResidualRegression : LowPrime.lowPrimeResidual LowPrime.low3 ≡ 2
p3ResidualRegression = LowPrime.p3ResidualIsTwo

p2LocalGroupDepthRegression : LocalDepth.twoBLocalTwoDepth ≡ 46
p2LocalGroupDepthRegression = LocalDepth.twoBLocalTwoDepthIs46

p3LocalGroupDepthRegression : LocalDepth.threeBLocalThreeDepth ≡ 20
p3LocalGroupDepthRegression = LocalDepth.threeBLocalThreeDepthIs20

p2RHSPlusResidualClosesToLocalDepthRegression :
  LowPrime.commonDuncanSwisherRHS LowPrime.low2
    + LowPrime.lowPrimeResidual LowPrime.low2
  ≡ LocalDepth.twoBLocalTwoDepth
p2RHSPlusResidualClosesToLocalDepthRegression =
  LocalDepth.p2RHSPlusResidualEqualsLocalDepth

p3RHSPlusResidualClosesToLocalDepthRegression :
  LowPrime.commonDuncanSwisherRHS LowPrime.low3
    + LowPrime.lowPrimeResidual LowPrime.low3
  ≡ LocalDepth.threeBLocalThreeDepth
p3RHSPlusResidualClosesToLocalDepthRegression =
  LocalDepth.p3RHSPlusResidualEqualsLocalDepth

------------------------------------------------------------------------
-- Low-characteristic analytic/geometric obstruction: the two special elliptic
-- residue roles collapse exactly at p=2,3.
------------------------------------------------------------------------

specialEllipticSeparationRegression : Elliptic.specialJ1Separation ≡ 1728
specialEllipticSeparationRegression = refl

p2SpecialEllipticResiduesCollideRegression :
  Elliptic.specialResidueRepresentative LowPrime.low2 Elliptic.jZeroRole
  ≡ Elliptic.specialResidueRepresentative LowPrime.low2 Elliptic.j1728Role
p2SpecialEllipticResiduesCollideRegression =
  Elliptic.lowPrimeSpecialResiduesCollide LowPrime.low2

p3SpecialEllipticResiduesCollideRegression :
  Elliptic.specialResidueRepresentative LowPrime.low3 Elliptic.jZeroRole
  ≡ Elliptic.specialResidueRepresentative LowPrime.low3 Elliptic.j1728Role
p3SpecialEllipticResiduesCollideRegression =
  Elliptic.lowPrimeSpecialResiduesCollide LowPrime.low3

p2LowResidueCannotReconstructEllipticRoleRegression :
  Elliptic.ExactRoleReconstructionFromLowResidue LowPrime.low2 → ⊥
p2LowResidueCannotReconstructEllipticRoleRegression =
  Elliptic.lowResidueCannotReconstructEllipticRole LowPrime.low2

p3LowResidueCannotReconstructEllipticRoleRegression :
  Elliptic.ExactRoleReconstructionFromLowResidue LowPrime.low3 → ⊥
p3LowResidueCannotReconstructEllipticRoleRegression =
  Elliptic.lowResidueCannotReconstructEllipticRole LowPrime.low3

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DuncanSwisherExponentDepthHighestAlphaBoundary : Set where
  field
    supportTheoremAlreadyClosed : Bool
    fullExponentDepthNowRetained : Bool
    modularThreeTermDepthNowRetained : Bool
    singletonExtraResidualDerived : Bool
    positiveGenusZeroExponentDerived : Bool
    geometricAndModularObserversShareConsumer : Bool
    supportExposedAsCoarserProjection : Bool
    p2p3ResidualsIsolated : Bool
    lowPrimeFullExponentRecoveredFromLocalSubgroupStructure : Bool
    lowPrimeEllipticStratumCollisionExposed : Bool
    residualIdentifiedWithSpecificLocalSimpleGroupFactor : Bool
    causalBridgeFromEllipticCollisionToResidualProved : Bool
    finiteMonsterPrimeLaneUsedForPgt3Proof : Bool
    nextPgt3FrontierIsExplicitModularFunctionOperators : Bool
    nextLowPrimeFrontierIsAnalyticLocalGroupBridge : Bool

canonicalDuncanSwisherExponentDepthHighestAlphaBoundary :
  DuncanSwisherExponentDepthHighestAlphaBoundary
canonicalDuncanSwisherExponentDepthHighestAlphaBoundary = record
  { supportTheoremAlreadyClosed = true
  ; fullExponentDepthNowRetained = true
  ; modularThreeTermDepthNowRetained = true
  ; singletonExtraResidualDerived = true
  ; positiveGenusZeroExponentDerived = true
  ; geometricAndModularObserversShareConsumer = true
  ; supportExposedAsCoarserProjection = true
  ; p2p3ResidualsIsolated = true
  ; lowPrimeFullExponentRecoveredFromLocalSubgroupStructure = true
  ; lowPrimeEllipticStratumCollisionExposed = true
  ; residualIdentifiedWithSpecificLocalSimpleGroupFactor = false
  ; causalBridgeFromEllipticCollisionToResidualProved = false
  ; finiteMonsterPrimeLaneUsedForPgt3Proof = false
  ; nextPgt3FrontierIsExplicitModularFunctionOperators = true
  ; nextLowPrimeFrontierIsAnalyticLocalGroupBridge = true
  }
