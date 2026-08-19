module DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused highest-alpha root for the post-support Monster exponent problem.
--
-- SOURCE:
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- This root deliberately sits ABOVE the already-closed prime-support theorem.
-- It asks what the EXPONENT v_p(|M|) remembers once
--
--   p | |M| <=> g(X_0^+(p)) = 0
--
-- is already known.
--
-- The answer now formalized is:
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
-- The same doubled Monster valuation is now explicitly exposed as a consumer of
-- TWO source-natural observers: supersingular geometry and the three modular
-- valuation contributions.  Support is a further coarse projection.
--
-- At p=2,3 the two Duncan--Swisher right-hand sides still agree, but miss the
-- actual Monster exponents by exact residuals 10 and 2.  Those residuals, not a
-- fake extension of the p>3 theorem, are the low-prime explanatory frontier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as Exponent
import DASHI.Moonshine.DuncanSwisherExponentFrickeGenusRefinementExact as Genus
import DASHI.Moonshine.DuncanSwisherModularValuationDepthMechanismExact as Modular
import DASHI.Moonshine.DuncanSwisherExponentObserverFactorizationExact as Observers
import DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact as LowPrime
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
-- Low-prime residuals are explicit rather than hidden under p>3 notation.
------------------------------------------------------------------------

p2UnexplainedResidualRegression : LowPrime.lowPrimeResidual LowPrime.low2 ≡ 10
p2UnexplainedResidualRegression = LowPrime.p2ResidualIsTen

p3UnexplainedResidualRegression : LowPrime.lowPrimeResidual LowPrime.low3 ≡ 2
p3UnexplainedResidualRegression = LowPrime.p3ResidualIsTwo

------------------------------------------------------------------------
-- Boundary: for p>3 the next explanatory frontier is BELOW the valuation
-- formulas: construct the modular functions / U_p / rigidity mechanism rather
-- than importing Theorems 1.1/1.2 only as numerical laws.  For p=2,3 the
-- frontier is the common exceptional residual itself.
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
    finiteMonsterPrimeLaneUsedForPgt3Proof : Bool
    nextFrontierIsExplicitModularFunctionOperators : Bool
    lowPrimeResidualMechanismStillOpen : Bool

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
  ; finiteMonsterPrimeLaneUsedForPgt3Proof = false
  ; nextFrontierIsExplicitModularFunctionOperators = true
  ; lowPrimeResidualMechanismStillOpen = true
  }
