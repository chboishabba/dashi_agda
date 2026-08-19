module DASHI.Moonshine.PublishedMonsterFrickeHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused table-free Monster/Fricke root for EVERY prime p.
--
-- PRIME SUPPORT now has two distinct modern mechanisms:
--
--   FORWARD  p | |M| -> g(X_0^+(p)) = 0
--     global Conway--Norton / Borcherds genus-zero Moonshine theorem
--       +
--     p-specific prime-class identification Gamma_g = Gamma_0(p)^+.
--
--   CONVERSE g(X_0^+(p)) = 0 -> p | |M|
--     Duncan--Swisher Theorem 1.2 (2026): for p>3, Monster p-adic exponent
--     support is equivalent to emptiness of the non-rational supersingular
--     locus; the existing Deligne--Rapoport geometry identifies that with zero
--     Fricke pair defect.  The exceptional primes 2,3 are handled separately.
--
-- The forward authority is FACTORED: genus zero is imported globally once; the
-- only p-indexed classification input is the selected prime-order class and the
-- exact equality of its Moonshine group with Gamma_0(p)^+.
--
-- QUANTITATIVE DEPTH is now public too.  For p>3 the full Duncan--Swisher
-- theorem retains v_p(|M|), the rational/quadratic supersingular stratum, m_p,
-- and the three modular valuation contributions.  Two source-natural observers
-- compute the same doubled valuation consumer without being identified:
--
--   supersingular geometry  --->  2 v_p(|M|)
--   modular valuations      --->  2 v_p(|M|).
--
-- Ogg/Fricke support is a further coarse projection of this depth.  For p=2,3
-- the two Duncan--Swisher right-hand sides agree but miss the actual Monster
-- exponents by residuals 10 and 2 respectively; those residual mechanisms are
-- kept explicit rather than hidden under a false extension of the p>3 theorem.
--
-- The older Duncan--Ono/Ogg supersingular support equivalence remains only an
-- independent historical/cross-check route.  No MonsterPrimeLane / SSP15
-- enumeration and no finite under-72 Fricke table participates in the primary
-- arbitrary-prime support theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as HistoricalGe5
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as All
import DASHI.Moonshine.MonsterPrimeMoonshineFrickeFactoredAuthorityExact as Moonshine
import DASHI.Moonshine.MonsterPrimeMoonshineFrobeniusForwardExact as MoonshineFrob
import DASHI.Moonshine.DuncanSwisherMonsterFrickeAllPrimesExact as DSAll
import DASHI.Moonshine.MonsterFrickeModernDirectionalMechanismExact as Modern
import DASHI.Moonshine.DuncanSwisherMonsterFrobeniusFixedExact as FrobeniusModern
import DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything as Depth
import DASHI.Moonshine.DuncanSwisherExponentObserverFactorizationExact as DepthObservers
import DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact as LowPrime

------------------------------------------------------------------------
-- Primary arbitrary-prime theorem: moonshine forward, exponent-support
-- converse.
------------------------------------------------------------------------

monsterFrickeAllPrimeRegression :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ All.primeFrickeGenus p prime ≡ 0
monsterFrickeAllPrimeRegression =
  Modern.monsterPrimeIffFrickeGenusZeroModern

moonshineForwardRegression :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  All.primeFrickeGenus p prime ≡ 0
moonshineForwardRegression =
  Modern.monsterPrimeImpliesFrickeGenusZeroByMoonshine

exponentSupportConverseRegression :
  (p : Nat) → (prime : Prime p) →
  All.primeFrickeGenus p prime ≡ 0 →
  Monster.PrimeDividesMonsterOrder p
exponentSupportConverseRegression =
  Modern.frickeGenusZeroImpliesMonsterPrimeByExponentSupport

------------------------------------------------------------------------
-- p>=5 geometric observer forms.
------------------------------------------------------------------------

monsterIffCoarseFrobeniusFixedRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Fricke.PublishedFrobeniusFullyFixed p prime ge5
monsterIffCoarseFrobeniusFixedRegression =
  FrobeniusModern.monsterDividesIffCoarseFrobeniusFullyFixed

monsterIffZeroFrobeniusPairResidualRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ DR.pairedCount
      (Selector.supersingularFrobenius
        (Fricke.publishedAuthorityAt p prime ge5)) ≡ 0
monsterIffZeroFrobeniusPairResidualRegression =
  FrobeniusModern.monsterDividesIffFrobeniusPairResidualZero

zeroPairResidualIffFixedRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  DR.pairedCount
      (Selector.supersingularFrobenius
        (Fricke.publishedAuthorityAt p prime ge5)) ≡ 0
  ↔ Fricke.PublishedFrobeniusFullyFixed p prime ge5
zeroPairResidualIffFixedRegression =
  FrobeniusModern.pairResidualZeroIffFullyFixed

-- Direct conceptual FORWARD route: no Duncan--Swisher in the theorem owner.
moonshineDirectlyForcesCoarseFrobeniusFixedRegression :
  (n : Nat) → (prime : Prime (5 + n)) →
  Monster.PrimeDividesMonsterOrder (5 + n) →
  Fricke.PublishedFrobeniusFullyFixed
    (5 + n) prime (NatP.m≤m+n 5 n)
moonshineDirectlyForcesCoarseFrobeniusFixedRegression =
  MoonshineFrob.monsterPrimeImpliesCoarseFrobeniusFixedByMoonshine

------------------------------------------------------------------------
-- Quantitative depth above support.
------------------------------------------------------------------------

fullExponentDepthPublicRegression :
  Depth.fullExponentDepthNowRetained
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
fullExponentDepthPublicRegression = refl

geometricAndModularDepthShareConsumerRegression :
  Depth.geometricAndModularObserversShareConsumer
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
geometricAndModularDepthShareConsumerRegression = refl

supportIsCoarserThanGeometricDepthRegression :
  Depth.supportExposedAsCoarserProjection
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
supportIsCoarserThanGeometricDepthRegression = refl

p2ExceptionalResidualRegression : LowPrime.lowPrimeResidual LowPrime.low2 ≡ 10
p2ExceptionalResidualRegression = LowPrime.p2ResidualIsTen

p3ExceptionalResidualRegression : LowPrime.lowPrimeResidual LowPrime.low3 ≡ 2
p3ExceptionalResidualRegression = LowPrime.p3ResidualIsTwo

------------------------------------------------------------------------
-- Independent routes remain available for regression/cross-checking.
------------------------------------------------------------------------

duncanSwisherAlsoProvesForwardRegression :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  All.primeFrickeGenus p prime ≡ 0
duncanSwisherAlsoProvesForwardRegression =
  Modern.duncanSwisherAlsoProvesForward

historicalDuncanOnoGe5Regression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
historicalDuncanOnoGe5Regression =
  HistoricalGe5.monsterPrimeIffFrickeGenusZero

------------------------------------------------------------------------
-- Promotion / explanatory boundaries.
------------------------------------------------------------------------

primaryProofImportsDuncanOnoSupportRegression :
  Modern.DuncanOnoSupportEquivalenceImported
    Modern.canonicalMonsterFrickeModernDirectionalBoundary ≡ false
primaryProofImportsDuncanOnoSupportRegression = refl

forwardUsesMoonshineRegression :
  Modern.forwardMechanismIsMoonshine
    Modern.canonicalMonsterFrickeModernDirectionalBoundary ≡ true
forwardUsesMoonshineRegression = refl

forwardAuthorityFactoredRegression :
  Modern.forwardGenusZeroAuthorityFactoredFromPrimeSelection
    Modern.canonicalMonsterFrickeModernDirectionalBoundary ≡ true
forwardAuthorityFactoredRegression = refl

forwardExactGroupEqualityLoadBearingRegression :
  Modern.forwardExactClassGroupEqualityIsLoadBearing
    Modern.canonicalMonsterFrickeModernDirectionalBoundary ≡ true
forwardExactGroupEqualityLoadBearingRegression = refl

converseUsesExponentSupportRegression :
  Modern.converseMechanismIsExponentSupport
    Modern.canonicalMonsterFrickeModernDirectionalBoundary ≡ true
converseUsesExponentSupportRegression = refl

globalMoonshineGenusZeroImportedOnceRegression :
  Moonshine.globalConwayNortonGenusZeroAuthorityImportedOnce
    Moonshine.canonicalMonsterPrimeMoonshineFrickeFactoredBoundary ≡ true
globalMoonshineGenusZeroImportedOnceRegression = refl

perPrimeGenusZeroNotReimportedRegression :
  Moonshine.perPrimeGenusZeroImportedSeparately
    Moonshine.canonicalMonsterPrimeMoonshineFrickeFactoredBoundary ≡ false
perPrimeGenusZeroNotReimportedRegression = refl

directForwardAvoidsDuncanSwisherRegression :
  MoonshineFrob.DuncanSwisherSupportImportedHere
    MoonshineFrob.canonicalMonsterPrimeMoonshineFrobeniusForwardBoundary ≡ false
directForwardAvoidsDuncanSwisherRegression = refl

noFiniteMonsterLaneTableRegression :
  All.MonsterPrimeLaneImported
    All.canonicalPublishedMonsterFrickeAllSupportedPrimesBoundary ≡ false
noFiniteMonsterLaneTableRegression = refl

noFiniteUnder72FrickeTableRegression :
  All.finiteUnder72FrickeTableImported
    All.canonicalPublishedMonsterFrickeAllSupportedPrimesBoundary ≡ false
noFiniteUnder72FrickeTableRegression = refl

arbitraryPrimeExhaustionRegression :
  All.arbitraryPrimeCaseExhaustionDerivedInternally
    All.canonicalPublishedMonsterFrickeAllSupportedPrimesBoundary ≡ true
arbitraryPrimeExhaustionRegression = refl

duncanSwisherAllPrimeSupportRegression :
  DSAll.arbitraryPrimeSupportEquivalenceDerived
    DSAll.canonicalDuncanSwisherMonsterFrickeAllPrimesBoundary ≡ true
duncanSwisherAllPrimeSupportRegression = refl

directFrobeniusRouteAvoidsOldDuncanOnoRegression :
  FrobeniusModern.oldDuncanOnoEquivalenceImportedHere
    FrobeniusModern.canonicalDuncanSwisherMonsterFrobeniusFixedBoundary ≡ false
directFrobeniusRouteAvoidsOldDuncanOnoRegression = refl
