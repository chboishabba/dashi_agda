module DASHI.Moonshine.PublishedMonsterFrickeHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused table-free Monster/Fricke root for EVERY prime p.
--
-- The primary equivalence now has two distinct modern mechanisms:
--
--   FORWARD  p | |M| -> g(X_0^+(p)) = 0
--     Conway--Norton / Borcherds monstrous moonshine: the relevant prime-order
--     Monster class has moonshine group Gamma_0(p)^+, hence genus zero.
--
--   CONVERSE g(X_0^+(p)) = 0 -> p | |M|
--     Duncan--Swisher Theorem 1.2 (2026): for p>3, Monster p-adic exponent
--     support is equivalent to emptiness of the non-rational supersingular
--     locus; the existing Deligne--Rapoport geometry identifies that with zero
--     Fricke pair defect.  The exceptional primes 2,3 are handled separately.
--
-- The older Duncan--Ono/Ogg supersingular SUPPORT equivalence is no longer
-- imported by this primary all-prime proof.  It remains an independent
-- historical/cross-check route elsewhere in the repository.
--
-- No MonsterPrimeLane / SSP15 enumeration and no finite under-72 Fricke table
-- participates in the arbitrary-prime theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as HistoricalGe5
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as All
import DASHI.Moonshine.MonsterPrimeMoonshineFrickeStandardAuthorityExact as Moonshine
import DASHI.Moonshine.DuncanSwisherMonsterFrickeAllPrimesExact as DSAll
import DASHI.Moonshine.MonsterFrickeModernDirectionalMechanismExact as Modern

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

converseUsesExponentSupportRegression :
  Modern.converseMechanismIsExponentSupport
    Modern.canonicalMonsterFrickeModernDirectionalBoundary ≡ true
converseUsesExponentSupportRegression = refl

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

moonshineGroupDatumReusedRegression :
  Moonshine.existingMoonshineGroupDatumReused
    Moonshine.canonicalMonsterPrimeMoonshineFrickeAuthorityBoundary ≡ true
moonshineGroupDatumReusedRegression = refl

duncanSwisherAllPrimeSupportRegression :
  DSAll.arbitraryPrimeSupportEquivalenceDerived
    DSAll.canonicalDuncanSwisherMonsterFrickeAllPrimesBoundary ≡ true
duncanSwisherAllPrimeSupportRegression = refl
