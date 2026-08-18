module DASHI.Moonshine.PublishedMonsterFrickeHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused table-free Monster/Ogg/Fricke root for EVERY prime p.
--
-- The final equivalence now has DIRECTIONAL proof provenance:
--
--   FORWARD  p | |M| -> g(X_0^+(p)) = 0
--     uses Conway--Norton / Borcherds monstrous moonshine: a prime-order
--     Monster class has moonshine group Gamma_0(p)^+, whose McKay--Thompson
--     series is a Hauptmodul.
--
--   CONVERSE g(X_0^+(p)) = 0 -> p | |M|
--     still uses the Ogg / Duncan--Ono classification-equivalence route.
--
-- Thus moonshine now explains the PRESENCE of all Monster prime divisors in
-- Ogg's genus-zero set without passing through supersingular rationality.  It
-- does not yet explain why the genus-zero set has no additional primes.
--
-- Prime provenance remains split underneath the arbitrary-prime genus carrier:
--   p = 2,3 use explicit classical low-level Fricke genus-zero authority;
--   p >= 5 uses prime-level Deligne--Rapoport/Fricke special-fibre geometry.
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
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as Ge5
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as All
import DASHI.Moonshine.MonsterPrimeMoonshineFrickeStandardAuthorityExact as Moonshine
import DASHI.Moonshine.MonsterFrickeDirectionalMechanismExact as Directional

------------------------------------------------------------------------
-- Primary arbitrary-prime theorem: moonshine forward, Ogg converse.
------------------------------------------------------------------------

monsterFrickeAllPrimeRegression :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ All.primeFrickeGenus p prime ≡ 0
monsterFrickeAllPrimeRegression =
  Directional.monsterPrimeIffFrickeGenusZeroDirectional

moonshineForwardRegression :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  All.primeFrickeGenus p prime ≡ 0
moonshineForwardRegression =
  Directional.monsterPrimeImpliesFrickeGenusZeroConceptually

oggConverseRegression :
  (p : Nat) → (prime : Prime p) →
  All.primeFrickeGenus p prime ≡ 0 →
  Monster.PrimeDividesMonsterOrder p
oggConverseRegression =
  Directional.frickeGenusZeroImpliesMonsterPrimeByOgg

------------------------------------------------------------------------
-- The p >= 5 supersingular/DR lane remains available as an independent second
-- proof of the forward direction and as the current converse authority.
------------------------------------------------------------------------

monsterFrickeGe5Regression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
monsterFrickeGe5Regression = Ge5.monsterPrimeIffFrickeGenusZero

------------------------------------------------------------------------
-- Promotion / explanatory boundaries.
------------------------------------------------------------------------

forwardUsesSupersingularRationalityRegression :
  Directional.forwardUsesSupersingularRationality
    Directional.canonicalMonsterFrickeDirectionalMechanismBoundary ≡ false
forwardUsesSupersingularRationalityRegression = refl

forwardUsesMoonshineRegression :
  Directional.forwardUsesMonstrousMoonshine
    Directional.canonicalMonsterFrickeDirectionalMechanismBoundary ≡ true
forwardUsesMoonshineRegression = refl

absenceOfExtraOggPrimesStillOpenRegression :
  Directional.absenceOfExtraGenusZeroPrimesExplainedByMoonshine
    Directional.canonicalMonsterFrickeDirectionalMechanismBoundary ≡ false
absenceOfExtraOggPrimesStillOpenRegression = refl

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

converseNotOversoldRegression :
  Directional.converseExplainedByMoonshineHere
    Directional.canonicalMonsterFrickeDirectionalMechanismBoundary ≡ false
converseNotOversoldRegression = refl
