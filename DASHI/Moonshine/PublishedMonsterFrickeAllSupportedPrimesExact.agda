module DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact where

------------------------------------------------------------------------
-- ALL-SUPPORTED-PRIME MONSTER / FRICKE WELD
--
-- This module composes two deliberately different published authority lanes:
--
--   p = 2,3 : explicit exceptional low-level Fricke genus-zero authority;
--   p >= 5  : Deligne--Rapoport / Fricke special-fibre geometry together with
--             Duncan--Ono/Ogg supersingular rationality.
--
-- The point is NOT to erase that source distinction.  It is to expose one
-- downstream theorem surface without reintroducing MonsterPrimeLane or the
-- finite under-72 genus table.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedLowPrimeFrickeGenusExact as Low
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as High
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Published
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector

------------------------------------------------------------------------
-- Proof-relevant source case.  The p>=5 branch retains its actual primality
-- and lower-bound witnesses rather than collapsing them into a Boolean tag.
------------------------------------------------------------------------

data SupportedPrimeFrickeCase : Set where
  exceptional2 : SupportedPrimeFrickeCase
  exceptional3 : SupportedPrimeFrickeCase
  primeAtLeast5 :
    (p : Nat) → Prime p → 5 ≤ p → SupportedPrimeFrickeCase

caseLevel : SupportedPrimeFrickeCase → Nat
caseLevel exceptional2 = 2
caseLevel exceptional3 = 3
caseLevel (primeAtLeast5 p prime ge5) = p

caseFrickeGenus : SupportedPrimeFrickeCase → Nat
caseFrickeGenus exceptional2 = Low.lowPrimeFrickeGenus Low.prime2
caseFrickeGenus exceptional3 = Low.lowPrimeFrickeGenus Low.prime3
caseFrickeGenus (primeAtLeast5 p prime ge5) =
  Selector.genericFrickeGenus (Published.publishedAuthorityAt p prime ge5)

caseMonsterDivides : SupportedPrimeFrickeCase → Set
caseMonsterDivides c = Monster.PrimeDividesMonsterOrder (caseLevel c)

------------------------------------------------------------------------
-- One theorem surface, provenance-preserving by constructor case.
------------------------------------------------------------------------

caseMonsterImpliesFrickeGenusZero :
  (c : SupportedPrimeFrickeCase) →
  caseMonsterDivides c →
  caseFrickeGenus c ≡ 0
caseMonsterImpliesFrickeGenusZero exceptional2 divides =
  Low.lowPrimeMonsterImpliesFrickeGenusZero Low.prime2 divides
caseMonsterImpliesFrickeGenusZero exceptional3 divides =
  Low.lowPrimeMonsterImpliesFrickeGenusZero Low.prime3 divides
caseMonsterImpliesFrickeGenusZero (primeAtLeast5 p prime ge5) divides =
  High.monsterPrimeImpliesFrickeGenusZero p prime ge5 divides

caseFrickeGenusZeroImpliesMonster :
  (c : SupportedPrimeFrickeCase) →
  caseFrickeGenus c ≡ 0 →
  caseMonsterDivides c
caseFrickeGenusZeroImpliesMonster exceptional2 genusZero =
  Low.lowPrimeFrickeGenusZeroImpliesMonster Low.prime2 genusZero
caseFrickeGenusZeroImpliesMonster exceptional3 genusZero =
  Low.lowPrimeFrickeGenusZeroImpliesMonster Low.prime3 genusZero
caseFrickeGenusZeroImpliesMonster (primeAtLeast5 p prime ge5) genusZero =
  High.frickeGenusZeroImpliesMonsterPrime p prime ge5 genusZero

caseMonsterIffFrickeGenusZero :
  (c : SupportedPrimeFrickeCase) →
  caseMonsterDivides c ↔ caseFrickeGenus c ≡ 0
caseMonsterIffFrickeGenusZero c =
  caseMonsterImpliesFrickeGenusZero c
  , caseFrickeGenusZeroImpliesMonster c

------------------------------------------------------------------------
-- Concrete exceptional regressions prove the low-prime branch is not a dead
-- interface around an imported Monster-prime list.
------------------------------------------------------------------------

prime2MonsterFrickeRegression :
  caseMonsterDivides exceptional2 ↔ caseFrickeGenus exceptional2 ≡ 0
prime2MonsterFrickeRegression = caseMonsterIffFrickeGenusZero exceptional2

prime3MonsterFrickeRegression :
  caseMonsterDivides exceptional3 ↔ caseFrickeGenus exceptional3 ≡ 0
prime3MonsterFrickeRegression = caseMonsterIffFrickeGenusZero exceptional3

record PublishedMonsterFrickeAllSupportedPrimesBoundary : Set where
  field
    p2Included : Bool
    p3Included : Bool
    pAtLeastFiveIncluded : Bool
    exceptionalAuthorityKeptSeparate : Bool
    MonsterPrimeLaneImported : Bool
    finiteUnder72FrickeTableImported : Bool
    oneDownstreamEquivalenceSurfaceConstructed : Bool
    arbitraryPrimeCaseExhaustionDerivedInternally : Bool

canonicalPublishedMonsterFrickeAllSupportedPrimesBoundary :
  PublishedMonsterFrickeAllSupportedPrimesBoundary
canonicalPublishedMonsterFrickeAllSupportedPrimesBoundary = record
  { p2Included = true
  ; p3Included = true
  ; pAtLeastFiveIncluded = true
  ; exceptionalAuthorityKeptSeparate = true
  ; MonsterPrimeLaneImported = false
  ; finiteUnder72FrickeTableImported = false
  ; oneDownstreamEquivalenceSurfaceConstructed = true
  ; arbitraryPrimeCaseExhaustionDerivedInternally = false
  }
