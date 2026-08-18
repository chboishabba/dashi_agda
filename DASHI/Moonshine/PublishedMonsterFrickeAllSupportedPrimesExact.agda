module DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact where

------------------------------------------------------------------------
-- ALL-PRIME MONSTER / FRICKE WELD
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
--
-- The stdlib primality decision is used only to discharge the impossible
-- natural-number cases 0,1,4.  Consequently every proof-relevant Prime p is
-- internally classified into exactly one source lane: 2, 3, or p >= 5.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Primality using (Prime)
import Data.Nat.Primality as Primality
open import Relation.Nullary.Decidable using (from-no)

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
-- Internal exhaustion of Prime p into 2, 3, or >=5.
------------------------------------------------------------------------

notPrime0 : Prime 0 → ⊥
notPrime0 = from-no (Primality.prime? 0)

notPrime1 : Prime 1 → ⊥
notPrime1 = from-no (Primality.prime? 1)

notPrime4 : Prime 4 → ⊥
notPrime4 = from-no (Primality.prime? 4)

classifyPrime : (p : Nat) → Prime p → SupportedPrimeFrickeCase
classifyPrime 0 prime = ⊥-elim (notPrime0 prime)
classifyPrime 1 prime = ⊥-elim (notPrime1 prime)
classifyPrime 2 prime = exceptional2
classifyPrime 3 prime = exceptional3
classifyPrime 4 prime = ⊥-elim (notPrime4 prime)
classifyPrime (suc (suc (suc (suc (suc n))))) prime =
  primeAtLeast5 (5 + n) prime (NatP.m≤m+n 5 n)

classifiedLevelIsOriginal :
  (p : Nat) → (prime : Prime p) →
  caseLevel (classifyPrime p prime) ≡ p
classifiedLevelIsOriginal 0 prime = ⊥-elim (notPrime0 prime)
classifiedLevelIsOriginal 1 prime = ⊥-elim (notPrime1 prime)
classifiedLevelIsOriginal 2 prime = refl
classifiedLevelIsOriginal 3 prime = refl
classifiedLevelIsOriginal 4 prime = ⊥-elim (notPrime4 prime)
classifiedLevelIsOriginal (suc (suc (suc (suc (suc n))))) prime = refl

------------------------------------------------------------------------
-- Arbitrary-prime public surface.
------------------------------------------------------------------------

primeFrickeGenus : (p : Nat) → Prime p → Nat
primeFrickeGenus p prime = caseFrickeGenus (classifyPrime p prime)

primeMonsterImpliesFrickeGenusZero :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  primeFrickeGenus p prime ≡ 0
primeMonsterImpliesFrickeGenusZero 0 prime divides = ⊥-elim (notPrime0 prime)
primeMonsterImpliesFrickeGenusZero 1 prime divides = ⊥-elim (notPrime1 prime)
primeMonsterImpliesFrickeGenusZero 2 prime divides =
  caseMonsterImpliesFrickeGenusZero exceptional2 divides
primeMonsterImpliesFrickeGenusZero 3 prime divides =
  caseMonsterImpliesFrickeGenusZero exceptional3 divides
primeMonsterImpliesFrickeGenusZero 4 prime divides = ⊥-elim (notPrime4 prime)
primeMonsterImpliesFrickeGenusZero
  (suc (suc (suc (suc (suc n))))) prime divides =
  caseMonsterImpliesFrickeGenusZero
    (primeAtLeast5 (5 + n) prime (NatP.m≤m+n 5 n))
    divides

primeFrickeGenusZeroImpliesMonster :
  (p : Nat) → (prime : Prime p) →
  primeFrickeGenus p prime ≡ 0 →
  Monster.PrimeDividesMonsterOrder p
primeFrickeGenusZeroImpliesMonster 0 prime genusZero = ⊥-elim (notPrime0 prime)
primeFrickeGenusZeroImpliesMonster 1 prime genusZero = ⊥-elim (notPrime1 prime)
primeFrickeGenusZeroImpliesMonster 2 prime genusZero =
  caseFrickeGenusZeroImpliesMonster exceptional2 genusZero
primeFrickeGenusZeroImpliesMonster 3 prime genusZero =
  caseFrickeGenusZeroImpliesMonster exceptional3 genusZero
primeFrickeGenusZeroImpliesMonster 4 prime genusZero = ⊥-elim (notPrime4 prime)
primeFrickeGenusZeroImpliesMonster
  (suc (suc (suc (suc (suc n))))) prime genusZero =
  caseFrickeGenusZeroImpliesMonster
    (primeAtLeast5 (5 + n) prime (NatP.m≤m+n 5 n))
    genusZero

primeMonsterIffFrickeGenusZero :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ primeFrickeGenus p prime ≡ 0
primeMonsterIffFrickeGenusZero p prime =
  primeMonsterImpliesFrickeGenusZero p prime
  , primeFrickeGenusZeroImpliesMonster p prime

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
  ; arbitraryPrimeCaseExhaustionDerivedInternally = true
  }
