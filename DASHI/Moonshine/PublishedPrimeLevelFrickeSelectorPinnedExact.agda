module DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact where

------------------------------------------------------------------------
-- PRIME-PINNED GLOBAL SELECTOR
--
-- Consume only the strengthened published authority whose internal modular
-- prime is proved equal to the requested p.  All selector equations are then
-- derived by the existing Deligne--Rapoport/Fricke theorem chain.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.PrimeLevelDeligneRapoportStandardAuthorityAtExact as Authority
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

publishedAuthorityAt :
  (p : Nat) → Prime p → 5 ≤ p → Selector.PrimeLevelFrickeSpecialFibreAuthority
publishedAuthorityAt p prime ge5 =
  Authority.authority (Authority.publishedPrimeLevelAuthorityAt p prime ge5)

publishedAuthorityReallyAtRequestedPrime :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  DR.prime (Selector.supersingularFrobenius (publishedAuthorityAt p prime ge5)) ≡ p
publishedAuthorityReallyAtRequestedPrime p prime ge5 =
  Authority.authorityPrimeIsRequestedPrime
    (Authority.publishedPrimeLevelAuthorityAt p prime ge5)

publishedPairDefectEqualsFrickeGenus :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Selector.genericFrickeGenus (publishedAuthorityAt p prime ge5)
  ≡ DR.pairedCount
      (Selector.supersingularFrobenius (publishedAuthorityAt p prime ge5))
publishedPairDefectEqualsFrickeGenus p prime ge5 =
  Selector.genericFrickeGenusEqualsDeclaredPairDefect
    (publishedAuthorityAt p prime ge5)

PublishedFrobeniusFullyFixed :
  (p : Nat) → Prime p → 5 ≤ p → Set
PublishedFrobeniusFullyFixed p prime ge5 =
  Selector.GeometricallyFullyFixed (publishedAuthorityAt p prime ge5)

publishedFrobeniusFullyFixedIffFrickeGenusZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  PublishedFrobeniusFullyFixed p prime ge5
  ↔ Selector.genericFrickeGenus (publishedAuthorityAt p prime ge5) ≡ 0
publishedFrobeniusFullyFixedIffFrickeGenusZero p prime ge5 =
  Selector.frobeniusFullyFixedIffGenericFrickeGenusZero
    (publishedAuthorityAt p prime ge5)

record PublishedPrimePinnedSelectorBoundary : Set where
  field
    internalPrimePinnedToRequestedPrime : Bool
    pairDefectEqualsGenusDerived : Bool
    allFixedIffGenusZeroDerived : Bool
    finiteOggTableUsed : Bool
    monsterLabelUsed : Bool

canonicalPublishedPrimePinnedSelectorBoundary :
  PublishedPrimePinnedSelectorBoundary
canonicalPublishedPrimePinnedSelectorBoundary = record
  { internalPrimePinnedToRequestedPrime = true
  ; pairDefectEqualsGenusDerived = true
  ; allFixedIffGenusZeroDerived = true
  ; finiteOggTableUsed = false
  ; monsterLabelUsed = false
  }
