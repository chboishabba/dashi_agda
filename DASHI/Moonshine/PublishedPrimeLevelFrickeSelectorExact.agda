module DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorExact where

------------------------------------------------------------------------
-- GLOBAL TABLE-FREE SELECTOR FROM THE PUBLISHED PRIME-LEVEL GEOMETRY
--
-- This file consumes PrimeLevelDeligneRapoportStandardAuthority and derives
-- every selector statement through the theorem-producing local machinery.
-- No finite Fricke/Ogg control table and no Monster prime label is imported.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.PrimeLevelDeligneRapoportStandardAuthority as Authority
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

publishedAuthority :
  (p : Nat) → Prime p → 5 ≤ p → Selector.PrimeLevelFrickeSpecialFibreAuthority
publishedAuthority = Authority.publishedPrimeLevelFrickeAuthority

publishedGenericFrickeGenusEqualsPairDefect :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Selector.genericFrickeGenus (publishedAuthority p prime ge5)
  ≡ DR.pairedCount
      (Selector.supersingularFrobenius (publishedAuthority p prime ge5))
publishedGenericFrickeGenusEqualsPairDefect p prime ge5 =
  Selector.genericFrickeGenusEqualsDeclaredPairDefect
    (publishedAuthority p prime ge5)

PublishedGeometricallyFullyFixed :
  (p : Nat) → Prime p → 5 ≤ p → Set
PublishedGeometricallyFullyFixed p prime ge5 =
  Selector.GeometricallyFullyFixed (publishedAuthority p prime ge5)

publishedFrobeniusFullyFixedIffFrickeGenusZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  PublishedGeometricallyFullyFixed p prime ge5
  ↔ Selector.genericFrickeGenus (publishedAuthority p prime ge5) ≡ 0
publishedFrobeniusFullyFixedIffFrickeGenusZero p prime ge5 =
  Selector.frobeniusFullyFixedIffGenericFrickeGenusZero
    (publishedAuthority p prime ge5)

record PublishedPrimeLevelFrickeSelectorBoundary : Set where
  field
    standardGeometryAuthorityConsumed : Bool
    sameObjectSpecialFibreUsed : Bool
    completedLocalNodesUsed : Bool
    flatHilbertGenusTransportUsed : Bool
    pairDefectEqualsGenusDerived : Bool
    allFixedIffGenusZeroDerived : Bool
    finiteOggControlTableUsed : Bool
    monsterPrimeSetUsed : Bool

canonicalPublishedPrimeLevelFrickeSelectorBoundary :
  PublishedPrimeLevelFrickeSelectorBoundary
canonicalPublishedPrimeLevelFrickeSelectorBoundary = record
  { standardGeometryAuthorityConsumed = true
  ; sameObjectSpecialFibreUsed = true
  ; completedLocalNodesUsed = true
  ; flatHilbertGenusTransportUsed = true
  ; pairDefectEqualsGenusDerived = true
  ; allFixedIffGenusZeroDerived = true
  ; finiteOggControlTableUsed = false
  ; monsterPrimeSetUsed = false
  }
