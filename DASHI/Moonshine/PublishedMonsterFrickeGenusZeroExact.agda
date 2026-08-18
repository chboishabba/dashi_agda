module DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact where

------------------------------------------------------------------------
-- TABLE-FREE MONSTER / FRICKE GENUS-ZERO WELD FOR p >= 5
--
-- Import only the Duncan--Ono Monster-prime / supersingular-rationality
-- equivalence, then compose it with the independently imported-and-derived
-- Deligne--Rapoport/Fricke geometric selector.
--
-- Thus the final statement
--
--   p divides |M|  iff  g(X_0^+(p)) = 0
--
-- is DERIVED here; it is not the imported authority itself, and no repository
-- MonsterPrimeLane / SSP15 finite table participates in the proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.DuncanOnoMonsterSupersingularStandardAuthority as DuncanOno
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Published
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector

monsterPrimeImpliesFrickeGenusZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p →
  Selector.genericFrickeGenus (Published.publishedAuthorityAt p prime ge5) ≡ 0
monsterPrimeImpliesFrickeGenusZero p prime ge5 divides =
  let
    monsterIffFixed =
      DuncanOno.duncanOnoMonsterPrimeIffCoarseSupersingularFullyFixed
        p prime ge5
    fixedIffGenus =
      Published.publishedFrobeniusFullyFixedIffFrickeGenusZero
        p prime ge5
  in
  proj₁ fixedIffGenus (proj₁ monsterIffFixed divides)

frickeGenusZeroImpliesMonsterPrime :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Selector.genericFrickeGenus (Published.publishedAuthorityAt p prime ge5) ≡ 0 →
  Monster.PrimeDividesMonsterOrder p
frickeGenusZeroImpliesMonsterPrime p prime ge5 genusZero =
  let
    monsterIffFixed =
      DuncanOno.duncanOnoMonsterPrimeIffCoarseSupersingularFullyFixed
        p prime ge5
    fixedIffGenus =
      Published.publishedFrobeniusFullyFixedIffFrickeGenusZero
        p prime ge5
  in
  proj₂ monsterIffFixed (proj₂ fixedIffGenus genusZero)

monsterPrimeIffFrickeGenusZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Published.publishedAuthorityAt p prime ge5) ≡ 0
monsterPrimeIffFrickeGenusZero p prime ge5 =
  monsterPrimeImpliesFrickeGenusZero p prime ge5
  , frickeGenusZeroImpliesMonsterPrime p prime ge5

record PublishedMonsterFrickeGenusZeroBoundary : Set where
  field
    MonsterPrimeLaneTableUsed : Bool
    actualMonsterOrderDivisibilityUsed : Bool
    duncanOnoSupersingularEquivalenceImported : Bool
    deligneRapoportGenusSelectorUsed : Bool
    monsterPrimeIffFrickeGenusZeroDerived : Bool
    converseConceptualMechanismProvedBeyondImportedOggTheorem : Bool
    primesTwoAndThreeIncluded : Bool

canonicalPublishedMonsterFrickeGenusZeroBoundary :
  PublishedMonsterFrickeGenusZeroBoundary
canonicalPublishedMonsterFrickeGenusZeroBoundary = record
  { MonsterPrimeLaneTableUsed = false
  ; actualMonsterOrderDivisibilityUsed = true
  ; duncanOnoSupersingularEquivalenceImported = true
  ; deligneRapoportGenusSelectorUsed = true
  ; monsterPrimeIffFrickeGenusZeroDerived = true
  ; converseConceptualMechanismProvedBeyondImportedOggTheorem = false
  ; primesTwoAndThreeIncluded = false
  }
