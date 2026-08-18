module DASHI.Moonshine.DuncanSwisherMonsterFrobeniusFixedExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schemas de modules de courbes elliptiques", LNM 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- DASHI CONTRIBUTION
--
-- Remove the genus coordinate from the modern p>=5 Monster-support statement
-- and expose the actual geometric observer selected by the proof:
--
--   p divides |M|
--      <=>
--   coarse supersingular Frobenius is pointwise fixed.
--
-- The forward/backward implications are NOT obtained from the older Ogg /
-- Duncan--Ono support equivalence.  They compose:
--
--   Duncan--Swisher exponent support
--       <=> zero Frobenius-pair defect
--
-- with the independently derived Deligne--Rapoport/Fricke geometry
--
--   zero Frobenius-pair defect
--       <=> g(X_0^+(p)) = 0
--       <=> pointwise-fixed coarse Frobenius.
--
-- Thus the surviving finite residual coordinate is literally the nonfixed
-- Frobenius-pair count.  No MonsterPrimeLane enumeration and no finite Ogg table
-- enters this p>=5 theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.DuncanSwisherMonsterFrickeGe5Exact as DS
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- Direct Monster-support <=> geometric fixedness.
------------------------------------------------------------------------

monsterDividesIffCoarseFrobeniusFullyFixed :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Fricke.PublishedFrobeniusFullyFixed p prime ge5
monsterDividesIffCoarseFrobeniusFullyFixed p prime ge5 =
  let
    supportGenus = DS.duncanSwisherMonsterIffFrickeGenusZero p prime ge5
    fixedGenus = Fricke.publishedFrobeniusFullyFixedIffFrickeGenusZero p prime ge5
  in
  (λ divides → proj₂ fixedGenus (proj₁ supportGenus divides))
  ,
  (λ fixed → proj₂ supportGenus (proj₁ fixedGenus fixed))

monsterDividesImpliesCoarseFrobeniusFullyFixed :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p →
  Fricke.PublishedFrobeniusFullyFixed p prime ge5
monsterDividesImpliesCoarseFrobeniusFullyFixed p prime ge5 =
  proj₁ (monsterDividesIffCoarseFrobeniusFullyFixed p prime ge5)

coarseFrobeniusFullyFixedImpliesMonsterDivides :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Fricke.PublishedFrobeniusFullyFixed p prime ge5 →
  Monster.PrimeDividesMonsterOrder p
coarseFrobeniusFullyFixedImpliesMonsterDivides p prime ge5 =
  proj₂ (monsterDividesIffCoarseFrobeniusFullyFixed p prime ge5)

------------------------------------------------------------------------
-- Equivalent residual formulation: Monster support is exactly vanishing of
-- the nonfixed Frobenius-pair coordinate on the prime-pinned special fibre.
------------------------------------------------------------------------

monsterDividesIffFrobeniusPairResidualZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ DR.pairedCount
      (Selector.supersingularFrobenius
        (Fricke.publishedAuthorityAt p prime ge5)) ≡ 0
monsterDividesIffFrobeniusPairResidualZero =
  DS.monsterDividesIffZeroPairDefect

pairResidualZeroIffFullyFixed :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  DR.pairedCount
      (Selector.supersingularFrobenius
        (Fricke.publishedAuthorityAt p prime ge5)) ≡ 0
  ↔ Fricke.PublishedFrobeniusFullyFixed p prime ge5
pairResidualZeroIffFullyFixed p prime ge5 =
  let
    pairGenus = DS.zeroPairDefectIffFrickeGenusZero p prime ge5
    fixedGenus = Fricke.publishedFrobeniusFullyFixedIffFrickeGenusZero p prime ge5
  in
  (λ pairZero → proj₂ fixedGenus (proj₁ pairGenus pairZero))
  ,
  (λ fixed → proj₂ pairGenus (proj₁ fixedGenus fixed))

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DuncanSwisherMonsterFrobeniusFixedBoundary : Set where
  field
    DuncanSwisherExponentSupportConsumed : Bool
    DeligneRapoportFrickeGeometryConsumed : Bool
    internalPrimePinnedToRequestedPrime : Bool
    monsterSupportEqualsZeroPairResidual : Bool
    monsterSupportEqualsPointwiseFixedFrobenius : Bool
    oldDuncanOnoEquivalenceImportedHere : Bool
    finiteOggTableImportedHere : Bool
    MonsterPrimeLaneImportedHere : Bool

canonicalDuncanSwisherMonsterFrobeniusFixedBoundary :
  DuncanSwisherMonsterFrobeniusFixedBoundary
canonicalDuncanSwisherMonsterFrobeniusFixedBoundary = record
  { DuncanSwisherExponentSupportConsumed = true
  ; DeligneRapoportFrickeGeometryConsumed = true
  ; internalPrimePinnedToRequestedPrime = true
  ; monsterSupportEqualsZeroPairResidual = true
  ; monsterSupportEqualsPointwiseFixedFrobenius = true
  ; oldDuncanOnoEquivalenceImportedHere = false
  ; finiteOggTableImportedHere = false
  ; MonsterPrimeLaneImportedHere = false
  }
