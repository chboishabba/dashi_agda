module DASHI.Moonshine.DuncanSwisherMonsterFrickeGe5Exact where

------------------------------------------------------------------------
-- p >= 5 MONSTER / FRICKE SUPPORT FROM THE 2026 EXPONENT THEOREM
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Combine the arbitrary-prime-above-three support consequence of Theorem 1.2
-- with the independently constructed Deligne--Rapoport/Fricke geometry.
--
-- Duncan--Swisher side:
--   p | |M| <=> the non-rational supersingular locus S_p^2 is empty.
--
-- Existing geometric side:
--   |S_p^2| = 2*d_p,
--   d_p = g(X_0^+(p)).
--
-- Hence for every p >= 5 the full Monster/Fricke support equivalence follows
-- from the stronger p-adic exponent theorem.  No MonsterPrimeLane enumeration
-- and no finite Ogg/under-72 table is consumed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.DuncanSwisherMonsterSupportStandardAuthorityExact as DS
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- Support is first identified with zero Frobenius pair defect.
------------------------------------------------------------------------

monsterDividesIffZeroPairDefect :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ DR.pairedCount
      (Selector.supersingularFrobenius
        (Fricke.publishedAuthorityAt p prime ge5)) ≡ 0
monsterDividesIffZeroPairDefect p prime ge5 =
  let
    support = DS.monsterDividesIffNoQuadraticSupersingularPoints p prime ge5
    pairReduction = DS.noQuadraticPointsIffNoFrobeniusPairs p prime ge5
  in
  (λ divides → proj₁ pairReduction (proj₁ support divides))
  ,
  (λ pairZero → proj₂ support (proj₂ pairReduction pairZero))

------------------------------------------------------------------------
-- Deligne--Rapoport/Fricke geometry turns pair defect into genus.
------------------------------------------------------------------------

zeroPairDefectIffFrickeGenusZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  DR.pairedCount
      (Selector.supersingularFrobenius
        (Fricke.publishedAuthorityAt p prime ge5)) ≡ 0
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
zeroPairDefectIffFrickeGenusZero p prime ge5 =
  let genusEqualsPair = Fricke.publishedPairDefectEqualsFrickeGenus p prime ge5
  in
  (λ pairZero → trans genusEqualsPair pairZero)
  ,
  (λ genusZero → trans (sym genusEqualsPair) genusZero)

------------------------------------------------------------------------
-- Full p>=5 theorem from the exponent-support route.
------------------------------------------------------------------------

duncanSwisherMonsterIffFrickeGenusZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
duncanSwisherMonsterIffFrickeGenusZero p prime ge5 =
  let
    support = monsterDividesIffZeroPairDefect p prime ge5
    genus = zeroPairDefectIffFrickeGenusZero p prime ge5
  in
  (λ divides → proj₁ genus (proj₁ support divides))
  ,
  (λ genusZero → proj₂ support (proj₂ genus genusZero))

record DuncanSwisherMonsterFrickeGe5Boundary : Set where
  field
    DuncanSwisherExponentTheoremUsed : Bool
    oldDuncanOnoSupportEquivalenceImportedHere : Bool
    DeligneRapoportPairDefectGenusUsed : Bool
    MonsterPrimeLaneEnumerationImported : Bool
    finiteUnder72TableImported : Bool
    pGe5FullSupportEquivalenceDerived : Bool

canonicalDuncanSwisherMonsterFrickeGe5Boundary :
  DuncanSwisherMonsterFrickeGe5Boundary
canonicalDuncanSwisherMonsterFrickeGe5Boundary = record
  { DuncanSwisherExponentTheoremUsed = true
  ; oldDuncanOnoSupportEquivalenceImportedHere = false
  ; DeligneRapoportPairDefectGenusUsed = true
  ; MonsterPrimeLaneEnumerationImported = false
  ; finiteUnder72TableImported = false
  ; pGe5FullSupportEquivalenceDerived = true
  }
