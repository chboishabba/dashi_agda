module DASHI.Moonshine.PublishedMonsterFrickeHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused table-free Monster/Ogg/Fricke root for EVERY prime p.
--
-- Monster side:
--   actual published Monster order + Nat divisibility;
--   Duncan--Ono/Ogg imported equivalence with coarse supersingular
--   rationality / Frobenius pointwise fixedness on the p >= 5 lane;
--   exact direct divisibility witnesses at the exceptional primes 2 and 3.
--
-- Modular-curve side:
--   p >= 5: prime-pinned Deligne--Rapoport/Fricke special-fibre authority;
--   p = 2,3: explicit classical low-level Fricke genus-zero authority.
--
-- The stdlib primality decision exhausts every Prime p into exactly one of
-- those source lanes.  Therefore, without MonsterPrimeLane / SSP15 enumeration
-- and without the finite under-72 Fricke table,
--
--   p divides |M|  iff  g(X_0^+(p)) = 0
--
-- on the proof-relevant arbitrary-prime genus carrier exported by
-- PublishedMonsterFrickeAllSupportedPrimesExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as Ge5
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as All

------------------------------------------------------------------------
-- Arbitrary-prime public regression.
------------------------------------------------------------------------

monsterFrickeAllPrimeRegression :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ All.primeFrickeGenus p prime ≡ 0
monsterFrickeAllPrimeRegression = All.primeMonsterIffFrickeGenusZero

------------------------------------------------------------------------
-- The p >= 5 geometric lane remains available with its original source-native
-- genus carrier; the all-prime wrapper does not erase that theorem surface.
------------------------------------------------------------------------

monsterFrickeGe5Regression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
monsterFrickeGe5Regression = Ge5.monsterPrimeIffFrickeGenusZero

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

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

actualOrderDivisibilityRegression :
  Ge5.actualMonsterOrderDivisibilityUsed
    Ge5.canonicalPublishedMonsterFrickeGenusZeroBoundary ≡ true
actualOrderDivisibilityRegression = refl

converseNotOversoldRegression :
  Ge5.converseConceptualMechanismProvedBeyondImportedOggTheorem
    Ge5.canonicalPublishedMonsterFrickeGenusZeroBoundary ≡ false
converseNotOversoldRegression = refl
