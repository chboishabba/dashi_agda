module DASHI.Moonshine.PublishedMonsterFrickeHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused table-free Monster/Ogg/Fricke root for prime p >= 5.
--
-- Monster side:
--   actual published Monster order + Nat divisibility;
--   Duncan--Ono/Ogg imported equivalence with coarse supersingular
--   rationality / Frobenius pointwise fixedness.
--
-- Modular-curve side:
--   prime-pinned Deligne--Rapoport/Fricke special-fibre authority;
--   same-object nodal model + completed-local node authority;
--   proper-flat Hilbert-polynomial genus transport;
--   derived Frobenius pair defect = g(X_0^+(p)).
--
-- Therefore, without MonsterPrimeLane / SSP15 enumeration,
--
--   p divides |M|  iff  g(X_0^+(p)) = 0
--
-- for the prime range currently covered by the prime-level geometric authority.
-- The exceptional primes 2 and 3 remain deliberately separate from this root.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PublishedMonsterFrickeGenusZeroExact as Weld

monsterFrickeRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0
monsterFrickeRegression = Weld.monsterPrimeIffFrickeGenusZero

noFiniteMonsterLaneTableRegression :
  Weld.MonsterPrimeLaneTableUsed
    Weld.canonicalPublishedMonsterFrickeGenusZeroBoundary ≡ false
noFiniteMonsterLaneTableRegression = refl

actualOrderDivisibilityRegression :
  Weld.actualMonsterOrderDivisibilityUsed
    Weld.canonicalPublishedMonsterFrickeGenusZeroBoundary ≡ true
actualOrderDivisibilityRegression = refl

converseNotOversoldRegression :
  Weld.converseConceptualMechanismProvedBeyondImportedOggTheorem
    Weld.canonicalPublishedMonsterFrickeGenusZeroBoundary ≡ false
converseNotOversoldRegression = refl
