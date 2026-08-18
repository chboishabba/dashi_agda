module DASHI.Moonshine.DuncanSwisherMonsterFrickeAllPrimesExact where

------------------------------------------------------------------------
-- ALL-PRIME MONSTER / FRICKE SUPPORT VIA DUNCAN--SWISHER + LOW EXCEPTIONS
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Their Theorem 1.2 applies for p > 3 and supplies the p>=5 support theorem.
-- The paper explicitly records that p=2,3 are exceptional for its formulas.
-- We therefore reuse the separate classical low-level Fricke authority already
-- constructed for exactly those two primes.
--
-- The resulting arbitrary-prime theorem does NOT import the older
-- Duncan--Ono/Ogg supersingular support equivalence, MonsterPrimeLane, or the
-- finite under-72 Fricke table.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedLowPrimeFrickeGenusExact as Low
import DASHI.Moonshine.PublishedMonsterFrickeAllSupportedPrimesExact as All
import DASHI.Moonshine.DuncanSwisherMonsterFrickeGe5Exact as DSGe5

------------------------------------------------------------------------
-- Arbitrary-prime theorem.  The five-suc branch is definitionally the p>=5
-- genus carrier used by DSGe5; 2 and 3 reduce to the exceptional low-level
-- genera inside All.primeFrickeGenus.
------------------------------------------------------------------------

duncanSwisherMonsterIffFrickeGenusZeroAllPrimes :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ All.primeFrickeGenus p prime ≡ 0
duncanSwisherMonsterIffFrickeGenusZeroAllPrimes 0 prime =
  ⊥-elim (All.notPrime0 prime)
duncanSwisherMonsterIffFrickeGenusZeroAllPrimes 1 prime =
  ⊥-elim (All.notPrime1 prime)
duncanSwisherMonsterIffFrickeGenusZeroAllPrimes 2 prime =
  Low.lowPrimeMonsterIffFrickeGenusZero Low.prime2
duncanSwisherMonsterIffFrickeGenusZeroAllPrimes 3 prime =
  Low.lowPrimeMonsterIffFrickeGenusZero Low.prime3
duncanSwisherMonsterIffFrickeGenusZeroAllPrimes 4 prime =
  ⊥-elim (All.notPrime4 prime)
duncanSwisherMonsterIffFrickeGenusZeroAllPrimes
  (suc (suc (suc (suc (suc n))))) prime =
  DSGe5.duncanSwisherMonsterIffFrickeGenusZero
    (5 + n) prime (Data.Nat.Properties.m≤m+n 5 n)

------------------------------------------------------------------------
-- Directional projections, useful for combining with the independent
-- Conway--Norton/Borcherds forward explanation.
------------------------------------------------------------------------

duncanSwisherMonsterImpliesFrickeGenusZeroAllPrimes :
  (p : Nat) → (prime : Prime p) →
  Monster.PrimeDividesMonsterOrder p →
  All.primeFrickeGenus p prime ≡ 0
duncanSwisherMonsterImpliesFrickeGenusZeroAllPrimes p prime =
  proj₁ (duncanSwisherMonsterIffFrickeGenusZeroAllPrimes p prime)

duncanSwisherFrickeGenusZeroImpliesMonsterAllPrimes :
  (p : Nat) → (prime : Prime p) →
  All.primeFrickeGenus p prime ≡ 0 →
  Monster.PrimeDividesMonsterOrder p
duncanSwisherFrickeGenusZeroImpliesMonsterAllPrimes p prime =
  proj₂ (duncanSwisherMonsterIffFrickeGenusZeroAllPrimes p prime)

record DuncanSwisherMonsterFrickeAllPrimesBoundary : Set where
  field
    theorem12UsedForEveryPrimeAboveThree : Bool
    explicitExceptionalTwoThreeLaneUsed : Bool
    DuncanOnoSupportEquivalenceImported : Bool
    MonsterPrimeLaneImported : Bool
    finiteUnder72FrickeTableImported : Bool
    arbitraryPrimeSupportEquivalenceDerived : Bool

canonicalDuncanSwisherMonsterFrickeAllPrimesBoundary :
  DuncanSwisherMonsterFrickeAllPrimesBoundary
canonicalDuncanSwisherMonsterFrickeAllPrimesBoundary = record
  { theorem12UsedForEveryPrimeAboveThree = true
  ; explicitExceptionalTwoThreeLaneUsed = true
  ; DuncanOnoSupportEquivalenceImported = false
  ; MonsterPrimeLaneImported = false
  ; finiteUnder72FrickeTableImported = false
  ; arbitraryPrimeSupportEquivalenceDerived = true
  }
