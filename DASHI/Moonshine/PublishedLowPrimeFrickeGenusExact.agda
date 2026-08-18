module DASHI.Moonshine.PublishedLowPrimeFrickeGenusExact where

------------------------------------------------------------------------
-- PUBLISHED LOW-PRIME FRICKE AUTHORITY
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974--1975), expose 7, pp. 1--8.
-- MR 0417184; no DOI assigned.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- SOURCE ROLE
--
-- The generic prime-level Deligne--Rapoport authority used elsewhere in this
-- branch is intentionally stated only for p >= 5.  The two excluded Monster
-- primes are classical low-level exceptions:
--
--   g(X_0^+(2)) = 0,
--   g(X_0^+(3)) = 0.
--
-- This module records ONLY those two exceptional values.  It does not import
-- MonsterPrimeLane, the SSP15 list, or the finite odd-prime under-72 genus
-- control table.
--
-- The Monster-order divisibility statements are not imported as booleans:
-- they are the exact Nat divisibility witnesses constructed in
-- MonsterOrderDivisibilityExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster

------------------------------------------------------------------------
-- Exactly the two prime-level cases excluded by the p >= 5 authority.
------------------------------------------------------------------------

data ExceptionalLowPrime : Set where
  prime2 prime3 : ExceptionalLowPrime

lowPrimeLevel : ExceptionalLowPrime → Nat
lowPrimeLevel prime2 = 2
lowPrimeLevel prime3 = 3

-- Published classical Fricke genera at the two exceptional levels.
lowPrimeFrickeGenus : ExceptionalLowPrime → Nat
lowPrimeFrickeGenus prime2 = 0
lowPrimeFrickeGenus prime3 = 0

prime2FrickeGenusZero : lowPrimeFrickeGenus prime2 ≡ 0
prime2FrickeGenusZero = refl

prime3FrickeGenusZero : lowPrimeFrickeGenus prime3 ≡ 0
prime3FrickeGenusZero = refl

------------------------------------------------------------------------
-- Exact Monster-order side, reusing ordinary Nat divisibility.
------------------------------------------------------------------------

lowPrimeDividesMonsterOrder :
  (p : ExceptionalLowPrime) →
  Monster.PrimeDividesMonsterOrder (lowPrimeLevel p)
lowPrimeDividesMonsterOrder prime2 = Monster.twoDividesMonsterOrder
lowPrimeDividesMonsterOrder prime3 = Monster.threeDividesMonsterOrder

------------------------------------------------------------------------
-- Exceptional Monster/Fricke equivalence.  Both directions are constructive:
-- the right side is the published low-level genus value and the left side is
-- exact divisibility of the actual Monster order.
------------------------------------------------------------------------

lowPrimeMonsterImpliesFrickeGenusZero :
  (p : ExceptionalLowPrime) →
  Monster.PrimeDividesMonsterOrder (lowPrimeLevel p) →
  lowPrimeFrickeGenus p ≡ 0
lowPrimeMonsterImpliesFrickeGenusZero prime2 divides = refl
lowPrimeMonsterImpliesFrickeGenusZero prime3 divides = refl

lowPrimeFrickeGenusZeroImpliesMonster :
  (p : ExceptionalLowPrime) →
  lowPrimeFrickeGenus p ≡ 0 →
  Monster.PrimeDividesMonsterOrder (lowPrimeLevel p)
lowPrimeFrickeGenusZeroImpliesMonster p genusZero =
  lowPrimeDividesMonsterOrder p

lowPrimeMonsterIffFrickeGenusZero :
  (p : ExceptionalLowPrime) →
  Monster.PrimeDividesMonsterOrder (lowPrimeLevel p)
  ↔ lowPrimeFrickeGenus p ≡ 0
lowPrimeMonsterIffFrickeGenusZero p =
  lowPrimeMonsterImpliesFrickeGenusZero p
  , lowPrimeFrickeGenusZeroImpliesMonster p

record PublishedLowPrimeFrickeBoundary : Set where
  field
    onlyExceptionalTwoAndThreeCarried : Bool
    finiteMonsterPrimeLaneImported : Bool
    finiteOddPrimeGenusTableImported : Bool
    exactMonsterDivisibilityReused : Bool
    p2FrickeGenusZeroSourceBacked : Bool
    p3FrickeGenusZeroSourceBacked : Bool
    exceptionalMonsterFrickeEquivalenceDerived : Bool

canonicalPublishedLowPrimeFrickeBoundary : PublishedLowPrimeFrickeBoundary
canonicalPublishedLowPrimeFrickeBoundary = record
  { onlyExceptionalTwoAndThreeCarried = true
  ; finiteMonsterPrimeLaneImported = false
  ; finiteOddPrimeGenusTableImported = false
  ; exactMonsterDivisibilityReused = true
  ; p2FrickeGenusZeroSourceBacked = true
  ; p3FrickeGenusZeroSourceBacked = true
  ; exceptionalMonsterFrickeEquivalenceDerived = true
  }
