module DASHI.Moonshine.MonsterOrderDivisibilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker,
-- Robert A. Wilson,
-- "Atlas of Finite Groups: Maximal Subgroups and Ordinary Characters for
-- Simple Groups", Oxford University Press, 1985.
-- No DOI asserted here.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Represent Monster-prime membership by ordinary natural-number divisibility
-- of the ACTUAL published Monster group order, not by the repository's finite
-- MonsterPrimeLane / SSP15 enumeration.
--
-- The decimal order is the standard ATLAS value
--
--   808017424794512875886459904961710757005754368000000000
--
-- with factorization
--
--   2^46 3^20 5^9 7^6 11^2 13^3
--   *17*19*23*29*31*41*47*59*71.
--
-- This module deliberately does not enumerate the fifteen prime divisors.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Divisibility using (_∣_)

monsterOrder : Nat
monsterOrder = 808017424794512875886459904961710757005754368000000000

PrimeDividesMonsterOrder : Nat → Set
PrimeDividesMonsterOrder p = p ∣ monsterOrder

record MonsterOrderDivisibilityBoundary : Set where
  field
    actualPublishedMonsterOrderUsed : Bool
    membershipDefinedByNatDivisibility : Bool
    MonsterPrimeLaneEnumerationImported : Bool
    finiteFifteenPrimeListInsertedHere : Bool

canonicalMonsterOrderDivisibilityBoundary : MonsterOrderDivisibilityBoundary
canonicalMonsterOrderDivisibilityBoundary = record
  { actualPublishedMonsterOrderUsed = true
  ; membershipDefinedByNatDivisibility = true
  ; MonsterPrimeLaneEnumerationImported = false
  ; finiteFifteenPrimeListInsertedHere = false
  }
