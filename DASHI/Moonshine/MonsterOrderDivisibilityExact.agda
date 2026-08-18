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
-- It DOES now expose exact divisibility witnesses for the two exceptional
-- low primes 2 and 3 so the later p>=5 geometric theorem can be completed
-- without reintroducing a finite Monster-prime lane.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Divisibility using (_∣_; divides)

monsterOrder : Nat
monsterOrder = 808017424794512875886459904961710757005754368000000000

PrimeDividesMonsterOrder : Nat → Set
PrimeDividesMonsterOrder p = p ∣ monsterOrder

------------------------------------------------------------------------
-- Exact exceptional-prime divisibility witnesses.
------------------------------------------------------------------------

twoDividesMonsterOrder : PrimeDividesMonsterOrder 2
twoDividesMonsterOrder =
  divides 404008712397256437943229952480855378502877184000000000 refl

threeDividesMonsterOrder : PrimeDividesMonsterOrder 3
threeDividesMonsterOrder =
  divides 269339141598170958628819968320570252335251456000000000 refl

record MonsterOrderDivisibilityBoundary : Set where
  field
    actualPublishedMonsterOrderUsed : Bool
    membershipDefinedByNatDivisibility : Bool
    exactExceptionalTwoDivisibilityConstructed : Bool
    exactExceptionalThreeDivisibilityConstructed : Bool
    MonsterPrimeLaneEnumerationImported : Bool
    finiteFifteenPrimeListInsertedHere : Bool

canonicalMonsterOrderDivisibilityBoundary : MonsterOrderDivisibilityBoundary
canonicalMonsterOrderDivisibilityBoundary = record
  { actualPublishedMonsterOrderUsed = true
  ; membershipDefinedByNatDivisibility = true
  ; exactExceptionalTwoDivisibilityConstructed = true
  ; exactExceptionalThreeDivisibilityConstructed = true
  ; MonsterPrimeLaneEnumerationImported = false
  ; finiteFifteenPrimeListInsertedHere = false
  }
