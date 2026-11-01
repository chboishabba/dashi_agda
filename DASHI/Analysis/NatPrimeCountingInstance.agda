module DASHI.Analysis.NatPrimeCountingInstance where

-- Concrete executable instance of the finite prime-counting layer using the
-- Agda standard library's proof-bearing Nat primality predicate and decider.

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Primality as NatPrimality using (Prime; prime?)
open import DASHI.Analysis.PrimeCountingFunction

natPrimePredicate : PrimePredicate
natPrimePredicate = record
  { Prime = NatPrimality.Prime
  ; prime? = NatPrimality.prime?
  }

natPrimeIndicator : Nat → Nat
natPrimeIndicator = primeIndicator natPrimePredicate

natPrimeCountLE : Nat → Nat
natPrimeCountLE = primeCountLE natPrimePredicate

natPrimesUpTo : Nat → List Nat
natPrimesUpTo = primesUpTo natPrimePredicate

natPrimeCountSymmetricTwice : Nat → Nat
natPrimeCountSymmetricTwice =
  primeCountSymmetricTwice natPrimePredicate

natPrimeEnumerationCountExact :
  (n : Nat) →
  listLength (natPrimesUpTo n) ≡ natPrimeCountLE n
natPrimeEnumerationCountExact =
  primeListCountExact natPrimePredicate
