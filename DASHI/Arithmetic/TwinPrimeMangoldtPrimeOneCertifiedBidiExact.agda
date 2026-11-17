module DASHI.Arithmetic.TwinPrimeMangoldtPrimeOneCertifiedBidiExact where

------------------------------------------------------------------------
-- M14/M16 GENUINE PRIME-PRIME CASE ↔ ORIGINAL CERTIFIED TwinPrimeAt
--
-- Reuse the ORIGINAL ChebyshevPrimeOwnership / NatPrimeCountingInstance
-- mapping, rather than falsely assuming AllPrimeArithmetic.Prime is
-- automatically identical to Data.Nat.Primality.Prime.
--
-- The only power arithmetic used here is p^1 = p, from the
-- ORIGINAL RiemannPrimePowerArithmetic.natPow and Nat mul identity.
-- Two exact inverse maps preserve actual prime certificates on
-- both endpoints. These maps do NOT identify different proof terms
-- by proof irrelevance or treat prime powers p^k (k>=2) as primes.
--
-- Mathematical roots: Euclid and classical von Mangoldt.
-- Original code owners: ChebyshevPrimeCounting,
-- NatPrimeCountingInstance, TwinPrimeSixWheelExact.
-- DASHI bridge source-written; kernel pending, 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
import Data.Nat.Primality as NatPrime
import Data.Nat.Properties as NP

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Analysis.ChebyshevPrimeCounting as Cheb
import DASHI.Analysis.NatPrimeCountingInstance as PrimeNat
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin

-- Unlike an untyped two-point residue match, these records
-- contain two original all-prime witnesses AND precise Nat endpoints.
record PrimeOnePair
    (space : Weil.WeilTestSpace)
    (arithmetic : VM.AllPrimeArithmetic space)
    (n : Nat) : Set where
  constructor prime-one-pair
  field
    lower : VM.AllPrimeArithmetic.Prime arithmetic
    upper : VM.AllPrimeArithmetic.Prime arithmetic
    lowerValue :
      n ≡ VM.primePowerNat space arithmetic lower zero
    upperValue :
      n + Twin.two ≡ VM.primePowerNat space arithmetic upper zero
open PrimeOnePair public

-- The reused prime-identity owner explicitly bridges all-prime
-- log-carrier objects with certified Nat primality. No new oracle.
primeOnePairToTwin :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic) →
  (n : Nat) →
  PrimeOnePair space arithmetic n →
  Twin.TwinPrimeAt n
primeOnePairToTwin space arithmetic theta ownership n pair =
  ( subst NatPrime.Prime
      (sym (trans (lowerValue pair)
        (NP.*-identityʳ (VM.AllPrimeArithmetic.toNat arithmetic
          (lower pair)))))
      (Cheb.ChebyshevPrimeOwnership.carrierIsPrime ownership
        (lower pair))
  , subst NatPrime.Prime
      (sym (trans (upperValue pair)
        (NP.*-identityʳ (VM.AllPrimeArithmetic.toNat arithmetic
          (upper pair)))))
      (Cheb.ChebyshevPrimeOwnership.carrierIsPrime ownership
        (upper pair))
  )

twinToPrimeOnePair :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic) →
  (n : Nat) →
  Twin.TwinPrimeAt n →
  PrimeOnePair space arithmetic n
twinToPrimeOnePair space arithmetic theta ownership n certified
  with Cheb.ChebyshevPrimeOwnership.primeToCarrier ownership
        (proj₁ certified)
     | Cheb.ChebyshevPrimeOwnership.primeToCarrier ownership
        (proj₂ certified)
... | lowerPrime , lowerEqualsNat
    | upperPrime , upperEqualsNat =
  prime-one-pair lowerPrime upperPrime
    (trans (sym lowerEqualsNat)
      (sym (NP.*-identityʳ
        (VM.AllPrimeArithmetic.toNat arithmetic lowerPrime))))
    (trans (sym upperEqualsNat)
      (sym (NP.*-identityʳ
        (VM.AllPrimeArithmetic.toNat arithmetic upperPrime))))

-- Logical BIDI, no equality-of-proofs axiom. The pair-representation
-- may contain different evidence for identical mathematical facts.
record PrimeOneTwinBidi
    (space : Weil.WeilTestSpace)
    (arithmetic : VM.AllPrimeArithmetic space)
    (n : Nat) : Set where
  constructor prime-one-twin-bidi
  field
    toCertified : PrimeOnePair space arithmetic n → Twin.TwinPrimeAt n
    fromCertified : Twin.TwinPrimeAt n → PrimeOnePair space arithmetic n

primeOneTwinBidi :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic) →
  (n : Nat) →
  PrimeOneTwinBidi space arithmetic n
primeOneTwinBidi space arithmetic theta ownership n =
  prime-one-twin-bidi
    (primeOnePairToTwin space arithmetic theta ownership n)
    (twinToPrimeOnePair space arithmetic theta ownership n)
