module DASHI.Analysis.PrimeCountingAlgorithms where

-- Computational contracts for exact evaluation of π(n).
--
-- This module separates three layers:
--   * a proof-bearing sieve output,
--   * the Legendre / inclusion-exclusion Φ recurrence,
--   * the Meissel decomposition through P₂.
--
-- These are exact finite algorithms and do not imply asymptotic estimates.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _∸_; _*_)
open import DASHI.Analysis.PrimeCountingFunction

------------------------------------------------------------------------
-- Sieve contract
------------------------------------------------------------------------

data ListContains {A : Set} (x : A) : List A → Set where
  containsHere : {xs : List A} → ListContains x (x ∷ xs)
  containsThere :
    {y : A} {xs : List A} →
    ListContains x xs →
    ListContains x (y ∷ xs)

record PrimeSieve
  (primes : PrimePredicate) : Set₁ where
  field
    sieveUpTo : Nat → List Nat

    outputSound :
      (bound p : Nat) →
      ListContains p (sieveUpTo bound) →
      PrimePredicate.Prime primes p

    outputBounded :
      (bound p : Nat) →
      ListContains p (sieveUpTo bound) →
      p ≤ bound

    outputComplete :
      (bound p : Nat) →
      PrimePredicate.Prime primes p →
      p ≤ bound →
      ListContains p (sieveUpTo bound)

    NoDuplicates : List Nat → Set
    noDuplicates :
      (bound : Nat) →
      NoDuplicates (sieveUpTo bound)

    sieveCountExact :
      (bound : Nat) →
      listLength (sieveUpTo bound)
      ≡ primeCountLE primes bound

------------------------------------------------------------------------
-- Legendre Φ recurrence
------------------------------------------------------------------------

record OrderedPrimeDivision
  (primes : PrimePredicate) : Set₁ where
  field
    primeAt : Nat → Nat
    quotientByPrime : Nat → Nat → Nat

    primeAtIsPrime :
      (index : Nat) →
      PrimePredicate.Prime primes (primeAt index)

    QuotientCorrect : Nat → Nat → Set
    quotientCorrect :
      (m index : Nat) →
      QuotientCorrect m index

-- Φ(m,a): numbers in [1,m] not divisible by the first a primes.
phiCount :
  {primes : PrimePredicate} →
  OrderedPrimeDivision primes →
  Nat →
  Nat →
  Nat
phiCount sequence m zero = m
phiCount sequence m (suc a) =
  phiCount sequence m a
  ∸ phiCount sequence
      (OrderedPrimeDivision.quotientByPrime sequence m a)
      a

phiCountStep :
  {primes : PrimePredicate} →
  (sequence : OrderedPrimeDivision primes) →
  (m a : Nat) →
  phiCount sequence m (suc a)
  ≡
  (phiCount sequence m a
   ∸ phiCount sequence
       (OrderedPrimeDivision.quotientByPrime sequence m a)
       a)
phiCountStep sequence m a = refl

record LegendrePrimeCountingIdentity
  (primes : PrimePredicate)
  (sequence : OrderedPrimeDivision primes) : Set₁ where
  field
    sqrtFloor : Nat → Nat
    SqrtFloorCorrect : Nat → Set
    sqrtFloorCorrect :
      (m : Nat) →
      SqrtFloorCorrect m

    legendreIdentity :
      (m : Nat) →
      primeCountLE primes m
      ≡
      ((phiCount sequence m
          (primeCountLE primes (sqrtFloor m))
        + primeCountLE primes (sqrtFloor m))
       ∸ suc zero)

------------------------------------------------------------------------
-- Meissel decomposition
------------------------------------------------------------------------

record MeisselPrimeCountingIdentity
  (primes : PrimePredicate)
  (sequence : OrderedPrimeDivision primes) : Set₁ where
  field
    cubeRootFloor : Nat → Nat
    sqrtFloor : Nat → Nat
    chosenY : Nat → Nat

    RootWindowCorrect : Nat → Set
    rootWindowCorrect :
      (m : Nat) →
      RootWindowCorrect m

    p2Count : Nat → Nat → Nat

    P2CountsExactlyTwoLargePrimeFactors : Nat → Nat → Set
    p2Correct :
      (m primeCutoff : Nat) →
      P2CountsExactlyTwoLargePrimeFactors m primeCutoff

    noThreeLargePrimeFactors : Nat → Set
    noThreeLargePrimeFactorsProof :
      (m : Nat) →
      noThreeLargePrimeFactors m

    meisselIdentity :
      (m : Nat) →
      let n = primeCountLE primes (chosenY m)
      in
      primeCountLE primes m
      ≡
      ((phiCount sequence m n + n)
       ∸ (suc zero + p2Count m n))

record PrimeCountingAlgorithmBoundary : Set where
  field
    sieveRequiresSoundnessCompleteness : ⊤
    phiIsFiniteInclusionExclusion : ⊤
    legendreNeedsSquareRootCutoffProof : ⊤
    meisselNeedsP2AndCubeRootWindowProof : ⊤
    algorithmsDoNotSupplyPNT : ⊤
    algorithmsDoNotSupplyRH : ⊤

primeCountingAlgorithmBoundary : PrimeCountingAlgorithmBoundary
primeCountingAlgorithmBoundary = record
  { sieveRequiresSoundnessCompleteness = tt
  ; phiIsFiniteInclusionExclusion = tt
  ; legendreNeedsSquareRootCutoffProof = tt
  ; meisselNeedsP2AndCubeRootWindowProof = tt
  ; algorithmsDoNotSupplyPNT = tt
  ; algorithmsDoNotSupplyRH = tt
  }
