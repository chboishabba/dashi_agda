module DASHI.Arithmetic.CertifiedPrimePairPeriodExact where

------------------------------------------------------------------------
-- SOURCE AND REUSE
--
-- Classical modular arithmetic / Eratosthenes / Brun. The existing
-- DASHI.Arithmetic.CertifiedPrimePairModulusExact owns all local pair
-- sieve semantics, while Agda stdlib DivMod owns the modular identity.
--
-- The product of ANY finite list of certified prime moduli is a
-- period of its pair-survival predicate. Coprimality is NOT needed
-- for periodicity, unlike arithmetic CRT reconstruction.
--
-- This gives a genuine arbitrary-prime finite-sieve transport.
-- It does NOT prove primality of a survivor, the full CRT inverse,
-- twin-prime infinitude, or analytic prime distribution.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm)
open import Data.Nat.DivMod using (_%_; [m+kn]%n≡m%n)

import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair

------------------------------------------------------------------------
-- Iterated local residue symmetry, reusing the same pair predicate.
------------------------------------------------------------------------

localKPeriod :
  (axis : Pair.CertifiedPrimeAxis) →
  (n k : Nat) →
  (n + k * Pair.primeModulus axis) % Pair.primeModulus axis
    ≡ n % Pair.primeModulus axis
localKPeriod axis n k =
  [m+kn]%n≡m%n n k (Pair.primeModulus axis)

localKOffsetPeriod :
  (axis : Pair.CertifiedPrimeAxis) →
  (n k : Nat) →
  ((n + k * Pair.primeModulus axis) + Pair.two)
    % Pair.primeModulus axis
    ≡ (n + Pair.two) % Pair.primeModulus axis
localKOffsetPeriod axis n k =
  trans
    (cong
      (λ x → x % Pair.primeModulus axis)
      (Pair.addOffsetCommute n (k * Pair.primeModulus axis)))
    ([m+kn]%n≡m%n (n + Pair.two) k (Pair.primeModulus axis))

localKPeriodic :
  (axis : Pair.CertifiedPrimeAxis) →
  (n k : Nat) →
  Pair.LocalPairSurvives axis n →
  Pair.LocalPairSurvives axis
    (n + k * Pair.primeModulus axis)
localKPeriodic axis n k (left , right) =
  (λ atShift →
    left (trans (sym (localKPeriod axis n k)) atShift))
  ,
  (λ atShift →
    right (trans (sym (localKOffsetPeriod axis n k)) atShift))

localKPeriodicBack :
  (axis : Pair.CertifiedPrimeAxis) →
  (n k : Nat) →
  Pair.LocalPairSurvives axis
    (n + k * Pair.primeModulus axis) →
  Pair.LocalPairSurvives axis n
localKPeriodicBack axis n k (left , right) =
  (λ atBase →
    left (trans (localKPeriod axis n k) atBase))
  ,
  (λ atBase →
    right (trans (localKOffsetPeriod axis n k) atBase))

------------------------------------------------------------------------
-- A proof of common periodicity is a proof of an integer multiple
-- for each local axis. The modulus list need not be pairwise coprime.
------------------------------------------------------------------------

data CommonPeriod : List Pair.CertifiedPrimeAxis → Nat → Set where
  emptyPeriod :
    ∀ {M} →
    CommonPeriod [] M
  appendPeriod :
    ∀ {M axis rest} →
    (k : Nat) →
    M ≡ k * Pair.primeModulus axis →
    CommonPeriod rest M →
    CommonPeriod (axis ∷ rest) M

scaleCommonPeriod :
  (axes : List Pair.CertifiedPrimeAxis) →
  (M factor : Nat) →
  CommonPeriod axes M →
  CommonPeriod axes (factor * M)
scaleCommonPeriod [] M factor emptyPeriod =
  emptyPeriod
scaleCommonPeriod (axis ∷ rest) M factor
    (appendPeriod k divisible restProof) =
  appendPeriod
    (factor * k)
    (trans
      (cong (λ x → factor * x) divisible)
      (sym (*-assoc factor k (Pair.primeModulus axis))))
    (scaleCommonPeriod rest M factor restProof)

modulusProduct : List Pair.CertifiedPrimeAxis → Nat
modulusProduct [] = 1
modulusProduct (axis ∷ rest) =
  Pair.primeModulus axis * modulusProduct rest

productIsCommonPeriod :
  (axes : List Pair.CertifiedPrimeAxis) →
  CommonPeriod axes (modulusProduct axes)
productIsCommonPeriod [] = emptyPeriod
productIsCommonPeriod (axis ∷ rest) =
  appendPeriod
    (modulusProduct rest)
    (*-comm (Pair.primeModulus axis) (modulusProduct rest))
    (scaleCommonPeriod rest (modulusProduct rest)
      (Pair.primeModulus axis)
      (productIsCommonPeriod rest))

------------------------------------------------------------------------
-- Transport all local pair witnesses under the certified common
-- period, with a two-way theorem. This does not use a CRT inverse.
------------------------------------------------------------------------

allPairCommonPeriodic :
  (axes : List Pair.CertifiedPrimeAxis) →
  (M n : Nat) →
  CommonPeriod axes M →
  Pair.AllPairSurvive axes n →
  Pair.AllPairSurvive axes (n + M)
allPairCommonPeriodic [] M n emptyPeriod witness = witness
allPairCommonPeriodic (axis ∷ rest) M n
    (appendPeriod k divisible restPeriod)
    (headWitness , restWitness) =
  subst
    (Pair.LocalPairSurvives axis)
    (cong (n +_) (sym divisible))
    (localKPeriodic axis n k headWitness)
  ,
  allPairCommonPeriodic rest M n restPeriod restWitness

allPairCommonPeriodicBack :
  (axes : List Pair.CertifiedPrimeAxis) →
  (M n : Nat) →
  CommonPeriod axes M →
  Pair.AllPairSurvive axes (n + M) →
  Pair.AllPairSurvive axes n
allPairCommonPeriodicBack [] M n emptyPeriod witness = witness
allPairCommonPeriodicBack (axis ∷ rest) M n
    (appendPeriod k divisible restPeriod)
    (headWitness , restWitness) =
  localKPeriodicBack axis n k
    (subst
      (Pair.LocalPairSurvives axis)
      (cong (n +_) divisible)
      headWitness)
  ,
  allPairCommonPeriodicBack rest M n restPeriod restWitness

allPairProductPeriodic :
  (axes : List Pair.CertifiedPrimeAxis) →
  (n : Nat) →
  Pair.AllPairSurvive axes n →
  Pair.AllPairSurvive axes (n + modulusProduct axes)
allPairProductPeriodic axes n =
  allPairCommonPeriodic axes (modulusProduct axes) n
    (productIsCommonPeriod axes)

allPairProductPeriodicBack :
  (axes : List Pair.CertifiedPrimeAxis) →
  (n : Nat) →
  Pair.AllPairSurvive axes (n + modulusProduct axes) →
  Pair.AllPairSurvive axes n
allPairProductPeriodicBack axes n =
  allPairCommonPeriodicBack axes (modulusProduct axes) n
    (productIsCommonPeriod axes)

------------------------------------------------------------------------
-- Finite filter symmetry, with no duplicate-prime promotion.
--
-- Reordering constraints has no effect on the truth of a conjunction.
-- Repeating a prime modulus adds no new arithmetic information.
-- These are the exact safe symmetries that coexist with the SSP
-- prime-identity-preserving address action.
------------------------------------------------------------------------

swapFirstTwoPrimeFilters :
  (first second : Pair.CertifiedPrimeAxis) →
  (rest : List Pair.CertifiedPrimeAxis) →
  (n : Nat) →
  Pair.AllPairSurvive (first ∷ second ∷ rest) n →
  Pair.AllPairSurvive (second ∷ first ∷ rest) n
swapFirstTwoPrimeFilters first second rest n
  (firstProof , (secondProof , tail)) =
  secondProof , (firstProof , tail)

swapFirstTwoFiltersInvolution :
  (first second : Pair.CertifiedPrimeAxis) →
  (rest : List Pair.CertifiedPrimeAxis) →
  (n : Nat) →
  (witness : Pair.AllPairSurvive (first ∷ second ∷ rest) n) →
  swapFirstTwoPrimeFilters second first rest n
    (swapFirstTwoPrimeFilters first second rest n witness)
    ≡ witness
swapFirstTwoFiltersInvolution first second rest n
  (firstProof , (secondProof , tail)) = refl

duplicatePrimeFilterErases :
  (axis : Pair.CertifiedPrimeAxis) →
  (rest : List Pair.CertifiedPrimeAxis) →
  (n : Nat) →
  Pair.AllPairSurvive (axis ∷ axis ∷ rest) n →
  Pair.AllPairSurvive (axis ∷ rest) n
duplicatePrimeFilterErases axis rest n
  (first , (second , tail)) =
  first , tail

duplicatePrimeFilterInserts :
  (axis : Pair.CertifiedPrimeAxis) →
  (rest : List Pair.CertifiedPrimeAxis) →
  (n : Nat) →
  Pair.AllPairSurvive (axis ∷ rest) n →
  Pair.AllPairSurvive (axis ∷ axis ∷ rest) n
duplicatePrimeFilterInserts axis rest n
  (first , tail) =
  first , (first , tail)

duplicatePrimeFilterRoundTrip :
  (axis : Pair.CertifiedPrimeAxis) →
  (rest : List Pair.CertifiedPrimeAxis) →
  (n : Nat) →
  (witness : Pair.AllPairSurvive (axis ∷ rest) n) →
  duplicatePrimeFilterErases axis rest n
    (duplicatePrimeFilterInserts axis rest n witness)
    ≡ witness
duplicatePrimeFilterRoundTrip axis rest n
  (first , tail) = refl

------------------------------------------------------------------------
-- Repeated product period is a theorem for every natural multiplier.
-- This is about the finite candidate sieve, not genuine prime pairs.
------------------------------------------------------------------------

allPairProductPeriodicMultiple :
  (axes : List Pair.CertifiedPrimeAxis) →
  (n k : Nat) →
  Pair.AllPairSurvive axes n →
  Pair.AllPairSurvive axes (n + k * modulusProduct axes)
allPairProductPeriodicMultiple axes n k =
  allPairCommonPeriodic axes (k * modulusProduct axes) n
    (scaleCommonPeriod axes (modulusProduct axes) k
      (productIsCommonPeriod axes))

allPairProductPeriodicMultipleBack :
  (axes : List Pair.CertifiedPrimeAxis) →
  (n k : Nat) →
  Pair.AllPairSurvive axes (n + k * modulusProduct axes) →
  Pair.AllPairSurvive axes n
allPairProductPeriodicMultipleBack axes n k =
  allPairCommonPeriodicBack axes (k * modulusProduct axes) n
    (scaleCommonPeriod axes (modulusProduct axes) k
      (productIsCommonPeriod axes))
