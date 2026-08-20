module DASHI.Moonshine.AristotleHeckeGeneralPrimePowerDecompositionExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source module:
--   RequestProject.HeckeGeneral
--   SHA-256 a45235046a9f46c7fb0b8c86282db5be52f8637ee309096e0dfbc0b4b013c2cf
--
-- The upstream README requests @Aristotle-Harmonic attribution and the commit
-- trailer
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- PRIMARY MATHEMATICAL SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7, Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- CONSTRUCTIVE FOUNDATION REUSED
--
-- Agda standard library,
-- `Data.Nat.Primality.Factorisation`: constructive `factorise` producing a
-- proof-carrying list of prime factors for every nonzero natural number.
-- No DOI asserted for the software library.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact algebraic induction behind Aristotle's arbitrary-S Hecke
-- closure.  Repeated prime factors must first be grouped into prime-power
-- blocks: a raw factor list cannot be multiplied coefficient-by-coefficient,
-- because a(p^e) is controlled by the Hecke recurrence rather than a(p)^e.
--
-- A proof-carrying decomposition therefore consists of pairwise-coprime
-- positive prime powers.  Equality at every allowed prime gives equality on
-- every prime-power block by the already-constructed recurrence theorem, and
-- coprime multiplicativity then gives equality on the complete decomposition.
--
-- The stdlib already supplies raw constructive factorisation.  The only Nat
-- combinatorics not constructed here is the canonical grouping of that raw
-- factor list into pairwise-coprime positive prime-power blocks.  Thus the
-- Hecke algebraic theorem is closed while the exact remaining source-parity
-- seam is a finite factor-list normalization theorem, not analytic modular-form
-- theory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_^_; NonZero)
open import Data.Nat.Coprimality using (Coprime)
open import Data.Nat.Primality using (Prime)
open import Data.Nat.Primality.Factorisation
  using (PrimeFactorisation; factorise)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Moonshine.AristotleHeckeRecurrenceCoreExact as Recurrence

------------------------------------------------------------------------
-- Positive prime powers and their pairwise-coprime product decomposition.
------------------------------------------------------------------------

record PositivePrimePower : Set where
  constructor positivePrimePower
  field
    prime : Nat
    exponentMinusOne : Nat
    primeProof : Prime prime

open PositivePrimePower public

primePowerValue : PositivePrimePower → Nat
primePowerValue atom =
  prime atom ^ suc (exponentMinusOne atom)

data PrimePowerDecomposition : Nat → Set where
  decompositionOne : PrimePowerDecomposition 1
  decompositionCons :
    (atom : PositivePrimePower) →
    {rest : Nat} →
    PrimePowerDecomposition rest →
    Coprime (primePowerValue atom) rest →
    PrimePowerDecomposition (primePowerValue atom * rest)

------------------------------------------------------------------------
-- S-restricted version: every block prime must lie in Allowed.
------------------------------------------------------------------------

data AllowedPrimePowerDecomposition
    (Allowed : Nat → Set) : Nat → Set where
  allowedOne : AllowedPrimePowerDecomposition Allowed 1
  allowedCons :
    (atom : PositivePrimePower) →
    Allowed (prime atom) →
    {rest : Nat} →
    AllowedPrimePowerDecomposition Allowed rest →
    Coprime (primePowerValue atom) rest →
    AllowedPrimePowerDecomposition Allowed (primePowerValue atom * rest)

------------------------------------------------------------------------
-- Hecke system restricted to exactly the source laws used by the closure:
-- normalisation, coprime multiplicativity, and the prime-power recurrence.
------------------------------------------------------------------------

record NatHeckeClosureSystem
    (A : Recurrence.RecurrenceCoefficientAlgebra)
    (scale : Nat → Recurrence.Carrier A)
    (coefficient : Nat → Recurrence.Carrier A) : Set₁ where
  field
    normalisedOne : coefficient 1 ≡ Recurrence.one A

    coprimeMultiplicative :
      (m n : Nat) →
      Coprime m n →
      coefficient (m * n)
      ≡ Recurrence.mul A (coefficient m) (coefficient n)

    primePowerLane :
      (p : Nat) →
      Prime p →
      Recurrence.PrimePowerHeckeSystem
        A (scale p) (λ exponent → coefficient (p ^ exponent))

open NatHeckeClosureSystem public

------------------------------------------------------------------------
-- Prime agreement propagates along each complete prime-power lane.
------------------------------------------------------------------------

primeAgreementGivesPrimePowerAgreement :
  (A : Recurrence.RecurrenceCoefficientAlgebra) →
  (scale : Nat → Recurrence.Carrier A) →
  (a b : Nat → Recurrence.Carrier A) →
  NatHeckeClosureSystem A scale a →
  NatHeckeClosureSystem A scale b →
  (p : Nat) →
  (primeP : Prime p) →
  a p ≡ b p →
  (exponent : Nat) →
  a (p ^ exponent) ≡ b (p ^ exponent)
primeAgreementGivesPrimePowerAgreement
  A scale a b ha hb p primeP agreeP exponent =
  Recurrence.primePowerDeterminedByPrimeEigenvalue
    A (scale p)
    (λ e → a (p ^ e))
    (λ e → b (p ^ e))
    (primePowerLane ha p primeP)
    (primePowerLane hb p primeP)
    agreeP exponent

positivePrimePowerAgreement :
  (A : Recurrence.RecurrenceCoefficientAlgebra) →
  (scale : Nat → Recurrence.Carrier A) →
  (a b : Nat → Recurrence.Carrier A) →
  NatHeckeClosureSystem A scale a →
  NatHeckeClosureSystem A scale b →
  ((p : Nat) → Prime p → a p ≡ b p) →
  (atom : PositivePrimePower) →
  a (primePowerValue atom) ≡ b (primePowerValue atom)
positivePrimePowerAgreement A scale a b ha hb agreePrime atom =
  primeAgreementGivesPrimePowerAgreement
    A scale a b ha hb
    (prime atom) (primeProof atom)
    (agreePrime (prime atom) (primeProof atom))
    (suc (exponentMinusOne atom))

------------------------------------------------------------------------
-- Full multiplicative closure on a proof-carrying decomposition.
------------------------------------------------------------------------

agreeOnPrimePowerDecomposition :
  (A : Recurrence.RecurrenceCoefficientAlgebra) →
  (scale : Nat → Recurrence.Carrier A) →
  (a b : Nat → Recurrence.Carrier A) →
  (ha : NatHeckeClosureSystem A scale a) →
  (hb : NatHeckeClosureSystem A scale b) →
  ((p : Nat) → Prime p → a p ≡ b p) →
  {n : Nat} →
  PrimePowerDecomposition n →
  a n ≡ b n
agreeOnPrimePowerDecomposition A scale a b ha hb agreePrime decompositionOne =
  trans (normalisedOne ha) (sym (normalisedOne hb))
agreeOnPrimePowerDecomposition
  A scale a b ha hb agreePrime
  (decompositionCons atom {rest} restDecomposition coprime) =
  trans
    (coprimeMultiplicative ha (primePowerValue atom) rest coprime)
    (trans
      (cong₂ (Recurrence.mul A)
        (positivePrimePowerAgreement
          A scale a b ha hb agreePrime atom)
        (agreeOnPrimePowerDecomposition
          A scale a b ha hb agreePrime restDecomposition))
      (sym
        (coprimeMultiplicative hb
          (primePowerValue atom) rest coprime)))

------------------------------------------------------------------------
-- Arbitrary-S closure on the same decomposition.
------------------------------------------------------------------------

agreeOnAllowedPrimePowerDecomposition :
  (A : Recurrence.RecurrenceCoefficientAlgebra) →
  (scale : Nat → Recurrence.Carrier A) →
  (a b : Nat → Recurrence.Carrier A) →
  (ha : NatHeckeClosureSystem A scale a) →
  (hb : NatHeckeClosureSystem A scale b) →
  (Allowed : Nat → Set) →
  ((p : Nat) → Prime p → Allowed p → a p ≡ b p) →
  {n : Nat} →
  AllowedPrimePowerDecomposition Allowed n →
  a n ≡ b n
agreeOnAllowedPrimePowerDecomposition
  A scale a b ha hb Allowed agreePrime allowedOne =
  trans (normalisedOne ha) (sym (normalisedOne hb))
agreeOnAllowedPrimePowerDecomposition
  A scale a b ha hb Allowed agreePrime
  (allowedCons atom allowed {rest} restDecomposition coprime) =
  trans
    (coprimeMultiplicative ha (primePowerValue atom) rest coprime)
    (trans
      (cong₂ (Recurrence.mul A)
        (primeAgreementGivesPrimePowerAgreement
          A scale a b ha hb
          (prime atom) (primeProof atom)
          (agreePrime (prime atom) (primeProof atom) allowed)
          (suc (exponentMinusOne atom)))
        (agreeOnAllowedPrimePowerDecomposition
          A scale a b ha hb Allowed agreePrime restDecomposition))
      (sym
        (coprimeMultiplicative hb
          (primePowerValue atom) rest coprime)))

------------------------------------------------------------------------
-- The constructive Nat factorisation producer really exists in the pinned
-- stdlib.  We expose it here so the remaining grouping seam cannot be mistaken
-- for a missing fundamental-theorem-of-arithmetic assumption.
------------------------------------------------------------------------

canonicalRawPrimeFactorisation :
  (n : Nat) →
  {{nonzero : NonZero n}} →
  PrimeFactorisation n
canonicalRawPrimeFactorisation n = factorise n

record AristotleHeckeGeneralDecompositionBoundary : Set where
  field
    stdlibRawPrimeFactorisationConstructed : Bool
    stdlibRawPrimeFactorisationConstructedIsTrue :
      stdlibRawPrimeFactorisationConstructed ≡ true

    primePowerAgreementConstructed : Bool
    primePowerAgreementConstructedIsTrue :
      primePowerAgreementConstructed ≡ true

    arbitrarySDecompositionClosureConstructed : Bool
    arbitrarySDecompositionClosureConstructedIsTrue :
      arbitrarySDecompositionClosureConstructed ≡ true

    rawFactorsGroupedIntoCoprimePrimePowersHere : Bool
    rawFactorsGroupedIntoCoprimePrimePowersHereIsFalse :
      rawFactorsGroupedIntoCoprimePrimePowersHere ≡ false

    sourceFiniteSeparatingBoundConstructedHere : Bool
    sourceFiniteSeparatingBoundConstructedHereIsFalse :
      sourceFiniteSeparatingBoundConstructedHere ≡ false

canonicalAristotleHeckeGeneralDecompositionBoundary :
  AristotleHeckeGeneralDecompositionBoundary
canonicalAristotleHeckeGeneralDecompositionBoundary = record
  { stdlibRawPrimeFactorisationConstructed = true
  ; stdlibRawPrimeFactorisationConstructedIsTrue = refl
  ; primePowerAgreementConstructed = true
  ; primePowerAgreementConstructedIsTrue = refl
  ; arbitrarySDecompositionClosureConstructed = true
  ; arbitrarySDecompositionClosureConstructedIsTrue = refl
  ; rawFactorsGroupedIntoCoprimePrimePowersHere = false
  ; rawFactorsGroupedIntoCoprimePrimePowersHereIsFalse = refl
  ; sourceFiniteSeparatingBoundConstructedHere = false
  ; sourceFiniteSeparatingBoundConstructedHereIsFalse = refl
  }
