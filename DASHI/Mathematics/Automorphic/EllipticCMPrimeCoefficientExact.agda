module DASHI.Mathematics.Automorphic.EllipticCMPrimeCoefficientExact where

------------------------------------------------------------------------
-- CM PRIME-LEVEL COEFFICIENT ALGEBRA FOR E : y^2 = x^3 - x
--
-- For a split good prime with a supplied sum-of-two-squares witness
--
--   p = u^2 + v^2,
--
-- the CM coefficient has magnitude 2u (up to the standard sign/primary
-- normalization).  The exact identity
--
--   (2u)^2 + (2v)^2 = 4p
--
-- is enough to expose the Hasse-size control algebraically without invoking
-- square roots.  Inert good primes have coefficient zero.
--
-- This module intentionally does NOT assert that every good prime has already
-- been classified into the correct CM case, nor does it choose the sign of the
-- split coefficient.  Those are the remaining number-theoretic producer seams.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Primality using (Prime)
open import Data.Nat.Tactic.RingSolver using (solve)

square : Nat → Nat
square n = n * n

double : Nat → Nat
double n = n + n

fourTimes : Nat → Nat
fourTimes n = double (double n)

record SplitPrimeSumOfSquares (p : Nat) : Set where
  constructor split-prime-sum-of-squares
  field
    u v : Nat

    normExact :
      p ≡ square u + square v

open SplitPrimeSumOfSquares public

splitCoefficientMagnitude :
  ∀ {p} →
  SplitPrimeSumOfSquares p →
  Nat
splitCoefficientMagnitude witness =
  double (u witness)

splitCompanionMagnitude :
  ∀ {p} →
  SplitPrimeSumOfSquares p →
  Nat
splitCompanionMagnitude witness =
  double (v witness)

splitPrimeCoefficientNormIdentity :
  ∀ {p}
    (witness : SplitPrimeSumOfSquares p) →
  square (splitCoefficientMagnitude witness)
  + square (splitCompanionMagnitude witness)
  ≡ fourTimes p
splitPrimeCoefficientNormIdentity
    {p} (split-prime-sum-of-squares u v normExact)
    rewrite normExact =
  solve (u ∷ v ∷ [])
  where
    open import Agda.Builtin.List using ([]; _∷_)

data GoodPrimeCMCase (p : Nat) : Set where
  inertCase :
    GoodPrimeCMCase p

  splitCase :
    SplitPrimeSumOfSquares p →
    GoodPrimeCMCase p

cmPrimeCoefficientMagnitude :
  ∀ {p} →
  GoodPrimeCMCase p →
  Nat
cmPrimeCoefficientMagnitude inertCase =
  zero
cmPrimeCoefficientMagnitude (splitCase witness) =
  splitCoefficientMagnitude witness

inertPrimeCoefficientMagnitudeZero :
  ∀ {p} →
  cmPrimeCoefficientMagnitude
    (inertCase {p})
  ≡ zero
inertPrimeCoefficientMagnitudeZero = refl

record GoodPrimeCMClassification : Set₁ where
  field
    classify :
      (p : Nat) →
      Prime p →
      p ≡ 2 →
      GoodPrimeCMCase p

open GoodPrimeCMClassification public

record EllipticCMPrimeCoefficientBoundary : Set where
  constructor elliptic-cm-prime-coefficient-boundary
  field
    splitPrimeSumOfSquaresCarrierPaid : Bool
    splitCoefficientMagnitudePaid : Bool
    splitPrimeCoefficientNormIdentityPaid : Bool
    inertPrimeCoefficientZeroPaid : Bool
    splitCoefficientSignNormalizationPaid : Bool
    allGoodPrimeCMClassificationPaid : Bool
    allPrimeEllipticCoefficientFamilyPaid : Bool
    primePowerHeckePropagationPaid : Bool
    allNCoefficientFamilyPaid : Bool
    globalCoefficientGrowthBoundPaid : Bool
    dirichletTailPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticCMPrimeCoefficientBoundary :
  EllipticCMPrimeCoefficientBoundary
canonicalEllipticCMPrimeCoefficientBoundary =
  elliptic-cm-prime-coefficient-boundary
    true true true true false false false false false false false false
