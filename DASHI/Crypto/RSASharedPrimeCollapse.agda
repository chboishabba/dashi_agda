module DASHI.Crypto.RSASharedPrimeCollapse where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat.Coprimality using (Coprime)
open import Data.Nat.Divisibility using
  ( _∣_
  ; divides
  ; m∣n⇒n≡m*quotient
  ; ∣m⇒∣m*n
  )
open import Data.Nat.Properties using (*-assoc; *-comm)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  ( _≡_
  ; refl
  ; subst
  )

import DASHI.Arithmetic.CoprimeLayer as CoprimeLayer
import DASHI.Crypto.RSABatchSharedPrimeBoundary as Batch

------------------------------------------------------------------------
-- Shared-prime collapse witness surface.
--
-- This module keeps the proof-carrying part narrow and honest:
--   * a common divisor witness records a divisor and its two divisibility
--     projections,
--   * a nontrivial common divisor only asserts that the divisor is not 1,
--   * a recovered factor witness records the factor, quotient, and
--     reconstruction equation for one modulus.
--
-- The central theorem here is projection-only:
-- a nontrivial common divisor for N1 and N2 yields a recovered factor
-- witness for N1 and a recovered factor witness for N2.  We stop there and
-- do not claim a gcd equality theorem.

_≢_ : Nat → Nat → Set
m ≢ n = m ≡ n → ⊥

------------------------------------------------------------------------
-- Proof-bearing witness records.

record CommonDivisorWitness : Set where
  constructor mkCommonDivisorWitness
  field
    leftModulus :
      Nat

    rightModulus :
      Nat

    commonDivisor :
      Nat

    commonDivisorDividesLeft :
      commonDivisor ∣ leftModulus

    commonDivisorDividesRight :
      commonDivisor ∣ rightModulus

open CommonDivisorWitness public

record NontrivialCommonDivisor : Set where
  constructor mkNontrivialCommonDivisor
  field
    commonDivisorWitness :
      CommonDivisorWitness

    commonDivisorNonUnit :
      commonDivisor commonDivisorWitness ≢ 1

open NontrivialCommonDivisor public

record RecoveredFactorWitness : Set where
  constructor mkRecoveredFactorWitness
  field
    recoveredModulus :
      Nat

    recoveredFactor :
      Nat

    recoveredFactorQuotient :
      Nat

    recoveredFactorDividesModulus :
      recoveredFactor ∣ recoveredModulus

    recoveredFactorReconstruction :
      recoveredModulus ≡ recoveredFactor * recoveredFactorQuotient

open RecoveredFactorWitness public

------------------------------------------------------------------------
-- Projection lemmas.

commonDivisorDividesProduct :
  ∀ w →
  commonDivisor w ∣ leftModulus w * rightModulus w
commonDivisorDividesProduct w =
  ∣m⇒∣m*n (rightModulus w) (commonDivisorDividesLeft w)

commonDivisorWitness→RecoveredFactorWitnessLeft :
  CommonDivisorWitness →
  RecoveredFactorWitness
commonDivisorWitness→RecoveredFactorWitnessLeft w =
  mkRecoveredFactorWitness
    (leftModulus w)
    (commonDivisor w)
    (_∣_.quotient (commonDivisorDividesLeft w))
    (commonDivisorDividesLeft w)
    (m∣n⇒n≡m*quotient (commonDivisorDividesLeft w))

commonDivisorWitness→RecoveredFactorWitnessRight :
  CommonDivisorWitness →
  RecoveredFactorWitness
commonDivisorWitness→RecoveredFactorWitnessRight w =
  mkRecoveredFactorWitness
    (rightModulus w)
    (commonDivisor w)
    (_∣_.quotient (commonDivisorDividesRight w))
    (commonDivisorDividesRight w)
    (m∣n⇒n≡m*quotient (commonDivisorDividesRight w))

nontrivialCommonDivisor→RecoveredFactorWitnessLeft :
  NontrivialCommonDivisor →
  RecoveredFactorWitness
nontrivialCommonDivisor→RecoveredFactorWitnessLeft w =
  commonDivisorWitness→RecoveredFactorWitnessLeft
    (commonDivisorWitness w)

nontrivialCommonDivisor→RecoveredFactorWitnessRight :
  NontrivialCommonDivisor →
  RecoveredFactorWitness
nontrivialCommonDivisor→RecoveredFactorWitnessRight w =
  commonDivisorWitness→RecoveredFactorWitnessRight
    (commonDivisorWitness w)

nontrivialCommonDivisorIsWitness :
  ∀ w →
  CommonDivisorWitness
nontrivialCommonDivisorIsWitness =
  commonDivisorWitness

nontrivialCommonDivisorIsNonUnit :
  ∀ w →
  commonDivisor (commonDivisorWitness w) ≢ 1
nontrivialCommonDivisorIsNonUnit =
  commonDivisorNonUnit

recoveredFactorWitnessLeftModulus :
  ∀ w →
  recoveredModulus (nontrivialCommonDivisor→RecoveredFactorWitnessLeft w)
  ≡
  leftModulus (commonDivisorWitness w)
recoveredFactorWitnessLeftModulus _ = refl

recoveredFactorWitnessRightModulus :
  ∀ w →
  recoveredModulus (nontrivialCommonDivisor→RecoveredFactorWitnessRight w)
  ≡
  rightModulus (commonDivisorWitness w)
recoveredFactorWitnessRightModulus _ = refl

recoveredFactorWitnessLeftFactor :
  ∀ w →
  recoveredFactor (nontrivialCommonDivisor→RecoveredFactorWitnessLeft w)
  ≡
  commonDivisor (commonDivisorWitness w)
recoveredFactorWitnessLeftFactor _ = refl

recoveredFactorWitnessRightFactor :
  ∀ w →
  recoveredFactor (nontrivialCommonDivisor→RecoveredFactorWitnessRight w)
  ≡
  commonDivisor (commonDivisorWitness w)
recoveredFactorWitnessRightFactor _ = refl

------------------------------------------------------------------------
-- Product-sharing helpers.

coprimeProductDivides :
  ∀ m n o →
  Coprime m n →
  m ∣ o →
  n ∣ o →
  m * n ∣ o
coprimeProductDivides =
  CoprimeLayer.coprimeProductDivides

commonDivisorProductShares :
  ∀ w →
  commonDivisor w ∣ leftModulus w * rightModulus w
commonDivisorProductShares w =
  ∣m⇒∣m*n (rightModulus w) (commonDivisorDividesLeft w)

leftFactorSharesAcrossProduct :
  ∀ w →
  recoveredFactor (nontrivialCommonDivisor→RecoveredFactorWitnessLeft w)
  ∣
  leftModulus (commonDivisorWitness w) * rightModulus (commonDivisorWitness w)
leftFactorSharesAcrossProduct w =
  subst
    (λ n → n ∣ leftModulus (commonDivisorWitness w) * rightModulus (commonDivisorWitness w))
    (recoveredFactorWitnessLeftFactor w)
    (commonDivisorProductShares (commonDivisorWitness w))

rightFactorSharesAcrossProduct :
  ∀ w →
  recoveredFactor (nontrivialCommonDivisor→RecoveredFactorWitnessRight w)
  ∣
  leftModulus (commonDivisorWitness w) * rightModulus (commonDivisorWitness w)
rightFactorSharesAcrossProduct w =
  subst
    (λ n → n ∣ leftModulus (commonDivisorWitness w) * rightModulus (commonDivisorWitness w))
    (recoveredFactorWitnessRightFactor w)
    (commonDivisorProductShares (commonDivisorWitness w))

record RSASharedPrimeCollapseVerifier : Set₁ where
  field
    witnessToRecoveredFactorWitnessLeft :
      CommonDivisorWitness →
      RecoveredFactorWitness

    witnessToRecoveredFactorWitnessRight :
      CommonDivisorWitness →
      RecoveredFactorWitness

    nontrivialWitnessToRecoveredFactorWitnessLeft :
      NontrivialCommonDivisor →
      RecoveredFactorWitness

    nontrivialWitnessToRecoveredFactorWitnessRight :
      NontrivialCommonDivisor →
      RecoveredFactorWitness

    commonDivisorProductSharesVerifier :
      ∀ w →
      commonDivisor w ∣ leftModulus w * rightModulus w

    coprimeProductDividesVerifier :
      ∀ m n o →
      Coprime m n →
      m ∣ o →
      n ∣ o →
      m * n ∣ o

open RSASharedPrimeCollapseVerifier public

canonicalRSASharedPrimeCollapseVerifier :
  RSASharedPrimeCollapseVerifier
canonicalRSASharedPrimeCollapseVerifier = record
  { witnessToRecoveredFactorWitnessLeft =
      commonDivisorWitness→RecoveredFactorWitnessLeft
  ; witnessToRecoveredFactorWitnessRight =
      commonDivisorWitness→RecoveredFactorWitnessRight
  ; nontrivialWitnessToRecoveredFactorWitnessLeft =
      nontrivialCommonDivisor→RecoveredFactorWitnessLeft
  ; nontrivialWitnessToRecoveredFactorWitnessRight =
      nontrivialCommonDivisor→RecoveredFactorWitnessRight
  ; commonDivisorProductSharesVerifier =
      commonDivisorDividesProduct
  ; coprimeProductDividesVerifier =
      coprimeProductDivides
  }

------------------------------------------------------------------------
-- Shared-prime collapse boundary surface.

data RSASharedPrimeCollapseBoundaryKind : Set where
  commonDivisorWitnessKind : RSASharedPrimeCollapseBoundaryKind

  nontrivialCommonDivisorKind : RSASharedPrimeCollapseBoundaryKind

  recoveredFactorWitnessKind : RSASharedPrimeCollapseBoundaryKind

  batchBoundaryIntegrationKind : RSASharedPrimeCollapseBoundaryKind

  futureRSAArithmeticCoreKind : RSASharedPrimeCollapseBoundaryKind

canonicalRSASharedPrimeCollapseBoundaryKinds :
  List RSASharedPrimeCollapseBoundaryKind
canonicalRSASharedPrimeCollapseBoundaryKinds =
  commonDivisorWitnessKind
  ∷ nontrivialCommonDivisorKind
  ∷ recoveredFactorWitnessKind
  ∷ batchBoundaryIntegrationKind
  ∷ futureRSAArithmeticCoreKind
  ∷ []

record RSASharedPrimeCollapseSurface : Set₁ where
  constructor mkRSASharedPrimeCollapseSurface
  field
    surfaceLabel :
      String

    batchBoundaryReference :
      String

    futureRSAArithmeticCoreReference :
      String

    surfaceBatchBoundary :
      Batch.RSABatchSharedPrimeBoundarySurface

    surfaceBatchBoundaryReceipt :
      Batch.RSABatchSharedPrimeBoundaryReceipt surfaceBatchBoundary

    surfaceVerifier :
      RSASharedPrimeCollapseVerifier

    surfaceWitness :
      NontrivialCommonDivisor

    surfaceRecoveredFactorWitnessLeft :
      RecoveredFactorWitness

    surfaceRecoveredFactorWitnessRight :
      RecoveredFactorWitness

    surfaceKinds :
      List RSASharedPrimeCollapseBoundaryKind

    surfaceKindsAreCanonical :
      surfaceKinds ≡ canonicalRSASharedPrimeCollapseBoundaryKinds

    surfaceCandidateOnly :
      Bool

    surfaceVerified :
      Bool

    surfaceBlocked :
      Bool

    surfaceStatement :
      String

    surfaceGap :
      String

open RSASharedPrimeCollapseSurface public

record RSASharedPrimeCollapseSurfaceReceipt
  (surface : RSASharedPrimeCollapseSurface) :
  Set where
  constructor mkRSASharedPrimeCollapseSurfaceReceipt
  field
    surfaceKindsCanonical :
      surfaceKinds surface ≡ canonicalRSASharedPrimeCollapseBoundaryKinds

    surfaceCandidateOnlyIsTrue :
      surfaceCandidateOnly surface ≡ true

    surfaceVerifiedIsTrue :
      surfaceVerified surface ≡ true

    surfaceBlockedIsFalse :
      surfaceBlocked surface ≡ false

    surfaceLeftRecoveredFromWitness :
      surfaceRecoveredFactorWitnessLeft surface
      ≡
      nontrivialCommonDivisor→RecoveredFactorWitnessLeft
        (surfaceWitness surface)

    surfaceRightRecoveredFromWitness :
      surfaceRecoveredFactorWitnessRight surface
      ≡
      nontrivialCommonDivisor→RecoveredFactorWitnessRight
        (surfaceWitness surface)

open RSASharedPrimeCollapseSurfaceReceipt public

------------------------------------------------------------------------
-- Canonical concrete witness.

canonicalCommonDivisorWitness :
  CommonDivisorWitness
canonicalCommonDivisorWitness =
  mkCommonDivisorWitness
    15
    21
    3
    (divides 5 refl)
    (divides 7 refl)

canonicalNontrivialCommonDivisor :
  NontrivialCommonDivisor
canonicalNontrivialCommonDivisor =
  mkNontrivialCommonDivisor
    canonicalCommonDivisorWitness
    (λ ())

canonicalRecoveredFactorWitnessLeft :
  RecoveredFactorWitness
canonicalRecoveredFactorWitnessLeft =
  nontrivialCommonDivisor→RecoveredFactorWitnessLeft
    canonicalNontrivialCommonDivisor

canonicalRecoveredFactorWitnessRight :
  RecoveredFactorWitness
canonicalRecoveredFactorWitnessRight =
  nontrivialCommonDivisor→RecoveredFactorWitnessRight
    canonicalNontrivialCommonDivisor

canonicalRSASharedPrimeCollapseSurface :
  RSASharedPrimeCollapseSurface
canonicalRSASharedPrimeCollapseSurface =
  mkRSASharedPrimeCollapseSurface
    "RSA shared-prime collapse"
    "DASHI.Crypto.RSABatchSharedPrimeBoundary"
    "DASHI.Crypto.RSAArithmeticCore"
    Batch.canonicalRSABatchSharedPrimeBoundarySurface
    Batch.canonicalRSABatchSharedPrimeBoundaryReceipt
    canonicalRSASharedPrimeCollapseVerifier
    canonicalNontrivialCommonDivisor
    canonicalRecoveredFactorWitnessLeft
    canonicalRecoveredFactorWitnessRight
    canonicalRSASharedPrimeCollapseBoundaryKinds
    refl
    true
    true
    false
    "shared-prime common divisor witness with projected factor recovery for both moduli"
    "the module stops short of gcd equality and only records the recovered-factor projection surface"

canonicalRSASharedPrimeCollapseSurfaceReceipt :
  RSASharedPrimeCollapseSurfaceReceipt
    canonicalRSASharedPrimeCollapseSurface
canonicalRSASharedPrimeCollapseSurfaceReceipt =
  mkRSASharedPrimeCollapseSurfaceReceipt
    refl
    refl
    refl
    refl
    refl
    refl

canonicalRSASharedPrimeCollapseSurfaceKindsAreCanonical :
  surfaceKinds canonicalRSASharedPrimeCollapseSurface
  ≡
  canonicalRSASharedPrimeCollapseBoundaryKinds
canonicalRSASharedPrimeCollapseSurfaceKindsAreCanonical =
  surfaceKindsCanonical canonicalRSASharedPrimeCollapseSurfaceReceipt

canonicalRSASharedPrimeCollapseSurfaceCandidateOnlyIsTrue :
  surfaceCandidateOnly canonicalRSASharedPrimeCollapseSurface ≡ true
canonicalRSASharedPrimeCollapseSurfaceCandidateOnlyIsTrue =
  surfaceCandidateOnlyIsTrue canonicalRSASharedPrimeCollapseSurfaceReceipt

canonicalRSASharedPrimeCollapseSurfaceVerifiedIsTrue :
  surfaceVerified canonicalRSASharedPrimeCollapseSurface ≡ true
canonicalRSASharedPrimeCollapseSurfaceVerifiedIsTrue =
  surfaceVerifiedIsTrue canonicalRSASharedPrimeCollapseSurfaceReceipt

canonicalRSASharedPrimeCollapseSurfaceBlockedIsFalse :
  surfaceBlocked canonicalRSASharedPrimeCollapseSurface ≡ false
canonicalRSASharedPrimeCollapseSurfaceBlockedIsFalse =
  surfaceBlockedIsFalse canonicalRSASharedPrimeCollapseSurfaceReceipt

canonicalRSASharedPrimeCollapseSurfaceLeftRecoveredFromWitness :
  surfaceRecoveredFactorWitnessLeft canonicalRSASharedPrimeCollapseSurface
  ≡
  nontrivialCommonDivisor→RecoveredFactorWitnessLeft
    canonicalNontrivialCommonDivisor
canonicalRSASharedPrimeCollapseSurfaceLeftRecoveredFromWitness =
  surfaceLeftRecoveredFromWitness canonicalRSASharedPrimeCollapseSurfaceReceipt

canonicalRSASharedPrimeCollapseSurfaceRightRecoveredFromWitness :
  surfaceRecoveredFactorWitnessRight canonicalRSASharedPrimeCollapseSurface
  ≡
  nontrivialCommonDivisor→RecoveredFactorWitnessRight
    canonicalNontrivialCommonDivisor
canonicalRSASharedPrimeCollapseSurfaceRightRecoveredFromWitness =
  surfaceRightRecoveredFromWitness canonicalRSASharedPrimeCollapseSurfaceReceipt
