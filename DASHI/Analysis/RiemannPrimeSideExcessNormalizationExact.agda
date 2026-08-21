module DASHI.Analysis.RiemannPrimeSideExcessNormalizationExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Normalize the nonzero Alpöge--Furman Frobenius main term before asking an
-- arithmetic estimate to kill a Hermitian transverse excess.
--
-- Source scale:
--   tr Gtilde^2 = (T L / 2pi) (ell_1^2 + L^2/3) (1 + O(E_T)).
--
-- Hence raw Frobenius energy is not the vanishing observable.  The relevant
-- object is an excess above a critical-line-compatible main term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Data.Empty using (⊥)

record PrimeSideExcessNormalization : Set where
  constructor primeSideExcessNormalization
  field
    criticalCompatibleMainTerm : Nat
    normalizedHermitianExcess : Nat
    rawFrobeniusTrace : Nat
    normalizationIdentity :
      criticalCompatibleMainTerm + normalizedHermitianExcess ≡ rawFrobeniusTrace

open PrimeSideExcessNormalization public

record PrimeSideExcessErrorLedger
  (n : PrimeSideExcessNormalization) : Set where
  constructor primeSideExcessErrorLedger
  field
    arithmeticErrorBudget : Nat
    errorSlack : Nat
    excessWithinError :
      normalizedHermitianExcess n + errorSlack ≡ arithmeticErrorBudget

open PrimeSideExcessErrorLedger public

zeroExcessNonzeroRawWitness : PrimeSideExcessNormalization
zeroExcessNonzeroRawWitness = primeSideExcessNormalization 10 0 10 refl

rawTraceCanRemainTenAtZeroExcess :
  rawFrobeniusTrace zeroExcessNonzeroRawWitness ≡ 10
rawTraceCanRemainTenAtZeroExcess = refl

normalizedExcessCanVanishAtRawTen :
  normalizedHermitianExcess zeroExcessNonzeroRawWitness ≡ zero
normalizedExcessCanVanishAtRawTen = refl

tenIsNotZero : 10 ≡ zero → ⊥
tenIsNotZero ()

rawTraceNeedNotVanishWhenExcessVanishes :
  rawFrobeniusTrace zeroExcessNonzeroRawWitness ≡ zero → ⊥
rawTraceNeedNotVanishWhenExcessVanishes = tenIsNotZero

record AlpogeFurmanTraceScaleAdapter : Set₁ where
  field
    HeightScale : Set
    T : HeightScale → Nat
    L : HeightScale → Nat
    ell1 : HeightScale → Nat
    criticalCompatibleMainTerm : HeightScale → Nat
    rawFrobeniusTrace : HeightScale → Nat
    normalizedExcess : HeightScale → Nat
    arithmeticErrorBudget : HeightScale → Nat
    normalization : HeightScale → PrimeSideExcessNormalization

record PrimeSideExcessNormalizationBoundary : Set where
  field
    nonzeroMainTermNormalizationConstructed : Bool
    rawTraceNoGoWitnessConstructed : Bool
    normalizedErrorLedgerConstructed : Bool
    sourceTraceAsymptoticRecorded : Bool
    exactSourceMainTermExtractionProvedHere : Bool
    normalizedZetaExcessBoundProvedHere : Bool
    normalizedExcessTendsToZeroProvedHere : Bool

primeSideExcessNormalizationBoundary : PrimeSideExcessNormalizationBoundary
primeSideExcessNormalizationBoundary = record
  { nonzeroMainTermNormalizationConstructed = true
  ; rawTraceNoGoWitnessConstructed = true
  ; normalizedErrorLedgerConstructed = true
  ; sourceTraceAsymptoticRecorded = true
  ; exactSourceMainTermExtractionProvedHere = false
  ; normalizedZetaExcessBoundProvedHere = false
  ; normalizedExcessTendsToZeroProvedHere = false
  }
