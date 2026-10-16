module DASHI.Analysis.CollatzSyracuseSharpBarrierTransitionExact where

------------------------------------------------------------------------
-- SHARP BARRIER TRANSITION UNDER LATE EVEN STEPS
--
-- Appending a late even parity bit preserves the affine correction A and odd
-- count while enlarging the positive coefficient gap.  Therefore the exact
-- sharp threshold floor(A/g)+1 can only decrease (or stay fixed).
--
-- This is the first rank-like law for the sharp affine barrier.  It is local
-- to an already-contracting literal word and does not prove that every actual
-- trajectory reaches such a word.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _<_)
import Data.Nat.Properties as NatP

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox
import DASHI.Analysis.CollatzSyracuseSharpBarrierThresholdExact as Sharp
import DASHI.Analysis.CollatzSyracuseTrailingZeroCertificateExact as Zero
import DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact as Cert

appendZeroSharpCoefficient :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Paradox.ContractingCoefficientGap (Zero.appendZero word)
appendZeroSharpCoefficient word coefficient =
  let
    certificate = Sharp.sharpContractingWordCertificate word coefficient
    oldGap = Paradox.gap coefficient
    newGap = Zero.extendedGap word certificate

    oldGapBelowNew : oldGap ≤ newGap
    oldGapBelowNew =
      NatP.m≤m+n
        oldGap
        (Affine.powNat 3 (Affine.parityCount word) + oldGap)

    newPositive : zero < newGap
    newPositive =
      NatP.<-≤-trans
        (Paradox.gapPositive coefficient)
        oldGapBelowNew
  in
  record
    { Paradox.gap = newGap
    ; Paradox.gapPositive = newPositive
    ; Paradox.denominatorSplit =
        Zero.trailingZeroDenominatorSplit word certificate
    }

trailingEvenSharpThresholdNonincreasing :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Sharp.sharpMinimumStart
    (Zero.appendZero word)
    (appendZeroSharpCoefficient word coefficient)
  ≤ Sharp.sharpMinimumStart word coefficient
trailingEvenSharpThresholdNonincreasing word coefficient =
  let
    oldCertificate = Sharp.sharpContractingWordCertificate word coefficient
    newCoefficient = appendZeroSharpCoefficient word coefficient
  in
  Sharp.sharpThresholdIsMinimalUniformAffineThreshold
    (Zero.appendZero word)
    newCoefficient
    (Sharp.sharpMinimumStart word coefficient)
    (Zero.trailingZeroCorrectionFits word oldCertificate)

appendZerosSharpCoefficient :
  (r : Nat) →
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Paradox.ContractingCoefficientGap word →
  Paradox.ContractingCoefficientGap (Zero.appendZeros r word)
appendZerosSharpCoefficient zero word coefficient = coefficient
appendZerosSharpCoefficient (suc r) word coefficient =
  appendZeroSharpCoefficient
    (Zero.appendZeros r word)
    (appendZerosSharpCoefficient r word coefficient)

arbitraryTrailingEvenSharpThresholdNonincreasing :
  (r : Nat) →
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Sharp.sharpMinimumStart
    (Zero.appendZeros r word)
    (appendZerosSharpCoefficient r word coefficient)
  ≤ Sharp.sharpMinimumStart word coefficient
arbitraryTrailingEvenSharpThresholdNonincreasing zero word coefficient =
  NatP.≤-refl
arbitraryTrailingEvenSharpThresholdNonincreasing (suc r) word coefficient =
  NatP.≤-trans
    (trailingEvenSharpThresholdNonincreasing
      (Zero.appendZeros r word)
      (appendZerosSharpCoefficient r word coefficient))
    (arbitraryTrailingEvenSharpThresholdNonincreasing
      r word coefficient)

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record SharpBarrierTransitionBoundary : Set where
  constructor sharpBarrierTransitionBoundary
  field
    trailingEvenSharpCoefficientPaid : Nat
    trailingEvenSharpThresholdNonincreasingPaid : Nat
    arbitraryTrailingEvenSharpThresholdNonincreasingPaid : Nat
    rankLikeLocalMonotonicityPaid : Nat

    trailingOddSharpThresholdAlwaysNonincreasing : Nat
    localBarrierMonotonicityCreatesUniversalEscape : Nat

canonicalSharpBarrierTransitionBoundary : SharpBarrierTransitionBoundary
canonicalSharpBarrierTransitionBoundary =
  sharpBarrierTransitionBoundary
    1 1 1 1
    0 0
