module DASHI.Analysis.CollatzSyracuseContractingWordFamilyExact where

------------------------------------------------------------------------
-- PARAMETRIC CONTRACTING-WORD FAMILY THEOREM
--
-- If a literal parity word w has positive multiplicative gap
--
--   2^m = 3^(ones w) + g,   g > 0,
--
-- then the exact affine correction A(w) itself gives a canonical uniform
-- threshold.  Every matching literal start x >= A(w)+1 descends after m
-- Syracuse steps.
--
-- This removes the need to hand-prove one inequality per contracting word.
-- It does NOT prove that every residual start eventually reaches such a word.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_<_; _≤_)
import Data.Nat.Properties as NatP

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox
import DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact as Uniform

canonicalCorrectionThresholdFits :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Affine.affineAdditiveTerm word
  < Paradox.gap coefficient * suc (Affine.affineAdditiveTerm word)
canonicalCorrectionThresholdFits word coefficient =
  NatP.<-≤-trans
    (NatP.n<1+n (Affine.affineAdditiveTerm word))
    (NatP.*-monoˡ-≤
      (suc (Affine.affineAdditiveTerm word))
      (Paradox.gapPositive coefficient))

canonicalContractingWordCertificate :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Paradox.ContractingCoefficientGap word →
  Uniform.UniformWordDescentCertificate word
canonicalContractingWordCertificate word coefficient = record
  { Uniform.gap = Paradox.gap coefficient
  ; Uniform.minimumStart = suc (Affine.affineAdditiveTerm word)
  ; Uniform.denominatorSplit = Paradox.denominatorSplit coefficient
  ; Uniform.correctionBelowGapAtMinimum =
      canonicalCorrectionThresholdFits word coefficient
  }

contractingWordFamilyDescends :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  (x : Syracuse.PositiveNat) →
  suc (Affine.affineAdditiveTerm word) ≤ Syracuse.toNat x →
  Itinerary.parityWord m x ≡ word →
  Syracuse.toNat (Syracuse.syracuseIterate m x)
    < Syracuse.toNat x
contractingWordFamilyDescends word coefficient x aboveThreshold wordMatch =
  Uniform.uniformWordCertificateImpliesDescent
    word
    (canonicalContractingWordCertificate word coefficient)
    x
    aboveThreshold
    wordMatch

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ContractingWordFamilyBoundary : Set where
  constructor contractingWordFamilyBoundary
  field
    positiveGapToCorrectionBoundPaid : Nat
    canonicalCorrectionPlusOneThresholdPaid : Nat
    everyContractingWordGetsUniformCertificate : Nat
    literalParityMatchStillRequired : Nat

    contractingWordFamilyAutomaticallyCoversEveryResidualStart : Nat
    noncontractingPrefixAutomaticallyDescends : Nat
    finiteWordEnumerationPromotedToUniversalStopping : Nat

canonicalContractingWordFamilyBoundary : ContractingWordFamilyBoundary
canonicalContractingWordFamilyBoundary =
  contractingWordFamilyBoundary
    1 1 1 1
    0 0 0
