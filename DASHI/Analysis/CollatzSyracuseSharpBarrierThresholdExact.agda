module DASHI.Analysis.CollatzSyracuseSharpBarrierThresholdExact where

------------------------------------------------------------------------
-- SHARP AFFINE BARRIER THRESHOLD
--
-- For a contracting literal parity word w,
--
--   2^m = 3^(ones w) + g,  g > 0,
--   2^m T^m(x) = 3^(ones w) x + A(w),
--
-- the exact least uniform natural threshold forced by this affine inequality
-- is
--
--   N*(w) = floor(A(w) / g) + 1.
--
-- Every matching x >= N*(w) strictly descends.  Conversely, a literal
-- matching non-descending (paradoxical) prefix must satisfy
--
--   x <= floor(A(w) / g).
--
-- This sharpens the earlier safe A(w)+1 threshold without changing the
-- theorem-strength universal escape obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_; _<_; _/_; _%_; z≤n; s≤s)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; m%n<n; m/n*n≤m)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (yes; no)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox
import DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact as Uniform

------------------------------------------------------------------------
-- Positive-divisor quotient, exposing positivity constructively so the
-- stdlib division instance is available only in the suc branch.
------------------------------------------------------------------------

quotientByPositive :
  (numerator denominator : Nat) →
  zero < denominator →
  Nat
quotientByPositive numerator zero ()
quotientByPositive numerator (suc denominator) positive =
  numerator / suc denominator

sharpThreshold :
  (correction gap : Nat) →
  zero < gap →
  Nat
sharpThreshold correction gap positive =
  suc (quotientByPositive correction gap positive)

productSuccessorNormalize :
  (g q : Nat) →
  g + q * g ≡ g * suc q
productSuccessorNormalize =
  solve 2
    (λ g q → g :+ (q :* g) := g :* (con 1 :+ q))
    refl

quotientThresholdFits :
  (correction gap : Nat) →
  (positive : zero < gap) →
  correction < gap * sharpThreshold correction gap positive
quotientThresholdFits correction zero ()
quotientThresholdFits correction (suc gap) positive =
  let
    quotient = correction / suc gap
    remainder = correction % suc gap

    remainderBelow : remainder < suc gap
    remainderBelow = m%n<n correction (suc gap)

    decomposedBelow :
      remainder + quotient * suc gap
      < suc gap + quotient * suc gap
    decomposedBelow =
      NatP.+-monoˡ-< (quotient * suc gap) remainderBelow

    normalizedBelow :
      remainder + quotient * suc gap
      < suc gap * suc quotient
    normalizedBelow =
      subst
        (λ right → remainder + quotient * suc gap < right)
        (productSuccessorNormalize (suc gap) quotient)
        decomposedBelow
  in
  subst
    (λ left → left < suc gap * suc quotient)
    (sym (m≡m%n+[m/n]*n correction (suc gap)))
    normalizedBelow

quotientTimesGapBelowCorrection :
  (correction gap : Nat) →
  (positive : zero < gap) →
  gap * quotientByPositive correction gap positive ≤ correction
quotientTimesGapBelowCorrection correction zero ()
quotientTimesGapBelowCorrection correction (suc gap) positive =
  subst
    (λ left → left ≤ correction)
    (NatP.*-comm (correction / suc gap) (suc gap))
    (m/n*n≤m correction (suc gap))

sharpThresholdMinimal :
  (correction gap : Nat) →
  (positive : zero < gap) →
  (candidate : Nat) →
  correction < gap * candidate →
  sharpThreshold correction gap positive ≤ candidate
sharpThresholdMinimal correction zero () candidate fits
sharpThresholdMinimal correction (suc gap) positive candidate fits
  with sharpThreshold correction (suc gap) positive NatP.≤? candidate
... | yes thresholdFits = thresholdFits
... | no thresholdTooLarge =
  ⊥-elim
    (NatP.<⇒≱ fits gapCandidateBelowCorrection)
  where
  quotient = quotientByPositive correction (suc gap) positive

  candidateBelowThreshold :
    candidate < sharpThreshold correction (suc gap) positive
  candidateBelowThreshold = NatP.≰⇒> thresholdTooLarge

  candidateAtMostQuotient : candidate ≤ quotient
  candidateAtMostQuotient = NatP.<⇒≤pred candidateBelowThreshold

  scaled :
    suc gap * candidate ≤ suc gap * quotient
  scaled = NatP.*-monoʳ-≤ (suc gap) candidateAtMostQuotient

  gapQuotientBelowCorrection :
    suc gap * quotient ≤ correction
  gapQuotientBelowCorrection =
    quotientTimesGapBelowCorrection correction (suc gap) positive

  gapCandidateBelowCorrection :
    suc gap * candidate ≤ correction
  gapCandidateBelowCorrection =
    NatP.≤-trans scaled gapQuotientBelowCorrection

------------------------------------------------------------------------
-- Sharp certificate on the literal word carrier.
------------------------------------------------------------------------

sharpMinimumStart :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Paradox.ContractingCoefficientGap word →
  Nat
sharpMinimumStart word coefficient =
  sharpThreshold
    (Affine.affineAdditiveTerm word)
    (Paradox.gap coefficient)
    (Paradox.gapPositive coefficient)

sharpContractingWordCertificate :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Uniform.UniformWordDescentCertificate word
sharpContractingWordCertificate word coefficient = record
  { Uniform.gap = Paradox.gap coefficient
  ; Uniform.minimumStart = sharpMinimumStart word coefficient
  ; Uniform.denominatorSplit = Paradox.denominatorSplit coefficient
  ; Uniform.correctionBelowGapAtMinimum =
      quotientThresholdFits
        (Affine.affineAdditiveTerm word)
        (Paradox.gap coefficient)
        (Paradox.gapPositive coefficient)
  }

sharpContractingWordDescends :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  (x : Syracuse.PositiveNat) →
  sharpMinimumStart word coefficient ≤ Syracuse.toNat x →
  Itinerary.parityWord m x ≡ word →
  Syracuse.toNat (Syracuse.syracuseIterate m x)
    < Syracuse.toNat x
sharpContractingWordDescends word coefficient x aboveThreshold wordMatch =
  Uniform.uniformWordCertificateImpliesDescent
    word
    (sharpContractingWordCertificate word coefficient)
    x
    aboveThreshold
    wordMatch

sharpThresholdIsMinimalUniformAffineThreshold :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  (candidate : Nat) →
  Affine.affineAdditiveTerm word
    < Paradox.gap coefficient * candidate →
  sharpMinimumStart word coefficient ≤ candidate
sharpThresholdIsMinimalUniformAffineThreshold word coefficient candidate fits =
  sharpThresholdMinimal
    (Affine.affineAdditiveTerm word)
    (Paradox.gap coefficient)
    (Paradox.gapPositive coefficient)
    candidate
    fits

------------------------------------------------------------------------
-- Exact paradoxical bound: a matching non-descent is confined below N*.
------------------------------------------------------------------------

paradoxicalStartAtMostQuotientBarrier :
  {x : Syracuse.PositiveNat} {m : Nat} →
  (paradoxical : Paradox.ParadoxicalPrefix x m) →
  Syracuse.toNat x
  ≤ quotientByPositive
      (Affine.affineAdditiveTerm (Itinerary.parityWord m x))
      (Paradox.gap (Paradox.coefficientGap paradoxical))
      (Paradox.gapPositive (Paradox.coefficientGap paradoxical))
paradoxicalStartAtMostQuotientBarrier {x} {m} paradoxical
  with Syracuse.toNat x NatP.≤?
    quotientByPositive
      (Affine.affineAdditiveTerm (Itinerary.parityWord m x))
      (Paradox.gap (Paradox.coefficientGap paradoxical))
      (Paradox.gapPositive (Paradox.coefficientGap paradoxical))
... | yes bounded = bounded
... | no aboveQuotient =
  ⊥-elim
    (Paradox.noLiteralDescent paradoxical
      (sharpContractingWordDescends
        (Itinerary.parityWord m x)
        (Paradox.coefficientGap paradoxical)
        x
        (NatP.≰⇒> aboveQuotient)
        refl))

------------------------------------------------------------------------
-- Early-cylinder regressions: old hand thresholds become instances.
------------------------------------------------------------------------

word1100 : Binary.BinaryWord 4
word1100 =
  Binary.bit1 (Binary.bit1 (Binary.bit0 (Binary.bit0 Binary.end)))

word11010 : Binary.BinaryWord 5
word11010 =
  Binary.bit1
    (Binary.bit1
      (Binary.bit0
        (Binary.bit1 (Binary.bit0 Binary.end))))

word11100 : Binary.BinaryWord 5
word11100 =
  Binary.bit1
    (Binary.bit1
      (Binary.bit1
        (Binary.bit0 (Binary.bit0 Binary.end))))

coefficient1100 : Paradox.ContractingCoefficientGap word1100
coefficient1100 = record
  { Paradox.gap = 7
  ; Paradox.gapPositive = s≤s z≤n
  ; Paradox.denominatorSplit = refl
  }

coefficient11010 : Paradox.ContractingCoefficientGap word11010
coefficient11010 = record
  { Paradox.gap = 5
  ; Paradox.gapPositive = s≤s z≤n
  ; Paradox.denominatorSplit = refl
  }

coefficient11100 : Paradox.ContractingCoefficientGap word11100
coefficient11100 = record
  { Paradox.gap = 5
  ; Paradox.gapPositive = s≤s z≤n
  ; Paradox.denominatorSplit = refl
  }

sharp1100Threshold : sharpMinimumStart word1100 coefficient1100 ≡ 1
sharp1100Threshold = refl

sharp11010Threshold : sharpMinimumStart word11010 coefficient11010 ≡ 5
sharp11010Threshold = refl

sharp11100Threshold : sharpMinimumStart word11100 coefficient11100 ≡ 4
sharp11100Threshold = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record SharpBarrierThresholdBoundary : Set where
  constructor sharpBarrierThresholdBoundary
  field
    sharpQuotientThresholdPaid : Nat
    sharpThresholdMinimalityPaid : Nat
    paradoxicalQuotientUpperBoundPaid : Nat
    earlyCylinderThresholdsRecovered : Nat
    sameLiteralParityWordRequired : Nat

    sharpThresholdCreatesUniversalEscape : Nat
    nearResonanceClassificationAloneCreatesEscape : Nat
    finiteVerificationCreatesUniversalEscape : Nat

canonicalSharpBarrierThresholdBoundary : SharpBarrierThresholdBoundary
canonicalSharpBarrierThresholdBoundary =
  sharpBarrierThresholdBoundary
    1 1 1 1 1
    0 0 0
