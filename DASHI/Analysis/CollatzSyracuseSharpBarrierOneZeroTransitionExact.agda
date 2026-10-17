module DASHI.Analysis.CollatzSyracuseSharpBarrierOneZeroTransitionExact where

------------------------------------------------------------------------
-- SHARP BARRIER LAW FOR A LATE `10` BLOCK
--
-- Let a literal parity prefix w already be contracting:
--
--   D = 2^m = M + g,
--   M = 3^(ones w),
--   g > 0,
--   A = A(w).
--
-- Appending a late odd step and then a late even step gives
--
--   A(w10) = 3A + D,
--   M(w10) = 3M,
--   D(w10) = 4D,
--   g(w10) = D(w10) - M(w10) = M + 4g > 0.
--
-- Thus `w10` is ALWAYS contracting whenever w is contracting, even when the
-- intermediate `w1` is not.  Moreover the old sharp threshold is already a
-- valid threshold for `w10`, so sharp minimality yields
--
--   N*(w10) <= N*(w).
--
-- This pays an infinite parametric block family on the exact affine carrier;
-- it does not prove that every residual trajectory contains the required
-- contracting-prefix + `10` configuration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; module ≡-Reasoning)
open ≡-Reasoning

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox
import DASHI.Analysis.CollatzSyracuseSharpBarrierThresholdExact as Sharp
import DASHI.Analysis.CollatzSyracuseAffinePrefixTransitionExact as Prefix
import DASHI.Analysis.CollatzSyracuseTrailingZeroCertificateExact as Zero

appendOneZero :
  {m : Nat} →
  Binary.BinaryWord m →
  Binary.BinaryWord (suc (suc m))
appendOneZero word = Zero.appendZero (Prefix.appendOne word)

parityCountAppendOneZero :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.parityCount (appendOneZero word)
  ≡ suc (Affine.parityCount word)
parityCountAppendOneZero word =
  begin
    Affine.parityCount (appendOneZero word)
      ≡⟨ Zero.parityCountAppendZero (Prefix.appendOne word) ⟩
    Affine.parityCount (Prefix.appendOne word)
      ≡⟨ Prefix.parityCountAppendOne word ⟩
    suc (Affine.parityCount word)
      ∎

affineTermAppendOneZero :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.affineAdditiveTerm (appendOneZero word)
  ≡ 3 * Affine.affineAdditiveTerm word + Affine.powNat 2 m
affineTermAppendOneZero {m} word =
  begin
    Affine.affineAdditiveTerm (appendOneZero word)
      ≡⟨ Zero.affineTermAppendZero (Prefix.appendOne word) ⟩
    Affine.affineAdditiveTerm (Prefix.appendOne word)
      ≡⟨ Prefix.affineTermAppendOne word ⟩
    3 * Affine.affineAdditiveTerm word + Affine.powNat 2 m
      ∎

multiplierAppendOneZero :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.powNat 3 (Affine.parityCount (appendOneZero word))
  ≡ 3 * Affine.powNat 3 (Affine.parityCount word)
multiplierAppendOneZero word
  rewrite parityCountAppendOneZero word = refl

denominatorAppendOneZero :
  (m : Nat) →
  Affine.powNat 2 (suc (suc m))
  ≡ 4 * Affine.powNat 2 m
denominatorAppendOneZero m = refl

oneZeroGap :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Paradox.ContractingCoefficientGap word →
  Nat
oneZeroGap word coefficient =
  Affine.powNat 3 (Affine.parityCount word)
  + 4 * Paradox.gap coefficient

oneZeroGapPositive :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  zero < oneZeroGap word coefficient
oneZeroGapPositive word coefficient =
  NatP.<-≤-trans
    (Paradox.gapPositive coefficient)
    gapBelowPairGap
  where
  gapBelowFourGap :
    Paradox.gap coefficient ≤ 4 * Paradox.gap coefficient
  gapBelowFourGap =
    NatP.m≤m*n
      (Paradox.gap coefficient)
      4

  fourGapBelowPairGap :
    4 * Paradox.gap coefficient
    ≤ Affine.powNat 3 (Affine.parityCount word)
      + 4 * Paradox.gap coefficient
  fourGapBelowPairGap =
    NatP.m≤n+m
      (4 * Paradox.gap coefficient)
      (Affine.powNat 3 (Affine.parityCount word))

  gapBelowPairGap :
    Paradox.gap coefficient
    ≤ Affine.powNat 3 (Affine.parityCount word)
      + 4 * Paradox.gap coefficient
  gapBelowPairGap =
    NatP.≤-trans gapBelowFourGap fourGapBelowPairGap

pairGapNormalize :
  (multiplier gap : Nat) →
  4 * (multiplier + gap)
  ≡ 3 * multiplier + (multiplier + 4 * gap)
pairGapNormalize =
  solve 2
    (λ multiplier gap →
      con 4 :* (multiplier :+ gap)
      :=
      (con 3 :* multiplier)
        :+ (multiplier :+ (con 4 :* gap)))
    refl

appendOneZeroContractingCoefficient :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Paradox.ContractingCoefficientGap (appendOneZero word)
appendOneZeroContractingCoefficient {m} word coefficient = record
  { Paradox.gap = oneZeroGap word coefficient
  ; Paradox.gapPositive = oneZeroGapPositive word coefficient
  ; Paradox.denominatorSplit =
      begin
        Affine.powNat 2 (suc (suc m))
          ≡⟨ denominatorAppendOneZero m ⟩
        4 * Affine.powNat 2 m
          ≡⟨ cong (4 *_) (Paradox.denominatorSplit coefficient) ⟩
        4 *
          (Affine.powNat 3 (Affine.parityCount word)
           + Paradox.gap coefficient)
          ≡⟨ pairGapNormalize
              (Affine.powNat 3 (Affine.parityCount word))
              (Paradox.gap coefficient) ⟩
        3 * Affine.powNat 3 (Affine.parityCount word)
          + oneZeroGap word coefficient
          ≡⟨ cong
              (_+ oneZeroGap word coefficient)
              (sym (multiplierAppendOneZero word)) ⟩
        Affine.powNat 3 (Affine.parityCount (appendOneZero word))
          + oneZeroGap word coefficient
          ∎
  }

------------------------------------------------------------------------
-- The old sharp threshold remains valid for the whole late `10` block.
------------------------------------------------------------------------

baseTimesSuccessorLower :
  (base q : Nat) →
  base ≤ base * suc q
baseTimesSuccessorLower base q =
  subst
    (λ right → base ≤ right)
    (sym (NatP.*-suc base q))
    (NatP.m≤m+n base (base * q))

oneZeroCorrectionFitsAtOldSharpThreshold :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Affine.affineAdditiveTerm (appendOneZero word)
  <
  oneZeroGap word coefficient
    * Sharp.sharpMinimumStart word coefficient
oneZeroCorrectionFitsAtOldSharpThreshold {m} word coefficient =
  let
    correction = Affine.affineAdditiveTerm word
    multiplier = Affine.powNat 3 (Affine.parityCount word)
    denominator = Affine.powNat 2 m
    gap = Paradox.gap coefficient
    quotient =
      Sharp.quotientByPositive
        correction gap (Paradox.gapPositive coefficient)
    minimum = Sharp.sharpMinimumStart word coefficient

    oldFit : correction < gap * minimum
    oldFit =
      Sharp.quotientThresholdFits
        correction gap (Paradox.gapPositive coefficient)

    thriceOldFit :
      3 * correction < 3 * (gap * minimum)
    thriceOldFit = NatP.*-monoʳ-< 3 oldFit

    addDenominator :
      3 * correction + denominator
      < 3 * (gap * minimum) + denominator
    addDenominator = NatP.+-monoʳ-< denominator thriceOldFit

    denominatorAtMostScaled : denominator ≤ denominator * minimum
    denominatorAtMostScaled =
      baseTimesSuccessorLower denominator quotient

    boundedRight :
      3 * (gap * minimum) + denominator
      ≤ 3 * (gap * minimum) + denominator * minimum
    boundedRight =
      NatP.+-monoˡ-≤ (3 * (gap * minimum)) denominatorAtMostScaled

    strictToScaled :
      3 * correction + denominator
      < 3 * (gap * minimum) + denominator * minimum
    strictToScaled = NatP.<-≤-trans addDenominator boundedRight

    normalizeRight :
      3 * (gap * minimum) + denominator * minimum
      ≡ (denominator + 3 * gap) * minimum
    normalizeRight =
      solve 3
        (λ gap denominator minimum →
          (con 3 :* (gap :* minimum))
            :+ (denominator :* minimum)
          :=
          (denominator :+ (con 3 :* gap)) :* minimum)
        refl

    denominatorPlusThreeGap :
      denominator + 3 * gap
      ≡ multiplier + 4 * gap
    denominatorPlusThreeGap =
      begin
        denominator + 3 * gap
          ≡⟨ cong (_+ 3 * gap) (Paradox.denominatorSplit coefficient) ⟩
        (multiplier + gap) + 3 * gap
          ≡⟨ solve 2
              (λ multiplier gap →
                (multiplier :+ gap) :+ (con 3 :* gap)
                := multiplier :+ (con 4 :* gap))
              refl ⟩
        multiplier + 4 * gap
          ∎

    scaledPairGap :
      (denominator + 3 * gap) * minimum
      ≡ oneZeroGap word coefficient * minimum
    scaledPairGap =
      cong (_* minimum) denominatorPlusThreeGap
  in
  subst
    (λ left → left < oneZeroGap word coefficient * minimum)
    (sym (affineTermAppendOneZero word))
    (subst
      (λ right → 3 * correction + denominator < right)
      scaledPairGap
      (subst
        (λ right → 3 * correction + denominator < right)
        normalizeRight
        strictToScaled))

trailingOneZeroSharpThresholdNonincreasing :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Sharp.sharpMinimumStart
    (appendOneZero word)
    (appendOneZeroContractingCoefficient word coefficient)
  ≤ Sharp.sharpMinimumStart word coefficient
trailingOneZeroSharpThresholdNonincreasing word coefficient =
  Sharp.sharpThresholdIsMinimalUniformAffineThreshold
    (appendOneZero word)
    (appendOneZeroContractingCoefficient word coefficient)
    (Sharp.sharpMinimumStart word coefficient)
    (oneZeroCorrectionFitsAtOldSharpThreshold word coefficient)

record SharpBarrierOneZeroBoundary : Set where
  constructor sharpBarrierOneZeroBoundary
  field
    trailingOneZeroAlwaysContractsPaid : Nat
    trailingOneZeroExactGapPaid : Nat
    oldSharpThresholdRemainsCertificatePaid : Nat
    trailingOneZeroSharpThresholdNonincreasingPaid : Nat

    localOneZeroLawCreatesUniversalEscape : Nat
    arbitraryOddRunBarrierMonotonicityPaid : Nat

canonicalSharpBarrierOneZeroBoundary : SharpBarrierOneZeroBoundary
canonicalSharpBarrierOneZeroBoundary =
  sharpBarrierOneZeroBoundary
    1 1 1 1
    0 0
