module DASHI.Analysis.CollatzSyracuseAffinePrefixTransitionExact where

------------------------------------------------------------------------
-- EXACT LATE-BIT TRANSITIONS FOR THE AFFINE PREFIX STATE
--
-- Constructors encode the earliest parity bit outermost.  This module appends
-- one LATE bit and proves the exact coordinate recurrences:
--
--   late 0: s' = s,     A' = A
--   late 1: s' = s + 1, A' = 3 A + 2^m
--
-- while the denominator always doubles.  For an already-contracting prefix
--
--   2^m = 3^s + g,  g > 0,
--
-- the late-odd coefficient question is exactly the integer comparison
--
--   3^s ? 2 g.
--
-- If 3^s < 2g, the appended odd word remains contracting with exact new gap
--
--   g' = 2g - 3^s.
--
-- No floating logarithm is required for this regime classification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_<_; _≤_; _∸_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; module ≡-Reasoning)
open ≡-Reasoning

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox
import DASHI.Analysis.CollatzSyracuseTrailingZeroCertificateExact as Zero

------------------------------------------------------------------------
-- Late odd append.
------------------------------------------------------------------------

appendOne :
  {m : Nat} →
  Binary.BinaryWord m →
  Binary.BinaryWord (suc m)
appendOne Binary.end = Binary.bit1 Binary.end
appendOne (Binary.bit0 tail) = Binary.bit0 (appendOne tail)
appendOne (Binary.bit1 tail) = Binary.bit1 (appendOne tail)

parityCountAppendOne :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.parityCount (appendOne word)
  ≡ suc (Affine.parityCount word)
parityCountAppendOne Binary.end = refl
parityCountAppendOne (Binary.bit0 tail) = parityCountAppendOne tail
parityCountAppendOne (Binary.bit1 tail) =
  cong suc (parityCountAppendOne tail)

evenAppendOneCorrectionNormalize :
  (a p : Nat) →
  2 * (3 * a + p) ≡ 3 * (2 * a) + 2 * p
evenAppendOneCorrectionNormalize =
  solve 2
    (λ a p →
      con 2 :* ((con 3 :* a) :+ p)
      :=
      (con 3 :* (con 2 :* a)) :+ (con 2 :* p))
    refl

oddAppendOneCorrectionNormalize :
  (multiplier a p : Nat) →
  3 * multiplier + 2 * (3 * a + p)
  ≡ 3 * (multiplier + 2 * a) + 2 * p
oddAppendOneCorrectionNormalize =
  solve 3
    (λ multiplier a p →
      (con 3 :* multiplier)
        :+ (con 2 :* ((con 3 :* a) :+ p))
      :=
      (con 3 :* (multiplier :+ (con 2 :* a)))
        :+ (con 2 :* p))
    refl

affineTermAppendOne :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.affineAdditiveTerm (appendOne word)
  ≡ 3 * Affine.affineAdditiveTerm word + Affine.powNat 2 m
affineTermAppendOne {m = zero} Binary.end = refl
affineTermAppendOne {m = suc m} (Binary.bit0 tail)
  rewrite affineTermAppendOne tail =
  evenAppendOneCorrectionNormalize
    (Affine.affineAdditiveTerm tail)
    (Affine.powNat 2 m)
affineTermAppendOne {m = suc m} (Binary.bit1 tail)
  rewrite parityCountAppendOne tail
        | affineTermAppendOne tail =
  oddAppendOneCorrectionNormalize
    (Affine.powNat 3 (Affine.parityCount tail))
    (Affine.affineAdditiveTerm tail)
    (Affine.powNat 2 m)

multiplierAppendOne :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.powNat 3 (Affine.parityCount (appendOne word))
  ≡ 3 * Affine.powNat 3 (Affine.parityCount word)
multiplierAppendOne word
  rewrite parityCountAppendOne word = refl

denominatorAppendOne :
  (m : Nat) →
  Affine.powNat 2 (suc m) ≡ 2 * Affine.powNat 2 m
denominatorAppendOne m = refl

------------------------------------------------------------------------
-- Late even transition reuses the existing exact append-zero owner.
------------------------------------------------------------------------

parityCountAppendZero :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.parityCount (Zero.appendZero word)
  ≡ Affine.parityCount word
parityCountAppendZero = Zero.parityCountAppendZero

affineTermAppendZero :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.affineAdditiveTerm (Zero.appendZero word)
  ≡ Affine.affineAdditiveTerm word
affineTermAppendZero = Zero.affineTermAppendZero

denominatorAppendZero :
  (m : Nat) →
  Affine.powNat 2 (suc m) ≡ 2 * Affine.powNat 2 m
denominatorAppendZero m = refl

------------------------------------------------------------------------
-- Exact late-odd regime on an already-contracting prefix.
------------------------------------------------------------------------

data OddGapRegime
    {m : Nat}
    (word : Binary.BinaryWord m)
    (coefficient : Paradox.ContractingCoefficientGap word) : Set where
  remainsContracting :
    Affine.powNat 3 (Affine.parityCount word)
      < 2 * Paradox.gap coefficient →
    OddGapRegime word coefficient

  criticalBalance :
    Affine.powNat 3 (Affine.parityCount word)
      ≡ 2 * Paradox.gap coefficient →
    OddGapRegime word coefficient

  becomesExpanding :
    2 * Paradox.gap coefficient
      < Affine.powNat 3 (Affine.parityCount word) →
    OddGapRegime word coefficient

classifyOddGapRegime :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  OddGapRegime word coefficient
classifyOddGapRegime word coefficient
  with NatP.<-cmp
    (Affine.powNat 3 (Affine.parityCount word))
    (2 * Paradox.gap coefficient)
... | tri< multiplierBelow _ _ = remainsContracting multiplierBelow
... | tri≈ _ equal _ = criticalBalance equal
... | tri> _ _ doubleGapBelow = becomesExpanding doubleGapBelow

threeMultiplierNormalize :
  (multiplier : Nat) →
  2 * multiplier + multiplier ≡ 3 * multiplier
threeMultiplierNormalize =
  solve 1
    (λ multiplier →
      (con 2 :* multiplier) :+ multiplier
      := con 3 :* multiplier)
    refl

doubleSplitNormalize :
  (multiplier gap : Nat) →
  2 * multiplier + 2 * gap ≡ 2 * (multiplier + gap)
doubleSplitNormalize =
  solve 2
    (λ multiplier gap →
      (con 2 :* multiplier) :+ (con 2 :* gap)
      := con 2 :* (multiplier :+ gap))
    refl

oddSafeGapKeepsContracting :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Affine.powNat 3 (Affine.parityCount word)
    < 2 * Paradox.gap coefficient →
  Affine.powNat 3 (Affine.parityCount (appendOne word))
    < Affine.powNat 2 (suc m)
oddSafeGapKeepsContracting {m} word coefficient safe =
  let
    multiplier = Affine.powNat 3 (Affine.parityCount word)
    gap = Paradox.gap coefficient
    denominator = Affine.powNat 2 m

    shifted :
      2 * multiplier + multiplier
      < 2 * multiplier + 2 * gap
    shifted = NatP.+-monoˡ-< (2 * multiplier) safe

    leftNormalized :
      3 * multiplier < 2 * multiplier + 2 * gap
    leftNormalized =
      subst
        (λ left → left < 2 * multiplier + 2 * gap)
        (threeMultiplierNormalize multiplier)
        shifted

    threeBelowDoubleSplit :
      3 * multiplier < 2 * (multiplier + gap)
    threeBelowDoubleSplit =
      subst
        (λ right → 3 * multiplier < right)
        (doubleSplitNormalize multiplier gap)
        leftNormalized

    threeBelowDoubleDenominator :
      3 * multiplier < 2 * denominator
    threeBelowDoubleDenominator =
      subst
        (λ right → 3 * multiplier < 2 * right)
        (sym (Paradox.denominatorSplit coefficient))
        threeBelowDoubleSplit

    actualMultiplierBelow :
      Affine.powNat 3 (Affine.parityCount (appendOne word))
      < 2 * denominator
    actualMultiplierBelow =
      subst
        (λ left → left < 2 * denominator)
        (sym (multiplierAppendOne word))
        threeBelowDoubleDenominator
  in
  subst
    (λ right →
      Affine.powNat 3 (Affine.parityCount (appendOne word)) < right)
    (sym (denominatorAppendOne m))
    actualMultiplierBelow

oddExtendedGap :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Paradox.ContractingCoefficientGap word →
  Nat
oddExtendedGap word coefficient =
  2 * Paradox.gap coefficient
  ∸ Affine.powNat 3 (Affine.parityCount word)

oddExtendedGapPositive :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  Affine.powNat 3 (Affine.parityCount word)
    < 2 * Paradox.gap coefficient →
  zero < oddExtendedGap word coefficient
oddExtendedGapPositive word coefficient safe =
  NatP.m<n⇒0<n∸m safe

-- The solver language does not model truncated subtraction.  The proof below
-- therefore treats the subtraction result as an opaque `difference` and uses
-- the stdlib identity multiplier + (2g - multiplier) = 2g under
-- multiplier <= 2g.
oddExtendedDenominatorSplit :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  (safe :
    Affine.powNat 3 (Affine.parityCount word)
      < 2 * Paradox.gap coefficient) →
  Affine.powNat 2 (suc m)
  ≡
  Affine.powNat 3 (Affine.parityCount (appendOne word))
  + oddExtendedGap word coefficient
oddExtendedDenominatorSplit {m} word coefficient safe =
  let
    multiplier = Affine.powNat 3 (Affine.parityCount word)
    gap = Paradox.gap coefficient
    difference = 2 * gap ∸ multiplier

    balance : multiplier + difference ≡ 2 * gap
    balance = NatP.m+[n∸m]≡n (NatP.<⇒≤ safe)

    reassociate :
      3 * multiplier + difference
      ≡ 2 * multiplier + (multiplier + difference)
    reassociate =
      solve 3
        (λ multiplier gap difference →
          (con 3 :* multiplier) :+ difference
          :=
          (con 2 :* multiplier) :+ (multiplier :+ difference))
        refl
  in
  begin
    Affine.powNat 2 (suc m)
      ≡⟨ denominatorAppendOne m ⟩
    2 * Affine.powNat 2 m
      ≡⟨ cong (2 *_) (Paradox.denominatorSplit coefficient) ⟩
    2 * (multiplier + gap)
      ≡⟨ sym (doubleSplitNormalize multiplier gap) ⟩
    2 * multiplier + 2 * gap
      ≡⟨ cong (2 * multiplier +_) (sym balance) ⟩
    2 * multiplier + (multiplier + difference)
      ≡⟨ sym reassociate ⟩
    3 * multiplier + difference
      ≡⟨ cong (_+ difference) (sym (multiplierAppendOne word)) ⟩
    Affine.powNat 3 (Affine.parityCount (appendOne word)) + difference
      ∎

appendOneContractingCoefficient :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : Paradox.ContractingCoefficientGap word) →
  (safe :
    Affine.powNat 3 (Affine.parityCount word)
      < 2 * Paradox.gap coefficient) →
  Paradox.ContractingCoefficientGap (appendOne word)
appendOneContractingCoefficient word coefficient safe = record
  { Paradox.gap = oddExtendedGap word coefficient
  ; Paradox.gapPositive = oddExtendedGapPositive word coefficient safe
  ; Paradox.denominatorSplit =
      oddExtendedDenominatorSplit word coefficient safe
  }

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AffinePrefixTransitionBoundary : Set where
  constructor affinePrefixTransitionBoundary
  field
    trailingEvenTransitionPaid : Nat
    trailingOddTransitionPaid : Nat
    exactOddGapRegimeClassifierPaid : Nat
    safeOddConditionImpliesContractingPaid : Nat
    safeOddConditionBuildsNewGapPaid : Nat
    correctionCoordinateRetained : Nat

    floatingLogRequiredForRegimeClassification : Nat
    regimeClassifierCreatesUniversalEscape : Nat
    coefficientGapAloneDeterminesCorrection : Nat

canonicalAffinePrefixTransitionBoundary : AffinePrefixTransitionBoundary
canonicalAffinePrefixTransitionBoundary =
  affinePrefixTransitionBoundary
    1 1 1 1 1 1
    0 0 0
