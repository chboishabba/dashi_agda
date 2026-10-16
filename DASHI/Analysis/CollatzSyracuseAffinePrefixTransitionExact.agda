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
-- In particular 3^s < 2g implies the odd extension remains contracting.
-- No floating logarithm is required for this regime classification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_<_; _≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

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
affineTermAppendOne Binary.end = refl
affineTermAppendOne (Binary.bit0 tail)
  rewrite affineTermAppendOne tail =
  evenAppendOneCorrectionNormalize
    (Affine.affineAdditiveTerm tail)
    (Affine.powNat 2 _)
affineTermAppendOne (Binary.bit1 tail)
  rewrite parityCountAppendOne tail
        | affineTermAppendOne tail =
  oddAppendOneCorrectionNormalize
    (Affine.powNat 3 (Affine.parityCount tail))
    (Affine.affineAdditiveTerm tail)
    (Affine.powNat 2 _)

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

    threeBelowDoubleSplit :
      3 * multiplier < 2 * (multiplier + gap)
    threeBelowDoubleSplit =
      subst
        (λ left → left < 2 * multiplier + 2 * gap)
        (threeMultiplierNormalize multiplier)
        shifted
      |> subst
        (λ right → 3 * multiplier < right)
        (doubleSplitNormalize multiplier gap)

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
  where
  infixl 0 _|>_
  _|>_ : {A B : Set} → A → (A → B) → B
  value |> f = f value

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
    correctionCoordinateRetained : Nat

    floatingLogRequiredForRegimeClassification : Nat
    regimeClassifierCreatesUniversalEscape : Nat
    coefficientGapAloneDeterminesCorrection : Nat

canonicalAffinePrefixTransitionBoundary : AffinePrefixTransitionBoundary
canonicalAffinePrefixTransitionBoundary =
  affinePrefixTransitionBoundary
    1 1 1 1 1
    0 0 0
