{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98AveragingNormalizationDerivativeExact where

------------------------------------------------------------------------
-- ROW A / CMP98: CONSTANT REPRODUCTION -> ZERO TOTAL MASS OF DQ
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- CMP98's linear averaging map reproduces constant fields.  In kernel language
-- the averaging kernel therefore has total mass one at every background.  The
-- Row-A shell estimate needs the first background derivative of that kernel to
-- have total mass zero.
--
-- This file proves that implication abstractly for any finite kernel and any
-- linear derivation on rational-valued background functions:
--
--       sum_x K_b(x) = 1   for every b
--                  ==>  sum_x D K_b(x) = 0.
--
-- The proof uses only finite-sum linearity and "the derivative of a constant is
-- zero".  Thus zero mass is not an independent physical hypothesis once the
-- literal CMP98 constant-reproduction identity and derivative convention are
-- identified.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

sumRational : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumRational [] value = 0ℚ
sumRational (x ∷ xs) value = value x + sumRational xs value

record RationalBackgroundDerivation (Background : Set) : Set₁ where
  field
    derivative : (Background → ℚ) → Background → ℚ

    derivativeCong :
      ∀ f g → (∀ background → f background ≡ g background) →
      ∀ background → derivative f background ≡ derivative g background

    derivativeZero : ∀ background →
      derivative (λ _ → 0ℚ) background ≡ 0ℚ

    derivativeOne : ∀ background →
      derivative (λ _ → 1ℚ) background ≡ 0ℚ

    derivativeAdd : ∀ f g background →
      derivative (λ b → f b + g b) background
      ≡ derivative f background + derivative g background

open RationalBackgroundDerivation public

record NormalizedFiniteAveragingKernel
    (Background Atom : Set)
    (derivation : RationalBackgroundDerivation Background) : Set₁ where
  field
    atoms : List Atom
    weight : Atom → Background → ℚ

    totalMassOne : ∀ background →
      sumRational atoms (λ atom → weight atom background) ≡ 1ℚ

open NormalizedFiniteAveragingKernel public

derivativeWeight :
  ∀ {Background Atom}
    {derivation : RationalBackgroundDerivation Background} →
  NormalizedFiniteAveragingKernel Background Atom derivation →
  Atom → Background → ℚ
derivativeWeight {derivation = derivation} dataSet atom =
  derivative derivation (weight dataSet atom)

sumDerivativeEqualsDerivativeSum :
  ∀ {Background Atom}
    {derivation : RationalBackgroundDerivation Background}
    (dataSet : NormalizedFiniteAveragingKernel Background Atom derivation)
    (selected : List Atom) background →
  sumRational selected (λ atom → derivativeWeight dataSet atom background)
  ≡ derivative derivation
      (λ b → sumRational selected (λ atom → weight dataSet atom b))
      background
sumDerivativeEqualsDerivativeSum {derivation = derivation} dataSet [] background =
  sym (derivativeZero derivation background)
sumDerivativeEqualsDerivativeSum {derivation = derivation}
    dataSet (atom ∷ rest) background =
  trans
    (cong
      (derivativeWeight dataSet atom background +_)
      (sumDerivativeEqualsDerivativeSum dataSet rest background))
    (sym
      (derivativeAdd derivation
        (weight dataSet atom)
        (λ b → sumRational rest (λ x → weight dataSet x b))
        background))

derivativeKernelTotalMassZero :
  ∀ {Background Atom}
    {derivation : RationalBackgroundDerivation Background}
    (dataSet : NormalizedFiniteAveragingKernel Background Atom derivation)
    background →
  sumRational (atoms dataSet)
    (λ atom → derivativeWeight dataSet atom background)
  ≡ 0ℚ
derivativeKernelTotalMassZero {derivation = derivation} dataSet background =
  trans
    (sumDerivativeEqualsDerivativeSum dataSet (atoms dataSet) background)
    (trans
      (derivativeCong derivation
        (λ b → sumRational (atoms dataSet) (λ atom → weight dataSet atom b))
        (λ _ → 1ℚ)
        (totalMassOne dataSet)
        background)
      (derivativeOne derivation background))

cmp98ConstantReproductionToZeroDerivativeMassLevel : ProofLevel
cmp98ConstantReproductionToZeroDerivativeMassLevel = machineChecked

-- Physical/source seam: identify the literal finite CMP98/CMP99 linear averaging
-- kernel and the chosen background derivative with this carrier.  Once the
-- printed constant-reproduction identity is supplied, zero total mass of Q' is
-- downstream and must not be requested again as an independent estimate.
literalCMP98NormalizedKernelIdentificationLevel : ProofLevel
literalCMP98NormalizedKernelIdentificationLevel = conditional
