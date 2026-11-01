module DASHI.Physics.Closure.NSPeriodicFarLowMultiplierDifferenceKernel where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal Fourier-kernel ownership after the commutator split.
--
-- The signed difference is retained exactly.  The positive absolute-difference
-- kernel is a separate object and is never substituted definitionally for the
-- signed commutator kernel.
------------------------------------------------------------------------

record KernelScalarAlgebra
    {ℓ : Level}
    (Scalar : Set ℓ) : Set (lsuc ℓ) where
  field
    subtract : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    absolute : Scalar → Scalar

open KernelScalarAlgebra public

record FarLowFourierKernelData
    {ℓ : Level}
    (Shell Mode Scalar : Set ℓ)
    (A : KernelScalarAlgebra Scalar) : Set (lsuc ℓ) where
  field
    multiplier : Shell → Mode → Scalar

    -- This is the literal derivative/Leray/Biot-Savart bilinear symbol.  Its
    -- argument order is output, low input, high input.
    bilinearSymbol : Mode → Mode → Mode → Scalar

open FarLowFourierKernelData public

rawKernel :
  ∀ {ℓ} {Shell Mode Scalar : Set ℓ}
    {A : KernelScalarAlgebra Scalar} →
  FarLowFourierKernelData Shell Mode Scalar A →
  Shell → Mode → Mode → Mode → Scalar
rawKernel {A = A} K j k p q =
  multiply A (multiplier K j k) (bilinearSymbol K k p q)

multiplierDifference :
  ∀ {ℓ} {Shell Mode Scalar : Set ℓ}
    {A : KernelScalarAlgebra Scalar} →
  FarLowFourierKernelData Shell Mode Scalar A →
  Shell → Mode → Mode → Scalar
multiplierDifference {A = A} K j k q =
  subtract A (multiplier K j k) (multiplier K j q)

differenceKernel :
  ∀ {ℓ} {Shell Mode Scalar : Set ℓ}
    {A : KernelScalarAlgebra Scalar} →
  FarLowFourierKernelData Shell Mode Scalar A →
  Shell → Mode → Mode → Mode → Scalar
differenceKernel {A = A} K j k p q =
  multiply A
    (multiplierDifference K j k q)
    (bilinearSymbol K k p q)

absoluteDifferenceKernel :
  ∀ {ℓ} {Shell Mode Scalar : Set ℓ}
    {A : KernelScalarAlgebra Scalar} →
  FarLowFourierKernelData Shell Mode Scalar A →
  Shell → Mode → Mode → Mode → Scalar
absoluteDifferenceKernel {A = A} K j k p q =
  multiply A
    (absolute A (multiplierDifference K j k q))
    (absolute A (bilinearSymbol K k p q))

-- The exact Fourier commutator kernel is the signed difference kernel by
-- construction.  This definition is the connection to the algebraic identity;
-- it does not take absolute values.
commutatorKernel :
  ∀ {ℓ} {Shell Mode Scalar : Set ℓ}
    {A : KernelScalarAlgebra Scalar} →
  FarLowFourierKernelData Shell Mode Scalar A →
  Shell → Mode → Mode → Mode → Scalar
commutatorKernel = differenceKernel

record FarLowKernelTriple
    {ℓ : Level}
    (Shell Mode Scalar : Set ℓ)
    (A : KernelScalarAlgebra Scalar)
    (K : FarLowFourierKernelData Shell Mode Scalar A) : Set (lsuc ℓ) where
  field
    raw : Shell → Mode → Mode → Mode → Scalar
    difference : Shell → Mode → Mode → Mode → Scalar
    absoluteDifference : Shell → Mode → Mode → Mode → Scalar

    rawMeaning : ∀ j k p q →
      raw j k p q ≡ rawKernel K j k p q

    differenceMeaning : ∀ j k p q →
      difference j k p q ≡ differenceKernel K j k p q

    absoluteDifferenceMeaning : ∀ j k p q →
      absoluteDifference j k p q ≡ absoluteDifferenceKernel K j k p q

open FarLowKernelTriple public

literalFarLowKernelTriple :
  ∀ {ℓ} {Shell Mode Scalar : Set ℓ}
    {A : KernelScalarAlgebra Scalar}
    (K : FarLowFourierKernelData Shell Mode Scalar A) →
  FarLowKernelTriple Shell Mode Scalar A K
literalFarLowKernelTriple K = record
  { raw = rawKernel K
  ; difference = differenceKernel K
  ; absoluteDifference = absoluteDifferenceKernel K
  ; rawMeaning = λ j k p q → refl
  ; differenceMeaning = λ j k p q → refl
  ; absoluteDifferenceMeaning = λ j k p q → refl
  }

commutatorIsLiteralDifference :
  ∀ {ℓ} {Shell Mode Scalar : Set ℓ}
    {A : KernelScalarAlgebra Scalar}
    (K : FarLowFourierKernelData Shell Mode Scalar A) →
  ∀ j k p q →
  commutatorKernel K j k p q ≡ differenceKernel K j k p q
commutatorIsLiteralDifference K j k p q = refl

farLowMultiplierDifferenceKernelLevel : ProofLevel
farLowMultiplierDifferenceKernelLevel = machineChecked
