module DASHI.Physics.Closure.NSTriadKNLuoComplexLinearIntegralWeightedIncrementExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the weighted-increment multiplier identity on the repository's
-- literal complex Fourier carrier.  The only integral structure used is
-- complex linearity under addition and negation plus extensionality.  The
-- four-term identity is derived by the checked complex polynomial normalizer:
--
--   I[phi (chi_k-1)(chi_l-1)]
--     = hatPhi(k+l)-hatPhi(k)-hatPhi(l)+hatPhi(0).
--
-- This removes the rational-character restriction from the algebraic theorem.
-- A physical torus/Haar/Bochner realization must still inhabit the integral
-- laws and the exponential character/product equations.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality as Eq using (cong; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring

record ComplexLinearIntegral
    {r : Level}
    (F : C3.RealField r)
    (Sample : Set) : Set (lsuc r) where
  field
    integrate : (Sample → C3.Complex F) → C3.Complex F

    integralExtensional :
      (left right : Sample → C3.Complex F) →
      ((sample : Sample) → left sample ≡ right sample) →
      integrate left ≡ integrate right

    integralAdd :
      (left right : Sample → C3.Complex F) →
      integrate (λ sample → C3.complexAdd (left sample) (right sample))
      ≡ C3.complexAdd (integrate left) (integrate right)

    integralNegate :
      (value : Sample → C3.Complex F) →
      integrate (λ sample → C3.complexNegate (value sample))
      ≡ C3.complexNegate (integrate value)

open ComplexLinearIntegral public

integralSubtract :
  ∀ {r} {F : C3.RealField r} {Sample : Set}
    (integral : ComplexLinearIntegral F Sample)
    (left right : Sample → C3.Complex F) →
  integrate integral
    (λ sample → C3.complexSubtract (left sample) (right sample))
  ≡ C3.complexSubtract
      (integrate integral left)
      (integrate integral right)
integralSubtract integral left right =
  begin
    integrate integral
      (λ sample → C3.complexSubtract (left sample) (right sample))
  ≡⟨ refl ⟩
    integrate integral
      (λ sample →
        C3.complexAdd (left sample) (C3.complexNegate (right sample)))
  ≡⟨ integralAdd integral left (λ sample → C3.complexNegate (right sample)) ⟩
    C3.complexAdd
      (integrate integral left)
      (integrate integral (λ sample → C3.complexNegate (right sample)))
  ≡⟨ cong
       (λ value → C3.complexAdd (integrate integral left) value)
       (integralNegate integral right) ⟩
    C3.complexAdd
      (integrate integral left)
      (C3.complexNegate (integrate integral right))
  ≡⟨ refl ⟩
    C3.complexSubtract
      (integrate integral left)
      (integrate integral right)
  ∎

record ComplexIntegralCharacterSystem
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    Sample Mode : Set
    integral : ComplexLinearIntegral F Sample

    zeroMode : Mode
    addMode : Mode → Mode → Mode

    kernelWeight : Sample → C3.Complex F
    character : Mode → Sample → C3.Complex F

    characterProduct :
      (left right : Mode) →
      (sample : Sample) →
      character (addMode left right) sample
      ≡ C3.complexMultiply
          (character left sample)
          (character right sample)

    zeroCharacter :
      (sample : Sample) →
      character zeroMode sample ≡ C3.complexOne F

open ComplexIntegralCharacterSystem public

complexIntegralKernelTransform :
  ∀ {r} {F : C3.RealField r} →
  ComplexIntegralCharacterSystem F →
  C3.Complex F
complexIntegralKernelTransform system =
  integrate (integral system)
    (λ sample → kernelWeight system sample)

complexIntegralKernelTransformAt :
  ∀ {r} {F : C3.RealField r}
    (system : ComplexIntegralCharacterSystem F) →
  Mode system → C3.Complex F
complexIntegralKernelTransformAt system mode =
  integrate (integral system)
    (λ sample →
      C3.complexMultiply
        (kernelWeight system sample)
        (character system mode sample))

complexIntegralWeightedIncrement :
  ∀ {r} {F : C3.RealField r}
    (system : ComplexIntegralCharacterSystem F) →
  Mode system → Mode system → C3.Complex F
complexIntegralWeightedIncrement {F = F} system left right =
  integrate (integral system)
    (λ sample →
      C3.complexMultiply
        (kernelWeight system sample)
        (C3.complexMultiply
          (C3.complexSubtract
            (character system left sample)
            (C3.complexOne F))
          (C3.complexSubtract
            (character system right sample)
            (C3.complexOne F))))

complexWeightedIncrementPointwiseExpansion :
  ∀ {r} {F : C3.RealField r}
    (system : ComplexIntegralCharacterSystem F)
    (left right : Mode system)
    (sample : Sample system) →
  C3.complexMultiply
    (kernelWeight system sample)
    (C3.complexMultiply
      (C3.complexSubtract
        (character system left sample)
        (C3.complexOne F))
      (C3.complexSubtract
        (character system right sample)
        (C3.complexOne F)))
  ≡ C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract
          (C3.complexMultiply
            (kernelWeight system sample)
            (character system (addMode system left right) sample))
          (C3.complexMultiply
            (kernelWeight system sample)
            (character system left sample)))
        (C3.complexMultiply
          (kernelWeight system sample)
          (character system right sample)))
      (C3.complexMultiply
        (kernelWeight system sample)
        (character system (zeroMode system) sample))
complexWeightedIncrementPointwiseExpansion
  {F = F} system left right sample
  rewrite characterProduct system left right sample
        | zeroCharacter system sample =
  R.solve 3
    (λ kernel leftValue rightValue →
      let one = R.Κ (C3.complexOne F) in
      (kernel R.⊗
        ((leftValue R.⊕ (R.⊝ one)) R.⊗
         (rightValue R.⊕ (R.⊝ one))))
      R.⊜
      (((kernel R.⊗ (leftValue R.⊗ rightValue))
          R.⊕ (R.⊝ (kernel R.⊗ leftValue)))
          R.⊕ (R.⊝ (kernel R.⊗ rightValue)))
          R.⊕ (kernel R.⊗ one))
    refl
    (kernelWeight system sample)
    (character system left sample)
    (character system right sample)
  where module R = Ring.Solver F

complexLinearIntegralWeightedIncrementIdentity :
  ∀ {r} {F : C3.RealField r}
    (system : ComplexIntegralCharacterSystem F)
    (left right : Mode system) →
  complexIntegralWeightedIncrement system left right
  ≡ C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract
          (complexIntegralKernelTransformAt
            system (addMode system left right))
          (complexIntegralKernelTransformAt system left))
        (complexIntegralKernelTransformAt system right))
      (complexIntegralKernelTransformAt system (zeroMode system))
complexLinearIntegralWeightedIncrementIdentity
  {F = F} system left right =
  let
    I = integral system
    A = λ sample →
      C3.complexMultiply
        (kernelWeight system sample)
        (character system (addMode system left right) sample)
    B = λ sample →
      C3.complexMultiply
        (kernelWeight system sample)
        (character system left sample)
    C = λ sample →
      C3.complexMultiply
        (kernelWeight system sample)
        (character system right sample)
    D = λ sample →
      C3.complexMultiply
        (kernelWeight system sample)
        (character system (zeroMode system) sample)
  in
  begin
    complexIntegralWeightedIncrement system left right
  ≡⟨ integralExtensional I
       (λ sample →
         C3.complexMultiply
           (kernelWeight system sample)
           (C3.complexMultiply
             (C3.complexSubtract
               (character system left sample)
               (C3.complexOne F))
             (C3.complexSubtract
               (character system right sample)
               (C3.complexOne F))))
       (λ sample →
         C3.complexAdd
           (C3.complexSubtract
             (C3.complexSubtract (A sample) (B sample))
             (C sample))
           (D sample))
       (complexWeightedIncrementPointwiseExpansion system left right) ⟩
    integrate I
      (λ sample →
        C3.complexAdd
          (C3.complexSubtract
            (C3.complexSubtract (A sample) (B sample))
            (C sample))
          (D sample))
  ≡⟨ integralAdd I
       (λ sample →
         C3.complexSubtract
           (C3.complexSubtract (A sample) (B sample))
           (C sample))
       D ⟩
    C3.complexAdd
      (integrate I
        (λ sample →
          C3.complexSubtract
            (C3.complexSubtract (A sample) (B sample))
            (C sample)))
      (integrate I D)
  ≡⟨ cong
       (λ value → C3.complexAdd value (integrate I D))
       (integralSubtract I
         (λ sample → C3.complexSubtract (A sample) (B sample))
         C) ⟩
    C3.complexAdd
      (C3.complexSubtract
        (integrate I (λ sample → C3.complexSubtract (A sample) (B sample)))
        (integrate I C))
      (integrate I D)
  ≡⟨ cong
       (λ firstDifference →
         C3.complexAdd
           (C3.complexSubtract firstDifference (integrate I C))
           (integrate I D))
       (integralSubtract I A B) ⟩
    C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract (integrate I A) (integrate I B))
        (integrate I C))
      (integrate I D)
  ≡⟨ refl ⟩
    C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract
          (complexIntegralKernelTransformAt
            system (addMode system left right))
          (complexIntegralKernelTransformAt system left))
        (complexIntegralKernelTransformAt system right))
      (complexIntegralKernelTransformAt system (zeroMode system))
  ∎

complexIntegralZeroTransformEqualsKernelMass :
  ∀ {r} {F : C3.RealField r}
    (system : ComplexIntegralCharacterSystem F) →
  complexIntegralKernelTransformAt system (zeroMode system)
  ≡ complexIntegralKernelTransform system
complexIntegralZeroTransformEqualsKernelMass {F = F} system =
  integralExtensional
    (integral system)
    (λ sample →
      C3.complexMultiply
        (kernelWeight system sample)
        (character system (zeroMode system) sample))
    (kernelWeight system)
    (λ sample →
      trans
        (cong
          (λ value → C3.complexMultiply
            (kernelWeight system sample) value)
          (zeroCharacter system sample))
        (Ring.complexMultiplyOneRight
          (kernelWeight system sample)))

complexLinearIntegralMultiplierIdentityClosed : Bool
complexLinearIntegralMultiplierIdentityClosed = true

complexZeroTransformMassReductionClosed : Bool
complexZeroTransformMassReductionClosed = true

complexLinearIntegralMultiplierIdentityClosedIsTrue :
  complexLinearIntegralMultiplierIdentityClosed ≡ true
complexLinearIntegralMultiplierIdentityClosedIsTrue = refl

complexZeroTransformMassReductionClosedIsTrue :
  complexZeroTransformMassReductionClosed ≡ true
complexZeroTransformMassReductionClosedIsTrue = refl
