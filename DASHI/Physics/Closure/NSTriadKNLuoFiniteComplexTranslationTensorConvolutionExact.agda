module DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexTranslationTensorConvolutionExact where

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
-- Prove the translation, increment and tensor-convolution coefficient formula
-- on the literal complex Fourier carrier.  For a finite complex character
-- system and one mode pair, the weighted coefficient of
--
--   delta_y u_k * delta_y v_l
--
-- factors as the complex weighted increment multiplier times u_k v_l.  The
-- exact four-transform multiplier formula is then substituted from the
-- complex character theorem.  No rational surrogate is used in this module.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexWeightedIncrementExact as Complex

translatedCoefficient :
  ∀ {r} {F : C3.RealField r} {Sample Mode : Set} →
  (Mode → Sample → C3.Complex F) →
  (Mode → C3.Complex F) →
  Mode → Sample → C3.Complex F
translatedCoefficient character coefficient mode sample =
  C3.complexMultiply
    (character mode sample)
    (coefficient mode)

incrementCoefficient :
  ∀ {r} {F : C3.RealField r} {Sample Mode : Set} →
  (Mode → Sample → C3.Complex F) →
  (Mode → C3.Complex F) →
  Mode → Sample → C3.Complex F
incrementCoefficient character coefficient mode sample =
  C3.complexSubtract
    (translatedCoefficient character coefficient mode sample)
    (coefficient mode)

incrementCoefficientFactor :
  ∀ {r} {F : C3.RealField r} {Sample Mode : Set}
    (character : Mode → Sample → C3.Complex F)
    (coefficient : Mode → C3.Complex F)
    (mode : Mode)
    (sample : Sample) →
  incrementCoefficient character coefficient mode sample
  ≡ C3.complexMultiply
      (C3.complexSubtract
        (character mode sample)
        (C3.complexOne F))
      (coefficient mode)
incrementCoefficientFactor {F = F} character coefficient mode sample =
  R.solve 2
    (λ characterValue coefficientValue →
      ((characterValue R.⊗ coefficientValue)
        R.⊕ (R.⊝ coefficientValue))
      R.⊜
      ((characterValue R.⊕ (R.⊝ (R.Κ (C3.complexOne F))))
        R.⊗ coefficientValue))
    refl
    (character mode sample)
    (coefficient mode)
  where module R = Ring.Solver F

weightedIncrementTensorSum :
  ∀ {r} {F : C3.RealField r} {Sample Mode : Set} →
  List Sample →
  (Sample → C3.Complex F) →
  (Mode → Sample → C3.Complex F) →
  (Mode → C3.Complex F) →
  (Mode → C3.Complex F) →
  Mode → Mode → C3.Complex F
weightedIncrementTensorSum {F = F}
  [] kernelWeight character leftCoefficient rightCoefficient left right =
  C3.complexZero F
weightedIncrementTensorSum
  (sample ∷ samples)
  kernelWeight character leftCoefficient rightCoefficient left right =
  C3.complexAdd
    (C3.complexMultiply
      (kernelWeight sample)
      (C3.complexMultiply
        (incrementCoefficient character leftCoefficient left sample)
        (incrementCoefficient character rightCoefficient right sample)))
    (weightedIncrementTensorSum
      samples kernelWeight character leftCoefficient rightCoefficient left right)

weightedIncrementTensorFactors :
  ∀ {r} {F : C3.RealField r} {Sample Mode : Set}
    (samples : List Sample)
    (kernelWeight : Sample → C3.Complex F)
    (character : Mode → Sample → C3.Complex F)
    (leftCoefficient rightCoefficient : Mode → C3.Complex F)
    (left right : Mode) →
  weightedIncrementTensorSum
    samples kernelWeight character leftCoefficient rightCoefficient left right
  ≡ C3.complexMultiply
      (Complex.complexSum samples
        (λ sample →
          C3.complexMultiply
            (kernelWeight sample)
            (C3.complexMultiply
              (C3.complexSubtract
                (character left sample)
                (C3.complexOne F))
              (C3.complexSubtract
                (character right sample)
                (C3.complexOne F)))))
      (C3.complexMultiply
        (leftCoefficient left)
        (rightCoefficient right))
weightedIncrementTensorFactors {F = F}
  [] kernelWeight character leftCoefficient rightCoefficient left right =
  R.solve 2
    (λ leftValue rightValue →
      R.Κ (C3.complexZero F)
      R.⊜
      (R.Κ (C3.complexZero F) R.⊗ (leftValue R.⊗ rightValue)))
    refl
    (leftCoefficient left)
    (rightCoefficient right)
  where module R = Ring.Solver F
weightedIncrementTensorFactors {F = F}
  (sample ∷ samples)
  kernelWeight character leftCoefficient rightCoefficient left right
  rewrite incrementCoefficientFactor character leftCoefficient left sample
        | incrementCoefficientFactor character rightCoefficient right sample
        | weightedIncrementTensorFactors
            samples kernelWeight character
            leftCoefficient rightCoefficient left right =
  R.solve 6
    (λ kernel leftCharacter rightCharacter leftValue rightValue rest →
      let one = R.Κ (C3.complexOne F) in
      ( (kernel R.⊗
          (((leftCharacter R.⊕ (R.⊝ one)) R.⊗ leftValue)
            R.⊗
           ((rightCharacter R.⊕ (R.⊝ one)) R.⊗ rightValue)))
        R.⊕ (rest R.⊗ (leftValue R.⊗ rightValue)) )
      R.⊜
      ( ( (kernel R.⊗
            ((leftCharacter R.⊕ (R.⊝ one)) R.⊗
             (rightCharacter R.⊕ (R.⊝ one))))
          R.⊕ rest )
        R.⊗ (leftValue R.⊗ rightValue) ))
    refl
    (kernelWeight sample)
    (character left sample)
    (character right sample)
    (leftCoefficient left)
    (rightCoefficient right)
    (Complex.complexSum samples
      (λ next →
        C3.complexMultiply
          (kernelWeight next)
          (C3.complexMultiply
            (C3.complexSubtract
              (character left next)
              (C3.complexOne F))
            (C3.complexSubtract
              (character right next)
              (C3.complexOne F)))))
  where module R = Ring.Solver F

finiteComplexIncrementTensorPairCoefficient :
  ∀ {r} {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F) →
  (leftCoefficient rightCoefficient : Complex.Mode system → C3.Complex F) →
  Complex.Mode system → Complex.Mode system → C3.Complex F
finiteComplexIncrementTensorPairCoefficient
  system leftCoefficient rightCoefficient left right =
  weightedIncrementTensorSum
    (Complex.samples system)
    (Complex.kernelWeight system)
    (Complex.character system)
    leftCoefficient
    rightCoefficient
    left
    right

finiteComplexMultiplierTensorPairCoefficient :
  ∀ {r} {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F) →
  (leftCoefficient rightCoefficient : Complex.Mode system → C3.Complex F) →
  Complex.Mode system → Complex.Mode system → C3.Complex F
finiteComplexMultiplierTensorPairCoefficient
  system leftCoefficient rightCoefficient left right =
  C3.complexMultiply
    (C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract
          (Complex.finiteComplexKernelTransform
            system (Complex.addMode system left right))
          (Complex.finiteComplexKernelTransform system left))
        (Complex.finiteComplexKernelTransform system right))
      (Complex.finiteComplexKernelTransform
        system (Complex.zeroMode system)))
    (C3.complexMultiply
      (leftCoefficient left)
      (rightCoefficient right))

finiteComplexTranslationTensorConvolutionIdentity :
  ∀ {r} {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F)
    (leftCoefficient rightCoefficient : Complex.Mode system → C3.Complex F)
    (left right : Complex.Mode system) →
  finiteComplexIncrementTensorPairCoefficient
    system leftCoefficient rightCoefficient left right
  ≡ finiteComplexMultiplierTensorPairCoefficient
      system leftCoefficient rightCoefficient left right
finiteComplexTranslationTensorConvolutionIdentity
  system leftCoefficient rightCoefficient left right =
  trans
    (weightedIncrementTensorFactors
      (Complex.samples system)
      (Complex.kernelWeight system)
      (Complex.character system)
      leftCoefficient
      rightCoefficient
      left
      right)
    (cong
      (λ multiplier →
        C3.complexMultiply multiplier
          (C3.complexMultiply
            (leftCoefficient left)
            (rightCoefficient right)))
      (Complex.finiteComplexWeightedIncrementIdentity
        system left right))

finiteComplexTranslationCoefficientClosed : Bool
finiteComplexTranslationCoefficientClosed = true

finiteComplexIncrementTensorFactorizationClosed : Bool
finiteComplexIncrementTensorFactorizationClosed = true

finiteComplexPairMultiplierIdentityClosed : Bool
finiteComplexPairMultiplierIdentityClosed = true

finiteComplexTranslationCoefficientClosedIsTrue :
  finiteComplexTranslationCoefficientClosed ≡ true
finiteComplexTranslationCoefficientClosedIsTrue = refl

finiteComplexIncrementTensorFactorizationClosedIsTrue :
  finiteComplexIncrementTensorFactorizationClosed ≡ true
finiteComplexIncrementTensorFactorizationClosedIsTrue = refl

finiteComplexPairMultiplierIdentityClosedIsTrue :
  finiteComplexPairMultiplierIdentityClosed ≡ true
finiteComplexPairMultiplierIdentityClosedIsTrue = refl
