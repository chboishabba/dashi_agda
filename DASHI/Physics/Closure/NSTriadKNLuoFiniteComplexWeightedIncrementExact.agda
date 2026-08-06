module DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexWeightedIncrementExact where

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
-- Instantiate the complex linear-integral multiplier theorem on ordinary
-- finite sums.  Complex-sum extensionality, additivity and negation are proved
-- by induction using the repository's exact complex polynomial solver.  The
-- resulting finite theorem uses literal complex characters rather than the
-- earlier rational surrogate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLuoComplexLinearIntegralWeightedIncrementExact as Integral

complexSum :
  ∀ {r} {F : C3.RealField r} {Sample : Set} →
  List Sample → (Sample → C3.Complex F) → C3.Complex F
complexSum {F = F} [] value = C3.complexZero F
complexSum (sample ∷ samples) value =
  C3.complexAdd (value sample) (complexSum samples value)

complexSumExtensional :
  ∀ {r} {F : C3.RealField r} {Sample : Set}
    (samples : List Sample)
    (left right : Sample → C3.Complex F) →
  ((sample : Sample) → left sample ≡ right sample) →
  complexSum samples left ≡ complexSum samples right
complexSumExtensional [] left right pointwise = refl
complexSumExtensional (sample ∷ samples) left right pointwise
  rewrite pointwise sample
        | complexSumExtensional samples left right pointwise = refl

complexSumAdd :
  ∀ {r} {F : C3.RealField r} {Sample : Set}
    (samples : List Sample)
    (left right : Sample → C3.Complex F) →
  complexSum samples
    (λ sample → C3.complexAdd (left sample) (right sample))
  ≡ C3.complexAdd
      (complexSum samples left)
      (complexSum samples right)
complexSumAdd {F = F} [] left right =
  sym (Algebra.complexAddZeroLeft (C3.complexZero F))
complexSumAdd {F = F} (sample ∷ samples) left right
  rewrite complexSumAdd samples left right =
  R.solve 4
    (λ leftHead rightHead leftTail rightTail →
      ((leftHead R.⊕ rightHead) R.⊕ (leftTail R.⊕ rightTail))
      R.⊜
      ((leftHead R.⊕ leftTail) R.⊕ (rightHead R.⊕ rightTail)))
    refl
    (left sample)
    (right sample)
    (complexSum samples left)
    (complexSum samples right)
  where module R = Ring.Solver F

complexSumNegate :
  ∀ {r} {F : C3.RealField r} {Sample : Set}
    (samples : List Sample)
    (value : Sample → C3.Complex F) →
  complexSum samples (λ sample → C3.complexNegate (value sample))
  ≡ C3.complexNegate (complexSum samples value)
complexSumNegate {F = F} [] value
  rewrite C3.negateZero F = refl
complexSumNegate {F = F} (sample ∷ samples) value
  rewrite complexSumNegate samples value =
  R.solve 2
    (λ head tail →
      ((R.⊝ head) R.⊕ (R.⊝ tail))
      R.⊜ R.⊝ (head R.⊕ tail))
    refl
    (value sample)
    (complexSum samples value)
  where module R = Ring.Solver F

finiteComplexLinearIntegral :
  ∀ {r} {F : C3.RealField r} {Sample : Set} →
  List Sample → Integral.ComplexLinearIntegral F Sample
finiteComplexLinearIntegral samples = record
  { integrate = complexSum samples
  ; integralExtensional = complexSumExtensional samples
  ; integralAdd = complexSumAdd samples
  ; integralNegate = complexSumNegate samples
  }

record FiniteComplexCharacterSystem
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    Sample Mode : Set
    samples : List Sample

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

open FiniteComplexCharacterSystem public

asComplexIntegralCharacterSystem :
  ∀ {r} {F : C3.RealField r} →
  FiniteComplexCharacterSystem F →
  Integral.ComplexIntegralCharacterSystem F
asComplexIntegralCharacterSystem system = record
  { Sample = Sample system
  ; Mode = Mode system
  ; integral = finiteComplexLinearIntegral (samples system)
  ; zeroMode = zeroMode system
  ; addMode = addMode system
  ; kernelWeight = kernelWeight system
  ; character = character system
  ; characterProduct = characterProduct system
  ; zeroCharacter = zeroCharacter system
  }

finiteComplexKernelTransform :
  ∀ {r} {F : C3.RealField r}
    (system : FiniteComplexCharacterSystem F) →
  Mode system → C3.Complex F
finiteComplexKernelTransform system mode =
  complexSum (samples system)
    (λ sample →
      C3.complexMultiply
        (kernelWeight system sample)
        (character system mode sample))

finiteComplexWeightedIncrement :
  ∀ {r} {F : C3.RealField r}
    (system : FiniteComplexCharacterSystem F) →
  Mode system → Mode system → C3.Complex F
finiteComplexWeightedIncrement {F = F} system left right =
  complexSum (samples system)
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

finiteComplexWeightedIncrementIdentity :
  ∀ {r} {F : C3.RealField r}
    (system : FiniteComplexCharacterSystem F)
    (left right : Mode system) →
  finiteComplexWeightedIncrement system left right
  ≡ C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract
          (finiteComplexKernelTransform
            system (addMode system left right))
          (finiteComplexKernelTransform system left))
        (finiteComplexKernelTransform system right))
      (finiteComplexKernelTransform system (zeroMode system))
finiteComplexWeightedIncrementIdentity system left right =
  Integral.complexLinearIntegralWeightedIncrementIdentity
    (asComplexIntegralCharacterSystem system)
    left
    right

finiteComplexZeroTransformEqualsKernelMass :
  ∀ {r} {F : C3.RealField r}
    (system : FiniteComplexCharacterSystem F) →
  finiteComplexKernelTransform system (zeroMode system)
  ≡ complexSum (samples system) (kernelWeight system)
finiteComplexZeroTransformEqualsKernelMass system =
  Integral.complexIntegralZeroTransformEqualsKernelMass
    (asComplexIntegralCharacterSystem system)

finiteComplexWeightedIncrementClosed : Bool
finiteComplexWeightedIncrementClosed = true

finiteComplexZeroTransformClosed : Bool
finiteComplexZeroTransformClosed = true

finiteComplexWeightedIncrementClosedIsTrue :
  finiteComplexWeightedIncrementClosed ≡ true
finiteComplexWeightedIncrementClosedIsTrue = refl

finiteComplexZeroTransformClosedIsTrue :
  finiteComplexZeroTransformClosed ≡ true
finiteComplexZeroTransformClosedIsTrue = refl
