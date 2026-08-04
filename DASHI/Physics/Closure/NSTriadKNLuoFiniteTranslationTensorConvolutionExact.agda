module DASHI.Physics.Closure.NSTriadKNLuoFiniteTranslationTensorConvolutionExact where

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
-- Prove the finite translation/increment/tensor-convolution calculation that
-- sits between the character identity and the physical pair coefficient.
-- For one Fourier pair (k,l), the weighted coefficient of
--
--   delta_y u_k * delta_y v_l
--
-- factors exactly into the weighted increment multiplier times u_k v_l.
-- Combining that factorization with the already-proved character identity
-- yields the literal finite pair coefficient
--
--   [hat phi(k+l)-hat phi(k)-hat phi(l)+hat phi(0)] u_k v_l.
--
-- No pair-coefficient equality is accepted as an input.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterWeightedIncrementExact as Character

translatedCoefficient :
  ∀ {Sample Mode : Set} →
  (Mode → Sample → ℚ) →
  (Mode → ℚ) →
  Mode → Sample → ℚ
translatedCoefficient character coefficient mode sample =
  character mode sample * coefficient mode

incrementCoefficient :
  ∀ {Sample Mode : Set} →
  (Mode → Sample → ℚ) →
  (Mode → ℚ) →
  Mode → Sample → ℚ
incrementCoefficient character coefficient mode sample =
  translatedCoefficient character coefficient mode sample
  - coefficient mode

incrementCoefficientFactor :
  ∀ {Sample Mode : Set}
    (character : Mode → Sample → ℚ)
    (coefficient : Mode → ℚ)
    (mode : Mode)
    (sample : Sample) →
  incrementCoefficient character coefficient mode sample
  ≡ (character mode sample - 1ℚ) * coefficient mode
incrementCoefficientFactor character coefficient mode sample =
  solve (character mode sample ∷ coefficient mode ∷ [])

weightedIncrementTensorSum :
  ∀ {Sample Mode : Set} →
  List Sample →
  (Sample → ℚ) →
  (Mode → Sample → ℚ) →
  (Mode → ℚ) →
  (Mode → ℚ) →
  Mode → Mode → ℚ
weightedIncrementTensorSum
  [] kernelWeight character leftCoefficient rightCoefficient left right = 0ℚ
weightedIncrementTensorSum
  (sample ∷ samples)
  kernelWeight character leftCoefficient rightCoefficient left right =
  kernelWeight sample
    * ( incrementCoefficient character leftCoefficient left sample
      * incrementCoefficient character rightCoefficient right sample
      )
  + weightedIncrementTensorSum
      samples kernelWeight character leftCoefficient rightCoefficient left right

weightedIncrementTensorFactors :
  ∀ {Sample Mode : Set}
    (samples : List Sample)
    (kernelWeight : Sample → ℚ)
    (character : Mode → Sample → ℚ)
    (leftCoefficient rightCoefficient : Mode → ℚ)
    (left right : Mode) →
  weightedIncrementTensorSum
    samples kernelWeight character leftCoefficient rightCoefficient left right
  ≡ Character.weightedIncrementSum
      samples kernelWeight (character left) (character right)
      * (leftCoefficient left * rightCoefficient right)
weightedIncrementTensorFactors
  [] kernelWeight character leftCoefficient rightCoefficient left right =
  solve []
weightedIncrementTensorFactors
  (sample ∷ samples)
  kernelWeight character leftCoefficient rightCoefficient left right
  rewrite incrementCoefficientFactor character leftCoefficient left sample
        | incrementCoefficientFactor character rightCoefficient right sample
        | weightedIncrementTensorFactors
            samples kernelWeight character
            leftCoefficient rightCoefficient left right =
  solve
    ( kernelWeight sample
    ∷ character left sample
    ∷ character right sample
    ∷ leftCoefficient left
    ∷ rightCoefficient right
    ∷ Character.weightedIncrementSum
        samples kernelWeight (character left) (character right)
    ∷ []
    )

finiteIncrementTensorPairCoefficient :
  (system : Character.FiniteCharacterSystem) →
  (leftCoefficient rightCoefficient : Character.Mode system → ℚ) →
  Character.Mode system → Character.Mode system → ℚ
finiteIncrementTensorPairCoefficient system leftCoefficient rightCoefficient left right =
  weightedIncrementTensorSum
    (Character.samples system)
    (Character.kernelWeight system)
    (Character.character system)
    leftCoefficient
    rightCoefficient
    left
    right

finiteMultiplierTensorPairCoefficient :
  (system : Character.FiniteCharacterSystem) →
  (leftCoefficient rightCoefficient : Character.Mode system → ℚ) →
  Character.Mode system → Character.Mode system → ℚ
finiteMultiplierTensorPairCoefficient system leftCoefficient rightCoefficient left right =
  ( Character.finiteKernelTransform system
      (Character.addMode system left right)
    - Character.finiteKernelTransform system left
    - Character.finiteKernelTransform system right
    + Character.finiteKernelTransform system
        (Character.zeroMode system)
  )
  * (leftCoefficient left * rightCoefficient right)

finiteTranslationTensorConvolutionIdentity :
  (system : Character.FiniteCharacterSystem) →
  (leftCoefficient rightCoefficient : Character.Mode system → ℚ) →
  (left right : Character.Mode system) →
  finiteIncrementTensorPairCoefficient
    system leftCoefficient rightCoefficient left right
  ≡ finiteMultiplierTensorPairCoefficient
      system leftCoefficient rightCoefficient left right
finiteTranslationTensorConvolutionIdentity
  system leftCoefficient rightCoefficient left right =
  trans
    (weightedIncrementTensorFactors
      (Character.samples system)
      (Character.kernelWeight system)
      (Character.character system)
      leftCoefficient
      rightCoefficient
      left
      right)
    (cong
      (λ multiplier →
        multiplier * (leftCoefficient left * rightCoefficient right))
      (Character.finiteWeightedIncrementFourierIdentity
        system left right))

finiteTranslationCoefficientClosed : Bool
finiteTranslationCoefficientClosed = true

finiteIncrementTensorFactorizationClosed : Bool
finiteIncrementTensorFactorizationClosed = true

finitePairConvolutionMultiplierIdentityClosed : Bool
finitePairConvolutionMultiplierIdentityClosed = true

finiteTranslationCoefficientClosedIsTrue :
  finiteTranslationCoefficientClosed ≡ true
finiteTranslationCoefficientClosedIsTrue = refl

finiteIncrementTensorFactorizationClosedIsTrue :
  finiteIncrementTensorFactorizationClosed ≡ true
finiteIncrementTensorFactorizationClosedIsTrue = refl

finitePairConvolutionMultiplierIdentityClosedIsTrue :
  finitePairConvolutionMultiplierIdentityClosed ≡ true
finitePairConvolutionMultiplierIdentityClosedIsTrue = refl
