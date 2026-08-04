module DASHI.Physics.Closure.NSTriadKNLuoFiniteLinearIntegralRealizationExact where

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
-- PURPOSE
-- Instantiate the new rational linear-integral theorem by ordinary finite
-- summation and prove that it agrees exactly with the pre-existing finite
-- character definitions.  Addition, negation and extensionality of the finite
-- integral are proved by induction.  The two multiplier lanes therefore have
-- one checked common finite realization rather than unrelated definitions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; -_; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterWeightedIncrementExact as Character
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedIncrementFubiniExact as Finite
import DASHI.Physics.Closure.NSTriadKNLuoLinearIntegralWeightedIncrementExact as Integral

finiteSumExtensional :
  ∀ {Sample : Set}
    (samples : List Sample)
    (left right : Sample → ℚ) →
  ((sample : Sample) → left sample ≡ right sample) →
  Finite.sumList samples left ≡ Finite.sumList samples right
finiteSumExtensional [] left right pointwise = refl
finiteSumExtensional (sample ∷ samples) left right pointwise
  rewrite pointwise sample
        | finiteSumExtensional samples left right pointwise = refl

finiteSumAdd :
  ∀ {Sample : Set}
    (samples : List Sample)
    (left right : Sample → ℚ) →
  Finite.sumList samples (λ sample → left sample + right sample)
  ≡ Finite.sumList samples left + Finite.sumList samples right
finiteSumAdd = Finite.sumListPointwiseAdd

finiteSumNegate :
  ∀ {Sample : Set}
    (samples : List Sample)
    (value : Sample → ℚ) →
  Finite.sumList samples (λ sample → - value sample)
  ≡ - Finite.sumList samples value
finiteSumNegate [] value = solve []
finiteSumNegate (sample ∷ samples) value
  rewrite finiteSumNegate samples value =
  solve (value sample ∷ Finite.sumList samples value ∷ [])

finiteSumLinearIntegral :
  ∀ {Sample : Set} →
  List Sample → Integral.RationalLinearIntegral Sample
finiteSumLinearIntegral samples = record
  { integrate = Finite.sumList samples
  ; integralExtensional = finiteSumExtensional samples
  ; integralAdd = finiteSumAdd samples
  ; integralNegate = finiteSumNegate samples
  }

linearIntegralSystemFromFinite :
  Character.FiniteCharacterSystem →
  Integral.LinearIntegralCharacterSystem
linearIntegralSystemFromFinite system = record
  { Sample = Character.Sample system
  ; Mode = Character.Mode system
  ; integral = finiteSumLinearIntegral (Character.samples system)
  ; zeroMode = Character.zeroMode system
  ; addMode = Character.addMode system
  ; kernelWeight = Character.kernelWeight system
  ; character = Character.character system
  ; characterProduct = Character.characterProduct system
  ; zeroCharacter = Character.zeroCharacter system
  }

finiteSumTransformAgreementOnList :
  ∀ {Sample : Set}
    (samples : List Sample)
    (kernelWeight character : Sample → ℚ) →
  Finite.sumList samples
    (λ sample → kernelWeight sample * character sample)
  ≡ Character.weightedCharacterSum samples kernelWeight character
finiteSumTransformAgreementOnList [] kernelWeight character = refl
finiteSumTransformAgreementOnList
  (sample ∷ samples) kernelWeight character
  rewrite finiteSumTransformAgreementOnList
            samples kernelWeight character = refl

finiteSumIncrementAgreementOnList :
  ∀ {Sample : Set}
    (samples : List Sample)
    (kernelWeight leftCharacter rightCharacter : Sample → ℚ) →
  Finite.sumList samples
    (λ sample →
      kernelWeight sample
      * ((leftCharacter sample - 1ℚ) * (rightCharacter sample - 1ℚ)))
  ≡ Character.weightedIncrementSum
      samples kernelWeight leftCharacter rightCharacter
finiteSumIncrementAgreementOnList [] kernelWeight leftCharacter rightCharacter = refl
finiteSumIncrementAgreementOnList
  (sample ∷ samples) kernelWeight leftCharacter rightCharacter
  rewrite finiteSumIncrementAgreementOnList
            samples kernelWeight leftCharacter rightCharacter = refl

finiteTransformAgreement :
  (system : Character.FiniteCharacterSystem) →
  (mode : Character.Mode system) →
  Integral.integralKernelTransform
    (linearIntegralSystemFromFinite system)
    mode
  ≡ Character.finiteKernelTransform system mode
finiteTransformAgreement system mode =
  finiteSumTransformAgreementOnList
    (Character.samples system)
    (Character.kernelWeight system)
    (Character.character system mode)

finiteIncrementAgreement :
  (system : Character.FiniteCharacterSystem) →
  (left right : Character.Mode system) →
  Integral.integralWeightedIncrement
    (linearIntegralSystemFromFinite system)
    left
    right
  ≡ Character.finiteWeightedIncrement system left right
finiteIncrementAgreement system left right =
  finiteSumIncrementAgreementOnList
    (Character.samples system)
    (Character.kernelWeight system)
    (Character.character system left)
    (Character.character system right)

finiteLinearIntegralRealizationClosed : Bool
finiteLinearIntegralRealizationClosed = true

finiteAndLinearIntegralMultiplierLanesAgree : Bool
finiteAndLinearIntegralMultiplierLanesAgree = true

finiteLinearIntegralRealizationClosedIsTrue :
  finiteLinearIntegralRealizationClosed ≡ true
finiteLinearIntegralRealizationClosedIsTrue = refl

finiteAndLinearIntegralMultiplierLanesAgreeIsTrue :
  finiteAndLinearIntegralMultiplierLanesAgree ≡ true
finiteAndLinearIntegralMultiplierLanesAgreeIsTrue = refl
