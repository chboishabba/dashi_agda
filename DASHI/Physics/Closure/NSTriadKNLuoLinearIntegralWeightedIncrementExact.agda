module DASHI.Physics.Closure.NSTriadKNLuoLinearIntegralWeightedIncrementExact where

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
-- Prove the weighted-increment multiplier identity for an arbitrary rational
-- linear integral, rather than only for a finite list.  The integral supplies
-- extensionality, addition and negation; the theorem derives subtraction and
-- the four-term identity itself:
--
--   I[phi (chi_k-1)(chi_l-1)]
--     = hatPhi(k+l)-hatPhi(k)-hatPhi(l)+hatPhi(0).
--
-- Thus the algebraic continuum/Haar step no longer needs to be postulated as
-- one whole equality.  A concrete torus realization must still instantiate
-- the integral laws and complex-character conventions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 1ℚ; -_; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; trans)
open Eq.≡-Reasoning

record RationalLinearIntegral (Sample : Set) : Set₁ where
  field
    integrate : (Sample → ℚ) → ℚ

    integralExtensional :
      (left right : Sample → ℚ) →
      ((sample : Sample) → left sample ≡ right sample) →
      integrate left ≡ integrate right

    integralAdd :
      (left right : Sample → ℚ) →
      integrate (λ sample → left sample + right sample)
      ≡ integrate left + integrate right

    integralNegate :
      (value : Sample → ℚ) →
      integrate (λ sample → - value sample)
      ≡ - integrate value

open RationalLinearIntegral public

integralSubtract :
  ∀ {Sample}
    (integral : RationalLinearIntegral Sample)
    (left right : Sample → ℚ) →
  integrate integral (λ sample → left sample - right sample)
  ≡ integrate integral left - integrate integral right
integralSubtract integral left right =
  begin
    integrate integral (λ sample → left sample - right sample)
  ≡⟨ refl ⟩
    integrate integral (λ sample → left sample + (- right sample))
  ≡⟨ integralAdd integral left (λ sample → - right sample) ⟩
    integrate integral left
      + integrate integral (λ sample → - right sample)
  ≡⟨ cong
       (λ value → integrate integral left + value)
       (integralNegate integral right) ⟩
    integrate integral left + (- integrate integral right)
  ≡⟨ refl ⟩
    integrate integral left - integrate integral right
  ∎

record LinearIntegralCharacterSystem : Set₁ where
  field
    Sample Mode : Set
    integral : RationalLinearIntegral Sample

    zeroMode : Mode
    addMode : Mode → Mode → Mode

    kernelWeight : Sample → ℚ
    character : Mode → Sample → ℚ

    characterProduct :
      (left right : Mode) →
      (sample : Sample) →
      character (addMode left right) sample
      ≡ character left sample * character right sample

    zeroCharacter :
      (sample : Sample) → character zeroMode sample ≡ 1ℚ

open LinearIntegralCharacterSystem public

integralKernelTransform :
  (system : LinearIntegralCharacterSystem) →
  Mode system → ℚ
integralKernelTransform system mode =
  integrate (integral system)
    (λ sample →
      kernelWeight system sample * character system mode sample)

integralWeightedIncrement :
  (system : LinearIntegralCharacterSystem) →
  Mode system → Mode system → ℚ
integralWeightedIncrement system left right =
  integrate (integral system)
    (λ sample →
      kernelWeight system sample
      * ( (character system left sample - 1ℚ)
        * (character system right sample - 1ℚ)
        ))

weightedIntegralPointwiseExpansion :
  (system : LinearIntegralCharacterSystem) →
  (left right : Mode system) →
  (sample : Sample system) →
  kernelWeight system sample
    * ( (character system left sample - 1ℚ)
      * (character system right sample - 1ℚ)
      )
  ≡ ((kernelWeight system sample
        * character system (addMode system left right) sample
      - kernelWeight system sample * character system left sample)
      - kernelWeight system sample * character system right sample)
      + kernelWeight system sample * character system (zeroMode system) sample
weightedIntegralPointwiseExpansion system left right sample
  rewrite characterProduct system left right sample
        | zeroCharacter system sample =
  solve
    ( kernelWeight system sample
    ∷ character system left sample
    ∷ character system right sample
    ∷ []
    )

linearIntegralWeightedIncrementIdentity :
  (system : LinearIntegralCharacterSystem) →
  (left right : Mode system) →
  integralWeightedIncrement system left right
  ≡ ((integralKernelTransform system (addMode system left right)
      - integralKernelTransform system left)
      - integralKernelTransform system right)
      + integralKernelTransform system (zeroMode system)
linearIntegralWeightedIncrementIdentity system left right =
  let
    I = integral system
    A = λ sample →
      kernelWeight system sample
      * character system (addMode system left right) sample
    B = λ sample →
      kernelWeight system sample * character system left sample
    C = λ sample →
      kernelWeight system sample * character system right sample
    D = λ sample →
      kernelWeight system sample * character system (zeroMode system) sample
  in
  begin
    integralWeightedIncrement system left right
  ≡⟨ integralExtensional I
       (λ sample →
         kernelWeight system sample
         * ( (character system left sample - 1ℚ)
           * (character system right sample - 1ℚ)
           ))
       (λ sample → ((A sample - B sample) - C sample) + D sample)
       (weightedIntegralPointwiseExpansion system left right) ⟩
    integrate I (λ sample → ((A sample - B sample) - C sample) + D sample)
  ≡⟨ integralAdd I
       (λ sample → (A sample - B sample) - C sample)
       D ⟩
    integrate I (λ sample → (A sample - B sample) - C sample)
      + integrate I D
  ≡⟨ cong
       (λ value → value + integrate I D)
       (integralSubtract I (λ sample → A sample - B sample) C) ⟩
    (integrate I (λ sample → A sample - B sample) - integrate I C)
      + integrate I D
  ≡⟨ cong
       (λ firstDifference →
         (firstDifference - integrate I C) + integrate I D)
       (integralSubtract I A B) ⟩
    ((integrate I A - integrate I B) - integrate I C) + integrate I D
  ≡⟨ refl ⟩
    ((integralKernelTransform system (addMode system left right)
      - integralKernelTransform system left)
      - integralKernelTransform system right)
      + integralKernelTransform system (zeroMode system)
  ∎

linearIntegralKernelZeroMeaning :
  (system : LinearIntegralCharacterSystem) →
  integralKernelTransform system (zeroMode system)
  ≡ integrate (integral system) (kernelWeight system)
linearIntegralKernelZeroMeaning system =
  integralExtensional
    (integral system)
    (λ sample →
      kernelWeight system sample
      * character system (zeroMode system) sample)
    (kernelWeight system)
    (λ sample →
      trans
        (cong
          (λ value → kernelWeight system sample * value)
          (zeroCharacter system sample))
        (solve (kernelWeight system sample ∷ [])))

linearIntegralWeightedIncrementClosed : Bool
linearIntegralWeightedIncrementClosed = true

linearIntegralZeroTransformReductionClosed : Bool
linearIntegralZeroTransformReductionClosed = true

linearIntegralWeightedIncrementClosedIsTrue :
  linearIntegralWeightedIncrementClosed ≡ true
linearIntegralWeightedIncrementClosedIsTrue = refl

linearIntegralZeroTransformReductionClosedIsTrue :
  linearIntegralZeroTransformReductionClosed ≡ true
linearIntegralZeroTransformReductionClosedIsTrue = refl
