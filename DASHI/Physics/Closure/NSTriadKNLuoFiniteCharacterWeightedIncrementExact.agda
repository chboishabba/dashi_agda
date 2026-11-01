module DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterWeightedIncrementExact where

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
-- Prove, rather than merely name, the exact finite weighted-character
-- identity underlying the Luo increment kernel.  For every finite sample
-- list, kernel weight and multiplicative character system,
--
--   sum_y phi(y) (chi_k(y)-1)(chi_l(y)-1)
--
-- equals
--
--   hatPhi(k+l) - hatPhi(k) - hatPhi(l) + hatPhi(0).
--
-- This is the complete finite-sum algebra and includes the zero-transform
-- normalization reduction.  The only remaining continuum step is to prove
-- that the official Bochner/Haar integral is the limit of this finite
-- realization with the same character and normalization conventions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

weightedCharacterSum :
  ∀ {Sample : Set} →
  List Sample →
  (Sample → ℚ) →
  (Sample → ℚ) →
  ℚ
weightedCharacterSum [] kernelWeight character = 0ℚ
weightedCharacterSum (sample ∷ samples) kernelWeight character =
  kernelWeight sample * character sample
  + weightedCharacterSum samples kernelWeight character

weightedIncrementSum :
  ∀ {Sample : Set} →
  List Sample →
  (Sample → ℚ) →
  (Sample → ℚ) →
  (Sample → ℚ) →
  ℚ
weightedIncrementSum [] kernelWeight leftCharacter rightCharacter = 0ℚ
weightedIncrementSum
  (sample ∷ samples) kernelWeight leftCharacter rightCharacter =
  kernelWeight sample
    * ((leftCharacter sample - 1ℚ) * (rightCharacter sample - 1ℚ))
  + weightedIncrementSum
      samples kernelWeight leftCharacter rightCharacter

kernelMass :
  ∀ {Sample : Set} →
  List Sample →
  (Sample → ℚ) →
  ℚ
kernelMass [] kernelWeight = 0ℚ
kernelMass (sample ∷ samples) kernelWeight =
  kernelWeight sample + kernelMass samples kernelWeight

weightedIncrementTermExpansion :
  ∀ kernel left right product zero →
  product ≡ left * right →
  zero ≡ 1ℚ →
  kernel * ((left - 1ℚ) * (right - 1ℚ))
  ≡ kernel * product
    - kernel * left
    - kernel * right
    + kernel * zero
weightedIncrementTermExpansion
  kernel left right product zero productMeaning zeroMeaning
  rewrite productMeaning | zeroMeaning =
  solve (kernel ∷ left ∷ right ∷ [])

finiteWeightedIncrementIdentityOnList :
  ∀ {Sample Mode : Set}
    (samples : List Sample)
    (kernelWeight : Sample → ℚ)
    (character : Mode → Sample → ℚ)
    (zeroMode : Mode)
    (addMode : Mode → Mode → Mode)
    (left right : Mode) →
  ((sample : Sample) →
    character (addMode left right) sample
    ≡ character left sample * character right sample) →
  ((sample : Sample) → character zeroMode sample ≡ 1ℚ) →
  weightedIncrementSum
    samples kernelWeight (character left) (character right)
  ≡ weightedCharacterSum
      samples kernelWeight (character (addMode left right))
    - weightedCharacterSum samples kernelWeight (character left)
    - weightedCharacterSum samples kernelWeight (character right)
    + weightedCharacterSum samples kernelWeight (character zeroMode)
finiteWeightedIncrementIdentityOnList
  [] kernelWeight character zeroMode addMode left right
  characterProduct zeroCharacter =
  solve []
finiteWeightedIncrementIdentityOnList
  (sample ∷ samples) kernelWeight character zeroMode addMode left right
  characterProduct zeroCharacter
  rewrite characterProduct sample
        | zeroCharacter sample
        | finiteWeightedIncrementIdentityOnList
            samples kernelWeight character zeroMode addMode left right
            characterProduct zeroCharacter =
  solve
    ( kernelWeight sample
    ∷ character left sample
    ∷ character right sample
    ∷ weightedCharacterSum
        samples kernelWeight (character (addMode left right))
    ∷ weightedCharacterSum samples kernelWeight (character left)
    ∷ weightedCharacterSum samples kernelWeight (character right)
    ∷ weightedCharacterSum samples kernelWeight (character zeroMode)
    ∷ []
    )

zeroTransformEqualsKernelMassOnList :
  ∀ {Sample Mode : Set}
    (samples : List Sample)
    (kernelWeight : Sample → ℚ)
    (character : Mode → Sample → ℚ)
    (zeroMode : Mode) →
  ((sample : Sample) → character zeroMode sample ≡ 1ℚ) →
  weightedCharacterSum samples kernelWeight (character zeroMode)
  ≡ kernelMass samples kernelWeight
zeroTransformEqualsKernelMassOnList
  [] kernelWeight character zeroMode zeroCharacter = refl
zeroTransformEqualsKernelMassOnList
  (sample ∷ samples) kernelWeight character zeroMode zeroCharacter
  rewrite zeroCharacter sample
        | zeroTransformEqualsKernelMassOnList
            samples kernelWeight character zeroMode zeroCharacter =
  solve
    ( kernelWeight sample
    ∷ kernelMass samples kernelWeight
    ∷ []
    )

record FiniteCharacterSystem : Set₁ where
  field
    Sample Mode : Set
    samples : List Sample

    zeroMode : Mode
    addMode : Mode → Mode → Mode

    addZeroLeft : (mode : Mode) → addMode zeroMode mode ≡ mode
    addZeroRight : (mode : Mode) → addMode mode zeroMode ≡ mode
    addCommutative :
      (left right : Mode) → addMode left right ≡ addMode right left

    kernelWeight : Sample → ℚ
    character : Mode → Sample → ℚ

    characterProduct :
      (left right : Mode) →
      (sample : Sample) →
      character (addMode left right) sample
      ≡ character left sample * character right sample

    zeroCharacter :
      (sample : Sample) → character zeroMode sample ≡ 1ℚ

open FiniteCharacterSystem public

finiteKernelTransform :
  (system : FiniteCharacterSystem) →
  Mode system →
  ℚ
finiteKernelTransform system mode =
  weightedCharacterSum
    (samples system)
    (kernelWeight system)
    (character system mode)

finiteWeightedIncrement :
  (system : FiniteCharacterSystem) →
  Mode system →
  Mode system →
  ℚ
finiteWeightedIncrement system left right =
  weightedIncrementSum
    (samples system)
    (kernelWeight system)
    (character system left)
    (character system right)

finiteWeightedIncrementFourierIdentity :
  (system : FiniteCharacterSystem) →
  (left right : Mode system) →
  finiteWeightedIncrement system left right
  ≡ finiteKernelTransform system (addMode system left right)
    - finiteKernelTransform system left
    - finiteKernelTransform system right
    + finiteKernelTransform system (zeroMode system)
finiteWeightedIncrementFourierIdentity system left right =
  finiteWeightedIncrementIdentityOnList
    (samples system)
    (kernelWeight system)
    (character system)
    (zeroMode system)
    (addMode system)
    left
    right
    (characterProduct system left right)
    (zeroCharacter system)

finiteZeroTransformEqualsKernelMass :
  (system : FiniteCharacterSystem) →
  finiteKernelTransform system (zeroMode system)
  ≡ kernelMass (samples system) (kernelWeight system)
finiteZeroTransformEqualsKernelMass system =
  zeroTransformEqualsKernelMassOnList
    (samples system)
    (kernelWeight system)
    (character system)
    (zeroMode system)
    (zeroCharacter system)

finiteZeroTransformNormalized :
  (system : FiniteCharacterSystem) →
  kernelMass (samples system) (kernelWeight system) ≡ 1ℚ →
  finiteKernelTransform system (zeroMode system) ≡ 1ℚ
finiteZeroTransformNormalized system normalizedMass =
  trans (finiteZeroTransformEqualsKernelMass system) normalizedMass

finiteWeightedCharacterIdentityClosed : Bool
finiteWeightedCharacterIdentityClosed = true

finiteKernelZeroNormalizationReductionClosed : Bool
finiteKernelZeroNormalizationReductionClosed = true

finiteWeightedCharacterIdentityClosedIsTrue :
  finiteWeightedCharacterIdentityClosed ≡ true
finiteWeightedCharacterIdentityClosedIsTrue = refl

finiteKernelZeroNormalizationReductionClosedIsTrue :
  finiteKernelZeroNormalizationReductionClosed ≡ true
finiteKernelZeroNormalizationReductionClosedIsTrue = refl
