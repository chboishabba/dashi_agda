module DASHI.Physics.Closure.NSTriadKNLuoFiniteJ12CommutatorDerivativeGainExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Annales scientifiques de l'Ecole Normale Superieure 14 (1981).
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the finite first-moment commutator estimate used by the J12 lane.
-- The exact algebraic commutator identity is proved termwise.  A first-order
-- increment bound, a high-frequency supremum, and the kernel first moment are
-- then combined by ordered-field monotonicity to yield the derivative gain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteSmoothHardMultiplierFactorExact as Finite

commutatorTermIdentity :
  (kernel lowTranslated lowBase highTranslated : ℚ) →
  kernel * (lowTranslated * highTranslated)
    - lowBase * (kernel * highTranslated)
  ≡ kernel * ((lowTranslated - lowBase) * highTranslated)
commutatorTermIdentity kernel lowTranslated lowBase highTranslated =
  solve (kernel ∷ lowTranslated ∷ lowBase ∷ highTranslated ∷ [])

record FiniteJ12CommutatorData (Sample : Set) : Set where
  field
    samples : List Sample

    kernelMagnitude distance lowDifferenceMagnitude highMagnitude :
      Sample → ℚ

    lowGradient highSup kernelFirstMoment : ℚ

    kernelNonnegative :
      (sample : Sample) → 0ℚ ≤ kernelMagnitude sample
    distanceNonnegative :
      (sample : Sample) → 0ℚ ≤ distance sample
    lowDifferenceNonnegative :
      (sample : Sample) → 0ℚ ≤ lowDifferenceMagnitude sample
    highMagnitudeNonnegative :
      (sample : Sample) → 0ℚ ≤ highMagnitude sample
    lowGradientNonnegative : 0ℚ ≤ lowGradient
    highSupNonnegative : 0ℚ ≤ highSup

    firstOrderIncrementBound :
      (sample : Sample) →
      lowDifferenceMagnitude sample
      ≤ distance sample * lowGradient

    highMagnitudeBound :
      (sample : Sample) → highMagnitude sample ≤ highSup

    firstMomentBound :
      Finite.sumList samples
        (λ sample → kernelMagnitude sample * distance sample)
      ≤ kernelFirstMoment

open FiniteJ12CommutatorData public

commutatorMagnitude :
  ∀ {Sample} → FiniteJ12CommutatorData Sample → Sample → ℚ
commutatorMagnitude data sample =
  kernelMagnitude data sample
  * lowDifferenceMagnitude data sample
  * highMagnitude data sample

kernelDistance :
  ∀ {Sample} → FiniteJ12CommutatorData Sample → Sample → ℚ
kernelDistance data sample =
  kernelMagnitude data sample * distance data sample

commutatorPointwiseDerivativeGain :
  ∀ {Sample}
    (data : FiniteJ12CommutatorData Sample)
    (sample : Sample) →
  commutatorMagnitude data sample
  ≤ kernelDistance data sample
      * (lowGradient data * highSup data)
commutatorPointwiseDerivativeGain data sample =
  let
    kernel = kernelMagnitude data sample
    dist = distance data sample
    difference = lowDifferenceMagnitude data sample
    high = highMagnitude data sample

    first : kernel * difference ≤ kernel * (dist * lowGradient data)
    first =
      let instance kernelIsNonnegative =
        nonNegative (kernelNonnegative data sample)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        kernel
        (firstOrderIncrementBound data sample)

    highIsNonnegative : 0ℚ ≤ high
    highIsNonnegative = highMagnitudeNonnegative data sample

    second :
      (kernel * difference) * high
      ≤ (kernel * (dist * lowGradient data)) * high
    second =
      let instance highIsNonnegativeInstance = nonNegative highIsNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg high first

    kernelDistanceGradientNonnegative :
      0ℚ ≤ (kernel * dist) * lowGradient data
    kernelDistanceGradientNonnegative =
      let
        instance
          kernelIsNonnegative = nonNegative (kernelNonnegative data sample)
          distanceIsNonnegative = nonNegative (distanceNonnegative data sample)
          kernelDistanceIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg kernel dist
          gradientIsNonnegative = nonNegative (lowGradientNonnegative data)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (kernel * dist)
              (lowGradient data)
      in
      ℚₚ.nonNegative⁻¹ ((kernel * dist) * lowGradient data)

    third :
      ((kernel * dist) * lowGradient data) * high
      ≤ ((kernel * dist) * lowGradient data) * highSup data
    third =
      let instance coefficientIsNonnegative =
        nonNegative kernelDistanceGradientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        ((kernel * dist) * lowGradient data)
        (highMagnitudeBound data sample)

    leftAssociation :
      (kernel * (dist * lowGradient data)) * high
      ≡ ((kernel * dist) * lowGradient data) * high
    leftAssociation =
      solve (kernel ∷ dist ∷ lowGradient data ∷ high ∷ [])

    targetAssociation :
      ((kernel * dist) * lowGradient data) * highSup data
      ≡ (kernel * dist) * (lowGradient data * highSup data)
    targetAssociation =
      solve
        (kernel ∷ dist ∷ lowGradient data ∷ highSup data ∷ [])
  in
  ℚₚ.≤-trans second
    (subst
      (λ lower → lower ≤ kernelDistance data sample
        * (lowGradient data * highSup data))
      (sym leftAssociation)
      (subst
        (λ upper →
          ((kernel * dist) * lowGradient data) * high ≤ upper)
        targetAssociation
        third))

finiteJ12DerivativeGain :
  ∀ {Sample}
    (data : FiniteJ12CommutatorData Sample) →
  Finite.sumList (samples data) (commutatorMagnitude data)
  ≤ kernelFirstMoment data * (lowGradient data * highSup data)
finiteJ12DerivativeGain data =
  let
    pointwise :
      Finite.sumList (samples data) (commutatorMagnitude data)
      ≤ Finite.sumList (samples data)
          (λ sample →
            kernelDistance data sample
            * (lowGradient data * highSup data))
    pointwise =
      Finite.sumListMonotone
        (samples data)
        (commutatorMagnitude data)
        (λ sample →
          kernelDistance data sample
          * (lowGradient data * highSup data))
        (commutatorPointwiseDerivativeGain data)

    scaleNonnegative :
      0ℚ ≤ lowGradient data * highSup data
    scaleNonnegative =
      let
        instance
          gradientIsNonnegative = nonNegative (lowGradientNonnegative data)
          highSupIsNonnegative = nonNegative (highSupNonnegative data)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (lowGradient data)
              (highSup data)
      in
      ℚₚ.nonNegative⁻¹ (lowGradient data * highSup data)

    momentScaled :
      Finite.sumList (samples data) (kernelDistance data)
        * (lowGradient data * highSup data)
      ≤ kernelFirstMoment data * (lowGradient data * highSup data)
    momentScaled =
      let instance scaleIsNonnegative = nonNegative scaleNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (lowGradient data * highSup data)
        (firstMomentBound data)
  in
  ℚₚ.≤-trans pointwise
    (subst
      (λ lower →
        lower
        ≤ kernelFirstMoment data * (lowGradient data * highSup data))
      (sym
        (Finite.sumListScaleRight
          (lowGradient data * highSup data)
          (samples data)
          (kernelDistance data)))
      momentScaled)
