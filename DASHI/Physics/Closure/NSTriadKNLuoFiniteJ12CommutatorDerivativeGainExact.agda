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
commutatorMagnitude commutatorData sample =
  kernelMagnitude commutatorData sample
  * lowDifferenceMagnitude commutatorData sample
  * highMagnitude commutatorData sample

kernelDistance :
  ∀ {Sample} → FiniteJ12CommutatorData Sample → Sample → ℚ
kernelDistance commutatorData sample =
  kernelMagnitude commutatorData sample * distance commutatorData sample

commutatorPointwiseDerivativeGain :
  ∀ {Sample}
    (commutatorData : FiniteJ12CommutatorData Sample)
    (sample : Sample) →
  commutatorMagnitude commutatorData sample
  ≤ kernelDistance commutatorData sample
      * (lowGradient commutatorData * highSup commutatorData)
commutatorPointwiseDerivativeGain commutatorData sample =
  let
    kernel = kernelMagnitude commutatorData sample
    dist = distance commutatorData sample
    difference = lowDifferenceMagnitude commutatorData sample
    high = highMagnitude commutatorData sample

    first : kernel * difference
      ≤ kernel * (dist * lowGradient commutatorData)
    first =
      let
        instance
          kernelIsNonnegative =
            nonNegative (kernelNonnegative commutatorData sample)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        kernel
        (firstOrderIncrementBound commutatorData sample)

    highIsNonnegative : 0ℚ ≤ high
    highIsNonnegative = highMagnitudeNonnegative commutatorData sample

    second :
      (kernel * difference) * high
      ≤ (kernel * (dist * lowGradient commutatorData)) * high
    second =
      let
        instance
          highIsNonnegativeInstance = nonNegative highIsNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg high first

    kernelDistanceGradientNonnegative :
      0ℚ ≤ (kernel * dist) * lowGradient commutatorData
    kernelDistanceGradientNonnegative =
      let
        instance
          kernelIsNonnegative =
            nonNegative (kernelNonnegative commutatorData sample)
          distanceIsNonnegative =
            nonNegative (distanceNonnegative commutatorData sample)
          kernelDistanceIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg kernel dist
          gradientIsNonnegative =
            nonNegative (lowGradientNonnegative commutatorData)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (kernel * dist)
              (lowGradient commutatorData)
      in
      ℚₚ.nonNegative⁻¹
        ((kernel * dist) * lowGradient commutatorData)

    third :
      ((kernel * dist) * lowGradient commutatorData) * high
      ≤ ((kernel * dist) * lowGradient commutatorData)
          * highSup commutatorData
    third =
      let
        instance
          coefficientIsNonnegative =
            nonNegative kernelDistanceGradientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        ((kernel * dist) * lowGradient commutatorData)
        (highMagnitudeBound commutatorData sample)

    leftAssociation :
      (kernel * (dist * lowGradient commutatorData)) * high
      ≡ ((kernel * dist) * lowGradient commutatorData) * high
    leftAssociation =
      solve (kernel ∷ dist ∷ lowGradient commutatorData ∷ high ∷ [])

    targetAssociation :
      ((kernel * dist) * lowGradient commutatorData)
        * highSup commutatorData
      ≡ (kernel * dist)
          * (lowGradient commutatorData * highSup commutatorData)
    targetAssociation =
      solve
        ( kernel
        ∷ dist
        ∷ lowGradient commutatorData
        ∷ highSup commutatorData
        ∷ []
        )
  in
  ℚₚ.≤-trans second
    (subst
      (λ lower → lower ≤ kernelDistance commutatorData sample
        * (lowGradient commutatorData * highSup commutatorData))
      (sym leftAssociation)
      (subst
        (λ upper →
          ((kernel * dist) * lowGradient commutatorData) * high ≤ upper)
        targetAssociation
        third))

finiteJ12DerivativeGain :
  ∀ {Sample}
    (commutatorData : FiniteJ12CommutatorData Sample) →
  Finite.sumList (samples commutatorData)
    (commutatorMagnitude commutatorData)
  ≤ kernelFirstMoment commutatorData
      * (lowGradient commutatorData * highSup commutatorData)
finiteJ12DerivativeGain commutatorData =
  let
    pointwise :
      Finite.sumList (samples commutatorData)
        (commutatorMagnitude commutatorData)
      ≤ Finite.sumList (samples commutatorData)
          (λ sample →
            kernelDistance commutatorData sample
            * (lowGradient commutatorData * highSup commutatorData))
    pointwise =
      Finite.sumListMonotone
        (samples commutatorData)
        (commutatorMagnitude commutatorData)
        (λ sample →
          kernelDistance commutatorData sample
          * (lowGradient commutatorData * highSup commutatorData))
        (commutatorPointwiseDerivativeGain commutatorData)

    scaleNonnegative :
      0ℚ ≤ lowGradient commutatorData * highSup commutatorData
    scaleNonnegative =
      let
        instance
          gradientIsNonnegative =
            nonNegative (lowGradientNonnegative commutatorData)
          highSupIsNonnegative =
            nonNegative (highSupNonnegative commutatorData)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (lowGradient commutatorData)
              (highSup commutatorData)
      in
      ℚₚ.nonNegative⁻¹
        (lowGradient commutatorData * highSup commutatorData)

    momentScaled :
      Finite.sumList (samples commutatorData)
        (kernelDistance commutatorData)
        * (lowGradient commutatorData * highSup commutatorData)
      ≤ kernelFirstMoment commutatorData
          * (lowGradient commutatorData * highSup commutatorData)
    momentScaled =
      let
        instance
          scaleIsNonnegative = nonNegative scaleNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (lowGradient commutatorData * highSup commutatorData)
        (firstMomentBound commutatorData)
  in
  ℚₚ.≤-trans pointwise
    (subst
      (λ lower →
        lower
        ≤ kernelFirstMoment commutatorData
          * (lowGradient commutatorData * highSup commutatorData))
      (sym
        (Finite.sumListScaleRight
          (lowGradient commutatorData * highSup commutatorData)
          (samples commutatorData)
          (kernelDistance commutatorData)))
      momentScaled)
