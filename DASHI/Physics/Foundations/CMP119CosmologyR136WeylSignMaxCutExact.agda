{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionWeylTraceExact as Weyl
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record RationalWeylSignIntegrationLaws
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) : Set₁ where
  field
    base : Integral.RationalFiniteMeasureIntegrationLaws measure
    haarIntegralNegate : ∀ observable →
      Physical.haarIntegral measure (λ configuration → - observable configuration)
      ≡ - Physical.haarIntegral measure observable
open RationalWeylSignIntegrationLaws public

weightedNonWilsonWeylNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  Source.CompleteFiniteMetricVariation Configuration → ℚ
weightedNonWilsonWeylNumerator measure d =
  Physical.haarIntegral measure
    (λ configuration →
      Physical.density measure configuration
      * Weyl.nonWilsonDiagonalTrace d configuration)

fixedHaarResponseIsNegativeWeightedNonWilsonNumerator :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : RationalWeylSignIntegrationLaws measure) →
  (∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ) →
  Weyl.fourDiagonalPartitionDerivativeSum measure d
  ≡ - weightedNonWilsonWeylNumerator measure d
fixedHaarResponseIsNegativeWeightedNonWilsonNumerator measure d laws referenceFixed =
  trans
    (Weyl.fixedHaarPartitionWeylTrace measure d (base laws) referenceFixed)
    (trans
      (Integral.haarIntegralCongruent (base laws)
        (λ configuration → Physical.density measure configuration * (- Weyl.nonWilsonDiagonalTrace d configuration))
        (λ configuration → - (Physical.density measure configuration * Weyl.nonWilsonDiagonalTrace d configuration))
        (λ configuration →
          Ring.solve-∀
            (Physical.density measure configuration)
            (Weyl.nonWilsonDiagonalTrace d configuration)))
      (haarIntegralNegate laws
        (λ configuration →
          Physical.density measure configuration
          * Weyl.nonWilsonDiagonalTrace d configuration)))

positiveWeightedNonWilsonNumeratorForcesNegativeWeylResponse :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : RationalWeylSignIntegrationLaws measure)
    (referenceFixed : ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ) →
  0ℚ < weightedNonWilsonWeylNumerator measure d →
  Weyl.fourDiagonalPartitionDerivativeSum measure d < 0ℚ
positiveWeightedNonWilsonNumeratorForcesNegativeWeylResponse measure d laws referenceFixed numeratorPositive =
  subst
    (λ value → value < 0ℚ)
    (sym (fixedHaarResponseIsNegativeWeightedNonWilsonNumerator measure d laws referenceFixed))
    (ℚP.neg-mono-< numeratorPositive)

negativeWeightedNonWilsonNumeratorForcesPositiveWeylResponse :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : RationalWeylSignIntegrationLaws measure)
    (referenceFixed : ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ) →
  weightedNonWilsonWeylNumerator measure d < 0ℚ →
  0ℚ < Weyl.fourDiagonalPartitionDerivativeSum measure d
negativeWeightedNonWilsonNumeratorForcesPositiveWeylResponse measure d laws referenceFixed numeratorNegative =
  let
    negatedPositive : - 0ℚ < - weightedNonWilsonWeylNumerator measure d
    negatedPositive = ℚP.neg-antimono-< numeratorNegative
  in
  subst
    (λ value → 0ℚ < value)
    (sym (fixedHaarResponseIsNegativeWeightedNonWilsonNumerator measure d laws referenceFixed))
    (subst
      (λ left → left < - weightedNonWilsonWeylNumerator measure d)
      (Ring.solve [])
      negatedPositive)

classicalWilsonSectorAlreadyCancelledFromSignNumerator : Bool
classicalWilsonSectorAlreadyCancelledFromSignNumerator = true

strictWeylSignResidualIsWeightedNonWilsonNumerator : Bool
strictWeylSignResidualIsWeightedNonWilsonNumerator = true

strictWeylSignIsBidirectionalInWeightedNonWilsonNumerator : Bool
strictWeylSignIsBidirectionalInWeightedNonWilsonNumerator = true
