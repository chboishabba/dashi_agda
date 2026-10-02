{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record RationalHaarScaleLaw
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    : Set₁ where
  field
    haarIntegralScale :
      ∀ scalar observable →
      Physical.haarIntegral measure
        (λ x → scalar * observable x)
      ≡
      scalar * Physical.haarIntegral measure observable

open RationalHaarScaleLaw public

record VacuumTraceConstant
    {Configuration : Set}
    (d : Source.CompleteFiniteMetricVariation Configuration)
    : Set₁ where
  field
    coefficient : ℚ
    vacuumTraceConstant :
      ∀ x → Sector.vacuumDiagonalTrace d x ≡ coefficient

open VacuumTraceConstant public

vacuumNumeratorFactors :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (scaleLaw : RationalHaarScaleLaw measure)
    (constant : VacuumTraceConstant d) →
  Sector.vacuumNumerator measure d
  ≡
  coefficient constant
    * Physical.haarIntegral measure (Physical.density measure)
vacuumNumeratorFactors measure d scaleLaw constant =
  trans
    (cong
      (Physical.haarIntegral measure)
      (funext λ x →
        cong
          (λ value → Physical.density measure x * value)
          (vacuumTraceConstant constant x)))
    (trans
      (cong
        (Physical.haarIntegral measure)
        (funext λ x →
          Data.Rational.Properties.*-comm
            (Physical.density measure x)
            (coefficient constant)))
      (haarIntegralScale scaleLaw
        (coefficient constant)
        (Physical.density measure))))

vacuumSectorSignNowReducesToConstantCoefficient : Bool
vacuumSectorSignNowReducesToConstantCoefficient = true
