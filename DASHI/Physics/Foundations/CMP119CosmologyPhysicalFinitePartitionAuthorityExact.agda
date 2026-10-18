{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact where

------------------------------------------------------------------------
-- CLOSE THE FREE Z / DIVIDE LOOPHOLE OF PhysicalFiniteYMMeasure.
--
-- The carrier YangMillsClayPinnedPhysicalCarriersExact intentionally stores
-- partitionFunction and divide as data. For gravitational first response this
-- is too weak unless the selected physical measure proves:
--
--   Z = integral rho dnu,
--   Z > 0,
--   divide x y = x / y.
--
-- This module records exactly those physical algebra laws and derives the
-- normalized first partition response from the already-computed DZ.
--
-- It still does NOT define a derivative operator on metric families, so the
-- result is DZ/Z, not an independently proved Fréchet derivative of log Z.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _/_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; sym)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as First
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K

record PhysicalFinitePartitionAuthority
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) : Set₁ where
  field
    partitionIsDensityIntegral :
      Physical.partitionFunction measure
      ≡ Physical.haarIntegral measure (Physical.density measure)

    partitionPositive :
      0ℚ < Physical.partitionFunction measure

    divideIsRationalDivision :
      ∀ numerator denominator →
      Physical.divide measure numerator denominator
      ≡ numerator / denominator

open PhysicalFinitePartitionAuthority public

module _
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : PhysicalFinitePartitionAuthority measure)
    (variation : First.CompleteFiniteMetricVariation Configuration)
  where

  selectedPartition : ℚ
  selectedPartition = Physical.partitionFunction measure

  selectedPartitionDerivative :
    K.SymmetricTensorComponent4 → ℚ
  selectedPartitionDerivative =
    First.partitionDerivative measure variation

  normalizedPartitionFirstResponse :
    K.SymmetricTensorComponent4 → ℚ
  normalizedPartitionFirstResponse h =
    selectedPartitionDerivative h / selectedPartition

  formalCarrierResponseIsRationalDZOverZ :
    ∀ h →
    First.formalNormalizedPartitionResponse measure variation h
    ≡ normalizedPartitionFirstResponse h
  formalCarrierResponseIsRationalDZOverZ h =
    divideIsRationalDivision authority
      (selectedPartitionDerivative h)
      selectedPartition

  selectedPartitionIsActualDensityIntegral :
    selectedPartition
    ≡ Physical.haarIntegral measure (Physical.density measure)
  selectedPartitionIsActualDensityIntegral =
    partitionIsDensityIntegral authority

  selectedPartitionStrictlyPositive :
    0ℚ < selectedPartition
  selectedPartitionStrictlyPositive =
    partitionPositive authority
