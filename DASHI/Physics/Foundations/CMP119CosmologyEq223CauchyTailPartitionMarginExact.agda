{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223CauchyTailPartitionMarginExact where

------------------------------------------------------------------------
-- FINAL SOURCE-FACING B2 COMPILER.
--
-- The literal Eq.(2.23) source already admits three uniform per-diagonal
-- Cauchy bounds.  Let
--
--   M = 4 (M_E + M_R + M_B).
--
-- Since every weighted source contribution is integrated against the same
-- positive finite density and the vacuum trace is configuration-independent,
-- the ONE coefficient inequality
--
--   M + Tail_109(k) < - c_V
--
-- suffices for
--
--   Tail_109(k) * Z_k < D_Weyl Z_k.
--
-- Thus B2 needs no separately estimated partition normalization and no
-- connected normalized-response theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyEq223CauchyVacuumScalarMaxCutExact as CauchyCut
import DASHI.Physics.Foundations.CMP119CosmologyEq223DiagonalCauchyMajorantExact as Cauchy
import DASHI.Physics.Foundations.CMP119CosmologyEq223PointwiseVacuumMarginExact as PointwiseMargin
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyPartitionTailSourceScalarMarginExact as Scalar
import DASHI.Physics.Foundations.CMP119CosmologyPartitionWeylTraceExact as Weyl
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm}
    {scale : Nat}
    (realization :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration scale)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (orderLaws : Order.RationalPositiveFiniteMeasureOrderLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (signLaws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation realization) h x
      ≡ 0ℚ)
  where

  d = Eq223.sourceCompleteFiniteMetricVariation realization

  module C = Cauchy realization measure orderLaws
  module Cut = CauchyCut realization measure orderLaws partition scaleLaw
  module PM = PointwiseMargin realization measure orderLaws partition scaleLaw

  densityIntegral : ℚ
  densityIntegral = Physical.haarIntegral measure (Physical.density measure)

  densityIntegralPositive : 0ℚ < densityIntegral
  densityIntegralPositive =
    subst
      (λ value → 0ℚ < value)
      (Partition.partitionIsDensityIntegral partition)
      (Partition.partitionPositive partition)

  erbNumerator : ℚ
  erbNumerator =
    (Sector.regularNumerator measure d + Sector.rOperationNumerator measure d)
      + Sector.boundaryNumerator measure d

  cauchyCoefficient : C.UniformDiagonalCauchyUpperBounds → ℚ
  cauchyCoefficient = Cut.fourSourceCauchyTotal

  erbBelowCauchyCoefficientTimesDensity :
    (bounds : C.UniformDiagonalCauchyUpperBounds) →
    erbNumerator ≤ cauchyCoefficient bounds * densityIntegral
  erbBelowCauchyCoefficientTimesDensity bounds =
    let
      pointwise = C.asPointwiseERBTraceUpperBounds bounds
      weighted = PM.P.asLiteralERBUpperMajorants pointwise
      numeratorBelowWeighted = PM.M.literalERBBelowUpperTotal weighted
      weightedFactors = PM.weightedUpperTotalFactors pointwise
      sourceUpperIsCauchy = Cut.pointwiseSourceUpperTotalIsFourSourceCauchyTotal bounds
    in
    ℚP.≤-trans
      numeratorBelowWeighted
      (subst
        (λ right → PM.M.erbUpperTotal weighted ≤ right)
        (trans
          weightedFactors
          (cong (λ coefficient → coefficient * densityIntegral)
            sourceUpperIsCauchy))
        ℚP.≤-refl)

  partitionDerivativeIsNegativeERBPlusVacuum :
    Weyl.fourDiagonalPartitionDerivativeSum measure d
    ≡ - (erbNumerator
          + Eq223.eq223VacuumTraceCoefficient realization * densityIntegral)
  partitionDerivativeIsNegativeERBPlusVacuum =
    let
      split =
        Sector.weightedNonWilsonNumeratorSplitsFourWays
          measure d (Sign.base signLaws)
      vacuumFactor =
        Vacuum.vacuumNumeratorFactors
          measure d (Sign.base signLaws) scaleLaw
          (Eq223.eq223VacuumTraceConstant realization)
    in
    trans
      (Sign.fixedHaarResponseIsNegativeWeightedNonWilsonNumerator
        measure d signLaws referenceFixed)
      (trans
        (cong -_ split)
        (trans
          (cong
            (λ vacuumValue →
              - ((Sector.regularNumerator measure d
                  + Sector.rOperationNumerator measure d)
                + (Sector.boundaryNumerator measure d + vacuumValue)))
            vacuumFactor)
          (Ring.solve-∀
            (Sector.regularNumerator measure d)
            (Sector.rOperationNumerator measure d)
            (Sector.boundaryNumerator measure d)
            (Eq223.eq223VacuumTraceCoefficient realization)
            densityIntegral)))

  cauchyPlusTailCoefficientMarginForcesPartitionB2 :
    (bounds : C.UniformDiagonalCauchyUpperBounds)
    (tail : ℚ) →
    cauchyCoefficient bounds + tail
      < - Eq223.eq223VacuumTraceCoefficient realization →
    tail * Physical.partitionFunction measure
      < Weyl.fourDiagonalPartitionDerivativeSum measure d
  cauchyPlusTailCoefficientMarginForcesPartitionB2 bounds tail margin =
    let
      onDensity :
        tail * densityIntegral
          < Weyl.fourDiagonalPartitionDerivativeSum measure d
      onDensity =
        Scalar.sourceScalarMarginForcesPartitionTailDominance
          densityIntegralPositive
          (erbBelowCauchyCoefficientTimesDensity bounds)
          partitionDerivativeIsNegativeERBPlusVacuum
          margin
    in
    subst
      (λ z → tail * z < Weyl.fourDiagonalPartitionDerivativeSum measure d)
      (sym (Partition.partitionIsDensityIntegral partition))
      onDensity

cauchyPlusTailCoefficientMarginPaysPartitionB2 : Bool
cauchyPlusTailCoefficientMarginPaysPartitionB2 = true

partitionNormalizationCancelsFromCauchyTailB2 : Bool
partitionNormalizationCancelsFromCauchyTailB2 = true

connectedNormalizedResponseNotUsedInCauchyTailB2 : Bool
connectedNormalizedResponseNotUsedInCauchyTailB2 = true
