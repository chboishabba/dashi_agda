{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223PointwiseVacuumMarginExact where

------------------------------------------------------------------------
-- SOURCE-LEVEL SIGN CUT AFTER CANCELLING THE COMMON POSITIVE DENSITY FACTOR.
--
-- Suppose the literal Eq.(2.23) four-diagonal traces satisfy pointwise bounds
--
--   tr_E <= M_E,   tr_R <= M_R,   tr_B <= M_B.
--
-- Positive Haar integration gives weighted numerator majorants
--   N_E <= M_E I, N_R <= M_R I, N_B <= M_B I,
-- where I = integral rho.  The configuration-independent vacuum numerator is
--   N_V = c_V I.
--
-- Since I>0, the ONE source-level scalar inequality
--
--   M_E + M_R + M_B < -c_V
--
-- implies the full literal finite-measure dominance
--   N_E + N_R + N_B < -N_V.
--
-- This is the sharp Pareto form of the preferred Eq.(2.23) sign route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _*_; -_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyEq223ERBUpperMajorantExact as ERB
import DASHI.Physics.Foundations.CMP119CosmologyEq223NegativeSectorDominanceExact as Dominance
import DASHI.Physics.Foundations.CMP119CosmologyEq223PointwiseToNumeratorMajorantExact as Pointwise
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

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
  where

  d = Eq223.sourceCompleteFiniteMetricVariation realization

  densityIntegral : ℚ
  densityIntegral =
    Physical.haarIntegral measure (Physical.density measure)

  densityIntegralPositive : 0ℚ < densityIntegral
  densityIntegralPositive =
    subst
      (λ value → 0ℚ < value)
      (Partition.partitionIsDensityIntegral partition)
      (Partition.partitionPositive partition)

  module P = Pointwise realization measure orderLaws
  module M = ERB realization measure

  sourceUpperTotal :
    P.PointwiseERBDiagonalTraceUpperBounds → ℚ
  sourceUpperTotal bounds =
    (P.regularPointwiseUpper bounds + P.rOperationPointwiseUpper bounds)
      + P.boundaryPointwiseUpper bounds

  weightedUpperTotalFactors :
    (bounds : P.PointwiseERBDiagonalTraceUpperBounds) →
    M.erbUpperTotal (P.asLiteralERBUpperMajorants bounds)
    ≡ sourceUpperTotal bounds * densityIntegral
  weightedUpperTotalFactors bounds =
    let
      e = Order.weightedConstantFactorsDensityIntegral
        orderLaws (P.regularPointwiseUpper bounds)
      r = Order.weightedConstantFactorsDensityIntegral
        orderLaws (P.rOperationPointwiseUpper bounds)
      b = Order.weightedConstantFactorsDensityIntegral
        orderLaws (P.boundaryPointwiseUpper bounds)
    in
    trans
      (cong₂ _+_
        (cong₂ _+_ e r)
        b)
      (Ring.solve-∀
        (P.regularPointwiseUpper bounds)
        (P.rOperationPointwiseUpper bounds)
        (P.boundaryPointwiseUpper bounds)
        densityIntegral)

  sourceScalarMarginForcesLiteralDominance :
    (bounds : P.PointwiseERBDiagonalTraceUpperBounds) →
    sourceUpperTotal bounds
      < - Eq223.eq223VacuumTraceCoefficient realization →
    Dominance.LiteralNegativeSectorDominance realization measure
  sourceScalarMarginForcesLiteralDominance bounds sourceMargin =
    let
      instance
        densityIntegralPositiveI : Positive densityIntegral
        densityIntegralPositiveI = positive densityIntegralPositive

      scaled :
        sourceUpperTotal bounds * densityIntegral
        < (- Eq223.eq223VacuumTraceCoefficient realization) * densityIntegral
      scaled =
        ℚP.*-monoʳ-<-pos densityIntegral sourceMargin

      weightedMargin :
        M.erbUpperTotal (P.asLiteralERBUpperMajorants bounds)
        <
        - (Vacuum.coefficient (Eq223.eq223VacuumTraceConstant realization)
            * densityIntegral)
      weightedMargin =
        subst
          (λ left → left
            < - (Vacuum.coefficient
                  (Eq223.eq223VacuumTraceConstant realization)
                  * densityIntegral))
          (sym (weightedUpperTotalFactors bounds))
          (subst
            (λ right → sourceUpperTotal bounds * densityIntegral < right)
            (Ring.solve-∀
              (Eq223.eq223VacuumTraceCoefficient realization)
              densityIntegral)
            scaled)
    in
    M.factoredVacuumMarginForcesDominance
      (P.asLiteralERBUpperMajorants bounds)
      scaleLaw
      (Eq223.eq223VacuumTraceConstant realization)
      weightedMargin

finiteMeasureNormalizationCancelsFromPreferredSourceSign : Bool
finiteMeasureNormalizationCancelsFromPreferredSourceSign = true

preferredEq223SignLeafIsPointwiseCauchyBoundsPlusOneScalarMargin : Bool
preferredEq223SignLeafIsPointwiseCauchyBoundsPlusOneScalarMargin = true
