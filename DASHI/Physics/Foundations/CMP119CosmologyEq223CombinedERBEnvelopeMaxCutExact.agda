{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact where

------------------------------------------------------------------------
-- SHARPER EQ.(2.23) SOURCE SIGN CUT.
--
-- The cosmology consumer never needs E, R and B upper bounds separately.  It
-- only needs a uniform upper bound on their COMBINED four-diagonal metric
-- trace.  This owner therefore replaces the terminal three-calibration cut by
-- one source theorem
--
--   E_diag4(U) + R_diag4(U) + B_diag4(U) <= M_ERB
--
-- together with one scalar vacuum margin
--
--   M_ERB < - c_V.
--
-- Positive Haar integration and the common density factor then compile this
-- directly to
--
--   N_E + N_R + N_B < - N_V.
--
-- The existing three Cauchy constants remain a useful PRODUCER strategy for
-- this combined envelope; they are no longer terminal cosmology premises.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; Positive; positive; _+_; _*_; _≤_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyEq223NegativeSectorDominanceExact as Dominance
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyVacuumDominatedWeylSignExact as VacuumCut
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
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

  combinedERBDiagonalTrace : Configuration → ℚ
  combinedERBDiagonalTrace configuration =
    (Sector.regularDiagonalTrace d configuration
      + Sector.rOperationDiagonalTrace d configuration)
      + Sector.boundaryDiagonalTrace d configuration

  combinedERBNumerator : ℚ
  combinedERBNumerator =
    Order.weightedNumerator measure combinedERBDiagonalTrace

  combinedERBNumeratorIsLiteralERB :
    combinedERBNumerator ≡ VacuumCut.erbNumerator measure d
  combinedERBNumeratorIsLiteralERB =
    let
      laws = Order.linear orderLaws
      fr = λ x →
        Physical.density measure x * Sector.regularDiagonalTrace d x
      fR = λ x →
        Physical.density measure x * Sector.rOperationDiagonalTrace d x
      fb = λ x →
        Physical.density measure x * Sector.boundaryDiagonalTrace d x
    in
    trans
      (Integral.haarIntegralCongruent laws _ _
        (λ x →
          Ring.solve-∀
            (Physical.density measure x)
            (Sector.regularDiagonalTrace d x)
            (Sector.rOperationDiagonalTrace d x)
            (Sector.boundaryDiagonalTrace d x)))
      (trans
        (Integral.haarIntegralAdd laws
          (λ x → fr x + fR x) fb)
        (cong₂ _+_
          (Integral.haarIntegralAdd laws fr fR)
          refl))

  record CombinedERBTraceEnvelope : Set₁ where
    field
      combinedUpper : ℚ
      combinedTraceBelow :
        ∀ configuration →
        combinedERBDiagonalTrace configuration ≤ combinedUpper

  open CombinedERBTraceEnvelope public

  densityIntegral : ℚ
  densityIntegral =
    Physical.haarIntegral measure (Physical.density measure)

  densityIntegralPositive : 0ℚ < densityIntegral
  densityIntegralPositive =
    subst
      (λ value → 0ℚ < value)
      (Partition.partitionIsDensityIntegral partition)
      (Partition.partitionPositive partition)

  combinedERBNumeratorBelowFactoredUpper :
    (envelope : CombinedERBTraceEnvelope) →
    combinedERBNumerator
      ≤ combinedUpper envelope * densityIntegral
  combinedERBNumeratorBelowFactoredUpper envelope =
    ℚP.≤-trans
      (Order.weightedNumeratorBelowConstant
        orderLaws combinedERBDiagonalTrace
        (combinedUpper envelope)
        (combinedTraceBelow envelope))
      (ℚP.≤-reflexive
        (Order.weightedConstantFactorsDensityIntegral
          orderLaws (combinedUpper envelope)))

  combinedEnvelopeVacuumMarginForcesLiteralDominance :
    (envelope : CombinedERBTraceEnvelope) →
    combinedUpper envelope
      < - Eq223.eq223VacuumTraceCoefficient realization →
    Dominance.LiteralNegativeSectorDominance realization measure
  combinedEnvelopeVacuumMarginForcesLiteralDominance envelope sourceMargin =
    let
      instance densityIntegralPositiveI : Positive densityIntegral
      densityIntegralPositiveI = positive densityIntegralPositive

      scaledMargin :
        combinedUpper envelope * densityIntegral
        <
        (- Eq223.eq223VacuumTraceCoefficient realization) * densityIntegral
      scaledMargin =
        ℚP.*-monoʳ-<-pos densityIntegral sourceMargin

      combinedBelowScaledNegativeVacuum :
        combinedERBNumerator
        <
        (- Eq223.eq223VacuumTraceCoefficient realization) * densityIntegral
      combinedBelowScaledNegativeVacuum =
        ℚP.≤-<-trans
          (combinedERBNumeratorBelowFactoredUpper envelope)
          scaledMargin

      combinedBelowNegativeVacuumFactored :
        combinedERBNumerator
        <
        - (Eq223.eq223VacuumTraceCoefficient realization * densityIntegral)
      combinedBelowNegativeVacuumFactored =
        subst
          (λ right → combinedERBNumerator < right)
          (Ring.solve-∀
            (Eq223.eq223VacuumTraceCoefficient realization)
            densityIntegral)
          combinedBelowScaledNegativeVacuum

      combinedBelowNegativeVacuumNumerator :
        combinedERBNumerator < - Sector.vacuumNumerator measure d
      combinedBelowNegativeVacuumNumerator =
        subst
          (λ right → combinedERBNumerator < - right)
          (sym
            (Vacuum.vacuumNumeratorFactors
              measure d (Order.linear orderLaws) scaleLaw
              (Eq223.eq223VacuumTraceConstant realization)))
          combinedBelowNegativeVacuumFactored
    in
    subst
      (λ left →
        left < - Dominance.literalVacuumNumerator realization measure)
      (combinedERBNumeratorIsLiteralERB)
      combinedBelowNegativeVacuumNumerator

  combinedERBEnvelopeReplacesThreeTerminalSectorBounds : Bool
  combinedERBEnvelopeReplacesThreeTerminalSectorBounds = true

  oldThreeCauchyCalibrationRouteRemainsProducerStrategy : Bool
  oldThreeCauchyCalibrationRouteRemainsProducerStrategy = true

  terminalEq223SignDataAreOneCombinedEnvelopeAndOneVacuumMargin : Bool
  terminalEq223SignDataAreOneCombinedEnvelopeAndOneVacuumMargin = true
