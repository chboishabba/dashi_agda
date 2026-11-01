{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223FiniteEffectiveActionUpperExact where

------------------------------------------------------------------------
-- QUANTITATIVE FINITE EQ.(2.23) BOUND.
--
-- Under fixed Haar,
--
--   D_Gamma^Weyl = N_nonWilson / Z.
--
-- If the combined E/R/B four-diagonal trace is bounded by M_ERB and the
-- vacuum four-diagonal trace is the constant c_V, then the common positive
-- density factor cancels and
--
--   D_Gamma^Weyl <= M_ERB + c_V.
--
-- This is stronger than a sign theorem and is the quantity needed to compare a
-- finite source margin directly with the explicit Round109 remaining tail.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; positive; _+_; _*_; _≤_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact as Envelope
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
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
    (signLaws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation realization) h x
      ≡ 0ℚ)
  where

  d = Eq223.sourceCompleteFiniteMetricVariation realization
  module E = Envelope realization measure orderLaws partition scaleLaw

  z : ℚ
  z = Physical.partitionFunction measure

  densityIntegral : ℚ
  densityIntegral = Physical.haarIntegral measure (Physical.density measure)

  nonWilsonNumerator : ℚ
  nonWilsonNumerator = Sign.weightedNonWilsonWeylNumerator measure d

  finiteEffectiveActionWeyl : ℚ
  finiteEffectiveActionWeyl =
    Convention.matterEffectiveActionWeylResponse measure partition d

  nonWilsonNumeratorIsCombinedERBPlusVacuum :
    nonWilsonNumerator
    ≡ E.combinedERBNumerator + Sector.vacuumNumerator measure d
  nonWilsonNumeratorIsCombinedERBPlusVacuum =
    trans
      (Sector.weightedNonWilsonNumeratorSplitsFourWays
        measure d (Sign.base signLaws))
      (trans
        (Ring.solve-∀
          (Sector.regularNumerator measure d)
          (Sector.rOperationNumerator measure d)
          (Sector.boundaryNumerator measure d)
          (Sector.vacuumNumerator measure d))
        (cong
          (λ erb → erb + Sector.vacuumNumerator measure d)
          (sym (E.combinedERBNumeratorIsLiteralERB))))

  finiteEffectiveActionWeylIsNormalizedNonWilsonNumerator :
    finiteEffectiveActionWeyl
    ≡ Quot.dividePositive nonWilsonNumerator z (Partition.partitionPositive partition)
  finiteEffectiveActionWeylIsNormalizedNonWilsonNumerator =
    let
      partitionIsNegativeNumerator =
        Sign.fixedHaarResponseIsNegativeWeightedNonWilsonNumerator
          measure d signLaws referenceFixed
    in
    trans
      (cong -_
        (cong
          (λ numerator →
            Quot.dividePositive numerator z (Partition.partitionPositive partition))
          partitionIsNegativeNumerator))
      (Ring.solve-∀
        nonWilsonNumerator
        (Quot.positiveReciprocal z (Partition.partitionPositive partition)))

  numeratorBelowCombinedEnvelopePlusVacuum :
    (envelope : E.CombinedERBTraceEnvelope) →
    nonWilsonNumerator
    ≤ (E.combinedUpper envelope
        + Eq223.eq223VacuumTraceCoefficient realization)
      * densityIntegral
  numeratorBelowCombinedEnvelopePlusVacuum envelope =
    let
      erbBelow = E.combinedERBNumeratorBelowFactoredUpper envelope
      vacuumFactors =
        Vacuum.vacuumNumeratorFactors
          measure d (Order.linear orderLaws) scaleLaw
          (Eq223.eq223VacuumTraceConstant realization)

      summed :
        E.combinedERBNumerator + Sector.vacuumNumerator measure d
        ≤
        (E.combinedUpper envelope * densityIntegral)
        + (Eq223.eq223VacuumTraceCoefficient realization * densityIntegral)
      summed =
        ℚP.+-mono-≤
          erbBelow
          (ℚP.≤-reflexive vacuumFactors)
    in
    subst
      (λ left →
        left
        ≤ (E.combinedUpper envelope
            + Eq223.eq223VacuumTraceCoefficient realization)
          * densityIntegral)
      (sym nonWilsonNumeratorIsCombinedERBPlusVacuum)
      (subst
        (λ right →
          E.combinedERBNumerator + Sector.vacuumNumerator measure d ≤ right)
        (Ring.solve-∀
          (E.combinedUpper envelope)
          (Eq223.eq223VacuumTraceCoefficient realization)
          densityIntegral)
        summed)

  numeratorBelowCombinedEnvelopeTimesPartition :
    (envelope : E.CombinedERBTraceEnvelope) →
    nonWilsonNumerator
    ≤ (E.combinedUpper envelope
        + Eq223.eq223VacuumTraceCoefficient realization) * z
  numeratorBelowCombinedEnvelopeTimesPartition envelope =
    subst
      (λ densityValue →
        nonWilsonNumerator
        ≤ (E.combinedUpper envelope
            + Eq223.eq223VacuumTraceCoefficient realization)
          * densityValue)
      (sym (Partition.partitionIsDensityIntegral partition))
      (numeratorBelowCombinedEnvelopePlusVacuum envelope)

  divideUpperTimesPartitionCancels :
    ∀ upper →
    Quot.dividePositive (upper * z) z (Partition.partitionPositive partition)
    ≡ upper
  divideUpperTimesPartitionCancels upper =
    trans
      (ℚP.*-assoc upper z
        (Quot.positiveReciprocal z (Partition.partitionPositive partition)))
      (trans
        (cong
          (upper *_)
          (Quot.positiveReciprocalRightInverse
            z (Partition.partitionPositive partition)))
        (ℚP.*-identityʳ upper))

  finiteEffectiveActionWeylBelowCombinedSourceUpper :
    (envelope : E.CombinedERBTraceEnvelope) →
    finiteEffectiveActionWeyl
    ≤ E.combinedUpper envelope
      + Eq223.eq223VacuumTraceCoefficient realization
  finiteEffectiveActionWeylBelowCombinedSourceUpper envelope =
    subst
      (λ left →
        left
        ≤ E.combinedUpper envelope
          + Eq223.eq223VacuumTraceCoefficient realization)
      (sym finiteEffectiveActionWeylIsNormalizedNonWilsonNumerator)
      (subst
        (λ right →
          Quot.dividePositive nonWilsonNumerator z
            (Partition.partitionPositive partition)
          ≤ right)
        (divideUpperTimesPartitionCancels
          (E.combinedUpper envelope
            + Eq223.eq223VacuumTraceCoefficient realization))
        (Quot.dividePositiveNumeratorMonotone
          nonWilsonNumerator
          ((E.combinedUpper envelope
            + Eq223.eq223VacuumTraceCoefficient realization) * z)
          z (Partition.partitionPositive partition)
          (numeratorBelowCombinedEnvelopeTimesPartition envelope)))

  quantitativeFiniteSourceBoundCompilerOwned : Bool
  quantitativeFiniteSourceBoundCompilerOwned = true

  finiteUpperIsCombinedERBPlusVacuumCoefficient : Bool
  finiteUpperIsCombinedERBPlusVacuumCoefficient = true
