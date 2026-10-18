{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR144EffectiveActionStressExpectationExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyR144CompleteActionPartitionResponseExact as R144Partition
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.BalabanR144ToCMP119StressInsertionExact as R144Stress
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact as R118
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

module _
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (composite : R144.CompositeStressFirstVariationInputs actionWeld laws)
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    (domain :
      Domain.CanonicalMetricSourceDomain
        Scale Volume (R144.stressActivity composite))
    (representation : StressRep.CanonicalMetricStressRepresentation domain)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate)
    (attachment :
      R144Attach.R144CanonicalMetricTangentAttachment
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld} {laws = laws}
        composite
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        domain representation {coordinate = coordinate} selected)
  where

  Configuration : Set
  Configuration =
    R144Partition.Configuration
      composite domain representation selected attachment

  MetricTangent : Set
  MetricTangent =
    R144Partition.MetricTangent
      composite domain representation selected attachment

  weightedActionDerivativeNumerator :
    Physical.PhysicalFiniteYMMeasure Configuration ℚ →
    MetricTangent → ℚ
  weightedActionDerivativeNumerator measure tangent =
    Physical.haarIntegral measure
      (λ configuration →
        Physical.density measure configuration
        * R144Partition.completeLocalizedActionDerivative
            composite domain representation selected attachment
            tangent configuration)

  normalizedStressExpectation :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
    Partition.PhysicalFinitePartitionAuthority measure →
    MetricTangent → ℚ
  normalizedStressExpectation measure authority tangent =
    Quot.dividePositive
      (weightedActionDerivativeNumerator measure tangent)
      (Physical.partitionFunction measure)
      (Partition.partitionPositive authority)

  effectiveActionMetricResponse :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
    Partition.PhysicalFinitePartitionAuthority measure →
    MetricTangent → ℚ
  effectiveActionMetricResponse measure authority tangent =
    Quot.dividePositive
      (- R144Partition.completeActionPartitionDerivative
        composite domain representation selected attachment
        measure tangent)
      (Physical.partitionFunction measure)
      (Partition.partitionPositive authority)

  negativePartitionDerivativeIsWeightedActionDerivative :
    ∀ (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      (integrationLaws : Sign.RationalWeylSignIntegrationLaws measure)
      tangent →
    - R144Partition.completeActionPartitionDerivative
        composite domain representation selected attachment measure tangent
    ≡ weightedActionDerivativeNumerator measure tangent
  negativePartitionDerivativeIsWeightedActionDerivative
      measure integrationLaws tangent =
    let
      f = λ configuration →
        Physical.density measure configuration
        * R144Partition.completeLocalizedActionDerivative
            composite domain representation selected attachment
            tangent configuration

      negIntegral =
        Sign.haarIntegralNegate integrationLaws f
    in
    trans
      (cong -_
        (R144Partition.completeActionPartitionDerivativeIsLiteralHaarD1
          composite domain representation selected attachment
          measure tangent))
      (trans
        (cong -_ negIntegral)
        (Ring.solve-∀ (Physical.haarIntegral measure f)))

  effectiveActionResponseIsNormalizedStressExpectation :
    ∀ (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      (authority : Partition.PhysicalFinitePartitionAuthority measure)
      (integrationLaws : Sign.RationalWeylSignIntegrationLaws measure)
      tangent →
    effectiveActionMetricResponse measure authority tangent
    ≡ normalizedStressExpectation measure authority tangent
  effectiveActionResponseIsNormalizedStressExpectation
      measure authority integrationLaws tangent =
    cong
      (λ numerator →
        Quot.dividePositive numerator
          (Physical.partitionFunction measure)
          (Partition.partitionPositive authority))
      (negativePartitionDerivativeIsWeightedActionDerivative
        measure integrationLaws tangent)

  finiteStressInsertionIsR144ActionDerivative :
    ∀ configuration tangent →
    R144Partition.completeLocalizedActionDerivative
      composite domain representation selected attachment
      tangent configuration
    ≡
    let
      oldWeld =
        R144Attach.asOldR144ToSelectedCMP119StressInsertion attachment
      metricBackground =
        R144Stress.toMetricBackground oldWeld configuration
      perturbation =
        R144Stress.toMetricPerturbation oldWeld tangent
    in
    R116.cmp119StressInsertionNumerator
      (R118.normalizedInsertion
        (R119.asRound118CanonicalMetricWeld selected)
        metricBackground perturbation)
  finiteStressInsertionIsR144ActionDerivative =
    R144Partition.completeActionDerivativeIsSelectedCMP119StressInsertion
      composite domain representation selected attachment

  finiteOnePointStressOrientationIsEffectiveActionResponse : Bool
  finiteOnePointStressOrientationIsEffectiveActionResponse = true

  finiteOnePointStressIsNotLogPartitionResponse : Bool
  finiteOnePointStressIsNotLogPartitionResponse = true

  remainingBridgeIsFiniteExpectationToR136VacuumExpectation : Bool
  remainingBridgeIsFiniteExpectationToR136VacuumExpectation = true
