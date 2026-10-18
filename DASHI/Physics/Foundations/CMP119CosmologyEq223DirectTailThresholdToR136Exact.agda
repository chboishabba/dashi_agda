{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223DirectTailThresholdToR136Exact where

------------------------------------------------------------------------
-- SHORTEST PREFERRED SIGN CONSUMER.
--
-- This consumer removes finite-family/observable presentation data entirely.
-- It consumes exactly two physical receipts:
--
--   B1: embed(Q_R136) <= embed(D_Gamma,k) + embed(Tail_R109(k))
--   A : c_V < -(M_ERB + Tail_R109(k)).
--
-- The existing Eq.(2.23) finite upper bound and ordered-scalar compilers then
-- force the literal rational R136 four-diagonal response negative.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact as Envelope
import DASHI.Physics.Foundations.CMP119CosmologyEq223FiniteEffectiveActionUpperExact as Finite
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumTailThresholdExact as Threshold
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136CompletedFourDiagonalExpectationExact as Completed
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealSign
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

module _
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld}
    {metricInputs : R134.PresentCutMetricSpecificInputs firstWeld}
    {representation : StressRep.CanonicalMetricStressRepresentation
      (R134.presentCutCanonicalMetricDomain metricInputs)}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {lane : StressLane.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      (R134.presentCutCanonicalMetricDomain metricInputs) representation}
    {scaleWeld : R135.UnifiedGeneratedActionStressScale lane}
    (recovery : R136.UnifiedGeneratedActionSectorRecovery scaleWeld)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        (R134.presentCutCanonicalMetricDomain metricInputs)
        representation coordinate)
    (directions :
      Continuum.FourAdmittedMetricDirections
        (R134.presentCutCanonicalMetricDomain metricInputs))
    (r109Source : R109.SourceNativeStressScaleCauchy)
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm}
    {sourceScale : Nat}
    (sourceVariation :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration sourceScale)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (orderLaws : Order.RationalPositiveFiniteMeasureOrderLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (signLaws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation sourceVariation) h x
      ≡ 0ℚ)
    (embedding : Additive.OrderedAdditiveRationalRealEmbedding)
    (realOrder : RealSign.RealWeakStrictTransitivity)
    (reflection :
      Readout.NegativeOrderReflectionAtZero (Additive.base embedding))
  where

  module F =
    Finite sourceVariation measure orderLaws partition scaleLaw signLaws referenceFixed
  module E = Envelope sourceVariation measure orderLaws partition scaleLaw

  completedResponse : ℚ
  completedResponse =
    Completed.completedFourDiagonalExpectation recovery selected directions

  directVacuumThresholdForcesNegativeR136 :
    (start : Nat)
    (anchor :
      Direct.DirectR144R109TailAnchor
        embedding r109Source completedResponse F.finiteEffectiveActionWeyl start)
    (envelope : E.CombinedERBTraceEnvelope) →
    Eq223.eq223VacuumTraceCoefficient sourceVariation
      < Threshold.requiredVacuumUpper
          (E.combinedUpper envelope)
          (Tail.r109RemainingTail r109Source start) →
    Continuum.continuumFourDiagonalResponse recovery selected directions < 0ℚ
  directVacuumThresholdForcesNegativeR136 start anchor envelope threshold =
    let
      sourceTailMargin :
        (E.combinedUpper envelope
          + Eq223.eq223VacuumTraceCoefficient sourceVariation)
          + Tail.r109RemainingTail r109Source start
          < 0ℚ
      sourceTailMargin =
        Threshold.vacuumBelowRequiredUpperForcesStrictMargin
          (E.combinedUpper envelope)
          (Eq223.eq223VacuumTraceCoefficient sourceVariation)
          (Tail.r109RemainingTail r109Source start)
          threshold

      finitePlusTailBelowSourcePlusTail :
        F.finiteEffectiveActionWeyl
          + Tail.r109RemainingTail r109Source start
        ≤
        (E.combinedUpper envelope
          + Eq223.eq223VacuumTraceCoefficient sourceVariation)
          + Tail.r109RemainingTail r109Source start
      finitePlusTailBelowSourcePlusTail =
        ℚP.+-mono-≤
          (F.finiteEffectiveActionWeylBelowCombinedSourceUpper envelope)
          ℚP.≤-refl

      finitePlusTailNegative :
        F.finiteEffectiveActionWeyl
          + Tail.r109RemainingTail r109Source start
        < 0ℚ
      finitePlusTailNegative =
        ℚP.≤-<-trans finitePlusTailBelowSourcePlusTail sourceTailMargin

      completedNegative : completedResponse < 0ℚ
      completedNegative =
        Direct.directTailMarginForcesNegativeRationalCompletion
          embedding realOrder reflection anchor finitePlusTailNegative
    in
    subst
      (λ value → value < 0ℚ)
      (Completed.completedFourDiagonalExpectationIsR136Response
        recovery selected directions)
      completedNegative

directPreferredConsumerNeedsFiniteFamilyOrObservable : Bool
directPreferredConsumerNeedsFiniteFamilyOrObservable = false

directPreferredConsumerUsesOneB1TailReceipt : Bool
directPreferredConsumerUsesOneB1TailReceipt = true

directPreferredConsumerUsesOneEq223VacuumThreshold : Bool
directPreferredConsumerUsesOneEq223VacuumThreshold = true

directPreferredConsumerNeedsFiniteEqualsContinuum : Bool
directPreferredConsumerNeedsFiniteEqualsContinuum = false
