{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119R144PartitionInsertionTrivialityExact where

------------------------------------------------------------------------
-- R144 PARTITION-STRESS INSERTION IS DEFINITIONALLY O = 1, DO = 0
--
-- The complete-action R144 partition response already packages the Gibbs data
-- with the constant observable 1 and zero insertion variation.  Therefore the
-- partition-derived stress route must not be charged an independent selected
-- observable O or DO[h].  Those are only additional data for a distinct
-- inserted-observable / connected-numerator consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ)

import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119CosmologyR144CompleteActionPartitionResponseExact as Complete

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
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

  finiteAction : Finite.FiniteLocalizedEffectiveAction
  finiteAction = Carrier.finiteAction (Present.bc1Carrier present)

  Configuration : Set
  Configuration = Finite.Configuration finiteAction

  MetricTangent : Set
  MetricTangent = Finite.Tangent finiteAction

  partitionObservableIsOne :
    ∀ (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      configuration →
    Gibbs.insertionObservable
      (Complete.completeActionGibbsData
        composite domain representation selected attachment measure)
      configuration
    ≡ 1ℚ
  partitionObservableIsOne measure configuration = refl

  partitionInsertionVariationIsZero :
    ∀ (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      tangent configuration →
    Gibbs.insertionVariation
      (Complete.completeActionGibbsData
        composite domain representation selected attachment measure)
      tangent configuration
    ≡ 0ℚ
  partitionInsertionVariationIsZero measure tangent configuration = refl

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

partitionResponseInsertionObservableRequiresIndependentSelection : Bool
partitionResponseInsertionObservableRequiresIndependentSelection = false

partitionResponseInsertionVariationRequiresIndependentSelection : Bool
partitionResponseInsertionVariationRequiresIndependentSelection = false

partitionStressRouteNeedsInsertedObservableMetricVariation : Bool
partitionStressRouteNeedsInsertedObservableMetricVariation = false

insertedObservableConnectedNumeratorRouteStillSeparate : Bool
insertedObservableConnectedNumeratorRouteStillSeparate = true
