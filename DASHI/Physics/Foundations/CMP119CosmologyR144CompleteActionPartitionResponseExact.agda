{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR144CompleteActionPartitionResponseExact where

------------------------------------------------------------------------
-- R144 COMPLETE GENERATED-ACTION D1 -> FIRST PARTITION METRIC RESPONSE
--
-- This is the source-native replacement for four independently supplied
-- E/R/B/vacuum metric-variation callbacks when the complete generated action
-- is already represented by the exact CMP109/CMP116 localized finite sum.
--
-- R142: finiteLocalizedFirstVariation = D1 of the exact finite localized sum.
-- R144: the selected stress first variation is that WHOLE localized D1 sum.
-- R144Attach/R119: the same tangent is attached to the canonical metric
-- perturbation and selected CMP119 stress coordinate.
--
-- Here that complete D1 is reused as the action derivative in the existing
-- Gibbs denominator derivative:
--
--   DZ[h] = integral[-rho * D_h S_complete].
--
-- This is a finite Euclidean fixed-Haar theorem. It does NOT prove:
--   * source CMP119 Eq.(2.23) = this finite action at all cutoffs,
--   * product Haar / gauge-fixing metric independence,
--   * Z>0 and true division/log differentiability,
--   * renormalized Lorentzian T_mu_nu,
--   * covariant conservation or an accelerating FLRW solution.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; -_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact as NZ
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
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

  finiteAction : Finite.FiniteLocalizedEffectiveAction
  finiteAction = Carrier.finiteAction (Present.bc1Carrier present)

  Configuration : Set
  Configuration = Finite.Configuration finiteAction

  MetricTangent : Set
  MetricTangent = Finite.Tangent finiteAction

  completeLocalizedActionDerivative :
    MetricTangent → Configuration → ℚ
  completeLocalizedActionDerivative tangent configuration =
    R144Attach.finiteD1ToCanonicalMetricRational attachment
      (D1.finiteLocalizedFirstVariation
        finiteAction
        (R143.asFirstVariationLinearity laws)
        configuration tangent)

  completeActionDerivativeIsSelectedCanonicalMetricReadout :
    ∀ configuration tangent →
    completeLocalizedActionDerivative tangent configuration
    ≡
    R144Attach.finiteD1ToCanonicalMetricRational attachment
      (D1.finiteLocalizedFirstVariation
        finiteAction
        (R143.asFirstVariationLinearity laws)
        configuration tangent)
  completeActionDerivativeIsSelectedCanonicalMetricReadout configuration tangent =
    refl

  completeActionGibbsData :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
    Gibbs.GibbsMetricInsertionData Configuration MetricTangent measure
  completeActionGibbsData measure = record
    { Gibbs.GibbsMetricInsertionData.insertionObservable = λ _ → 1ℚ
    ; Gibbs.GibbsMetricInsertionData.actionVariation =
        completeLocalizedActionDerivative
    ; Gibbs.GibbsMetricInsertionData.insertionVariation = λ _ _ → 0ℚ
    }

  completeActionPartitionDerivative :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
    MetricTangent → ℚ
  completeActionPartitionDerivative measure tangent =
    NZ.denominatorDerivative
      (Gibbs.asPhysicalMetricStressData (completeActionGibbsData measure))
      tangent

  completeActionPartitionDerivativeIsLiteralHaarD1 :
    ∀ (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) tangent →
    completeActionPartitionDerivative measure tangent
    ≡
    Physical.haarIntegral measure
      (λ configuration →
        - (Physical.density measure configuration
            * completeLocalizedActionDerivative tangent configuration))
  completeActionPartitionDerivativeIsLiteralHaarD1 measure tangent =
    Gibbs.denominatorDerivativeIsLiteralHaarMetricVariation
      (completeActionGibbsData measure) tangent

  completeActionDerivativeIsSelectedCMP119StressInsertion :
    ∀ configuration tangent →
    let
      oldWeld =
        R144Attach.asOldR144ToSelectedCMP119StressInsertion attachment
      metricBackground =
        R144Stress.toMetricBackground oldWeld configuration
      perturbation =
        R144Stress.toMetricPerturbation oldWeld tangent
      insertion =
        R116.cmp119StressInsertionNumerator
          (R118.normalizedInsertion
            (R119.asRound118CanonicalMetricWeld selected)
            metricBackground perturbation)
    in
    completeLocalizedActionDerivative tangent configuration ≡ insertion
  completeActionDerivativeIsSelectedCMP119StressInsertion configuration tangent =
    R144Stress.r144LocalizedD1IsSelectedCMP119Insertion
      (R144Attach.asOldR144ToSelectedCMP119StressInsertion attachment)
      configuration tangent

  -- The one-point Euclidean source numerator is therefore no longer an
  -- arbitrary DZ callback once the R144 action and tangent attachment exist.
  -- The remaining source seam is that the finite physical measure itself must
  -- be the selected CMP119 Gibbs measure for this complete action.
