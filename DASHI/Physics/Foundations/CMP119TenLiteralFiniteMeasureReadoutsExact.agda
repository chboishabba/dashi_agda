{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenLiteralFiniteMeasureReadoutsExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureDensityAnchorConstructorExact as Anchor
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as SourceFlow
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as Local
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- TERMINAL TEN VALUES, DIRECTLY ON THE LITERAL FINITE CLAY MEASURE
------------------------------------------------------------------------

module _
    {History Cell : Set} {cutoff : Nat}
    {trajectory split}
    {inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {source : SourceFlow.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs}
    {localization : Local.CMP119RegularELocalizationCarrier source}
    {bc1Canonical : Present10.SymmetricFunctionalRegularEBC1Inputs
      source localization}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        source localization bc1Canonical)
    {actionWeld :
      R132.UnifiedGeneratedActionDensity
        {trajectory = trajectory} {split = split} {inputs = inputs}
        (Present10.asPresentCutPhysicalSourceInputs presentData)}
    {laws :
      R143.PresentCutBC2FirstVariationLinearity
        (Present10.asPresentCutPhysicalSourceInputs presentData)}
    {composite : R144.CompositeStressFirstVariationInputs actionWeld laws}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {domain :
      Domain.CanonicalMetricSourceDomain
        Scale Volume (R144.stressActivity composite)}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    {selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate}
    (attachment :
      R144Attach.R144CanonicalMetricTangentAttachment
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = Present10.asPresentCutPhysicalSourceInputs presentData}
        {actionWeld = actionWeld} {laws = laws}
        composite
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        domain representation {coordinate = coordinate} selected)
    (background :
      Source.Background
        (Carrier.source
          (Present.bc1Carrier
            (Present10.asPresentCutPhysicalSourceInputs presentData))))
    (measureWeld :
      R124.BalabanDensityLiteralFiniteMeasureWeld
        {trajectory = trajectory} {split = split} {inputs = inputs}
        Y group)
    (calculus :
      FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus measureWeld)
    (anchorInputs :
      Anchor.LiteralFiniteMeasureDensityAnchorInputs
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        {activity = R144.stressActivity composite}
        {domain = domain} {representation = representation}
        {coordinate = coordinate}
        selected measureWeld calculus)
  where

  tangentAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    Finite.Tangent
      (Carrier.finiteAction
        (Present.bc1Carrier
          (Present10.asPresentCutPhysicalSourceInputs presentData)))
  tangentAtAxes a b =
    Present10.symmetricSlotAsPresentCutFiniteTangent
      presentData
      (MetricBasis.symmetricSlotOfAxes a b)

  metricPerturbationAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    Domain.MetricPerturbation domain
  metricPerturbationAtAxes a b =
    R144Attach.toMetricPerturbation attachment (tangentAtAxes a b)

  finiteMeasurePerturbationAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    FiniteSource.MetricPerturbation calculus
  finiteMeasurePerturbationAtAxes a b =
    Anchor.metricPerturbationToFiniteMeasurePerturbation
      anchorInputs (metricPerturbationAtAxes a b)

  selectedScaleIndex : Nat
  selectedScaleIndex =
    Anchor.sourceScaleIndex anchorInputs
      (Anchor.selectedScale anchorInputs)

  selectedLiteralFiniteMeasure : Top.FiniteMeasure C
  selectedLiteralFiniteMeasure =
    Top.finiteMeasure Y group
      (R124.cutoffAtScale measureWeld selectedScaleIndex)

  finiteMeasureConnectedNumeratorAtAxes :
    Flat.Axis4 → Flat.Axis4 → ℚ
  finiteMeasureConnectedNumeratorAtAxes a b =
    FiniteSource.connectedInsertionNumerator calculus
      selectedLiteralFiniteMeasure
      (finiteMeasurePerturbationAtAxes a b)

  selectedSourceConnectedNumeratorAtAxes :
    Flat.Axis4 → Flat.Axis4 → ℚ
  selectedSourceConnectedNumeratorAtAxes a b =
    R116.connectedInsertionNumerator
      (R119.normalizedSource selected
        (R144.globalBackgroundToStressBackground composite background)
        (metricPerturbationAtAxes a b))

  selectedSourceIsFiniteMeasureConnectedNumerator :
    ∀ a b →
    selectedSourceConnectedNumeratorAtAxes a b
    ≡ finiteMeasureConnectedNumeratorAtAxes a b
  selectedSourceIsFiniteMeasureConnectedNumerator a b =
    trans
      (R122.canonicalMetricConnectedInsertionIsOnLiteralDensity
        (Anchor.asDensityAnchoredCanonicalMetricStress anchorInputs)
        (R144.globalBackgroundToStressBackground composite background)
        (metricPerturbationAtAxes a b))
      (FiniteSource.connectedNumeratorAtBetaScaleIsFiniteMeasureNumerator
        calculus selectedScaleIndex (finiteMeasurePerturbationAtAxes a b))

  actual00 actual01 actual02 actual03 actual11
    actual12 actual13 actual22 actual23 actual33 : ℚ
  actual00 = finiteMeasureConnectedNumeratorAtAxes Flat.timeAxis Flat.timeAxis
  actual01 = finiteMeasureConnectedNumeratorAtAxes Flat.timeAxis Flat.xAxis
  actual02 = finiteMeasureConnectedNumeratorAtAxes Flat.timeAxis Flat.yAxis
  actual03 = finiteMeasureConnectedNumeratorAtAxes Flat.timeAxis Flat.zAxis
  actual11 = finiteMeasureConnectedNumeratorAtAxes Flat.xAxis Flat.xAxis
  actual12 = finiteMeasureConnectedNumeratorAtAxes Flat.xAxis Flat.yAxis
  actual13 = finiteMeasureConnectedNumeratorAtAxes Flat.xAxis Flat.zAxis
  actual22 = finiteMeasureConnectedNumeratorAtAxes Flat.yAxis Flat.yAxis
  actual23 = finiteMeasureConnectedNumeratorAtAxes Flat.yAxis Flat.zAxis
  actual33 = finiteMeasureConnectedNumeratorAtAxes Flat.zAxis Flat.zAxis
