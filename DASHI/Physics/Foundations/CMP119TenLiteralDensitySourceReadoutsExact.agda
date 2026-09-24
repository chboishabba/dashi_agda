{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenLiteralDensitySourceReadoutsExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as SourceFlow
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as Local
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact as R121
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- ACTUAL SELECTED CMP119 READOUT -> LITERAL BETA-DENSITY CONNECTED NUMERATOR
--
-- R122 already owns the exact equality between the selected R119 normalized
-- source and R121.crossDataAt on densityAt inputs selectedScale.  Therefore the
-- terminal ten-value problem can be expressed directly on the literal density
-- source; no synthetic normalization representative is needed.
------------------------------------------------------------------------

module _
    {History Cell : Set} {cutoff : Nat}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
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
    (densityAnchor :
      R122.DensityAnchoredCanonicalMetricStress
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        {activity = R144.stressActivity composite}
        {domain = domain} {representation = representation}
        {coordinate = coordinate}
        selected)
  where

  tangentAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact.Tangent
      (Carrier.finiteAction
        (Present.bc1Carrier
          (Present10.asPresentCutPhysicalSourceInputs presentData)))
  tangentAtAxes a b =
    Present10.symmetricSlotAsPresentCutFiniteTangent
      presentData
      (MetricBasis.symmetricSlotOfAxes a b)

  perturbationAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    Domain.MetricPerturbation domain
  perturbationAtAxes a b =
    R144Attach.toMetricPerturbation attachment (tangentAtAxes a b)

  literalDensityPerturbationAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    R121.MetricPerturbation (R122.densitySource densityAnchor)
  literalDensityPerturbationAtAxes a b =
    R122.metricPerturbationToDensityPerturbation
      densityAnchor (perturbationAtAxes a b)

  literalDensityConnectedNumeratorAtAxes :
    Flat.Axis4 → Flat.Axis4 → ℚ
  literalDensityConnectedNumeratorAtAxes a b =
    R121.connectedInsertionNumerator (R122.densitySource densityAnchor)
      (BetaDensity.densityAt inputs (R122.selectedDensityScale densityAnchor))
      (literalDensityPerturbationAtAxes a b)

  selectedConnectedNumeratorAtAxes :
    Flat.Axis4 → Flat.Axis4 → ℚ
  selectedConnectedNumeratorAtAxes a b =
    R116.connectedInsertionNumerator
      (R119.normalizedSource selected
        (R144.globalBackgroundToStressBackground composite background)
        (perturbationAtAxes a b))

  selectedConnectedNumeratorIsLiteralDensity :
    ∀ a b →
    selectedConnectedNumeratorAtAxes a b
    ≡ literalDensityConnectedNumeratorAtAxes a b
  selectedConnectedNumeratorIsLiteralDensity a b =
    R122.canonicalMetricConnectedInsertionIsOnLiteralDensity
      densityAnchor
      (R144.globalBackgroundToStressBackground composite background)
      (perturbationAtAxes a b)

  actual00 : ℚ
  actual00 =
    literalDensityConnectedNumeratorAtAxes Flat.timeAxis Flat.timeAxis

  actual01 : ℚ
  actual01 =
    literalDensityConnectedNumeratorAtAxes Flat.timeAxis Flat.xAxis

  actual02 : ℚ
  actual02 =
    literalDensityConnectedNumeratorAtAxes Flat.timeAxis Flat.yAxis

  actual03 : ℚ
  actual03 =
    literalDensityConnectedNumeratorAtAxes Flat.timeAxis Flat.zAxis

  actual11 : ℚ
  actual11 =
    literalDensityConnectedNumeratorAtAxes Flat.xAxis Flat.xAxis

  actual12 : ℚ
  actual12 =
    literalDensityConnectedNumeratorAtAxes Flat.xAxis Flat.yAxis

  actual13 : ℚ
  actual13 =
    literalDensityConnectedNumeratorAtAxes Flat.xAxis Flat.zAxis

  actual22 : ℚ
  actual22 =
    literalDensityConnectedNumeratorAtAxes Flat.yAxis Flat.yAxis

  actual23 : ℚ
  actual23 =
    literalDensityConnectedNumeratorAtAxes Flat.yAxis Flat.zAxis

  actual33 : ℚ
  actual33 =
    literalDensityConnectedNumeratorAtAxes Flat.zAxis Flat.zAxis
