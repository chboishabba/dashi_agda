{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenActualSourceReadoutsExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
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
import DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact as R118
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.BalabanR144ToCMP119StressInsertionExact as Old
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- ACTUAL TEN SOURCE READOUTS
--
-- Do not guess N, Z, dN or dZ.  R119 already constructs, for every selected
-- metric perturbation, the literal normalized CMP119 insertion object consumed
-- by the stress lane.  Its exact scalar is
--
--   R116.cmp119StressInsertionNumerator.
--
-- This module exposes those ten source-native scalars on the symmetric metric
-- basis and proves that the existing post-sum R144 finite-D1 readout is exactly
-- the same scalar.  Therefore the remaining numerical frontier is literally
-- "evaluate these ten selected CMP119 insertion numerators", with no D1a/D1b
-- or tensor-transport debt hiding behind it.
------------------------------------------------------------------------

module _
    {History Cell : Set} {cutoff : Nat}
    {trajectory split inputs}
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
  where

  finiteTangentAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact.Tangent
      (Carrier.finiteAction
        (Present.bc1Carrier
          (Present10.asPresentCutPhysicalSourceInputs presentData)))
  finiteTangentAtAxes a b =
    Present10.symmetricSlotAsPresentCutFiniteTangent
      presentData
      (MetricBasis.symmetricSlotOfAxes a b)

  metricPerturbationAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    Domain.MetricPerturbation domain
  metricPerturbationAtAxes a b =
    R144Attach.toMetricPerturbation attachment (finiteTangentAtAxes a b)

  selectedInsertionAtAxes :
    Flat.Axis4 → Flat.Axis4 →
    R116.MetricStressNormalizedInsertionWeld
  selectedInsertionAtAxes a b =
    R118.normalizedInsertion
      (R119.asRound118CanonicalMetricWeld selected)
      (R144.globalBackgroundToStressBackground composite background)
      (metricPerturbationAtAxes a b)

  actualCMP119ReadoutAtAxes :
    Flat.Axis4 → Flat.Axis4 → ℚ
  actualCMP119ReadoutAtAxes a b =
    R116.cmp119StressInsertionNumerator (selectedInsertionAtAxes a b)

  postSumFiniteD1ReadoutAtAxes :
    Flat.Axis4 → Flat.Axis4 → ℚ
  postSumFiniteD1ReadoutAtAxes a b =
    R144Attach.finiteD1ToCanonicalMetricRational attachment
      (DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact.finiteLocalizedFirstVariation
        (Carrier.finiteAction
          (Present.bc1Carrier
            (Present10.asPresentCutPhysicalSourceInputs presentData)))
        (R143.asFirstVariationLinearity laws)
        background
        (finiteTangentAtAxes a b))

  postSumFiniteD1IsActualCMP119Readout :
    ∀ a b →
    postSumFiniteD1ReadoutAtAxes a b
    ≡ actualCMP119ReadoutAtAxes a b
  postSumFiniteD1IsActualCMP119Readout a b =
    Old.r144LocalizedD1IsSelectedCMP119Insertion
      (R144Attach.asOldR144ToSelectedCMP119StressInsertion attachment)
      background
      (finiteTangentAtAxes a b)

  actual00 : ℚ
  actual00 = actualCMP119ReadoutAtAxes Flat.timeAxis Flat.timeAxis

  actual01 : ℚ
  actual01 = actualCMP119ReadoutAtAxes Flat.timeAxis Flat.xAxis

  actual02 : ℚ
  actual02 = actualCMP119ReadoutAtAxes Flat.timeAxis Flat.yAxis

  actual03 : ℚ
  actual03 = actualCMP119ReadoutAtAxes Flat.timeAxis Flat.zAxis

  actual11 : ℚ
  actual11 = actualCMP119ReadoutAtAxes Flat.xAxis Flat.xAxis

  actual12 : ℚ
  actual12 = actualCMP119ReadoutAtAxes Flat.xAxis Flat.yAxis

  actual13 : ℚ
  actual13 = actualCMP119ReadoutAtAxes Flat.xAxis Flat.zAxis

  actual22 : ℚ
  actual22 = actualCMP119ReadoutAtAxes Flat.yAxis Flat.yAxis

  actual23 : ℚ
  actual23 = actualCMP119ReadoutAtAxes Flat.yAxis Flat.zAxis

  actual33 : ℚ
  actual33 = actualCMP119ReadoutAtAxes Flat.zAxis Flat.zAxis
