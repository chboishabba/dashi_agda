{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenFinitePhysicalCompositeDerivativeExact where

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- TEN EXACT FINITE PHYSICAL COMPOSITE DERIVATIVES
--
-- On the source-native R122/R250-compatible present cut whose finite tangent
-- carrier is SymmetricTensorComponent4, evaluate the existing R142/R143 finite
-- localized first variation on each of the ten symmetric tangent slots.
--
-- R144/R119 already transports the SAME scalar through the canonical metric
-- first variation to the selected CMP119 stress insertion.  Hence this module
-- introduces no new stress law and no second component representation.
------------------------------------------------------------------------

finitePhysicalCompositeDerivative :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical)
    {laws :
      R143.PresentCutBC2FirstVariationLinearity
        (Present10.asPresentCutPhysicalSourceInputs presentData)}
    (background :
      Source.Background
        (Carrier.source
          (Present.bc1Carrier
            (Present10.asPresentCutPhysicalSourceInputs presentData)))) →
  K.SymmetricTensorComponent4 →
  ℝ
finitePhysicalCompositeDerivative presentData {laws = laws} background component =
  D1.finiteLocalizedFirstVariation
    (Carrier.finiteAction
      (Present.bc1Carrier
        (Present10.asPresentCutPhysicalSourceInputs presentData)))
    (R143.asFirstVariationLinearity laws)
    background
    (Present10.symmetricSlotAsPresentCutFiniteTangent presentData component)

rationalFinitePhysicalCompositeDerivative :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
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
            (Present10.asPresentCutPhysicalSourceInputs presentData)))) →
  K.SymmetricTensorComponent4 →
  ℚ
rationalFinitePhysicalCompositeDerivative
    presentData {laws = laws} attachment background component =
  R144Attach.finiteD1ToCanonicalMetricRational attachment
    (finitePhysicalCompositeDerivative
      presentData {laws = laws} background component)

record TenFinitePhysicalCompositeDerivativeReadouts : Set where
  constructor tenFinitePhysicalCompositeDerivativeReadouts
  field
    d00 d01 d02 d03 d11 d12 d13 d22 d23 d33 : ℚ

open TenFinitePhysicalCompositeDerivativeReadouts public

evaluateTenFinitePhysicalCompositeDerivatives :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
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
            (Present10.asPresentCutPhysicalSourceInputs presentData)))) →
  TenFinitePhysicalCompositeDerivativeReadouts
evaluateTenFinitePhysicalCompositeDerivatives
    presentData {laws = laws} attachment background =
  tenFinitePhysicalCompositeDerivativeReadouts
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component00)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component01)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component02)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component03)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component11)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component12)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component13)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component22)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component23)
    (rationalFinitePhysicalCompositeDerivative presentData {laws = laws}
      attachment background K.component33)

tenDerivativeExpressionsAreFiniteLocalizedD1 : Set
tenDerivativeExpressionsAreFiniteLocalizedD1 = Set

tenDerivativeReadoutIntroducesSecondStressLaw : Agda.Builtin.Bool.Bool
tenDerivativeReadoutIntroducesSecondStressLaw = Agda.Builtin.Bool.false
