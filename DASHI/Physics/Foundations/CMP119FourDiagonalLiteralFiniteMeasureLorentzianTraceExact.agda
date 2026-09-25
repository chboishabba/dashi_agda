{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119FourDiagonalLiteralFiniteMeasureLorentzianTraceExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119FourDiagonalLiteralFiniteMeasureActiveStressExact as FourFinite
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
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
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureDensityAnchorConstructorExact as Anchor
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- CORRECT LORENTZIAN TRACE ON THE SAME LITERAL FOUR-COMPONENT MEASURE
--
-- Existing four-component source code owns the covariant diagonal numerators
--
--   C00, C11, C22, C33.
--
-- In an orthonormal (-,+,+,+) frame the two relevant contractions are
--
--   trace  = -C00 + C11 + C22 + C33,
--   active =  C00 + C11 + C22 + C33.
--
-- This owner introduces no new source values and proves
--
--   active = trace + 2 C00.
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

  c00 : ℚ
  c00 =
    FourFinite.finiteMeasure00
      presentData attachment background measureWeld calculus anchorInputs

  c11 : ℚ
  c11 =
    FourFinite.finiteMeasure11
      presentData attachment background measureWeld calculus anchorInputs

  c22 : ℚ
  c22 =
    FourFinite.finiteMeasure22
      presentData attachment background measureWeld calculus anchorInputs

  c33 : ℚ
  c33 =
    FourFinite.finiteMeasure33
      presentData attachment background measureWeld calculus anchorInputs

  finiteMeasureLorentzianTrace : ℚ
  finiteMeasureLorentzianTrace =
    - c00 + c11 + c22 + c33

  finiteMeasureActiveStress : ℚ
  finiteMeasureActiveStress =
    FourFinite.finiteMeasureActiveStressSum
      presentData attachment background measureWeld calculus anchorInputs

  activeStressIsTracePlusTwiceC00 :
    finiteMeasureActiveStress
    ≡
    finiteMeasureLorentzianTrace + ((1ℚ + 1ℚ) * c00)
  activeStressIsTracePlusTwiceC00 =
    ℚRing.solve-∀ c00 c11 c22 c33

  record LorentzianTraceAndTimelikeClosure : Set where
    field
      traceNegative :
        finiteMeasureLorentzianTrace < 0ℚ

      tracePlusTwiceC00Negative :
        finiteMeasureLorentzianTrace + ((1ℚ + 1ℚ) * c00) < 0ℚ

  open LorentzianTraceAndTimelikeClosure public

  traceAndTimelikeClosureGivesActiveStressNegative :
    LorentzianTraceAndTimelikeClosure →
    finiteMeasureActiveStress < 0ℚ
  traceAndTimelikeClosureGivesActiveStressNegative input =
    subst
      (λ value → value < 0ℚ)
      (sym activeStressIsTracePlusTwiceC00)
      (tracePlusTwiceC00Negative input)
