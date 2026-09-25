{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119FourDiagonalLiteralFiniteMeasureActiveStressExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119FourDiagonalFiniteD1ActiveStressExact as Four
import DASHI.Physics.Foundations.CMP119TenActualSourceReadoutsExact as Actual
import DASHI.Physics.Foundations.CMP119TenLiteralFiniteMeasureReadoutsExact as FiniteReadouts
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureDensityAnchorConstructorExact as Anchor
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
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- FOUR-DIAGONAL SOURCE COLLAPSE TO THE LITERAL FINITE CLAY MEASURE
--
-- For each diagonal metric direction:
--
--   post-sum finite localized D1
--      = selected CMP119 insertion numerator
--      = connected numerator on R119 normalized source
--      = connected numerator on the literal finite Clay measure.
--
-- Therefore the antigravity-facing active sum is literally the sum of four
-- finite-measure connected numerators.  No off-diagonal source values enter.
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

  d1AtAxes : Flat.Axis4 → Flat.Axis4 → ℚ
  d1AtAxes a b =
    Actual.postSumFiniteD1ReadoutAtAxes
      presentData attachment background a b

  finiteMeasureAtAxes : Flat.Axis4 → Flat.Axis4 → ℚ
  finiteMeasureAtAxes a b =
    FiniteReadouts.finiteMeasureConnectedNumeratorAtAxes
      presentData attachment background measureWeld calculus anchorInputs a b

  d1IsFiniteMeasureAtAxes :
    ∀ a b → d1AtAxes a b ≡ finiteMeasureAtAxes a b
  d1IsFiniteMeasureAtAxes a b =
    trans
      (Actual.postSumFiniteD1IsActualCMP119Readout
        presentData attachment background a b)
      (trans
        (sym
          (R116.connectedInsertionIsSelectedCMP119StressInsertion
            (Actual.selectedInsertionAtAxes
              presentData attachment background a b)))
        (FiniteReadouts.selectedSourceIsFiniteMeasureConnectedNumerator
          presentData attachment background measureWeld calculus anchorInputs
          a b))

  finiteMeasure00 finiteMeasure11 finiteMeasure22 finiteMeasure33 : ℚ
  finiteMeasure00 = finiteMeasureAtAxes Flat.timeAxis Flat.timeAxis
  finiteMeasure11 = finiteMeasureAtAxes Flat.xAxis Flat.xAxis
  finiteMeasure22 = finiteMeasureAtAxes Flat.yAxis Flat.yAxis
  finiteMeasure33 = finiteMeasureAtAxes Flat.zAxis Flat.zAxis

  finiteMeasureActiveStressSum : ℚ
  finiteMeasureActiveStressSum =
    finiteMeasure00 + finiteMeasure11 + finiteMeasure22 + finiteMeasure33

  finiteD1ActiveStressIsFiniteMeasureActiveStress :
    Four.activeFiniteD1Sum presentData attachment background
    ≡ finiteMeasureActiveStressSum
  finiteD1ActiveStressIsFiniteMeasureActiveStress
    rewrite d1IsFiniteMeasureAtAxes Flat.timeAxis Flat.timeAxis
          | d1IsFiniteMeasureAtAxes Flat.xAxis Flat.xAxis
          | d1IsFiniteMeasureAtAxes Flat.yAxis Flat.yAxis
          | d1IsFiniteMeasureAtAxes Flat.zAxis Flat.zAxis =
    refl
