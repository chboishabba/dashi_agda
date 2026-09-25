{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119FourD1LocalizedPositiveGRepulsionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (0ℚ; _<_)

import DASHI.Physics.Foundations.CMP119FourDiagonalFiniteD1ActiveStressExact as Four
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.GRQFTLocalizedRepulsiveSourceCriterionExact as Local
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
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
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- SHORTEST CURRENT POSITIVE-G ANTIGRAVITY SOURCE ROUTE
--
-- The source-side premise is no longer ten normalized component values.
-- It is only strict negativity of the sum of the four ACTUAL diagonal,
-- post-sum finite localized CMP119 D1 readouts.
--
-- Under the already-explicit stationary/weak-field/spherical active-mass
-- adapter, this is enough to select the negative-active-mass branch, and
-- positive G then gives outward exterior response.
------------------------------------------------------------------------

module _
    {History Cell cutoff trajectory split inputs source localization bc1Canonical}
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
            (Present10.asPresentCutPhysicalSourceInputs presentData))))
  where

  finiteActive =
    Four.activeFiniteD1Sum presentData attachment background

  metricActive =
    Four.metricActiveStressSum presentData attachment background

  record FourD1NegativeActiveStressInput : Set where
    field
      finiteActiveNegative : finiteActive < 0ℚ

  open FourD1NegativeActiveStressInput public

  selectedCMP119ActiveStressNegative :
    FourD1NegativeActiveStressInput →
    metricActive < 0ℚ
  selectedCMP119ActiveStressNegative input =
    Four.negativeFiniteD1ActiveStressCompilesToMetricNegative
      presentData attachment background
      (finiteActiveNegative input)

  record CMP119LocalizedPositiveGRepulsionCriterion : Set where
    field
      assumptions :
        Local.LocalizedWeakFieldActiveMassAssumptions

      sourceInput :
        FourD1NegativeActiveStressInput

      selectedMetricActiveStressNegative :
        metricActive < 0ℚ

      couplingSign :
        Signed.CouplingSign

      couplingIsPositive :
        couplingSign ≡ Signed.positiveCoupling

      activeMassSign :
        Local.ActiveMassSign

      activeMassIsNegative :
        activeMassSign ≡ Local.negativeActiveMass

      exteriorResponse :
        Local.ExteriorRadialResponse

      exteriorResponseIsOutward :
        exteriorResponse ≡ Local.outwardExteriorAcceleration

  open CMP119LocalizedPositiveGRepulsionCriterion public

  compileLocalizedPositiveGRepulsion :
    FourD1NegativeActiveStressInput →
    CMP119LocalizedPositiveGRepulsionCriterion
  compileLocalizedPositiveGRepulsion input = record
    { assumptions =
        Local.canonicalLocalizedWeakFieldAssumptions
    ; sourceInput =
        input
    ; selectedMetricActiveStressNegative =
        selectedCMP119ActiveStressNegative input
    ; couplingSign =
        Signed.positiveCoupling
    ; couplingIsPositive =
        refl
    ; activeMassSign =
        Local.negativeActiveMass
    ; activeMassIsNegative =
        refl
    ; exteriorResponse =
        Local.exteriorResponse Signed.positiveCoupling Local.negativeActiveMass
    ; exteriorResponseIsOutward =
        Local.positiveGCouplingNegativeActiveMassRepels
    }
