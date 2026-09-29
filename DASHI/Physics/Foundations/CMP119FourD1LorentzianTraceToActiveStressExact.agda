{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119FourD1LorentzianTraceToActiveStressExact where

open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119FourDiagonalFiniteD1ActiveStressExact as Four
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
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
-- CORRECT LORENTZIAN TRACE -> ACTIVE-STRESS BRIDGE ON THE ACTUAL D1 SLOTS
--
-- For covariant orthonormal components with signature (-,+,+,+):
--
--   Theta = -T00 + T11 + T22 + T33
--   A     =  T00 + T11 + T22 + T33
--
-- hence
--
--   A = Theta + 2 T00.
--
-- The trace anomaly can therefore pay Theta, but the repulsion consumer needs
-- one additional timelike-component inequality.  No off-diagonal component is
-- involved.
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

  t00 : ℚ
  t00 = Four.d00 presentData attachment background

  t11 : ℚ
  t11 = Four.d11 presentData attachment background

  t22 : ℚ
  t22 = Four.d22 presentData attachment background

  t33 : ℚ
  t33 = Four.d33 presentData attachment background

  lorentzianTraceD1 : ℚ
  lorentzianTraceD1 =
    - t00 + t11 + t22 + t33

  activeStressD1 : ℚ
  activeStressD1 =
    Four.activeFiniteD1Sum presentData attachment background

  activeStressIsLorentzianTracePlusTwiceT00 :
    activeStressD1
    ≡
    lorentzianTraceD1 + ((1ℚ + 1ℚ) * t00)
  activeStressIsLorentzianTracePlusTwiceT00 =
    ℚRing.solve-∀ t00 t11 t22 t33

  record TraceToActiveStressInput : Set where
    field
      traceNegative :
        lorentzianTraceD1 < 0ℚ

      tracePlusTwiceT00Negative :
        lorentzianTraceD1 + ((1ℚ + 1ℚ) * t00) < 0ℚ

  open TraceToActiveStressInput public

  traceAndTimelikeControlGiveNegativeActiveStress :
    TraceToActiveStressInput →
    activeStressD1 < 0ℚ
  traceAndTimelikeControlGiveNegativeActiveStress input =
    subst
      (λ value → value < 0ℚ)
      (sym activeStressIsLorentzianTracePlusTwiceT00)
      (tracePlusTwiceT00Negative input)
