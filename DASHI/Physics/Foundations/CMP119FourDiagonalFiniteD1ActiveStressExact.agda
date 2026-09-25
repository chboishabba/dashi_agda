{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119FourDiagonalFiniteD1ActiveStressExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; +_; -[1+_]; _+_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119TenFiniteD1ComponentCompilerExact as Components
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutMetricBasisCompilerExact as PresentBasis
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
import DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerExact as Basis
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
-- ANTIGRAVITY-SPECIFIC FOUR-DIAGONAL MAX-CUT
--
-- The negative-active-stress consumer only uses
--
--   T00 + T11 + T22 + T33.
--
-- It therefore does not need the six off-diagonal CMP119 values.  The existing
-- component compiler already identifies each diagonal component with the exact
-- post-sum finite localized D1 readout on the corresponding symmetric tangent.
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

  d00 d11 d22 d33 : ℚ
  d00 =
    Components.finiteD1ReadoutAtAxes presentData attachment background
      Flat.timeAxis Flat.timeAxis
  d11 =
    Components.finiteD1ReadoutAtAxes presentData attachment background
      Flat.xAxis Flat.xAxis
  d22 =
    Components.finiteD1ReadoutAtAxes presentData attachment background
      Flat.yAxis Flat.yAxis
  d33 =
    Components.finiteD1ReadoutAtAxes presentData attachment background
      Flat.zAxis Flat.zAxis

  activeFiniteD1Sum : ℚ
  activeFiniteD1Sum = d00 + d11 + d22 + d33

  record NormalizedFourDiagonalFiniteD1Values : Set where
    field
      v00 : d00 ≡ + 1
      v11 : d11 ≡ -[1+ zero ]
      v22 : d22 ≡ -[1+ zero ]
      v33 : d33 ≡ -[1+ zero ]

  open NormalizedFourDiagonalFiniteD1Values public

  fourDiagonalValuesGiveNegativeTwo :
    NormalizedFourDiagonalFiniteD1Values →
    activeFiniteD1Sum ≡ -[1+ suc zero ]
  fourDiagonalValuesGiveNegativeTwo values
    rewrite v00 values | v11 values | v22 values | v33 values =
    refl

  -- The existing ten-slot compiler is used only as a component theorem here:
  -- no six off-diagonal numerical hypotheses are introduced.
  metric00IsD00 :
    let realization =
          PresentBasis.compilePresentCutTenSlotMetricBasis
            presentData attachment background
        basis =
          MetricBasis.compileSymmetricBasis16 realization
    in
    Basis.cmp119MetricBasisComponent
      basis
      (Components.canonicalR119Readout selected)
      (StressRep.stressTensor representation)
      Flat.timeAxis Flat.timeAxis
    ≡ d00
  metric00IsD00 =
    Components.metricComponentIsFiniteD1Readout
      presentData attachment background Flat.timeAxis Flat.timeAxis

  metric11IsD11 :
    let realization =
          PresentBasis.compilePresentCutTenSlotMetricBasis
            presentData attachment background
        basis =
          MetricBasis.compileSymmetricBasis16 realization
    in
    Basis.cmp119MetricBasisComponent
      basis
      (Components.canonicalR119Readout selected)
      (StressRep.stressTensor representation)
      Flat.xAxis Flat.xAxis
    ≡ d11
  metric11IsD11 =
    Components.metricComponentIsFiniteD1Readout
      presentData attachment background Flat.xAxis Flat.xAxis

  metric22IsD22 :
    let realization =
          PresentBasis.compilePresentCutTenSlotMetricBasis
            presentData attachment background
        basis =
          MetricBasis.compileSymmetricBasis16 realization
    in
    Basis.cmp119MetricBasisComponent
      basis
      (Components.canonicalR119Readout selected)
      (StressRep.stressTensor representation)
      Flat.yAxis Flat.yAxis
    ≡ d22
  metric22IsD22 =
    Components.metricComponentIsFiniteD1Readout
      presentData attachment background Flat.yAxis Flat.yAxis

  metric33IsD33 :
    let realization =
          PresentBasis.compilePresentCutTenSlotMetricBasis
            presentData attachment background
        basis =
          MetricBasis.compileSymmetricBasis16 realization
    in
    Basis.cmp119MetricBasisComponent
      basis
      (Components.canonicalR119Readout selected)
      (StressRep.stressTensor representation)
      Flat.zAxis Flat.zAxis
    ≡ d33
  metric33IsD33 =
    Components.metricComponentIsFiniteD1Readout
      presentData attachment background Flat.zAxis Flat.zAxis
