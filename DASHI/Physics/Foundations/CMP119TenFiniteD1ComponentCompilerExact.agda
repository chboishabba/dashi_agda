{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenFiniteD1ComponentCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (zero)
open import Data.Rational.Base using (ℚ; +_; -[1+_]; 0ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutMetricBasisCompilerExact as PresentBasis
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
import DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

canonicalR119Readout :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group} →
  (selected :
    R119.CanonicalMetricSelectedStressWeld
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation coordinate) →
  Basis.RationalStressPairingReadout representation
canonicalR119Readout selected = record
  { Basis.RationalStressPairingReadout.pairingToRational =
      R119.readoutToRational selected
  }

finiteD1ReadoutAtAxes :
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
  Flat.Axis4 → Flat.Axis4 → ℚ
finiteD1ReadoutAtAxes
    {laws = laws}
    presentData attachment background a b =
  R144Attach.finiteD1ToCanonicalMetricRational attachment
    (D1.finiteLocalizedFirstVariation
      (Carrier.finiteAction
        (Present.bc1Carrier
          (Present10.asPresentCutPhysicalSourceInputs presentData)))
      (R143.asFirstVariationLinearity laws)
      background
      (Present10.symmetricSlotAsPresentCutFiniteTangent
        presentData
        (MetricBasis.symmetricSlotOfAxes a b)))

metricComponentIsFiniteD1Readout :
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
            (Present10.asPresentCutPhysicalSourceInputs presentData))))
    (a b : Flat.Axis4) →
  let
    realization =
      PresentBasis.compilePresentCutTenSlotMetricBasis
        presentData attachment background
    basis =
      MetricBasis.compileSymmetricBasis16 realization
  in
  Basis.cmp119MetricBasisComponent
      basis
      (canonicalR119Readout selected)
      (StressRep.stressTensor representation)
      a b
  ≡ finiteD1ReadoutAtAxes presentData attachment background a b
metricComponentIsFiniteD1Readout
    {laws = laws} {composite = composite}
    {domain = domain} {representation = representation}
    {selected = selected}
    presentData attachment background a b =
  let
    tangent =
      Present10.symmetricSlotAsPresentCutFiniteTangent
        presentData
        (MetricBasis.symmetricSlotOfAxes a b)
    perturbation =
      R144Attach.toMetricPerturbation attachment tangent
    finiteToMetric =
      R144Attach.localizedD1IsCanonicalMetricReadout
        attachment background tangent
    metricToPairing =
      cong
        (R119.readoutToRational selected)
        (StressRep.firstVariationRepresentedByStress representation
          (R144.globalBackgroundToStressBackground composite background)
          perturbation
          (R144Attach.selectedMetricPerturbationAdmissible
            attachment background tangent))
  in
  sym (trans finiteToMetric metricToPairing)

record NormalizedTenFiniteD1Values
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
            (Present10.asPresentCutPhysicalSourceInputs presentData)))) : Set₁ where
  field
    d100 : finiteD1ReadoutAtAxes presentData attachment background Flat.timeAxis Flat.timeAxis ≡ + 1
    d101 : finiteD1ReadoutAtAxes presentData attachment background Flat.timeAxis Flat.xAxis ≡ 0ℚ
    d102 : finiteD1ReadoutAtAxes presentData attachment background Flat.timeAxis Flat.yAxis ≡ 0ℚ
    d103 : finiteD1ReadoutAtAxes presentData attachment background Flat.timeAxis Flat.zAxis ≡ 0ℚ
    d111 : finiteD1ReadoutAtAxes presentData attachment background Flat.xAxis Flat.xAxis ≡ -[1+ zero ]
    d112 : finiteD1ReadoutAtAxes presentData attachment background Flat.xAxis Flat.yAxis ≡ 0ℚ
    d113 : finiteD1ReadoutAtAxes presentData attachment background Flat.xAxis Flat.zAxis ≡ 0ℚ
    d122 : finiteD1ReadoutAtAxes presentData attachment background Flat.yAxis Flat.yAxis ≡ -[1+ zero ]
    d123 : finiteD1ReadoutAtAxes presentData attachment background Flat.yAxis Flat.zAxis ≡ 0ℚ
    d133 : finiteD1ReadoutAtAxes presentData attachment background Flat.zAxis Flat.zAxis ≡ -[1+ zero ]

open NormalizedTenFiniteD1Values public

tenStressValuesIndependentOfFiniteD1Evaluation : Bool
tenStressValuesIndependentOfFiniteD1Evaluation = false

tenStressValuesIndependentOfFiniteD1EvaluationIsFalse :
  tenStressValuesIndependentOfFiniteD1Evaluation ≡ false
tenStressValuesIndependentOfFiniteD1EvaluationIsFalse = refl

tenFiniteLocalizedD1EvaluationsStillRequired : Bool
tenFiniteLocalizedD1EvaluationsStillRequired = true

tenFiniteLocalizedD1EvaluationsStillRequiredIsTrue :
  tenFiniteLocalizedD1EvaluationsStillRequired ≡ true
tenFiniteLocalizedD1EvaluationsStillRequiredIsTrue = refl
