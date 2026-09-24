{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricFiniteTangentBasisCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
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
-- TEN SYMMETRIC SLOTS -> FINITE SOURCE TANGENTS -> CMP119 METRIC BASIS
--
-- R144 already owns the finite-tangent -> canonical metric-perturbation map
-- and proves that it realizes the SAME stress tangent.  Therefore GRQFT should
-- not request a second direct component->CMP119 metric map.
------------------------------------------------------------------------

record SymmetricFiniteSourceTangentBasis
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
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
        {present = present} {actionWeld = actionWeld} {laws = laws}
        composite
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        domain representation {coordinate = coordinate} selected) : Set₁ where
  field
    referenceBackground :
      Source.Background (Carrier.source (Present.bc1Carrier present))

    componentFiniteTangent :
      K.SymmetricTensorComponent4 →
      Finite.Tangent (Carrier.finiteAction (Present.bc1Carrier present))

open SymmetricFiniteSourceTangentBasis public

compileFiniteTangentBasisToCMP119MetricBasis :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws
      composite C S Y group Scale Volume domain representation coordinate selected}
    {attachment :
      R144Attach.R144CanonicalMetricTangentAttachment
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld} {laws = laws}
        composite
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        domain representation {coordinate = coordinate} selected} →
  SymmetricFiniteSourceTangentBasis attachment →
  MetricBasis.SymmetricMetricBasisRealization domain
compileFiniteTangentBasisToCMP119MetricBasis
    {attachment = attachment} finiteBasis = record
  { MetricBasis.SymmetricMetricBasisRealization.componentPerturbation =
      λ component →
        R144Attach.toMetricPerturbation attachment
          (componentFiniteTangent finiteBasis component)
  ; MetricBasis.SymmetricMetricBasisRealization.componentPerturbationAdmissible =
      λ component →
        R144Attach.selectedMetricPerturbationAdmissible attachment
          (referenceBackground finiteBasis)
          (componentFiniteTangent finiteBasis component)
  }

directSymmetricSlotToCMP119MetricPerturbationIsPrimitive : Bool
directSymmetricSlotToCMP119MetricPerturbationIsPrimitive = false

directSymmetricSlotToCMP119MetricPerturbationIsPrimitiveIsFalse :
  directSymmetricSlotToCMP119MetricPerturbationIsPrimitive ≡ false
directSymmetricSlotToCMP119MetricPerturbationIsPrimitiveIsFalse = refl

symmetricSlotToFiniteSourceTangentStillRequired : Bool
symmetricSlotToFiniteSourceTangentStillRequired = true

symmetricSlotToFiniteSourceTangentStillRequiredIsTrue :
  symmetricSlotToFiniteSourceTangentStillRequired ≡ true
symmetricSlotToFiniteSourceTangentStillRequiredIsTrue = refl

r144TangentTransportReused : Bool
r144TangentTransportReused = true

r144TangentTransportReusedIsTrue :
  r144TangentTransportReused ≡ true
r144TangentTransportReusedIsTrue = refl
