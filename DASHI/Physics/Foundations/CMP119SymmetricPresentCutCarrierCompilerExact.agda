{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as Source
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as Local
import DASHI.Physics.YangMills.BalabanFunctionalRegularEContinuationRound245Exact as R245
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as Composite
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanA1WQRPhysicalJetRound123Exact as A1
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier

------------------------------------------------------------------------
-- SOURCE-NATIVE FUNCTIONAL REGULAR-E -> R122 PRESENT CUT, WITH THE TEN-SLOT
-- SYMMETRIC TANGENT CARRIER CHOSEN AT CONSTRUCTION TIME.
--
-- R245 already makes Tangent a representation parameter.  Choose
-- SymmetricTensorComponent4 before BC1 is assembled.  The BC1/Present/Round103
-- compiler chain then preserves the same tangent carrier definitionally.
------------------------------------------------------------------------

record SymmetricFunctionalRegularEBC1Inputs
    {trajectory split inputs}
    (source : Source.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs)
    (localization : Local.CMP119RegularELocalizationCarrier source) : Set₁ where
  field
    calculus :
      Finite.SecondVariationLinearity
        (Source.Background source)
        K.SymmetricTensorComponent4

    equation51 :
      Eq51.CMP109Equation51OnContinuation
        (R245.asCMP109116Continuation
          source localization K.SymmetricTensorComponent4)
        calculus

    scale : Nat
    volume : Local.Volume localization

    analyticDemands :
      Canon.CMP116FiniteNormalizedAnalyticDemands

open SymmetricFunctionalRegularEBC1Inputs public

asBC1CanonicalPhysicalInputs :
  ∀ {trajectory split inputs source localization} →
  SymmetricFunctionalRegularEBC1Inputs
    {trajectory = trajectory} {split = split} {inputs = inputs}
    source localization →
  BC1.BC1CanonicalPhysicalInputs
asBC1CanonicalPhysicalInputs {source = source} {localization = localization} dataSet = record
  { BC1.BC1CanonicalPhysicalInputs.source =
      R245.asCMP109116Continuation
        source localization K.SymmetricTensorComponent4
  ; BC1.BC1CanonicalPhysicalInputs.calculus =
      calculus dataSet
  ; BC1.BC1CanonicalPhysicalInputs.equation51 =
      equation51 dataSet
  ; BC1.BC1CanonicalPhysicalInputs.scale =
      scale dataSet
  ; BC1.BC1CanonicalPhysicalInputs.volume =
      volume dataSet
  ; BC1.BC1CanonicalPhysicalInputs.analyticDemands =
      analyticDemands dataSet
  }

record SymmetricFunctionalRegularEPresentCutInputs
    (History Cell : Set) (cutoff : Nat)
    {trajectory split inputs}
    (source : Source.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs)
    (localization : Local.CMP119RegularELocalizationCarrier source)
    (bc1Canonical :
      SymmetricFunctionalRegularEBC1Inputs source localization) : Set₂ where
  field
    compositeFamily :
      Composite.BC1PhysicalCompositeComponentFamily
        (asBC1CanonicalPhysicalInputs bc1Canonical)

    a1 :
      A1.A1WQRPhysicalJetInputs History Cell

    a2 :
      A2.WardQuarticResponseProducer cutoff

    bc2 :
      BC2.CompactGroupHeatDoobOnCarrier
        (BC1.bc1CanonicalCarrier
          (asBC1CanonicalPhysicalInputs bc1Canonical))

open SymmetricFunctionalRegularEPresentCutInputs public

asBC1PhysicalCompositeInputs :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical} →
  SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
    {trajectory = trajectory} {split = split} {inputs = inputs}
    source localization bc1Canonical →
  Composite.BC1PhysicalCompositeInputs
asBC1PhysicalCompositeInputs {bc1Canonical = bc1Canonical} dataSet = record
  { Composite.BC1PhysicalCompositeInputs.canonical =
      asBC1CanonicalPhysicalInputs bc1Canonical
  ; Composite.BC1PhysicalCompositeInputs.compositeFamily =
      compositeFamily dataSet
  }

asPresentCutPhysicalSourceInputs :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical} →
  SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
    {trajectory = trajectory} {split = split} {inputs = inputs}
    source localization bc1Canonical →
  Present.PresentCutPhysicalSourceInputs History Cell cutoff
asPresentCutPhysicalSourceInputs dataSet = record
  { Present.PresentCutPhysicalSourceInputs.a1 =
      a1 dataSet
  ; Present.PresentCutPhysicalSourceInputs.a2 =
      a2 dataSet
  ; Present.PresentCutPhysicalSourceInputs.bc1 =
      asBC1PhysicalCompositeInputs dataSet
  ; Present.PresentCutPhysicalSourceInputs.bc2 =
      bc2 dataSet
  }

presentCutFiniteTangentIsSymmetricTenSlot :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (dataSet :
      SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical) →
  Finite.Tangent
    (Carrier.finiteAction
      (Present.bc1Carrier
        (asPresentCutPhysicalSourceInputs dataSet)))
  ≡ K.SymmetricTensorComponent4
presentCutFiniteTangentIsSymmetricTenSlot dataSet = refl

symmetricSlotAsPresentCutFiniteTangent :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (dataSet :
      SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical) →
  K.SymmetricTensorComponent4 →
  Finite.Tangent
    (Carrier.finiteAction
      (Present.bc1Carrier
        (asPresentCutPhysicalSourceInputs dataSet)))
symmetricSlotAsPresentCutFiniteTangent dataSet component = component

r144CompatibleTenSlotCarrierBuiltByConstruction : Bool
r144CompatibleTenSlotCarrierBuiltByConstruction = true

r144CompatibleTenSlotCarrierBuiltByConstructionIsTrue :
  r144CompatibleTenSlotCarrierBuiltByConstruction ≡ true
r144CompatibleTenSlotCarrierBuiltByConstructionIsTrue = refl

postHocR250ToR144CarrierEqualityRequired : Bool
postHocR250ToR144CarrierEqualityRequired = false

postHocR250ToR144CarrierEqualityRequiredIsFalse :
  postHocR250ToR144CarrierEqualityRequired ≡ false
postHocR250ToR144CarrierEqualityRequiredIsFalse = refl
