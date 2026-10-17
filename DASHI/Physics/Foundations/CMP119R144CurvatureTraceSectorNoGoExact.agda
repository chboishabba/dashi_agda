{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119R144CurvatureTraceSectorNoGoExact where

------------------------------------------------------------------------
-- R144 / CURVATURESIX SAME-OBJECT TRACE BOUNDARY
--
-- The present-cut tangent carrier is already the ten symmetric metric slots.
-- If the complete finite generated-action D1 on those slots is identified
-- pointwise with the existing classical CurvatureSix action variation, then its
-- four-diagonal trace is forced to vanish configuration-by-configuration.
--
-- This is the exact boundary needed before attempting the remaining nonlinear
-- same-object weld.  A nonzero (in particular negative) generated-action trace
-- therefore cannot be obtained by silently declaring the whole selected source
-- to be the classical CurvatureSix sector.  Any such completion must split out
-- a genuinely nonclassical/quantum insertion, anomaly, counterterm, or other
-- independently justified trace contribution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Curvature

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

Not : Set → Set
Not P = P → ⊥

module _
    {History Cell : Set} {cutoff : Nat}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {source localization bc1Canonical}
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
  where

  finiteAction : Finite.FiniteLocalizedEffectiveAction
  finiteAction =
    Carrier.finiteAction
      (Present.bc1Carrier
        (Present10.asPresentCutPhysicalSourceInputs presentData))

  Configuration : Set
  Configuration = Finite.Configuration finiteAction

  selectedFiniteD1At :
    K.SymmetricTensorComponent4 → Configuration → ℚ
  selectedFiniteD1At component configuration =
    R144Attach.finiteD1ToCanonicalMetricRational attachment
      (D1.finiteLocalizedFirstVariation
        finiteAction
        (R143.asFirstVariationLinearity laws)
        configuration
        (Present10.symmetricSlotAsPresentCutFiniteTangent
          presentData component))

  selectedFiniteD1DiagonalTrace : Configuration → ℚ
  selectedFiniteD1DiagonalTrace configuration =
    selectedFiniteD1At K.component00 configuration
    + selectedFiniteD1At K.component11 configuration
    + selectedFiniteD1At K.component22 configuration
    + selectedFiniteD1At K.component33 configuration

  record R144ClassicalCurvatureSameObject : Set₁ where
    field
      curvatureAt : Configuration → Curvature.CurvatureSix

      finiteD1IsClassicalCurvatureActionVariation :
        ∀ configuration component →
        selectedFiniteD1At component configuration
        ≡ Curvature.actionVariation (curvatureAt configuration) component

  open R144ClassicalCurvatureSameObject public

  selectedFiniteD1DiagonalTraceIsZero :
    (weld : R144ClassicalCurvatureSameObject) →
    ∀ configuration →
    selectedFiniteD1DiagonalTrace configuration ≡ 0ℚ
  selectedFiniteD1DiagonalTraceIsZero weld configuration
    rewrite finiteD1IsClassicalCurvatureActionVariation
              weld configuration K.component00
          | finiteD1IsClassicalCurvatureActionVariation
              weld configuration K.component11
          | finiteD1IsClassicalCurvatureActionVariation
              weld configuration K.component22
          | finiteD1IsClassicalCurvatureActionVariation
              weld configuration K.component33 =
    Curvature.diagonalTraceZero (curvatureAt weld configuration)

  nonzeroTraceRefutesWholeClassicalCurvatureIdentification :
    (weld : R144ClassicalCurvatureSameObject) →
    ∀ configuration →
    Not (selectedFiniteD1DiagonalTrace configuration ≡ 0ℚ) → ⊥
  nonzeroTraceRefutesWholeClassicalCurvatureIdentification
      weld configuration nonzero =
    nonzero (selectedFiniteD1DiagonalTraceIsZero weld configuration)

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

classicalCurvatureDiagonalTraceForcedZero : Bool
classicalCurvatureDiagonalTraceForcedZero = true

nonzeroGeneratedActionTraceRequiresNonclassicalSector : Bool
nonzeroGeneratedActionTraceRequiresNonclassicalSector = true

-- CurvatureSix can pay the whole ten-slot CLASSICAL action variation, but it
-- cannot by itself pay a nonzero generated-action trace.
fullGeneratedActionMayBeClassicalCurvatureWithoutTracePayment : Bool
fullGeneratedActionMayBeClassicalCurvatureWithoutTracePayment = false

nonlinearSameObjectWeldMustSplitClassicalAndQuantumTrace : Bool
nonlinearSameObjectWeldMustSplitClassicalAndQuantumTrace = true

classicalCurvatureStillPaysAllTenClassicalDS : Bool
classicalCurvatureStillPaysAllTenClassicalDS = true

independentQuantumTraceContributionStillPhysicalPayment : Bool
independentQuantumTraceContributionStillPhysicalPayment = true
