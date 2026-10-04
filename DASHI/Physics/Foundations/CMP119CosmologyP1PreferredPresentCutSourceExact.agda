{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PreferredPresentCutSourceExact where

------------------------------------------------------------------------
-- R1 PREFERRED SOURCE CONSTRUCTOR.
--
-- Build the exact Round122 present-cut object with BC2 already presented as the
-- derivative along the literal compact-gauge exponential path.  This removes
-- three independent downstream receipts:
--
--   * an arbitrary BC2 firstVariation;
--   * BC2 firstVariation = path derivative;
--   * Round143 first-variation linearity as separate source data.
--
-- The remaining non-compiler content is now exactly the literal compact-gauge
-- path geometry and the standard compact-group heat/log-Hessian theorem carried
-- by `PathDefinedCompactGroupHeatDoobOnCarrier`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119CosmologyP1CompactGaugeExponentialPathExact as GaugePath
import DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2Exact as PathBC2
import DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2LinearityExact as Linear
import DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutCompactGaugePathExact as PresentPath
import DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutPathDerivativeExact as PathBase
import DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceExact as Potential
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as SourceFlow
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as Localization
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as Composite
import DASHI.Physics.YangMills.BalabanA1WQRPhysicalJetRound123Exact as A1
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

record PreferredPathDefinedPresentCutSource
    (History Cell : Set) (cutoff : Nat)
    {trajectory split}
    {inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    (source : SourceFlow.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs)
    (localization : Localization.CMP119RegularELocalizationCarrier source)
    (bc1Canonical : Present10.SymmetricFunctionalRegularEBC1Inputs source localization)
    : Set₂ where

  private
    canonical = Present10.asBC1CanonicalPhysicalInputs bc1Canonical
    carrier = BC1.bc1CanonicalCarrier canonical
    Background = Source.Background (Carrier.source carrier)

  field
    compositeFamily :
      Composite.BC1PhysicalCompositeComponentFamily canonical

    a1 : A1.A1WQRPhysicalJetInputs History Cell
    a2 : A2.WardQuarticResponseProducer cutoff

    potentialGeometry :
      Potential.LiteralSourcePotentialEuclideanGeometry
        carrier Hyper.HypercubicGenerator

    derivativeLaws : Linear.LinearSignedPathDerivativeLaws

    Increment : Set

    compactGaugePath :
      GaugePath.CompactGaugeExponentialSourcePath
        Background Increment Hyper.HypercubicGenerator
        (Potential.actBackground potentialGeometry)
        Axis.hypercubicSignedAxisAction

    pathBC2 :
      PathBC2.PathDefinedCompactGroupHeatDoobOnCarrier
        carrier
        (Linear.signedLaws derivativeLaws)
        (GaugePath.sourcePath compactGaugePath)

open PreferredPathDefinedPresentCutSource public

asSymmetricPresentCutInputs :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical} →
  PreferredPathDefinedPresentCutSource History Cell cutoff
    {trajectory = trajectory} {split = split} {inputs = inputs}
    source localization bc1Canonical →
  Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
    {trajectory = trajectory} {split = split} {inputs = inputs}
    source localization bc1Canonical
asSymmetricPresentCutInputs data = record
  { Present10.SymmetricFunctionalRegularEPresentCutInputs.compositeFamily =
      compositeFamily data
  ; Present10.SymmetricFunctionalRegularEPresentCutInputs.a1 = a1 data
  ; Present10.SymmetricFunctionalRegularEPresentCutInputs.a2 = a2 data
  ; Present10.SymmetricFunctionalRegularEPresentCutInputs.bc2 =
      PathBC2.asCompactGroupHeatDoobOnCarrier (pathBC2 data)
  }

asPresentCutPhysicalSourceInputs :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical} →
  PreferredPathDefinedPresentCutSource History Cell cutoff
    {trajectory = trajectory} {split = split} {inputs = inputs}
    source localization bc1Canonical →
  Present.PresentCutPhysicalSourceInputs History Cell cutoff
asPresentCutPhysicalSourceInputs data =
  Present10.asPresentCutPhysicalSourceInputs (asSymmetricPresentCutInputs data)

asRound143Linearity :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (data :
      PreferredPathDefinedPresentCutSource History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical) →
  R143.PresentCutBC2FirstVariationLinearity
    (asPresentCutPhysicalSourceInputs data)
asRound143Linearity data =
  let
    sourcePath = GaugePath.sourcePath (compactGaugePath data)
    linear = Linear.pathFirstVariationLinearity (derivativeLaws data) sourcePath
  in record
    { R143.PresentCutBC2FirstVariationLinearity.firstVariationCong =
        D1.firstVariationCong linear
    ; R143.PresentCutBC2FirstVariationLinearity.zeroFirstVariation =
        D1.zeroFirstVariation linear
    ; R143.PresentCutBC2FirstVariationLinearity.addFirstVariation =
        D1.addFirstVariation linear
    }

asPresentCutCompactGaugePathDerivative :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (data :
      PreferredPathDefinedPresentCutSource History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical) →
  PresentPath.PresentCutCompactGaugePathDerivative
    (asSymmetricPresentCutInputs data)
    (asRound143Linearity data)
asPresentCutCompactGaugePathDerivative data = record
  { PresentPath.PresentCutCompactGaugePathDerivative.potentialGeometry =
      potentialGeometry data
  ; PresentPath.PresentCutCompactGaugePathDerivative.derivativeLaws =
      Linear.signedLaws (derivativeLaws data)
  ; PresentPath.PresentCutCompactGaugePathDerivative.Increment = Increment data
  ; PresentPath.PresentCutCompactGaugePathDerivative.compactGaugePath =
      compactGaugePath data
  ; PresentPath.PresentCutCompactGaugePathDerivative.bc2FirstVariationIsExponentialPathDerivative =
      λ background component → refl
  }

preferredPresentCutSignedFiniteD1Covariant :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (data :
      PreferredPathDefinedPresentCutSource History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical) →
  ∀ generator background component →
  PathBase.signedFiniteD1
    (asSymmetricPresentCutInputs data)
    (asRound143Linearity data)
    (Potential.actBackground (potentialGeometry data) generator background)
    (Signed.actSignedComponent
      (Axis.hypercubicSignedAxisAction generator) component)
  ≡
  PathBase.finiteD1AtComponent
    (asSymmetricPresentCutInputs data)
    (asRound143Linearity data)
    background component
preferredPresentCutSignedFiniteD1Covariant data =
  PresentPath.signedFiniteD1CovariantFromCompactGaugePath
    (asSymmetricPresentCutInputs data)
    (asRound143Linearity data)
    (asPresentCutCompactGaugePathDerivative data)

noIndependentBC2FirstVariationInPreferredPresentCut : Bool
noIndependentBC2FirstVariationInPreferredPresentCut = true

round143LinearityCompiledFromPathDerivative : Bool
round143LinearityCompiledFromPathDerivative = true

signedR144CovarianceNowDownstreamCompilerOutput : Bool
signedR144CovarianceNowDownstreamCompilerOutput = true

remainingR1SourceIsLiteralGroupGeometryAndStandardHeatTheorem : Bool
remainingR1SourceIsLiteralGroupGeometryAndStandardHeatTheorem = true
