{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PreferredPathDefinedPresentCutExact where

------------------------------------------------------------------------
-- R1 CARRIER-NEUTRAL PREFERRED SOURCE CONSTRUCTOR.
--
-- CMP109/116 leaves `Background` abstract and the present-cut compiler chooses
-- the ten metric/source slots as `Tangent`.  Do not assume that Background is a
-- compact-group carrier.  Instead select the ACTUAL one-parameter source path
-- in the source's own Background carrier and define BC2 firstVariation by that
-- path from the outset.
--
-- Consequences:
--   * BC2 firstVariation = path derivative is definitional;
--   * Round143 congruence/zero/additivity compile from ordinary derivative laws;
--   * signed R144 covariance compiles from potential invariance + B4-equivariant
--     source path.
--
-- The only source-specific Q1 object left is therefore the actual B4-equivariant
-- one-parameter source path itself.  A compact-gauge exponential path is merely
-- one optional producer strategy, not assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2Exact as PathBC2
import DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2LinearityExact as Linear
import DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutPathDerivativeExact as PresentPath
import DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceExact as Potential
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout

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

    sourcePath :
      Background → K.SymmetricTensorComponent4 → ℝ → Background

    sourcePathCovariant :
      ∀ generator background component t →
      let transformed =
            Signed.actSignedComponent
              (Axis.hypercubicSignedAxisAction generator) component
      in
      sourcePath
        (Potential.actBackground potentialGeometry generator background)
        (Signed.component transformed) t
      ≡
      Potential.actBackground potentialGeometry generator
        (sourcePath background component
          (Readout.applyBasisSign (Signed.sign transformed) t))

    pathBC2 :
      PathBC2.PathDefinedCompactGroupHeatDoobOnCarrier
        carrier
        (Linear.signedLaws derivativeLaws)
        sourcePath

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
  let linear =
        Linear.pathFirstVariationLinearity
          (derivativeLaws data) (sourcePath data)
  in record
    { R143.PresentCutBC2FirstVariationLinearity.firstVariationCong =
        D1.firstVariationCong linear
    ; R143.PresentCutBC2FirstVariationLinearity.zeroFirstVariation =
        D1.zeroFirstVariation linear
    ; R143.PresentCutBC2FirstVariationLinearity.addFirstVariation =
        D1.addFirstVariation linear
    }

asPresentCutSignedSourcePathDerivative :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (data :
      PreferredPathDefinedPresentCutSource History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical) →
  PresentPath.PresentCutSignedSourcePathDerivative
    (asSymmetricPresentCutInputs data)
    (asRound143Linearity data)
asPresentCutSignedSourcePathDerivative data = record
  { PresentPath.PresentCutSignedSourcePathDerivative.potentialGeometry =
      potentialGeometry data
  ; PresentPath.PresentCutSignedSourcePathDerivative.derivativeLaws =
      Linear.signedLaws (derivativeLaws data)
  ; PresentPath.PresentCutSignedSourcePathDerivative.sourcePath =
      sourcePath data
  ; PresentPath.PresentCutSignedSourcePathDerivative.sourcePathCovariant =
      sourcePathCovariant data
  ; PresentPath.PresentCutSignedSourcePathDerivative.bc2FirstVariationIsPathDerivative =
      λ background component → refl
  }

preferredSignedFiniteD1Covariant :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (data :
      PreferredPathDefinedPresentCutSource History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical) →
  ∀ generator background component →
  PresentPath.signedFiniteD1
    (asSymmetricPresentCutInputs data)
    (asRound143Linearity data)
    (Potential.actBackground (potentialGeometry data) generator background)
    (Signed.actSignedComponent
      (Axis.hypercubicSignedAxisAction generator) component)
  ≡
  PresentPath.finiteD1AtComponent
    (asSymmetricPresentCutInputs data)
    (asRound143Linearity data)
    background component
preferredSignedFiniteD1Covariant data =
  PresentPath.signedFiniteD1Covariant
    (asSymmetricPresentCutInputs data)
    (asRound143Linearity data)
    (asPresentCutSignedSourcePathDerivative data)

noIndependentBC2DerivativeSemantics : Bool
noIndependentBC2DerivativeSemantics = true

noIndependentRound143Linearity : Bool
noIndependentRound143Linearity = true

remainingQ1LeafIsActualB4EquivariantSourcePath : Bool
remainingQ1LeafIsActualB4EquivariantSourcePath = true

compactGaugeExponentialPathIsOnlyOptionalProducerStrategy : Bool
compactGaugeExponentialPathIsOnlyOptionalProducerStrategy = true
