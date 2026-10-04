{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutCompactGaugePathExact where

------------------------------------------------------------------------
-- R1 PRESENT-CUT SOURCE GEOMETRY COMPILER.
--
-- Replace the free `sourcePath` + `sourcePathCovariant` fields of the earlier
-- P1 present-cut package by one compact-gauge exponential-path realization.
-- The covariance field is derived from finite group-action algebra in
-- `P1CompactGaugeExponentialPathExact`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutPathDerivativeExact as PresentPath
import DASHI.Physics.Foundations.CMP119CosmologyP1CompactGaugeExponentialPathExact as GaugePath
import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as Path
import DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceExact as Potential
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

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
    (laws :
      R143.PresentCutBC2FirstVariationLinearity
        (Present10.asPresentCutPhysicalSourceInputs presentData))
  where

  present = Present10.asPresentCutPhysicalSourceInputs presentData
  carrier = Present.bc1Carrier present

  Background : Set
  Background = Source.Background (Carrier.source carrier)

  record PresentCutCompactGaugePathDerivative : Set₁ where
    field
      potentialGeometry :
        Potential.LiteralSourcePotentialEuclideanGeometry
          carrier Hyper.HypercubicGenerator

      derivativeLaws : Path.SignedPathDerivativeLaws

      Increment : Set

      compactGaugePath :
        GaugePath.CompactGaugeExponentialSourcePath
          Background Increment Hyper.HypercubicGenerator
          (Potential.actBackground potentialGeometry)
          Axis.hypercubicSignedAxisAction

      -- The one genuinely differentiated source statement left at this layer:
      -- BC2's selected first variation is the ordinary derivative along the
      -- literal compact-gauge exponential path.
      bc2FirstVariationIsExponentialPathDerivative :
        ∀ background component →
        BC2.firstVariation (Present.bc2 present)
          (Carrier.effectivePotential carrier)
          background
          (Present10.symmetricSlotAsPresentCutFiniteTangent
            presentData component)
        ≡
        Path.derivativeAtZero derivativeLaws
          (λ t →
            Carrier.effectivePotential carrier
              (GaugePath.sourcePath compactGaugePath
                background component t))

  open PresentCutCompactGaugePathDerivative public

  asPresentCutSignedSourcePathDerivative :
    PresentCutCompactGaugePathDerivative →
    PresentPath.PresentCutSignedSourcePathDerivative presentData laws
  asPresentCutSignedSourcePathDerivative data = record
    { PresentPath.PresentCutSignedSourcePathDerivative.potentialGeometry =
        potentialGeometry data
    ; PresentPath.PresentCutSignedSourcePathDerivative.derivativeLaws =
        derivativeLaws data
    ; PresentPath.PresentCutSignedSourcePathDerivative.sourcePath =
        GaugePath.sourcePath (compactGaugePath data)
    ; PresentPath.PresentCutSignedSourcePathDerivative.sourcePathCovariant =
        GaugePath.sourcePathCovariant (compactGaugePath data)
    ; PresentPath.PresentCutSignedSourcePathDerivative.bc2FirstVariationIsPathDerivative =
        bc2FirstVariationIsExponentialPathDerivative data
    }

  signedFiniteD1CovariantFromCompactGaugePath :
    (data : PresentCutCompactGaugePathDerivative) →
    ∀ generator background component →
    PresentPath.signedFiniteD1 presentData laws
      (Potential.actBackground
        (potentialGeometry data) generator background)
      (DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact.actSignedComponent
        (Axis.hypercubicSignedAxisAction generator) component)
    ≡ PresentPath.finiteD1AtComponent presentData laws background component
  signedFiniteD1CovariantFromCompactGaugePath data =
    PresentPath.signedFiniteD1Covariant presentData laws
      (asPresentCutSignedSourcePathDerivative data)

presentCutSourcePathCovarianceIsCompiled : Bool
presentCutSourcePathCovarianceIsCompiled = true

remainingQ1LeafIsBC2DerivativeSemanticsPlusLiteralGroupGeometry : Bool
remainingQ1LeafIsBC2DerivativeSemanticsPlusLiteralGroupGeometry = true
