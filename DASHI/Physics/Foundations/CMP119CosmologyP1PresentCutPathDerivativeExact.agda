{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutPathDerivativeExact where

------------------------------------------------------------------------
-- P1 PRESENT-CUT COMPILER.
--
-- This instantiates the invariant-path derivative theorem on the exact
-- symmetric ten-slot present-cut carrier.  The terminal signed D1 covariance is
-- no longer primitive.  It follows from:
--
--   * finite localized source geometry -> invariant scalar potential;
--   * one-parameter source-path equivariance under the literal B4 action;
--   * BC2.firstVariation is the ordinary derivative of that path.
--
-- R143 then transports the result to the exact finite localized D1 sum used by
-- R144.  No local-D1 covariance premise is used in this derivation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as Path
import DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceExact as Potential
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
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

  record PresentCutSignedSourcePathDerivative : Set₁ where
    field
      potentialGeometry :
        Potential.LiteralSourcePotentialEuclideanGeometry
          carrier Hyper.HypercubicGenerator

      derivativeLaws : Path.SignedPathDerivativeLaws

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
          (Signed.component transformed)
          t
        ≡
        Potential.actBackground potentialGeometry generator
          (sourcePath background component
            (Readout.applyBasisSign (Signed.sign transformed) t))

      bc2FirstVariationIsPathDerivative :
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
              (sourcePath background component t))

  open PresentCutSignedSourcePathDerivative public

  asInvariantSignedBasisPath :
    PresentCutSignedSourcePathDerivative →
    Path.InvariantSignedBasisPath
      Background Hyper.HypercubicGenerator
      Axis.hypercubicSignedAxisAction
  asInvariantSignedBasisPath data = record
    { Path.InvariantSignedBasisPath.actConfiguration =
        Potential.actBackground (potentialGeometry data)
    ; Path.InvariantSignedBasisPath.potential =
        Carrier.effectivePotential carrier
    ; Path.InvariantSignedBasisPath.potentialInvariant =
        Potential.effectivePotentialCovariant (potentialGeometry data)
    ; Path.InvariantSignedBasisPath.sourcePath =
        sourcePath data
    ; Path.InvariantSignedBasisPath.sourcePathCovariant =
        sourcePathCovariant data
    }

  finiteD1AtComponent :
    Background → K.SymmetricTensorComponent4 → ℝ
  finiteD1AtComponent background component =
    D1.finiteLocalizedFirstVariation
      (Carrier.finiteAction carrier)
      (R143.asFirstVariationLinearity laws)
      background
      (Present10.symmetricSlotAsPresentCutFiniteTangent
        presentData component)

  finiteD1IsPathDerivative :
    (data : PresentCutSignedSourcePathDerivative) →
    ∀ background component →
    finiteD1AtComponent background component
    ≡
    Path.componentDerivative
      (derivativeLaws data)
      (asInvariantSignedBasisPath data)
      background component
  finiteD1IsPathDerivative data background component =
    trans
      (sym
        (R143.bc2GlobalFirstVariationIsFiniteLocalizedSum
          laws background
          (Present10.symmetricSlotAsPresentCutFiniteTangent
            presentData component)))
      (bc2FirstVariationIsPathDerivative data background component)

  signedFiniteD1 :
    Background → Signed.SignedSymmetricComponent → ℝ
  signedFiniteD1 background signed =
    Readout.applyBasisSign (Signed.sign signed)
      (finiteD1AtComponent background (Signed.component signed))

  signedFiniteD1Covariant :
    (data : PresentCutSignedSourcePathDerivative) →
    ∀ generator background component →
    signedFiniteD1
      (Potential.actBackground
        (potentialGeometry data) generator background)
      (Signed.actSignedComponent
        (Axis.hypercubicSignedAxisAction generator) component)
    ≡ finiteD1AtComponent background component
  signedFiniteD1Covariant data generator background component =
    let
      transformed =
        Signed.actSignedComponent
          (Axis.hypercubicSignedAxisAction generator) component
      sign = Signed.sign transformed
      moved =
        Potential.actBackground
          (potentialGeometry data) generator background
    in
    trans
      (cong (Readout.applyBasisSign sign)
        (finiteD1IsPathDerivative data moved
          (Signed.component transformed)))
      (trans
        (Path.signedReadoutCovariantFromInvariantPotential
          (derivativeLaws data)
          (asInvariantSignedBasisPath data)
          generator background component)
        (sym (finiteD1IsPathDerivative data background component)))

  primitiveSignedD1CovarianceNoLongerRequired : Bool
  primitiveSignedD1CovarianceNoLongerRequired = true

  p1RemainingSourceDataIsPathSemanticsAndEquivariance : Bool
  p1RemainingSourceDataIsPathSemanticsAndEquivariance = true

  p1LocalD1CovarianceNoLongerPremise : Bool
  p1LocalD1CovarianceNoLongerPremise = true
