{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116FirstVariationStressPairingRound105Exact where

------------------------------------------------------------------------
-- ROUND105: SOURCE-NATIVE FIRST-VARIATION -> STRESS PAIRING TARGET
--
-- Existing Round102/103 machinery already supplies:
--
--   * one literal CMP109/CMP116 effective-action continuation;
--   * one common analytic domain;
--   * first source derivatives controlled by the SAME CMP116 hessian-mark shell;
--   * weighted spatial row control for those first derivatives.
--
-- Therefore a stress-energy construction should NOT introduce a second decay
-- theorem or a new analytic mark.  The remaining physical leaf is only the
-- source-coordinate identification and stress-pairing identity
--
--        D_g V_eff[h] = <T , h>
--
-- on that same first-gradient carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as FirstVariation
import DASHI.Physics.YangMills.BalabanCMP116FirstGradientSharedMarkedExact as Marked
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared

record FirstVariationStressPairing
    (Scale Volume Root : Set)
    (activity : Chain.SubstitutedActivitySecondVariation) : Set₁ where
  field
    markedFirstGradient :
      Marked.CMP116FirstGradientSharedMarkedControl Scale Volume Root

    scale : Scale
    volume : Volume
    root : Root

    MetricPerturbation : Set
    StressTensor : Set
    PairingScalar : Set

    stressTensor : StressTensor

    metricPerturbationToBackgroundTangent :
      Chain.Background activity →
      MetricPerturbation → Chain.BackgroundTangent activity

    stressMetricPairing :
      StressTensor → MetricPerturbation → PairingScalar

    firstVariationReadout : ℝ → PairingScalar

    -- Same physical first derivative represented in the source background
    -- coordinate.  This is the metric/source-coordinate weld.
    metricFirstVariationIsSubstitutedSourceVariation :
      ∀ background perturbation →
      firstVariationReadout
        (FirstVariation.substitutedFirstVariation activity background
          (metricPerturbationToBackgroundTangent background perturbation))
      ≡ stressMetricPairing stressTensor perturbation

    -- The literal first derivative uses the SAME source-native marked shell as
    -- the existing Heat/Doob first-gradient analysis.  No new localization
    -- constant is introduced for stress.
    sourceDerivativeShellDepth : Nat
    sourceDerivativeMagnitude : ℚ
    sourceDerivativeIsMarkedFirstGradient :
      sourceDerivativeMagnitude
      ≡ Marked.firstGradientShell
          markedFirstGradient scale volume root sourceDerivativeShellDepth

open FirstVariationStressPairing public

sourceDerivativeBelowExistingMarkedShell :
  ∀ {Scale Volume Root activity}
    (dataSet : FirstVariationStressPairing Scale Volume Root activity) →
  sourceDerivativeMagnitude dataSet
  ≤ Shared.markedAnalyticShell
      (Marked.shared (markedFirstGradient dataSet))
      Shared.hessianMark
      (scale dataSet) (volume dataSet) (root dataSet)
      (sourceDerivativeShellDepth dataSet)
sourceDerivativeBelowExistingMarkedShell dataSet =
  let
    existing = Marked.firstGradientBelowHessianMarkedAnalytic
      (markedFirstGradient dataSet)
      (scale dataSet) (volume dataSet) (root dataSet)
      (sourceDerivativeShellDepth dataSet)
  in
  transportLower (sourceDerivativeIsMarkedFirstGradient dataSet) existing
  where
    transportLower : ∀ {a b c : ℚ} → a ≡ b → b ≤ c → a ≤ c
    transportLower refl proof = proof

record FirstVariationStressBoundary : Set where
  constructor firstVariationStressBoundary
  field
    stressNeedsIndependentFourthAnalyticMark : Bool
    stressNeedsIndependentFourthAnalyticMarkIsFalse :
      stressNeedsIndependentFourthAnalyticMark ≡ false

    firstGradientLocalizationAloneIdentifiesStressTensor : Bool
    firstGradientLocalizationAloneIdentifiesStressTensorIsFalse :
      firstGradientLocalizationAloneIdentifiesStressTensor ≡ false

    metricSourceCoordinateWeldStillRequired : Bool
    metricSourceCoordinateWeldStillRequiredIsTrue :
      metricSourceCoordinateWeldStillRequired ≡ true

    stressPairingNormalizationStillRequired : Bool
    stressPairingNormalizationStillRequiredIsTrue :
      stressPairingNormalizationStillRequired ≡ true

canonicalFirstVariationStressBoundary : FirstVariationStressBoundary
canonicalFirstVariationStressBoundary =
  firstVariationStressBoundary false refl false refl true refl true refl

cmp116StressReusesFirstGradientMarkedShellLevel : ProofLevel
cmp116StressReusesFirstGradientMarkedShellLevel = machineChecked

literalCMP116MetricSourceCoordinateWeldLevel : ProofLevel
literalCMP116MetricSourceCoordinateWeldLevel = conditional

literalCMP116FirstVariationStressPairingLevel : ProofLevel
literalCMP116FirstVariationStressPairingLevel = conditional
