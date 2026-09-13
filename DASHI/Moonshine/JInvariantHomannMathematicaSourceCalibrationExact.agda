module DASHI.Moonshine.JInvariantHomannMathematicaSourceCalibrationExact where

------------------------------------------------------------------------
-- HOMANN / MATHEMATICA KLEIN-j SOURCE CALIBRATION
--
-- Purpose: pin the source-side normalization and rendering obligations before
-- a pixel-for-pixel comparison is allowed.
--
-- Source layer (non-kernel):
--   * Jan Homann, Commons File:KleinInvariantJ.jpg, uploaded 2007-08-03:
--       "function KleinInvariantJ[z] (= g_2^3 / Delta) in the complex plane"
--       and made with Mathematica.
--   * Jan Homann, Commons User:Jan Homann/Mathematics:
--       plots generated with Mathematica 5.0; colour mapping designed so phase
--       remains visible as |z| approaches zero or infinity.
--   * Jan Homann, Commons File:Complex coloring.jpg:
--       map of colours for complex functions; scale made using Sinh.
--   * Wolfram Functions, KleinInvariantJ, formula 09.50.06.0001.01:
--       Mathematica/Wolfram J has Fourier series
--         J(tau) = (q^-1 + 744 + ...)/1728.
--
-- Therefore the repo's existing runtime evaluator for the standard modular
-- j-function (j(i) ~= 1728) and Mathematica's KleinInvariantJ are related by a
-- positive real factor 1728 at the source-normalization level.  This owner
-- records that as a source calibration target, not as a newly kernel-proved
-- analytic theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Moonshine.JInvariantImageFractalSourceAtlasExact as Images

homannKleinImageSource : Debt.SourceIdentity
homannKleinImageSource = Images.kleinComplexImageSource

homannMathematicsSource : Debt.SourceIdentity
homannMathematicsSource =
  Debt.source-identity
    "Jan Homann / Wikimedia Commons contributors"
    "User:Jan Homann/Mathematics"
    "Commons user-page rendering notes"
    "https://commons.wikimedia.org/wiki/User:Jan_Homann/Mathematics"
    "page inspected 2026-09-09"

homannColourMapSource : Debt.SourceIdentity
homannColourMapSource =
  Debt.source-identity
    "Jan Homann / Wikimedia Commons contributors"
    "Complex coloring.jpg"
    "Commons File:Complex coloring.jpg"
    "https://commons.wikimedia.org/wiki/File:Complex_coloring.jpg"
    "upload 2007-08-03; page inspected 2026-09-09"

wolframKleinInvariantJSource : Debt.SourceIdentity
wolframKleinInvariantJSource =
  Debt.source-identity
    "Wolfram Research"
    "KleinInvariantJ"
    "Wolfram Functions formula 09.50.06.0001.01"
    "https://functions.wolfram.com/PDF/KleinInvariantJ.pdf"
    "Wolfram Functions PDF inspected 2026-09-09"

record CalibrationClaim : Set where
  constructor calibration-claim
  field
    source : Debt.SourceIdentity
    exactSourceClaim : String
    localUseScope : String
    sourceEntitlesKernelProof : Bool

open CalibrationClaim public

homannUsesMathematicaKleinJClaim : CalibrationClaim
homannUsesMathematicaKleinJClaim =
  calibration-claim
    homannKleinImageSource
    "The source image is described as KleinInvariantJ[z] (= g_2^3 / Delta) in the complex plane and as made with Mathematica."
    "pins the source function family and renderer software; does not prove viewport or colour-function details"
    false

homannPhaseVisibilityClaim : CalibrationClaim
homannPhaseVisibilityClaim =
  calibration-claim
    homannMathematicsSource
    "The plots were generated with Mathematica 5.0 and the colour mapping was designed so the phase remains visible even as absolute value approaches zero or infinity."
    "renderer-source constraint: hue/phase must not be discarded by magnitude extremes"
    false

homannSinhScaleClaim : CalibrationClaim
homannSinhScaleClaim =
  calibration-claim
    homannColourMapSource
    "The complex-colour map description states that its scale is made by using Sinh."
    "tone/magnitude calibration target; exact screenshot code still requires transcription"
    false

wolframNormalizedFourierClaim : CalibrationClaim
wolframNormalizedFourierClaim =
  calibration-claim
    wolframKleinInvariantJSource
    "Wolfram KleinInvariantJ has Fourier normalization J(tau) = (q^-1 + 744 + sum a_k q^k) / 1728."
    "normalization cross-check against the repo runtime standard-j evaluator"
    false

------------------------------------------------------------------------
-- Source-normalization relation.  The relation is recorded as a calibration
-- obligation rather than silently used as a definitional equality.
------------------------------------------------------------------------

data JNormalization : Set where
  standardModularJ : JNormalization
  mathematicaKleinInvariantJ : JNormalization

data NormalizationResidual : Set where
  missingKernelProofStandardJEquals1728TimesMathematicaJ : NormalizationResidual
  missingPositiveScalingPhaseInvarianceProof : NormalizationResidual
  missingExactHomannColourFunctionTranscription : NormalizationResidual
  missingSourceViewportCalibration : NormalizationResidual
  missingFiniteQSeriesPixelErrorBudget : NormalizationResidual
  missingJPEGPostprocessingModel : NormalizationResidual

firstNormalizationResidual : NormalizationResidual
firstNormalizationResidual =
  missingKernelProofStandardJEquals1728TimesMathematicaJ

record HomannMathematicaCalibrationBoundary : Set where
  constructor homann-mathematica-calibration-boundary
  field
    sourceUsesMathematica : Bool
    sourceCallsFunctionKleinInvariantJ : Bool
    wolframFourierSeriesCarriesOneOver1728 : Bool
    repoRuntimeStandardJAtIUses1728Normalization : Bool
    sourceAndRuntimeNormalizationsMayDifferBy1728 : Bool

    positiveRealRescalingChangesComplexArgumentMathematically : Bool
    positiveRealRescalingCanChangeMagnitudeTone : Bool

    exactHomannColourFunctionTranscribed : Bool
    sourceViewportKnown : Bool
    finiteQSeriesPixelErrorBudgetPaid : Bool
    jpegPostprocessingModelled : Bool
    pixelForPixelClaimPermitted : Bool

    firstResidual : NormalizationResidual

canonicalHomannMathematicaCalibrationBoundary : HomannMathematicaCalibrationBoundary
canonicalHomannMathematicaCalibrationBoundary =
  homann-mathematica-calibration-boundary
    true
    true
    true
    true
    true
    false
    true
    false
    false
    false
    false
    false
    firstNormalizationResidual

pixelPerfectStillBlocked :
  HomannMathematicaCalibrationBoundary.pixelForPixelClaimPermitted
    canonicalHomannMathematicaCalibrationBoundary ≡ false
pixelPerfectStillBlocked = refl

colourFunctionStillUntranscribed :
  HomannMathematicaCalibrationBoundary.exactHomannColourFunctionTranscribed
    canonicalHomannMathematicaCalibrationBoundary ≡ false
colourFunctionStillUntranscribed = refl
