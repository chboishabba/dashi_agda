module DASHI.Moonshine.JInvariantFormulaicRasterRuntimeContractExact where

------------------------------------------------------------------------
-- GOVERNED RUNTIME CONTRACT FOR THE FORMULAIC j RASTER PRODUCER
--
-- Runtime owner:
--   scripts/j_invariant_formulaic_raster_compare.py
--
-- The script reuses scripts/cm_j_alpha_scan.py:j_invariant and therefore does
-- not create a second E4/E6 numerical evaluator.  This contract records the
-- permitted runtime modes and fail-closed source-exact promotion gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.JInvariantHomannMathematicaSourceCalibrationExact as Source

runtimeScriptPath : String
runtimeScriptPath = "scripts/j_invariant_formulaic_raster_compare.py"

upstreamEvaluatorPath : String
upstreamEvaluatorPath = "scripts/cm_j_alpha_scan.py:j_invariant"

data RuntimeNormalization : Set where
  standardJRuntime : RuntimeNormalization
  mathematicaKleinJRuntime : RuntimeNormalization

data RuntimeColourModel : Set where
  phaseOnlyDiagnostic : RuntimeColourModel
  homannExactColour : RuntimeColourModel

record RasterRuntimeAdmission : Set where
  constructor raster-runtime-admission
  field
    normalization : RuntimeNormalization
    colourModel : RuntimeColourModel
    viewportCalibrated : Bool
    homannColourTranscribed : Bool
    finiteQSeriesErrorBudgetPaid : Bool
    jpegPostprocessingModelled : Bool

open RasterRuntimeAdmission public

sourceExactPermitted : RasterRuntimeAdmission → Bool
sourceExactPermitted
  (raster-runtime-admission
    standardJRuntime colour viewport colourReceipt errorBudget jpeg) = false
sourceExactPermitted
  (raster-runtime-admission
    mathematicaKleinJRuntime phaseOnlyDiagnostic viewport colourReceipt errorBudget jpeg) = false
sourceExactPermitted
  (raster-runtime-admission
    mathematicaKleinJRuntime homannExactColour false colourReceipt errorBudget jpeg) = false
sourceExactPermitted
  (raster-runtime-admission
    mathematicaKleinJRuntime homannExactColour true false errorBudget jpeg) = false
sourceExactPermitted
  (raster-runtime-admission
    mathematicaKleinJRuntime homannExactColour true true false jpeg) = false
sourceExactPermitted
  (raster-runtime-admission
    mathematicaKleinJRuntime homannExactColour true true true false) = false
sourceExactPermitted
  (raster-runtime-admission
    mathematicaKleinJRuntime homannExactColour true true true true) = true

currentDiagnosticAdmission : RasterRuntimeAdmission
currentDiagnosticAdmission =
  raster-runtime-admission
    mathematicaKleinJRuntime
    phaseOnlyDiagnostic
    false
    false
    false
    false

currentDiagnosticIsNotSourceExact :
  sourceExactPermitted currentDiagnosticAdmission ≡ false
currentDiagnosticIsNotSourceExact = refl

record FormulaicRasterRuntimeBoundary : Set where
  constructor formulaic-raster-runtime-boundary
  field
    reusesExistingNumericalJKernel : Bool
    standardAndMathematicaNormalizationsSeparated : Bool
    phaseOnlyDiagnosticAvailable : Bool
    exactHomannColourAvailable : Bool
    implicitViewportResamplingAllowed : Bool
    sourceExactGateFailClosed : Bool
    sourceCalibrationStillBlocksPixelPerfect : Bool

canonicalFormulaicRasterRuntimeBoundary : FormulaicRasterRuntimeBoundary
canonicalFormulaicRasterRuntimeBoundary =
  formulaic-raster-runtime-boundary
    true true true false false true true

sourceCalibrationBoundaryStillBlocksPixelPerfect :
  Source.HomannMathematicaCalibrationBoundary.pixelForPixelClaimPermitted
    Source.canonicalHomannMathematicaCalibrationBoundary ≡ false
sourceCalibrationBoundaryStillBlocksPixelPerfect = refl
