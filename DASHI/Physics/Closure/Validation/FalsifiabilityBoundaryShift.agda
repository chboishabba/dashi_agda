module DASHI.Physics.Closure.Validation.FalsifiabilityBoundaryShift where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
open import DASHI.Physics.Closure.ShiftObservablePredictionInstance as SOPI
open import DASHI.Physics.Closure.Validation.FalsifiabilityBoundary as FB
open import DASHI.Physics.Closure.Validation.FalsifiabilityBoundaryReport as FBR

shiftLabel : String
shiftLabel = "signed-permutation-shift-falsifiability-boundary"

shiftHarness : FB.FalsifiabilityBoundaryHarness
shiftHarness =
  record
    { label = shiftLabel
    ; falsifySig40 = OPP.ObservablePredictionPackage.falsifySig40
        SOPI.shiftObservablePrediction
    ; falsifySig22 = OPP.ObservablePredictionPackage.falsifySig22
        SOPI.shiftObservablePrediction
    ; falsifyMirror = OPP.ObservablePredictionPackage.falsifyMirror
        SOPI.shiftObservablePrediction
    ; falsifySig04 = OPP.ObservablePredictionPackage.falsifySig04
        SOPI.shiftObservablePrediction
    }

shiftReport : FBR.FalsifiabilityBoundaryReport
shiftReport = FBR.buildReport shiftHarness

shiftVerdict : FB.FalsifiabilityBoundaryVerdict
shiftVerdict = FBR.FalsifiabilityBoundaryReport.verdict shiftReport
