module DASHI.Physics.Closure.Validation.SnapThresholdLawShift where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.TernaryRealInstance as TRI
open import DASHI.Physics.SeverityGuard.Shift.Concrete as SGSC
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftWitness as CBW
open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL
open import DASHI.Physics.Closure.Validation.SnapThresholdLawReport as STLR

shiftLabel : String
shiftLabel = "signed-permutation-shift-snap-threshold"

shiftHarness : STL.SnapThresholdHarness
shiftHarness =
  record
    { label = shiftLabel
    ; X = _
    ; policy = SGSC.policyᵣ {TRI.m} {TRI.k}
    ; witnessState = CBW.witnessState
    ; witnessSnap = CBW.witnessSnap
    }

shiftReport : STLR.SnapThresholdReport
shiftReport = STLR.buildReport shiftHarness

shiftVerdict : STL.SnapThresholdVerdict
shiftVerdict = STLR.SnapThresholdReport.verdict shiftReport
