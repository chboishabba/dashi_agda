module DASHI.Physics.Closure.Validation.SnapThresholdLawShiftSecondary where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.TernaryRealInstance as TRI
open import DASHI.Physics.SeverityGuard.Shift.Concrete as SGSC
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftSecondaryWitness as CBSW
open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL
open import DASHI.Physics.Closure.Validation.SnapThresholdLawReport as STLR

secondaryLabel : String
secondaryLabel = "signed-permutation-shift-snap-threshold-secondary"

secondaryHarness : STL.SnapThresholdHarness
secondaryHarness =
  record
    { label = secondaryLabel
    ; X = _
    ; policy = SGSC.policyᵣ {TRI.m} {TRI.k}
    ; witnessState = CBSW.witnessState
    ; witnessSnap = CBSW.witnessSnap
    }

secondaryReport : STLR.SnapThresholdReport
secondaryReport = STLR.buildReport secondaryHarness

secondaryVerdict : STL.SnapThresholdVerdict
secondaryVerdict = STLR.SnapThresholdReport.verdict secondaryReport
