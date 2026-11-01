module DASHI.Physics.Closure.Validation.SnapThresholdLawShiftTertiary where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.TernaryRealInstance as TRI
open import DASHI.Physics.SeverityGuard.Shift.Concrete as SGSC
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftTertiaryWitness as CBTW
open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL
open import DASHI.Physics.Closure.Validation.SnapThresholdLawReport as STLR

tertiaryLabel : String
tertiaryLabel = "signed-permutation-shift-snap-threshold-tertiary"

tertiaryHarness : STL.SnapThresholdHarness
tertiaryHarness =
  record
    { label = tertiaryLabel
    ; X = _
    ; policy = SGSC.policyᵣ {TRI.m} {TRI.k}
    ; witnessState = CBTW.witnessState
    ; witnessSnap = CBTW.witnessSnap
    }

tertiaryReport : STLR.SnapThresholdReport
tertiaryReport = STLR.buildReport tertiaryHarness

tertiaryVerdict : STL.SnapThresholdVerdict
tertiaryVerdict = STLR.SnapThresholdReport.verdict tertiaryReport
