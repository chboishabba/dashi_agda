module DASHI.Physics.Closure.Validation.SnapThresholdLawBoolInversion where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.TernaryRealInstance as TRI
open import DASHI.Physics.SeverityGuard.Shift.Concrete as SGSC
open import DASHI.Physics.Closure.Validation.Chi2BoundaryBoolInversionWitness as CBIVW
open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL
open import DASHI.Physics.Closure.Validation.SnapThresholdLawReport as STLR

boolInvLabel : String
boolInvLabel = "bool-inversion-snap-threshold"

boolInvHarness : STL.SnapThresholdHarness
boolInvHarness =
  record
    { label = boolInvLabel
    ; X = _
    ; policy = SGSC.policyᵣ {TRI.m} {TRI.k}
    ; witnessState = CBIVW.witnessState
    ; witnessSnap = CBIVW.witnessSnap
    }

boolInvReport : STLR.SnapThresholdReport
boolInvReport = STLR.buildReport boolInvHarness

boolInvVerdict : STL.SnapThresholdVerdict
boolInvVerdict = STLR.SnapThresholdReport.verdict boolInvReport
