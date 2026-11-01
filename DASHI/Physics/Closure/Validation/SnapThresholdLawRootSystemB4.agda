module DASHI.Physics.Closure.Validation.SnapThresholdLawRootSystemB4 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Properties as NatP using (≤-refl)
open import UFTC_Lattice using (Code; Severity; normal; special)

open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C
open import DASHI.Physics.SeverityGuard.Core as SG
open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL
open import DASHI.Physics.Closure.Validation.SnapThresholdLawReport as STLR

b4Label : String
b4Label = "root-system-b4-snap-threshold"

codeB4 : B4C.B4ShellComparisonVerdict → Code
codeB4 B4C.exactShellMatch = special 4
codeB4 B4C.shellMismatch = normal 0

safeThresholdB4 : Severity
safeThresholdB4 = 3

brokenThresholdB4 : Severity
brokenThresholdB4 = 4

b4Policy : SG.SeverityPolicy B4C.B4ShellComparisonVerdict
b4Policy =
  record
    { code = codeB4
    ; safeThreshold = safeThresholdB4
    ; brokenThreshold = brokenThresholdB4
    }

b4WitnessState : B4C.B4ShellComparisonVerdict
b4WitnessState = B4C.exactShellMatch

b4WitnessSnap : SG.Snap b4Policy b4WitnessState
b4WitnessSnap = NatP.≤-refl

b4Harness : STL.SnapThresholdHarness
b4Harness =
  record
    { label = b4Label
    ; X = B4C.B4ShellComparisonVerdict
    ; policy = b4Policy
    ; witnessState = b4WitnessState
    ; witnessSnap = b4WitnessSnap
    }

b4Report : STLR.SnapThresholdReport
b4Report = STLR.buildReport b4Harness

b4Verdict : STL.SnapThresholdVerdict
b4Verdict = STLR.SnapThresholdReport.verdict b4Report
