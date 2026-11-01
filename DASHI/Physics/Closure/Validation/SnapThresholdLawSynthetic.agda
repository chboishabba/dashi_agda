module DASHI.Physics.Closure.Validation.SnapThresholdLawSynthetic where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)
open import Data.Nat.Properties as NatP using (≤-refl)

open import DASHI.Physics.SeverityGuard.Synthetic.Concrete as SGSCB
open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL
open import DASHI.Physics.Closure.Validation.SnapThresholdLawReport as STLR

syntheticLabel : String
syntheticLabel = "synthetic-bool-snap-threshold"

syntheticHarness : STL.SnapThresholdHarness
syntheticHarness =
  record
    { label = syntheticLabel
    ; X = Bool
    ; policy = SGSCB.policyᵇ
    ; witnessState = true
    ; witnessSnap = NatP.≤-refl
    }

syntheticReport : STLR.SnapThresholdReport
syntheticReport = STLR.buildReport syntheticHarness

syntheticVerdict : STL.SnapThresholdVerdict
syntheticVerdict = STLR.SnapThresholdReport.verdict syntheticReport
