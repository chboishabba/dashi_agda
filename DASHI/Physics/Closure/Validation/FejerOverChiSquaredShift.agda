module DASHI.Physics.Closure.Validation.FejerOverChiSquaredShift where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureShiftInstance as DCSI
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftWitness as CBW
open import DASHI.Physics.Closure.Validation.FejerOverChiSquared as FCS
open import DASHI.Physics.Closure.Validation.FejerOverChiSquaredReport as FCSR

shiftLabel : String
shiftLabel = "signed-permutation-shift-fejer-reference"

shiftHarness : FCS.FejerOverChi2Harness
shiftHarness =
  record
    { label = shiftLabel
    ; seams = λ {m} {k} → DC.DynamicalClosure.seams DCSI.shiftDynamics {m} {k}
    ; mdlFejerWitness = DC.DynamicalClosure.mdlFejerWitness DCSI.shiftDynamics
    ; chi2FalsifierStatus = FCS.formalized
    }

shiftReport : FCSR.FejerOverChi2Report
shiftReport = FCSR.buildReport shiftHarness

shiftVerdict : FCS.FejerBenchmarkVerdict
shiftVerdict = FCSR.FejerOverChi2Report.verdict shiftReport
