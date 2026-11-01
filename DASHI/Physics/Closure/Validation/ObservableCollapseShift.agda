module DASHI.Physics.Closure.Validation.ObservableCollapseShift where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.TernaryRealInstanceShift as TRIS
open import DASHI.Physics.RealClosureKitFiber as RKF
open import DASHI.Physics.Closure.Validation.ObservableCollapse as OC
open import DASHI.Physics.Closure.Validation.ObservableCollapseReport as OCR

shiftLabel : String
shiftLabel = "signed-permutation-shift-observable-collapse"

shiftHarness : OC.ObservableCollapseHarness
shiftHarness =
  record
    { label = shiftLabel
    ; Obs = RKF.RealClosureKitFiber.Obs TRIS.realKitFiber
    ; obs0 = RKF.RealClosureKitFiber.obs0 TRIS.realKitFiber
    ; obsT = RKF.RealClosureKitFiber.obsT TRIS.realKitFiber
    ; obsFixed = RKF.RealClosureKitFiber.obsFixed TRIS.realKitFiber
    ; obsUnique = RKF.RealClosureKitFiber.obsUnique TRIS.realKitFiber
    }

shiftReport : OCR.ObservableCollapseReport
shiftReport = OCR.buildReport shiftHarness

shiftVerdict : OC.ObservableCollapseVerdict
shiftVerdict = OCR.ObservableCollapseReport.verdict shiftReport
