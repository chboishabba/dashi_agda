module DASHI.Physics.Closure.ShiftClosureObservableWitnessInstance where

open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL

shiftClosureObservableWitness : COW.ClosureObservableWitness
shiftClosureObservableWitness =
  record
    { realizationLabel = "signed-permutation-shift"
    ; provedSignature = S31C.signature31
    ; observedOrientationTag = 31
    ; observedShell1 = OPD.shell1_p3_q1
    ; observedShell2 = OPD.shell2_p3_q1
    ; seams = λ {m} {k} → SSC.shiftSeams {m} {k}
    ; lyapunovShift = λ {m} {k} → MDLL.lyapunovShift {m} {k}
    }
