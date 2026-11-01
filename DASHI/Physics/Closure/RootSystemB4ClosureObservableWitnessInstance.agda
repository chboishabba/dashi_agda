module DASHI.Physics.Closure.RootSystemB4ClosureObservableWitnessInstance where

open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.OrbitProfileComputedRootSystemB4 as ORB4
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL

b4ClosureObservableWitness : COW.ClosureObservableWitness
b4ClosureObservableWitness =
  record
    { realizationLabel = "root-system-b4-standalone"
    ; provedSignature = S31C.signature31FromProvider S31C.b4CoreProvider
    ; observedOrientationTag = 31
    ; observedShell1 = ORB4.b4-shell1-computed
    ; observedShell2 = ORB4.b4-shell2-computed
    ; seams = λ {m} {k} → SSC.shiftSeams {m} {k}
    ; lyapunovShift = λ {m} {k} → MDLL.lyapunovShift {m} {k}
    }
