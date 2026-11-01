module DASHI.Physics.Closure.SyntheticClosureObservableWitnessInstance where

open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.SyntheticOneMinusShellRealization as SOM
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL

syntheticClosureObservableWitness : COW.ClosureObservableWitness
syntheticClosureObservableWitness =
  record
    { realizationLabel = SOM.label
    ; provedSignature = S31C.syntheticSignature31
    ; observedOrientationTag = 31
    ; observedShell1 = SOM.shell1Profile
    ; observedShell2 = SOM.shell2Profile
    ; seams = λ {m} {k} → SSC.shiftSeams {m} {k}
    ; lyapunovShift = λ {m} {k} → MDLL.lyapunovShift {m} {k}
    }
