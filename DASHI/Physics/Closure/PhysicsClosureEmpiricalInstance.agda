module DASHI.Physics.Closure.PhysicsClosureEmpiricalInstance where

open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.Closure.PhysicsClosureEmpirical as PCE
open import DASHI.Physics.MyRealInstance as MRI
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC

physicsClosureEmpirical : PCE.PhysicsClosureEmpirical
physicsClosureEmpirical =
  record
    { kit = MRI.myKit
    ; seams = λ {m} {k} → SSC.shiftSeams {m} {k}
    }
