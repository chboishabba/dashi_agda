module DASHI.Physics.Closure.ExecutionAdmissibilityShiftWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ExecutionAdmissibilityWitness as EAW
open import DASHI.Physics.RealConeInteriorPreservedShift as RCIPS

record ShiftExecutionAdmissibilityWitness {m k : Nat} : Setω where
  field
    coneInterior : RCIPS.ConeInteriorShift {m} {k}
    interiorPreserved : RCIPS.ConeInteriorPreservedShift coneInterior
    executionWitness : EAW.SomeExecutionAdmissibilityWitness

open ShiftExecutionAdmissibilityWitness public
