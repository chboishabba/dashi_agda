module DASHI.Physics.Closure.MinimalCrediblePhysicsClosureValidationShiftInstance where

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureValidation as MCPCV
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidityShift as RPRS

minimumCredibleClosureValidationShift :
  MCPCV.MinimalCrediblePhysicsClosureValidation
minimumCredibleClosureValidationShift =
  record
    { closure = MCCSI.minimumCredibleClosureShift
    ; rigidity = RPRS.rigiditySuite
    }
