module DASHI.Physics.Closure.MinimalCrediblePhysicsClosureValidation where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidityReport as RPRR

record MinimalCrediblePhysicsClosureValidation : Setω where
  field
    closure : MCPC.MinimalCrediblePhysicsClosure
    rigidity : RPRR.RealizationProfileRigiditySuite

open MinimalCrediblePhysicsClosureValidation public

admissibleVerdict :
  MinimalCrediblePhysicsClosureValidation → RPR.RigidityVerdict
admissibleVerdict bundle =
  RPRR.RealizationProfileRigidityReport.verdict
    (RPRR.RealizationProfileRigiditySuite.admissibleReport
      (rigidity bundle))

negativeControlVerdict :
  MinimalCrediblePhysicsClosureValidation → RPR.RigidityVerdict
negativeControlVerdict bundle =
  RPRR.RealizationProfileRigidityReport.verdict
    (RPRR.RealizationProfileRigiditySuite.negativeControlReport
      (rigidity bundle))

selfVerdict :
  MinimalCrediblePhysicsClosureValidation → RPR.RigidityVerdict
selfVerdict bundle =
  RPRR.RealizationProfileRigidityReport.verdict
    (RPRR.RealizationProfileRigiditySuite.selfReport
      (rigidity bundle))
