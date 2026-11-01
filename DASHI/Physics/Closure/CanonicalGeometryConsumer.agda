module DASHI.Physics.Closure.CanonicalGeometryConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.KnownLimitsRecoveredDynamicsTheorem as KLRD
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record GeometryConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    dynamicsWitness : DCW.DynamicalClosureWitness
    dynamicsStatus : DCS.DynamicalClosureStatus
    recoveredDynamics : KLRD.KnownLimitsRecoveredDynamicsTheorem

canonicalGeometryConsumer :
  GeometryConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalGeometryConsumer =
  record
    { dynamicsWitness =
        MCPC.authoritativeDynamicsWitness MCCSI.minimumCredibleClosureShift
    ; dynamicsStatus =
        DC.DynamicalClosure.status
          (MCPC.authoritativeDynamics MCCSI.minimumCredibleClosureShift)
    ; recoveredDynamics =
        KLRD.canonicalKnownLimitsRecoveredDynamicsTheorem
    }
