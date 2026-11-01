module DASHI.Physics.Closure.CanonicalPropagationConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.KnownLimitsExtendedLocalRecoveryTheorem as KLER
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record PropagationConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    dynamicsStatus : DCS.DynamicalClosureStatus
    dynamicsWitness : DCW.DynamicalClosureWitness
    extendedLocalRecovery : KLER.KnownLimitsExtendedLocalRecoveryTheorem

canonicalPropagationConsumer :
  PropagationConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalPropagationConsumer =
  record
    { dynamicsStatus =
        DC.DynamicalClosure.status
          (MCPC.authoritativeDynamics MCCSI.minimumCredibleClosureShift)
    ; dynamicsWitness =
        MCPC.authoritativeDynamicsWitness MCCSI.minimumCredibleClosureShift
    ; extendedLocalRecovery =
        KLER.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    }
