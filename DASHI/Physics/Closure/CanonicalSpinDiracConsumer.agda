module DASHI.Physics.Closure.CanonicalSpinDiracConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.CanonicalConstraintClosureStatus as CCCS
open import DASHI.Physics.Closure.KnownLimitsStatus as KLS
open import DASHI.Physics.Closure.KnownLimitsRecovery as KLR
open import DASHI.Physics.Closure.KnownLimitsRecoveryWitness as KLRW
open import DASHI.Physics.Closure.SpinDiracGateFromClosure as SDGC

record SpinDiracConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    dynamics : DC.DynamicalClosure
    dynamicsStatus : DCS.DynamicalClosureStatus
    dynamicsWitness : DCW.DynamicalClosureWitness
    constraintStatus : CCCS.CanonicalConstraintClosureStatus
    knownLimitsStatus : KLS.KnownLimitsStatus
    knownLimitsRecovery : KLR.KnownLimitsRecoveryWitness
    knownLimitsRecoveryWitnessPlus : KLRW.KnownLimitsRecoveryWitnessPlus

spinDiracConsumerFromMinimal :
  (C : MCPC.MinimalCrediblePhysicsClosure) →
  SpinDiracConsumerFromMinimal C
spinDiracConsumerFromMinimal C =
  record
    { dynamics = SDGC.requiredDynamicsFromMinimal C
    ; dynamicsStatus = SDGC.requiredDynamicsStatusFromMinimal C
    ; dynamicsWitness = SDGC.requiredDynamicsWitnessFromMinimal C
    ; constraintStatus = CCCS.canonicalConstraintClosureStatus
    ; knownLimitsStatus = KLS.canonicalKnownLimitsStatus
    ; knownLimitsRecovery = KLR.canonicalKnownLimitsRecovery
    ; knownLimitsRecoveryWitnessPlus = KLRW.canonicalKnownLimitsRecoveryWitness
    }
