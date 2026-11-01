module DASHI.Physics.Closure.CanonicalRecoveryTransportConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalRegimeConsumer as CRC
open import DASHI.Physics.Closure.KnownLimitsRecoveredTransportConsistencyTheorem as KLRTC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record RecoveryTransportConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    regimeConsumer : CRC.RegimeConsumerFromMinimal C
    recoveredTransportConsistency :
      KLRTC.KnownLimitsRecoveredTransportConsistencyTheorem

canonicalRecoveryTransportConsumer :
  RecoveryTransportConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalRecoveryTransportConsumer =
  record
    { regimeConsumer = CRC.canonicalRegimeConsumer
    ; recoveredTransportConsistency =
        KLRTC.canonicalKnownLimitsRecoveredTransportConsistencyTheorem
    }
