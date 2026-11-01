module DASHI.Physics.Closure.CanonicalRecoveryConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalRegimeConsumer as CRC
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservableRegimeTheorem as KLROR
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record RecoveryConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    regimeConsumer : CRC.RegimeConsumerFromMinimal C
    recoveredObservableRegime :
      KLROR.KnownLimitsRecoveredObservableRegimeTheorem

canonicalRecoveryConsumer :
  RecoveryConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalRecoveryConsumer =
  record
    { regimeConsumer = CRC.canonicalRegimeConsumer
    ; recoveredObservableRegime =
        KLROR.canonicalKnownLimitsRecoveredObservableRegimeTheorem
    }
