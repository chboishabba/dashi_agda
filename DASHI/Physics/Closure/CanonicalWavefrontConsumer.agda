module DASHI.Physics.Closure.CanonicalWavefrontConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalRecoveryTransportConsumer as CRTC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWavefrontTheorem as KLRW
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record WavefrontConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    recoveryTransportConsumer : CRTC.RecoveryTransportConsumerFromMinimal C
    recoveredWavefront :
      KLRW.KnownLimitsRecoveredWavefrontTheorem

canonicalWavefrontConsumer :
  WavefrontConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalWavefrontConsumer =
  record
    { recoveryTransportConsumer = CRTC.canonicalRecoveryTransportConsumer
    ; recoveredWavefront = KLRW.canonicalKnownLimitsRecoveredWavefrontTheorem
    }
