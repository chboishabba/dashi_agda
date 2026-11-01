module DASHI.Physics.Closure.KnownLimitsRecoveredWavefrontTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalPropagationConsumer as CPC
open import DASHI.Physics.Closure.KnownLimitsRecoveredTransportConsistencyTheorem as KLRTC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record KnownLimitsRecoveredWavefrontTheorem : Setω where
  field
    recoveredTransportConsistency :
      KLRTC.KnownLimitsRecoveredTransportConsistencyTheorem
    propagationConsumer :
      CPC.PropagationConsumerFromMinimal MCCSI.minimumCredibleClosureShift

canonicalKnownLimitsRecoveredWavefrontTheorem :
  KnownLimitsRecoveredWavefrontTheorem
canonicalKnownLimitsRecoveredWavefrontTheorem =
  record
    { recoveredTransportConsistency =
        KLRTC.canonicalKnownLimitsRecoveredTransportConsistencyTheorem
    ; propagationConsumer = CPC.canonicalPropagationConsumer
    }
