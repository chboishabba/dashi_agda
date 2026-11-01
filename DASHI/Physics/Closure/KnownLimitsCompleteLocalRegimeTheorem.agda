module DASHI.Physics.Closure.KnownLimitsCompleteLocalRegimeTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalPropagationConsumer as CPC
open import DASHI.Physics.Closure.KnownLimitsExtendedLocalRecoveryTheorem as KLER
open import DASHI.Physics.Closure.KnownLimitsLocalPhysicsCoherenceTheorem as KLLPC
open import DASHI.Physics.Closure.KnownLimitsRecoveredLocalRegimeTheorem as KLRLR
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record KnownLimitsCompleteLocalRegimeTheorem : Setω where
  field
    extendedRecovery : KLER.KnownLimitsExtendedLocalRecoveryTheorem
    localPhysicsCoherence : KLLPC.KnownLimitsLocalPhysicsCoherenceTheorem
    recoveredLocalRegime : KLRLR.KnownLimitsRecoveredLocalRegimeTheorem
    propagationConsumer :
      CPC.PropagationConsumerFromMinimal MCCSI.minimumCredibleClosureShift

canonicalKnownLimitsCompleteLocalRegimeTheorem :
  KnownLimitsCompleteLocalRegimeTheorem
canonicalKnownLimitsCompleteLocalRegimeTheorem =
  record
    { extendedRecovery = KLER.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    ; localPhysicsCoherence = KLLPC.canonicalKnownLimitsLocalPhysicsCoherenceTheorem
    ; recoveredLocalRegime = KLRLR.canonicalKnownLimitsRecoveredLocalRegimeTheorem
    ; propagationConsumer = CPC.canonicalPropagationConsumer
    }
