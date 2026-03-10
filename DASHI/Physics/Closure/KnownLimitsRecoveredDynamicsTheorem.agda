module DASHI.Physics.Closure.KnownLimitsRecoveredDynamicsTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalDynamicsLawTheorem as CDLT
open import DASHI.Physics.Closure.CanonicalPropagationConsumer as CPC
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.KnownLimitsCompleteLocalRegimeTheorem as KLCLR
open import DASHI.Physics.Closure.KnownLimitsLocalCausalEffectivePropagationTheorem as KLCEPT
open import DASHI.Physics.Closure.KnownLimitsLocalCausalGeometryCoherenceTheorem as KLCGCT
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record KnownLimitsRecoveredDynamicsTheorem : Setω where
  field
    completeLocalRegime : KLCLR.KnownLimitsCompleteLocalRegimeTheorem
    localCausalEffectivePropagation :
      KLCEPT.KnownLimitsLocalCausalEffectivePropagationTheorem
    localCausalGeometryCoherence :
      KLCGCT.KnownLimitsLocalCausalGeometryCoherenceTheorem
    canonicalDynamicsLaw : CDLT.CanonicalDynamicsLawTheorem
    propagationConsumer :
      CPC.PropagationConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    recoveredDynamicsWitness : DCW.DynamicalClosureWitness

canonicalKnownLimitsRecoveredDynamicsTheorem :
  KnownLimitsRecoveredDynamicsTheorem
canonicalKnownLimitsRecoveredDynamicsTheorem =
  record
    { completeLocalRegime = KLCLR.canonicalKnownLimitsCompleteLocalRegimeTheorem
    ; localCausalEffectivePropagation =
        KLCEPT.canonicalKnownLimitsLocalCausalEffectivePropagationTheorem
    ; localCausalGeometryCoherence =
        KLCGCT.canonicalKnownLimitsLocalCausalGeometryCoherenceTheorem
    ; canonicalDynamicsLaw = CDLT.canonicalDynamicsLawTheorem
    ; propagationConsumer = CPC.canonicalPropagationConsumer
    ; recoveredDynamicsWitness =
        CDLT.CanonicalDynamicsLawTheorem.canonicalDynamicsWitness
          CDLT.canonicalDynamicsLawTheorem
    }
