module DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.KnownLimitsLocalCoherenceTheorem as KLLCT
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record SpinLocalLorentzBridge
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    consumer : CSDC.SpinDiracConsumerFromMinimal C
    localCoherence : KLLCT.KnownLimitsLocalCoherenceTheorem

spinLocalLorentzBridgeFromMinimal :
  (C : MCPC.MinimalCrediblePhysicsClosure) →
  SpinLocalLorentzBridge C
spinLocalLorentzBridgeFromMinimal C =
  record
    { consumer = CSDC.spinDiracConsumerFromMinimal C
    ; localCoherence = KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    }

canonicalSpinLocalLorentzBridge :
  SpinLocalLorentzBridge MCCSI.minimumCredibleClosureShift
canonicalSpinLocalLorentzBridge =
  spinLocalLorentzBridgeFromMinimal MCCSI.minimumCredibleClosureShift
