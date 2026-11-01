module DASHI.Physics.Closure.CanonicalRegimeConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalObservableConsumer as COC
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservableGeometryTheorem as KLROG
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record RegimeConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    observableConsumer : COC.ObservableConsumerFromMinimal C
    recoveredObservableGeometry :
      KLROG.KnownLimitsRecoveredObservableGeometryTheorem

canonicalRegimeConsumer :
  RegimeConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalRegimeConsumer =
  record
    { observableConsumer = COC.canonicalObservableConsumer
    ; recoveredObservableGeometry =
        KLROG.canonicalKnownLimitsRecoveredObservableGeometryTheorem
    }
