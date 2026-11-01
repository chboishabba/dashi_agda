module DASHI.Physics.Closure.KnownLimitsRecoveredObservableRegimeTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalObservableConsumer as COC
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservableGeometryTheorem as KLROG
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record KnownLimitsRecoveredObservableRegimeTheorem : Setω where
  field
    recoveredObservableGeometry :
      KLROG.KnownLimitsRecoveredObservableGeometryTheorem
    observableConsumer :
      COC.ObservableConsumerFromMinimal MCCSI.minimumCredibleClosureShift

canonicalKnownLimitsRecoveredObservableRegimeTheorem :
  KnownLimitsRecoveredObservableRegimeTheorem
canonicalKnownLimitsRecoveredObservableRegimeTheorem =
  record
    { recoveredObservableGeometry =
        KLROG.canonicalKnownLimitsRecoveredObservableGeometryTheorem
    ; observableConsumer = COC.canonicalObservableConsumer
    }
