module DASHI.Physics.Closure.KnownLimitsRecoveredTransportConsistencyTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalRegimeConsumer as CRC
open import DASHI.Physics.Closure.KnownLimitsGeometryTransportTheorem as KLGT
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservableGeometryTheorem as KLROG
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record KnownLimitsRecoveredTransportConsistencyTheorem : Setω where
  field
    recoveredObservableGeometry :
      KLROG.KnownLimitsRecoveredObservableGeometryTheorem
    geometryTransport :
      KLGT.KnownLimitsGeometryTransportTheorem
    regimeConsumer :
      CRC.RegimeConsumerFromMinimal MCCSI.minimumCredibleClosureShift

canonicalKnownLimitsRecoveredTransportConsistencyTheorem :
  KnownLimitsRecoveredTransportConsistencyTheorem
canonicalKnownLimitsRecoveredTransportConsistencyTheorem =
  record
    { recoveredObservableGeometry =
        KLROG.canonicalKnownLimitsRecoveredObservableGeometryTheorem
    ; geometryTransport =
        KLGT.canonicalKnownLimitsGeometryTransportTheorem
    ; regimeConsumer = CRC.canonicalRegimeConsumer
    }
