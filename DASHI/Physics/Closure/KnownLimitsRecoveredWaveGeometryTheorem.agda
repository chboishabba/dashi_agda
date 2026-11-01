module DASHI.Physics.Closure.KnownLimitsRecoveredWaveGeometryTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalGeometryConsumer as CGC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWavefrontTheorem as KLRW
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record KnownLimitsRecoveredWaveGeometryTheorem : Setω where
  field
    recoveredWavefront :
      KLRW.KnownLimitsRecoveredWavefrontTheorem
    geometryConsumer :
      CGC.GeometryConsumerFromMinimal MCCSI.minimumCredibleClosureShift

canonicalKnownLimitsRecoveredWaveGeometryTheorem :
  KnownLimitsRecoveredWaveGeometryTheorem
canonicalKnownLimitsRecoveredWaveGeometryTheorem =
  record
    { recoveredWavefront =
        KLRW.canonicalKnownLimitsRecoveredWavefrontTheorem
    ; geometryConsumer = CGC.canonicalGeometryConsumer
    }
