module DASHI.Physics.Closure.CanonicalWaveGeometryConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalWavefrontConsumer as CWFC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveGeometryTheorem as KLRWG
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record WaveGeometryConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    wavefrontConsumer : CWFC.WavefrontConsumerFromMinimal C
    recoveredWaveGeometry :
      KLRWG.KnownLimitsRecoveredWaveGeometryTheorem

canonicalWaveGeometryConsumer :
  WaveGeometryConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalWaveGeometryConsumer =
  record
    { wavefrontConsumer = CWFC.canonicalWavefrontConsumer
    ; recoveredWaveGeometry =
        KLRWG.canonicalKnownLimitsRecoveredWaveGeometryTheorem
    }
