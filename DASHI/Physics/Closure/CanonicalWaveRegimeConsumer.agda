module DASHI.Physics.Closure.CanonicalWaveRegimeConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.CanonicalWaveGeometryConsumer as CWGC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveRegimeTheorem as KLRWR

record WaveRegimeConsumerFromMinimal
  (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    waveGeometryConsumer : CWGC.WaveGeometryConsumerFromMinimal cl
    recoveredWaveRegime : KLRWR.KnownLimitsRecoveredWaveRegimeTheorem

canonicalWaveRegimeConsumer :
  WaveRegimeConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalWaveRegimeConsumer =
  record
    { waveGeometryConsumer = CWGC.canonicalWaveGeometryConsumer
    ; recoveredWaveRegime = KLRWR.canonicalKnownLimitsRecoveredWaveRegimeTheorem
    }
