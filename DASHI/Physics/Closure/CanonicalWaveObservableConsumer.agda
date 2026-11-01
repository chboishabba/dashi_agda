module DASHI.Physics.Closure.CanonicalWaveObservableConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.CanonicalWaveRegimeConsumer as CWRC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem as KLRWO

record WaveObservableConsumerFromMinimal
  (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    waveRegimeConsumer : CWRC.WaveRegimeConsumerFromMinimal cl
    recoveredWaveObservables : KLRWO.KnownLimitsRecoveredWaveObservablesTheorem

canonicalWaveObservableConsumer :
  WaveObservableConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalWaveObservableConsumer =
  record
    { waveRegimeConsumer = CWRC.canonicalWaveRegimeConsumer
    ; recoveredWaveObservables =
        KLRWO.canonicalKnownLimitsRecoveredWaveObservablesTheorem
    }
