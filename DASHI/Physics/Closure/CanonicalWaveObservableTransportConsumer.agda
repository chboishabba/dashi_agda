module DASHI.Physics.Closure.CanonicalWaveObservableTransportConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableConsumer as CWOC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportTheorem as KLRWOT

record WaveObservableTransportConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportConsumer
  field
    waveObservableConsumer :
      CWOC.WaveObservableConsumerFromMinimal cl
    recoveredWaveObservableTransport :
      KLRWOT.KnownLimitsRecoveredWaveObservableTransportTheorem

canonicalWaveObservableTransportConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOC.WaveObservableConsumerFromMinimal cl →
  WaveObservableTransportConsumerFromMinimal cl
canonicalWaveObservableTransportConsumer waveObs =
  waveObservableTransportConsumer
    waveObs
    KLRWOT.canonicalKnownLimitsRecoveredWaveObservableTransportTheorem
