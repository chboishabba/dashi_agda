module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometryCoherenceConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometryConsumer as CWOTGC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem as KLRWOTGC

record WaveObservableTransportGeometryCoherenceConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryCoherenceConsumer
  field
    transportGeometryConsumer :
      CWOTGC.WaveObservableTransportGeometryConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryCoherence :
      KLRWOTGC.KnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem

canonicalWaveObservableTransportGeometryCoherenceConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGC.WaveObservableTransportGeometryConsumerFromMinimal cl →
  WaveObservableTransportGeometryCoherenceConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryCoherenceConsumer waveObsTransportGeometry =
  waveObservableTransportGeometryCoherenceConsumer
    waveObsTransportGeometry
    KLRWOTGC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem
