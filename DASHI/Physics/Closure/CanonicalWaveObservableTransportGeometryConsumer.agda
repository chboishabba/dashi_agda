module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometryConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportConsumer as CWOTC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometryTheorem as KLRWOTG

record WaveObservableTransportGeometryConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryConsumer
  field
    transportConsumer :
      CWOTC.WaveObservableTransportConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometry :
      KLRWOTG.KnownLimitsRecoveredWaveObservableTransportGeometryTheorem

canonicalWaveObservableTransportGeometryConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTC.WaveObservableTransportConsumerFromMinimal cl →
  WaveObservableTransportGeometryConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryConsumer waveObsTransport =
  waveObservableTransportGeometryConsumer
    waveObsTransport
    KLRWOTG.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryTheorem
