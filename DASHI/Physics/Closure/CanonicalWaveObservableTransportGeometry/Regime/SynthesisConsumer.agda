module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.SynthesisConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.IntegrationConsumer as CWOTGRINTGC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRSYN = RWR

record WaveObservableTransportGeometryRegimeSynthesisConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeSynthesisConsumer
  field
    transportGeometryRegimeIntegrationConsumer :
      CWOTGRINTGC.WaveObservableTransportGeometryRegimeIntegrationConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeSynthesis :
      KLRWOTGRSYN.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeSynthesisTheorem

canonicalWaveObservableTransportGeometryRegimeSynthesisConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRINTGC.WaveObservableTransportGeometryRegimeIntegrationConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeSynthesisConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeSynthesisConsumer prev =
  waveObservableTransportGeometryRegimeSynthesisConsumer
    prev
    KLRWOTGRSYN.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeSynthesisTheorem
