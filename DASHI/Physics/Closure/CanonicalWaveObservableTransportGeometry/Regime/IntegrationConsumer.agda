module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.IntegrationConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.AlignmentConsumer as CWOTGRALIGNC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRINTG = RWR

record WaveObservableTransportGeometryRegimeIntegrationConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeIntegrationConsumer
  field
    transportGeometryRegimeAlignmentConsumer :
      CWOTGRALIGNC.WaveObservableTransportGeometryRegimeAlignmentConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeIntegration :
      KLRWOTGRINTG.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeIntegrationTheorem

canonicalWaveObservableTransportGeometryRegimeIntegrationConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRALIGNC.WaveObservableTransportGeometryRegimeAlignmentConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeIntegrationConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeIntegrationConsumer prev =
  waveObservableTransportGeometryRegimeIntegrationConsumer
    prev
    KLRWOTGRINTG.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeIntegrationTheorem
