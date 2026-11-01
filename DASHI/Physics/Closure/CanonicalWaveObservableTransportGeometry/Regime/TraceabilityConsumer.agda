module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.TraceabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.IntegrityConsumer as CWOTGRINTC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRTRC = RWR

record WaveObservableTransportGeometryRegimeTraceabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeTraceabilityConsumer
  field
    transportGeometryRegimeIntegrityConsumer :
      CWOTGRINTC.WaveObservableTransportGeometryRegimeIntegrityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeTraceability :
      KLRWOTGRTRC.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeTraceabilityTheorem

canonicalWaveObservableTransportGeometryRegimeTraceabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRINTC.WaveObservableTransportGeometryRegimeIntegrityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeTraceabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeTraceabilityConsumer waveObsTransportGeometryRegimeIntegrity =
  waveObservableTransportGeometryRegimeTraceabilityConsumer
    waveObsTransportGeometryRegimeIntegrity
    KLRWOTGRTRC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeTraceabilityTheorem
