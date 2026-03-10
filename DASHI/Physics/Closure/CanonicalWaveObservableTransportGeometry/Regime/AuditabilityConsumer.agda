module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.AuditabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.TraceabilityConsumer as CWOTGRTRCC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRAT = RWR

record WaveObservableTransportGeometryRegimeAuditabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeAuditabilityConsumer
  field
    transportGeometryRegimeTraceabilityConsumer :
      CWOTGRTRCC.WaveObservableTransportGeometryRegimeTraceabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeAuditability :
      KLRWOTGRAT.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeAuditabilityTheorem

canonicalWaveObservableTransportGeometryRegimeAuditabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRTRCC.WaveObservableTransportGeometryRegimeTraceabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeAuditabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeAuditabilityConsumer waveObsTransportGeometryRegimeTraceability =
  waveObservableTransportGeometryRegimeAuditabilityConsumer
    waveObsTransportGeometryRegimeTraceability
    KLRWOTGRAT.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeAuditabilityTheorem
