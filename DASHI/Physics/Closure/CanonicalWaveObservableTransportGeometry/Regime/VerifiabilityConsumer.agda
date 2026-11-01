module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.VerifiabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.AuditabilityConsumer as CWOTGRATC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRVT = RWR

record WaveObservableTransportGeometryRegimeVerifiabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeVerifiabilityConsumer
  field
    transportGeometryRegimeAuditabilityConsumer :
      CWOTGRATC.WaveObservableTransportGeometryRegimeAuditabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeVerifiability :
      KLRWOTGRVT.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeVerifiabilityTheorem

canonicalWaveObservableTransportGeometryRegimeVerifiabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRATC.WaveObservableTransportGeometryRegimeAuditabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeVerifiabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeVerifiabilityConsumer waveObsTransportGeometryRegimeAuditability =
  waveObservableTransportGeometryRegimeVerifiabilityConsumer
    waveObsTransportGeometryRegimeAuditability
    KLRWOTGRVT.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeVerifiabilityTheorem
