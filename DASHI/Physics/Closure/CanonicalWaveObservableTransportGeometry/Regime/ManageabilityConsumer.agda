module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ManageabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.OperabilityConsumer as CWOTGROPERC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRMGT = RWR

record WaveObservableTransportGeometryRegimeManageabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeManageabilityConsumer
  field
    transportGeometryRegimeOperabilityConsumer :
      CWOTGROPERC.WaveObservableTransportGeometryRegimeOperabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeManageability :
      KLRWOTGRMGT.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeManageabilityTheorem

canonicalWaveObservableTransportGeometryRegimeManageabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGROPERC.WaveObservableTransportGeometryRegimeOperabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeManageabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeManageabilityConsumer waveObsTransportGeometryRegimeOperability =
  waveObservableTransportGeometryRegimeManageabilityConsumer
    waveObsTransportGeometryRegimeOperability
    KLRWOTGRMGT.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeManageabilityTheorem
