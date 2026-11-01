module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.DurabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.OperabilityConsumer as CWOTGROPERC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRDUR = RWR

record WaveObservableTransportGeometryRegimeDurabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeDurabilityConsumer
  field
    transportGeometryRegimeOperabilityConsumer :
      CWOTGROPERC.WaveObservableTransportGeometryRegimeOperabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeDurability :
      KLRWOTGRDUR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeDurabilityTheorem

canonicalWaveObservableTransportGeometryRegimeDurabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGROPERC.WaveObservableTransportGeometryRegimeOperabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeDurabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeDurabilityConsumer waveObsTransportGeometryRegimeOperability =
  waveObservableTransportGeometryRegimeDurabilityConsumer
    waveObsTransportGeometryRegimeOperability
    KLRWOTGRDUR.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeDurabilityTheorem
