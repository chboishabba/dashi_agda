module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.OperabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.UsabilityConsumer as CWOTGRUSAC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGROPER = RWR

record WaveObservableTransportGeometryRegimeOperabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeOperabilityConsumer
  field
    transportGeometryRegimeUsabilityConsumer :
      CWOTGRUSAC.WaveObservableTransportGeometryRegimeUsabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeOperability :
      KLRWOTGROPER.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeOperabilityTheorem

canonicalWaveObservableTransportGeometryRegimeOperabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRUSAC.WaveObservableTransportGeometryRegimeUsabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeOperabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeOperabilityConsumer waveObsTransportGeometryRegimeUsability =
  waveObservableTransportGeometryRegimeOperabilityConsumer
    waveObsTransportGeometryRegimeUsability
    KLRWOTGROPER.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeOperabilityTheorem
