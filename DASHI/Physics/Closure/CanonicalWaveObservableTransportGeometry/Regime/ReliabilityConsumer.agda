module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ReliabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.VerifiabilityConsumer as CWOTGRVTC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRREL = RWR

record WaveObservableTransportGeometryRegimeReliabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeReliabilityConsumer
  field
    transportGeometryRegimeVerifiabilityConsumer :
      CWOTGRVTC.WaveObservableTransportGeometryRegimeVerifiabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeReliability :
      KLRWOTGRREL.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeReliabilityTheorem

canonicalWaveObservableTransportGeometryRegimeReliabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRVTC.WaveObservableTransportGeometryRegimeVerifiabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeReliabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeReliabilityConsumer waveObsTransportGeometryRegimeVerifiability =
  waveObservableTransportGeometryRegimeReliabilityConsumer
    waveObsTransportGeometryRegimeVerifiability
    KLRWOTGRREL.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeReliabilityTheorem
