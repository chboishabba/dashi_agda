module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.UsabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ReliabilityConsumer as CWOTGRRELC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRUSA = RWR

record WaveObservableTransportGeometryRegimeUsabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeUsabilityConsumer
  field
    transportGeometryRegimeReliabilityConsumer :
      CWOTGRRELC.WaveObservableTransportGeometryRegimeReliabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeUsability :
      KLRWOTGRUSA.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeUsabilityTheorem

canonicalWaveObservableTransportGeometryRegimeUsabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRRELC.WaveObservableTransportGeometryRegimeReliabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeUsabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeUsabilityConsumer waveObsTransportGeometryRegimeReliability =
  waveObservableTransportGeometryRegimeUsabilityConsumer
    waveObsTransportGeometryRegimeReliability
    KLRWOTGRUSA.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeUsabilityTheorem
