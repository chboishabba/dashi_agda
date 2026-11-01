module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.RepeatabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ReliabilityConsumer as CWOTGRRELC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRREP = RWR

record WaveObservableTransportGeometryRegimeRepeatabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeRepeatabilityConsumer
  field
    transportGeometryRegimeReliabilityConsumer :
      CWOTGRRELC.WaveObservableTransportGeometryRegimeReliabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeRepeatability :
      KLRWOTGRREP.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeRepeatabilityTheorem

canonicalWaveObservableTransportGeometryRegimeRepeatabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRRELC.WaveObservableTransportGeometryRegimeReliabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeRepeatabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeRepeatabilityConsumer waveObsTransportGeometryRegimeReliability =
  waveObservableTransportGeometryRegimeRepeatabilityConsumer
    waveObsTransportGeometryRegimeReliability
    KLRWOTGRREP.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeRepeatabilityTheorem
