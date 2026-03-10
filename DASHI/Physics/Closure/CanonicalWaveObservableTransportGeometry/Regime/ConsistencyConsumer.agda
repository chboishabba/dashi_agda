module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ConsistencyConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.SoundnessConsumer as CWOTGRSOC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRCONS = RWR

record WaveObservableTransportGeometryRegimeConsistencyConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeConsistencyConsumer
  field
    transportGeometryRegimeSoundnessConsumer :
      CWOTGRSOC.WaveObservableTransportGeometryRegimeSoundnessConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeConsistency :
      KLRWOTGRCONS.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeConsistencyTheorem

canonicalWaveObservableTransportGeometryRegimeConsistencyConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRSOC.WaveObservableTransportGeometryRegimeSoundnessConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeConsistencyConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeConsistencyConsumer waveObsTransportGeometryRegimeSoundness =
  waveObservableTransportGeometryRegimeConsistencyConsumer
    waveObsTransportGeometryRegimeSoundness
    KLRWOTGRCONS.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeConsistencyTheorem
