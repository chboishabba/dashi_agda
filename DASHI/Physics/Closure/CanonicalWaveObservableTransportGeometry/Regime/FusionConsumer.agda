module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.FusionConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.SynthesisConsumer as CWOTGRSYNC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRFUS = RWR

record WaveObservableTransportGeometryRegimeFusionConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeFusionConsumer
  field
    transportGeometryRegimeSynthesisConsumer :
      CWOTGRSYNC.WaveObservableTransportGeometryRegimeSynthesisConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeFusion :
      KLRWOTGRFUS.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeFusionTheorem

canonicalWaveObservableTransportGeometryRegimeFusionConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRSYNC.WaveObservableTransportGeometryRegimeSynthesisConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeFusionConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeFusionConsumer prev =
  waveObservableTransportGeometryRegimeFusionConsumer
    prev
    KLRWOTGRFUS.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeFusionTheorem
