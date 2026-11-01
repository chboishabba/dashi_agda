module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.StewardshipConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.SustainabilityConsumer as CWOTGRSUSTC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRSTEW = RWR

record WaveObservableTransportGeometryRegimeStewardshipConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeStewardshipConsumer
  field
    transportGeometryRegimeSustainabilityConsumer :
      CWOTGRSUSTC.WaveObservableTransportGeometryRegimeSustainabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeStewardship :
      KLRWOTGRSTEW.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeStewardshipTheorem

canonicalWaveObservableTransportGeometryRegimeStewardshipConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRSUSTC.WaveObservableTransportGeometryRegimeSustainabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeStewardshipConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeStewardshipConsumer waveObsTransportGeometryRegimeSustainability =
  waveObservableTransportGeometryRegimeStewardshipConsumer
    waveObsTransportGeometryRegimeSustainability
    KLRWOTGRSTEW.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeStewardshipTheorem
