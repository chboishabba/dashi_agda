module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ResilienceConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.RobustnessConsumer as CWOTGRROBC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRRES = RWR

record WaveObservableTransportGeometryRegimeResilienceConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeResilienceConsumer
  field
    transportGeometryRegimeRobustnessConsumer :
      CWOTGRROBC.WaveObservableTransportGeometryRegimeRobustnessConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeResilience :
      KLRWOTGRRES.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeResilienceTheorem

canonicalWaveObservableTransportGeometryRegimeResilienceConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRROBC.WaveObservableTransportGeometryRegimeRobustnessConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeResilienceConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeResilienceConsumer waveObsTransportGeometryRegimeRobustness =
  waveObservableTransportGeometryRegimeResilienceConsumer
    waveObsTransportGeometryRegimeRobustness
    KLRWOTGRRES.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeResilienceTheorem
