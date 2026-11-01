module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.CompletenessConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.StabilityConsumer as CWOTGRSC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
private
  module KLRWOTGRC = RWR

record WaveObservableTransportGeometryRegimeCompletenessConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeCompletenessConsumer
  field
    transportGeometryRegimeStabilityConsumer :
      CWOTGRSC.WaveObservableTransportGeometryRegimeStabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeCompleteness :
      KLRWOTGRC.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeCompletenessTheorem

canonicalWaveObservableTransportGeometryRegimeCompletenessConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRSC.WaveObservableTransportGeometryRegimeStabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeCompletenessConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeCompletenessConsumer waveObsTransportGeometryRegimeStability =
  waveObservableTransportGeometryRegimeCompletenessConsumer
    waveObsTransportGeometryRegimeStability
    KLRWOTGRC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeCompletenessTheorem
