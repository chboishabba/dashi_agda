module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.CoherenceConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.Consumer as CWOTGRC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
private
  module KLRWOTGRC = RWR

record WaveObservableTransportGeometryRegimeCoherenceConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeCoherenceConsumer
  field
    transportGeometryRegimeConsumer :
      CWOTGRC.WaveObservableTransportGeometryRegimeConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeCoherence :
      KLRWOTGRC.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeCoherenceTheorem

canonicalWaveObservableTransportGeometryRegimeCoherenceConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRC.WaveObservableTransportGeometryRegimeConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeCoherenceConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeCoherenceConsumer waveObsTransportGeometryRegime =
  waveObservableTransportGeometryRegimeCoherenceConsumer
    waveObsTransportGeometryRegime
    KLRWOTGRC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeCoherenceTheorem
