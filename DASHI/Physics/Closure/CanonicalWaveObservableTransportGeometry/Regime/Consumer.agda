module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.Consumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometryCoherenceConsumer as CWOTGCC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.Theorem as KLRWOTGR

record WaveObservableTransportGeometryRegimeConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeConsumer
  field
    transportGeometryCoherenceConsumer :
      CWOTGCC.WaveObservableTransportGeometryCoherenceConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegime :
      KLRWOTGR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeTheorem

canonicalWaveObservableTransportGeometryRegimeConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGCC.WaveObservableTransportGeometryCoherenceConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeConsumer waveObsTransportGeometryCoherence =
  waveObservableTransportGeometryRegimeConsumer
    waveObsTransportGeometryCoherence
    KLRWOTGR.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeTheorem
