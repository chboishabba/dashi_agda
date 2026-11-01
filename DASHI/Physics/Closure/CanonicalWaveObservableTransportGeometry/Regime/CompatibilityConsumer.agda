module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.CompatibilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ContinuityConsumer as CWOTGRCONTC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
private
  module KLRWOTGRCOMP = RWR

record WaveObservableTransportGeometryRegimeCompatibilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeCompatibilityConsumer
  field
    transportGeometryRegimeContinuityConsumer :
      CWOTGRCONTC.WaveObservableTransportGeometryRegimeContinuityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeCompatibility :
      KLRWOTGRCOMP.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeCompatibilityTheorem

canonicalWaveObservableTransportGeometryRegimeCompatibilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRCONTC.WaveObservableTransportGeometryRegimeContinuityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeCompatibilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeCompatibilityConsumer waveObsTransportGeometryRegimeContinuity =
  waveObservableTransportGeometryRegimeCompatibilityConsumer
    waveObsTransportGeometryRegimeContinuity
    KLRWOTGRCOMP.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeCompatibilityTheorem
