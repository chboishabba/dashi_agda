module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ConcordanceConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.CompatibilityConsumer as CWOTGRCOMPC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRCONC = RWR

record WaveObservableTransportGeometryRegimeConcordanceConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeConcordanceConsumer
  field
    transportGeometryRegimeCompatibilityConsumer :
      CWOTGRCOMPC.WaveObservableTransportGeometryRegimeCompatibilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeConcordance :
      KLRWOTGRCONC.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeConcordanceTheorem

canonicalWaveObservableTransportGeometryRegimeConcordanceConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRCOMPC.WaveObservableTransportGeometryRegimeCompatibilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeConcordanceConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeConcordanceConsumer waveObsTransportGeometryRegimeCompatibility =
  waveObservableTransportGeometryRegimeConcordanceConsumer
    waveObsTransportGeometryRegimeCompatibility
    KLRWOTGRCONC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeConcordanceTheorem
