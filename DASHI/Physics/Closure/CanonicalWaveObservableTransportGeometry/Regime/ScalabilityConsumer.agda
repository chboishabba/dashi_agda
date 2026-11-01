module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ScalabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.AdaptabilityConsumer as CWOTGRADAPTC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRSCAL = RWR

record WaveObservableTransportGeometryRegimeScalabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeScalabilityConsumer
  field
    transportGeometryRegimeAdaptabilityConsumer :
      CWOTGRADAPTC.WaveObservableTransportGeometryRegimeAdaptabilityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeScalability :
      KLRWOTGRSCAL.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeScalabilityTheorem

canonicalWaveObservableTransportGeometryRegimeScalabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRADAPTC.WaveObservableTransportGeometryRegimeAdaptabilityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeScalabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeScalabilityConsumer waveObsTransportGeometryRegimeAdaptability =
  waveObservableTransportGeometryRegimeScalabilityConsumer
    waveObsTransportGeometryRegimeAdaptability
    KLRWOTGRSCAL.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeScalabilityTheorem
