module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.RobustnessConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.InvarianceConsumer as CWOTGRINVC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRROB = RWR

record WaveObservableTransportGeometryRegimeRobustnessConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeRobustnessConsumer
  field
    transportGeometryRegimeInvarianceConsumer :
      CWOTGRINVC.WaveObservableTransportGeometryRegimeInvarianceConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeRobustness :
      KLRWOTGRROB.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeRobustnessTheorem

canonicalWaveObservableTransportGeometryRegimeRobustnessConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRINVC.WaveObservableTransportGeometryRegimeInvarianceConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeRobustnessConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeRobustnessConsumer waveObsTransportGeometryRegimeInvariance =
  waveObservableTransportGeometryRegimeRobustnessConsumer
    waveObsTransportGeometryRegimeInvariance
    KLRWOTGRROB.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeRobustnessTheorem
