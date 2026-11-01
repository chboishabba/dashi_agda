module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.InvarianceConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ConsistencyConsumer as CWOTGRCONSC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRINV = RWR

record WaveObservableTransportGeometryRegimeInvarianceConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeInvarianceConsumer
  field
    transportGeometryRegimeConsistencyConsumer :
      CWOTGRCONSC.WaveObservableTransportGeometryRegimeConsistencyConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeInvariance :
      KLRWOTGRINV.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeInvarianceTheorem

canonicalWaveObservableTransportGeometryRegimeInvarianceConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRCONSC.WaveObservableTransportGeometryRegimeConsistencyConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeInvarianceConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeInvarianceConsumer waveObsTransportGeometryRegimeConsistency =
  waveObservableTransportGeometryRegimeInvarianceConsumer
    waveObsTransportGeometryRegimeConsistency
    KLRWOTGRINV.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeInvarianceTheorem
