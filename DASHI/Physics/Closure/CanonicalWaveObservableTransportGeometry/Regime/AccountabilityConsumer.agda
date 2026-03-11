module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.AccountabilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.StewardshipConsumer as CWOTGRSTEWC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR

module KLRWOTGRACC = RWR

record WaveObservableTransportGeometryRegimeAccountabilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeAccountabilityConsumer
  field
    transportGeometryRegimeStewardshipConsumer :
      CWOTGRSTEWC.WaveObservableTransportGeometryRegimeStewardshipConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeAccountability :
      KLRWOTGRACC.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeAccountabilityTheorem

canonicalWaveObservableTransportGeometryRegimeAccountabilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRSTEWC.WaveObservableTransportGeometryRegimeStewardshipConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeAccountabilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeAccountabilityConsumer waveObsTransportGeometryRegimeStewardship =
  waveObservableTransportGeometryRegimeAccountabilityConsumer
    waveObsTransportGeometryRegimeStewardship
    KLRWOTGRACC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeAccountabilityTheorem

