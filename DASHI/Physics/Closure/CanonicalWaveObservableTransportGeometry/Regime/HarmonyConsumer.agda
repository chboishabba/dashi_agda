module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.HarmonyConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.IntegrityConsumer as CWOTGRINTC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRHAR = RWR

record WaveObservableTransportGeometryRegimeHarmonyConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeHarmonyConsumer
  field
    transportGeometryRegimeIntegrityConsumer :
      CWOTGRINTC.WaveObservableTransportGeometryRegimeIntegrityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeHarmony :
      KLRWOTGRHAR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeHarmonyTheorem

canonicalWaveObservableTransportGeometryRegimeHarmonyConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRINTC.WaveObservableTransportGeometryRegimeIntegrityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeHarmonyConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeHarmonyConsumer waveObsTransportGeometryRegimeIntegrity =
  waveObservableTransportGeometryRegimeHarmonyConsumer
    waveObsTransportGeometryRegimeIntegrity
    KLRWOTGRHAR.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeHarmonyTheorem
