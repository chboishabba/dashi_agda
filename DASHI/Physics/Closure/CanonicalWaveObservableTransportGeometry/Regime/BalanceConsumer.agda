module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.BalanceConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.HarmonyConsumer as CWOTGRHARC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.BalanceTheorem as KLRWOTGRBAL

record WaveObservableTransportGeometryRegimeBalanceConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeBalanceConsumer
  field
    transportGeometryRegimeHarmonyConsumer :
      CWOTGRHARC.WaveObservableTransportGeometryRegimeHarmonyConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeBalance :
      KLRWOTGRBAL.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeBalanceTheorem

canonicalWaveObservableTransportGeometryRegimeBalanceConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRHARC.WaveObservableTransportGeometryRegimeHarmonyConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeBalanceConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeBalanceConsumer waveObsTransportGeometryRegimeHarmony =
  waveObservableTransportGeometryRegimeBalanceConsumer
    waveObsTransportGeometryRegimeHarmony
    KLRWOTGRBAL.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeBalanceTheorem
