module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.SymmetryConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.BalanceConsumer as CWOTGRBALC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRSYM = RWR

record WaveObservableTransportGeometryRegimeSymmetryConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeSymmetryConsumer
  field
    transportGeometryRegimeBalanceConsumer :
      CWOTGRBALC.WaveObservableTransportGeometryRegimeBalanceConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeSymmetry :
      KLRWOTGRSYM.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeSymmetryTheorem

canonicalWaveObservableTransportGeometryRegimeSymmetryConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRBALC.WaveObservableTransportGeometryRegimeBalanceConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeSymmetryConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeSymmetryConsumer waveObsTransportGeometryRegimeBalance =
  waveObservableTransportGeometryRegimeSymmetryConsumer
    waveObsTransportGeometryRegimeBalance
    KLRWOTGRSYM.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeSymmetryTheorem
