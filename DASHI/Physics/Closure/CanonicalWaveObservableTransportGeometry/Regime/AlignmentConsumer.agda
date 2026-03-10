module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.AlignmentConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.EquilibriumConsumer as CWOTGREQC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRALIGN = RWR

record WaveObservableTransportGeometryRegimeAlignmentConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeAlignmentConsumer
  field
    transportGeometryRegimeEquilibriumConsumer :
      CWOTGREQC.WaveObservableTransportGeometryRegimeEquilibriumConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeAlignment :
      KLRWOTGRALIGN.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeAlignmentTheorem

canonicalWaveObservableTransportGeometryRegimeAlignmentConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGREQC.WaveObservableTransportGeometryRegimeEquilibriumConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeAlignmentConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeAlignmentConsumer prev =
  waveObservableTransportGeometryRegimeAlignmentConsumer
    prev
    KLRWOTGRALIGN.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeAlignmentTheorem
