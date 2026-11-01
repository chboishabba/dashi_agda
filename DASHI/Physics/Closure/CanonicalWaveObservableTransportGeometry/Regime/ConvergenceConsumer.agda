module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ConvergenceConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.EquilibriumConsumer as CWOTGREQC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRCONV = RWR

record WaveObservableTransportGeometryRegimeConvergenceConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeConvergenceConsumer
  field
    transportGeometryRegimeEquilibriumConsumer :
      CWOTGREQC.WaveObservableTransportGeometryRegimeEquilibriumConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeConvergence :
      KLRWOTGRCONV.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeConvergenceTheorem

canonicalWaveObservableTransportGeometryRegimeConvergenceConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGREQC.WaveObservableTransportGeometryRegimeEquilibriumConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeConvergenceConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeConvergenceConsumer
    waveObservableTransportGeometryRegimeEquilibrium =
  waveObservableTransportGeometryRegimeConvergenceConsumer
    waveObservableTransportGeometryRegimeEquilibrium
    KLRWOTGRCONV.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeConvergenceTheorem
