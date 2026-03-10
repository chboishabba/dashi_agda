module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.EquilibriumConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.CohesionConsumer as CWOTGRCOHC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGREQ = RWR

record WaveObservableTransportGeometryRegimeEquilibriumConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeEquilibriumConsumer
  field
    transportGeometryRegimeCohesionConsumer :
      CWOTGRCOHC.WaveObservableTransportGeometryRegimeCohesionConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeEquilibrium :
      KLRWOTGREQ.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeEquilibriumTheorem

canonicalWaveObservableTransportGeometryRegimeEquilibriumConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRCOHC.WaveObservableTransportGeometryRegimeCohesionConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeEquilibriumConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeEquilibriumConsumer waveObsTransportGeometryRegimeCohesion =
  waveObservableTransportGeometryRegimeEquilibriumConsumer
    waveObsTransportGeometryRegimeCohesion
    KLRWOTGREQ.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeEquilibriumTheorem
