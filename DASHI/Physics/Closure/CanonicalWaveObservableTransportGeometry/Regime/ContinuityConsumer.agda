module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ContinuityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.SymmetryConsumer as CWOTGRSYMC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRCONT = RWR

record WaveObservableTransportGeometryRegimeContinuityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeContinuityConsumer
  field
    transportGeometryRegimeSymmetryConsumer :
      CWOTGRSYMC.WaveObservableTransportGeometryRegimeSymmetryConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeContinuity :
      KLRWOTGRCONT.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeContinuityTheorem

canonicalWaveObservableTransportGeometryRegimeContinuityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRSYMC.WaveObservableTransportGeometryRegimeSymmetryConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeContinuityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeContinuityConsumer waveObsTransportGeometryRegimeSymmetry =
  waveObservableTransportGeometryRegimeContinuityConsumer
    waveObsTransportGeometryRegimeSymmetry
    KLRWOTGRCONT.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeContinuityTheorem
