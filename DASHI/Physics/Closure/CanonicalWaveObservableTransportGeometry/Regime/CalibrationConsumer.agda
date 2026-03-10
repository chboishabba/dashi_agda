module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.CalibrationConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ResolutionConsumer as CWOTGRRSLC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRCAL = RWR

record WaveObservableTransportGeometryRegimeCalibrationConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeCalibrationConsumer
  field
    transportGeometryRegimeResolutionConsumer :
      CWOTGRRSLC.WaveObservableTransportGeometryRegimeResolutionConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeCalibration :
      KLRWOTGRCAL.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeCalibrationTheorem

canonicalWaveObservableTransportGeometryRegimeCalibrationConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRRSLC.WaveObservableTransportGeometryRegimeResolutionConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeCalibrationConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeCalibrationConsumer prev =
  waveObservableTransportGeometryRegimeCalibrationConsumer
    prev
    KLRWOTGRCAL.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeCalibrationTheorem
