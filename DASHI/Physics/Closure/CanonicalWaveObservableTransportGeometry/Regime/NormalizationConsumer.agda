module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.NormalizationConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.CalibrationConsumer as CWOTGRCALC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRNORM = RWR

record WaveObservableTransportGeometryRegimeNormalizationConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeNormalizationConsumer
  field
    transportGeometryRegimeCalibrationConsumer :
      CWOTGRCALC.WaveObservableTransportGeometryRegimeCalibrationConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeNormalization :
      KLRWOTGRNORM.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeNormalizationTheorem

canonicalWaveObservableTransportGeometryRegimeNormalizationConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRCALC.WaveObservableTransportGeometryRegimeCalibrationConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeNormalizationConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeNormalizationConsumer prev =
  waveObservableTransportGeometryRegimeNormalizationConsumer
    prev
    KLRWOTGRNORM.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeNormalizationTheorem
