module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ResolutionConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.PrecisionConsumer as CWOTGRPRECC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRRSL = RWR

record WaveObservableTransportGeometryRegimeResolutionConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeResolutionConsumer
  field
    transportGeometryRegimePrecisionConsumer :
      CWOTGRPRECC.WaveObservableTransportGeometryRegimePrecisionConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeResolution :
      KLRWOTGRRSL.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeResolutionTheorem

canonicalWaveObservableTransportGeometryRegimeResolutionConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRPRECC.WaveObservableTransportGeometryRegimePrecisionConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeResolutionConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeResolutionConsumer prev =
  waveObservableTransportGeometryRegimeResolutionConsumer
    prev
    KLRWOTGRRSL.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeResolutionTheorem
