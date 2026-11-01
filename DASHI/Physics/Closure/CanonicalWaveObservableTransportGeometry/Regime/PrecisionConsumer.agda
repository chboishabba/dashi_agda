module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.PrecisionConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.RefinementConsumer as CWOTGRREFC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRPREC = RWR

record WaveObservableTransportGeometryRegimePrecisionConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimePrecisionConsumer
  field
    transportGeometryRegimeRefinementConsumer :
      CWOTGRREFC.WaveObservableTransportGeometryRegimeRefinementConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimePrecision :
      KLRWOTGRPREC.KnownLimitsRecoveredWaveObservableTransportGeometryRegimePrecisionTheorem

canonicalWaveObservableTransportGeometryRegimePrecisionConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRREFC.WaveObservableTransportGeometryRegimeRefinementConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimePrecisionConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimePrecisionConsumer prev =
  waveObservableTransportGeometryRegimePrecisionConsumer
    prev
    KLRWOTGRPREC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimePrecisionTheorem
