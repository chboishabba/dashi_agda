module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.RefinementConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.AlignmentConsumer as CWOTGRALIGNC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRREF = RWR

record WaveObservableTransportGeometryRegimeRefinementConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeRefinementConsumer
  field
    transportGeometryRegimeAlignmentConsumer :
      CWOTGRALIGNC.WaveObservableTransportGeometryRegimeAlignmentConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeRefinement :
      KLRWOTGRREF.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeRefinementTheorem

canonicalWaveObservableTransportGeometryRegimeRefinementConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRALIGNC.WaveObservableTransportGeometryRegimeAlignmentConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeRefinementConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeRefinementConsumer prev =
  waveObservableTransportGeometryRegimeRefinementConsumer
    prev
    KLRWOTGRREF.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeRefinementTheorem
