module DASHI.Physics.Closure.CanonicalWaveObservableGeometryConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableConsumer as CWOC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableGeometryTheorem as KLRWOG

record WaveObservableGeometryConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableGeometryConsumer
  field
    waveObservableConsumer :
      CWOC.WaveObservableConsumerFromMinimal cl
    recoveredWaveObservableGeometry :
      KLRWOG.KnownLimitsRecoveredWaveObservableGeometryTheorem

canonicalWaveObservableGeometryConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOC.WaveObservableConsumerFromMinimal cl →
  WaveObservableGeometryConsumerFromMinimal cl
canonicalWaveObservableGeometryConsumer waveObs =
  waveObservableGeometryConsumer
    waveObs
    KLRWOG.canonicalKnownLimitsRecoveredWaveObservableGeometryTheorem
