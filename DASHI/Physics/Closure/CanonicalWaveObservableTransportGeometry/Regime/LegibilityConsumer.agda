module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.LegibilityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.FidelityConsumer as CWOTGRFIDC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRLEG = RWR

record WaveObservableTransportGeometryRegimeLegibilityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeLegibilityConsumer
  field
    transportGeometryRegimeFidelityConsumer :
      CWOTGRFIDC.WaveObservableTransportGeometryRegimeFidelityConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeLegibility :
      KLRWOTGRLEG.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeLegibilityTheorem

canonicalWaveObservableTransportGeometryRegimeLegibilityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRFIDC.WaveObservableTransportGeometryRegimeFidelityConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeLegibilityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeLegibilityConsumer
    waveObservableTransportGeometryRegimeFidelity =
  waveObservableTransportGeometryRegimeLegibilityConsumer
    waveObservableTransportGeometryRegimeFidelity
    KLRWOTGRLEG.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeLegibilityTheorem
