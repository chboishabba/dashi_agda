module DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.ClarityConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometry.Regime.TransparencyConsumer as CWOTGRTRNC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
module KLRWOTGRCLR = RWR

record WaveObservableTransportGeometryRegimeClarityConsumerFromMinimal
         (cl : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  constructor waveObservableTransportGeometryRegimeClarityConsumer
  field
    transportGeometryRegimeTransparencyConsumer :
      CWOTGRTRNC.WaveObservableTransportGeometryRegimeTransparencyConsumerFromMinimal cl
    recoveredWaveObservableTransportGeometryRegimeClarity :
      KLRWOTGRCLR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeClarityTheorem

canonicalWaveObservableTransportGeometryRegimeClarityConsumer :
  {cl : MCPC.MinimalCrediblePhysicsClosure} →
  CWOTGRTRNC.WaveObservableTransportGeometryRegimeTransparencyConsumerFromMinimal cl →
  WaveObservableTransportGeometryRegimeClarityConsumerFromMinimal cl
canonicalWaveObservableTransportGeometryRegimeClarityConsumer prev =
  waveObservableTransportGeometryRegimeClarityConsumer
    prev
    KLRWOTGRCLR.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeClarityTheorem
