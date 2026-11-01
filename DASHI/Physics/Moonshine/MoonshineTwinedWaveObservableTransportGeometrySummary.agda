module DASHI.Physics.Moonshine.MoonshineTwinedWaveObservableTransportGeometrySummary where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshineTwinedWaveObservableTransportSummary as MTWOTS
open import DASHI.Physics.Moonshine.MoonshineTwinedWaveObservableSummary as MTWOS

record MoonshineTwinedWaveObservableTransportGeometrySummary : Set where
  constructor moonshineTwinedWaveObservableTransportGeometrySummary
  field
    waveObservableTransportSummary :
      MTWOTS.MoonshineTwinedWaveObservableTransportSummary
    waveObservableSummary : MTWOS.MoonshineTwinedWaveObservableSummary
    summaryCount : Nat

canonicalMoonshineTwinedWaveObservableTransportGeometrySummary :
  MoonshineTwinedWaveObservableTransportGeometrySummary
canonicalMoonshineTwinedWaveObservableTransportGeometrySummary =
  moonshineTwinedWaveObservableTransportGeometrySummary
    MTWOTS.canonicalMoonshineTwinedWaveObservableTransportSummary
    MTWOS.canonicalMoonshineTwinedWaveObservableSummary
    2
