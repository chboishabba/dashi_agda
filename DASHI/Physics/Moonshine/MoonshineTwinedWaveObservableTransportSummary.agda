module DASHI.Physics.Moonshine.MoonshineTwinedWaveObservableTransportSummary where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshineTwinedWaveObservableSummary as MTWOS
open import DASHI.Physics.Moonshine.MoonshineWaveTraceConsistencySummary as MWTCS

record MoonshineTwinedWaveObservableTransportSummary : Set where
  constructor moonshineTwinedWaveObservableTransportSummary
  field
    waveObservableSummary : MTWOS.MoonshineTwinedWaveObservableSummary
    waveTraceConsistency : MWTCS.MoonshineWaveTraceConsistencySummary
    summaryCount : Nat

canonicalMoonshineTwinedWaveObservableTransportSummary :
  MoonshineTwinedWaveObservableTransportSummary
canonicalMoonshineTwinedWaveObservableTransportSummary =
  moonshineTwinedWaveObservableTransportSummary
    MTWOS.canonicalMoonshineTwinedWaveObservableSummary
    MWTCS.canonicalMoonshineWaveTraceConsistencySummary
    2
