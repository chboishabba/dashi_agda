module DASHI.Physics.Moonshine.MoonshineTwinedWaveRegimeSummary where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshineTwinedWaveFamilySummary as MTWFS
open import DASHI.Physics.Moonshine.MoonshineWaveTraceConsistencySummary as MWTCS

record MoonshineTwinedWaveRegimeSummary : Set where
  field
    familySummary : MTWFS.MoonshineTwinedWaveFamilySummary
    waveConsistency : MWTCS.MoonshineWaveTraceConsistencySummary
    summaryCount : Nat

canonicalMoonshineTwinedWaveRegimeSummary : MoonshineTwinedWaveRegimeSummary
canonicalMoonshineTwinedWaveRegimeSummary =
  record
    { familySummary = MTWFS.canonicalMoonshineTwinedWaveFamilySummary
    ; waveConsistency = MWTCS.canonicalMoonshineWaveTraceConsistencySummary
    ; summaryCount = 2
    }
