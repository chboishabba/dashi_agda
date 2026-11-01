module DASHI.Physics.Moonshine.MoonshineTwinedWaveBundleSummary where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshinePrototypeComparisonBundle as MPCB
open import DASHI.Physics.Moonshine.MoonshineWaveTraceConsistencySummary as MWTCS

record MoonshineTwinedWaveBundleSummary : Set where
  field
    prototypeBundle : MPCB.MoonshinePrototypeComparisonBundle
    waveTraceConsistency : MWTCS.MoonshineWaveTraceConsistencySummary
    bundleSummaryCount : Nat

canonicalMoonshineTwinedWaveBundleSummary :
  MoonshineTwinedWaveBundleSummary
canonicalMoonshineTwinedWaveBundleSummary =
  record
    { prototypeBundle = MPCB.canonicalMoonshinePrototypeComparisonBundle
    ; waveTraceConsistency =
        MWTCS.canonicalMoonshineWaveTraceConsistencySummary
    ; bundleSummaryCount = 2
    }
