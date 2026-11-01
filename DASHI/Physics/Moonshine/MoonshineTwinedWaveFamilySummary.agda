module DASHI.Physics.Moonshine.MoonshineTwinedWaveFamilySummary where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshineTwinedWaveBundleSummary as MTWBS
open import DASHI.Physics.Moonshine.MoonshineTraceFamilySummary as MTFS

record MoonshineTwinedWaveFamilySummary : Set where
  field
    twinedWaveBundle : MTWBS.MoonshineTwinedWaveBundleSummary
    traceFamily : MTFS.MoonshineTraceFamilySummary
    familySummaryCount : Nat

canonicalMoonshineTwinedWaveFamilySummary :
  MoonshineTwinedWaveFamilySummary
canonicalMoonshineTwinedWaveFamilySummary =
  record
    { twinedWaveBundle = MTWBS.canonicalMoonshineTwinedWaveBundleSummary
    ; traceFamily = MTFS.canonicalMoonshineTraceFamilySummary
    ; familySummaryCount = 2
    }
