module DASHI.Physics.Moonshine.MoonshineTwinedWaveObservableSummary where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshineTwinedWaveRegimeSummary as MTWRS
open import DASHI.Physics.Moonshine.MoonshineTraceFamilySummary as MTFS

record MoonshineTwinedWaveObservableSummary : Set where
  field
    regimeSummary : MTWRS.MoonshineTwinedWaveRegimeSummary
    traceFamily : MTFS.MoonshineTraceFamilySummary
    summaryCount : Nat

canonicalMoonshineTwinedWaveObservableSummary :
  MoonshineTwinedWaveObservableSummary
canonicalMoonshineTwinedWaveObservableSummary =
  record
    { regimeSummary = MTWRS.canonicalMoonshineTwinedWaveRegimeSummary
    ; traceFamily = MTFS.canonicalMoonshineTraceFamilySummary
    ; summaryCount = 2
    }
