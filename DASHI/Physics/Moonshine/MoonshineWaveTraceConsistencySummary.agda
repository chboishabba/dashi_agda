module DASHI.Physics.Moonshine.MoonshineWaveTraceConsistencySummary where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshineOrbitTraceSummary as MOTS
open import DASHI.Physics.Moonshine.WaveGradedShellPrototypeSummary as WGSPS

record MoonshineWaveTraceConsistencySummary : Set where
  field
    orbitTraceSummary : MOTS.MoonshineOrbitTraceSummary
    wavePrototypeSummary : WGSPS.WaveGradedShellPrototypeSummary
    consistencyGradeCount : Nat

canonicalMoonshineWaveTraceConsistencySummary :
  MoonshineWaveTraceConsistencySummary
canonicalMoonshineWaveTraceConsistencySummary =
  record
    { orbitTraceSummary = MOTS.canonicalMoonshineOrbitTraceSummary
    ; wavePrototypeSummary = WGSPS.shiftWaveGradedShellPrototypeSummary
    ; consistencyGradeCount = 3
    }
