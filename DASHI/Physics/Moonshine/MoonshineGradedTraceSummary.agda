module DASHI.Physics.Moonshine.MoonshineGradedTraceSummary where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshineOrbitTraceSummary as MOTS
open import DASHI.Physics.Moonshine.WaveGradedShellPrototypeSummary as WGSP

record MoonshineGradedTraceSummary : Set where
  field
    orbitTraceSummary : MOTS.MoonshineOrbitTraceSummary
    waveSummary : WGSP.WaveGradedShellPrototypeSummary
    gradedTraceCount : Nat

canonicalMoonshineGradedTraceSummary : MoonshineGradedTraceSummary
canonicalMoonshineGradedTraceSummary =
  record
    { orbitTraceSummary = MOTS.canonicalMoonshineOrbitTraceSummary
    ; waveSummary = WGSP.shiftWaveGradedShellPrototypeSummary
    ; gradedTraceCount =
        MOTS.MoonshineOrbitTraceSummary.orbitTraceCount
          MOTS.canonicalMoonshineOrbitTraceSummary
    }
