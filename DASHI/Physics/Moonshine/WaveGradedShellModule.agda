module DASHI.Physics.Moonshine.WaveGradedShellModule where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.FiniteGradedShellSeries as FGSS

record WaveGradedShellModule : Set where
  field
    baseSeries : FGSS.FiniteGradedShellSeries
    grade0Count : Nat
    grade1Count : Nat
    grade2Count : Nat

fromFiniteSeries : FGSS.FiniteGradedShellSeries → WaveGradedShellModule
fromFiniteSeries series =
  record
    { baseSeries = series
    ; grade0Count = FGSS.FiniteGradedShellSeries.grade0Count series
    ; grade1Count = FGSS.FiniteGradedShellSeries.grade1Count series
    ; grade2Count = FGSS.FiniteGradedShellSeries.grade2Count series
    }
