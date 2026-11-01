module DASHI.Physics.Moonshine.FiniteGradedShellSeries where

open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Maybe using (Maybe; just; nothing)

record FiniteGradedShellSeries : Set where
  field
    orientationTag : Maybe Nat
    grade0Count : Nat
    grade1Count : Nat
    grade2Count : Nat

orientationCount : Maybe Nat → Nat
orientationCount (just _) = 1
orientationCount nothing = 0

seriesFromCounts : Maybe Nat → Nat → Nat → FiniteGradedShellSeries
seriesFromCounts orientation shell1Count shell2Count =
  record
    { orientationTag = orientation
    ; grade0Count = orientationCount orientation
    ; grade1Count = shell1Count
    ; grade2Count = shell2Count
    }
