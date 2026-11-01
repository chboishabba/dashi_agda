module DASHI.Physics.Moonshine.FiniteGradedShellSeriesShift where

open import Data.List.Base using (length)
open import Data.Maybe using (just)

open import DASHI.Physics.Moonshine.FiniteGradedShellSeries as FGSS
open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPCSP

shiftFiniteGradedShellSeries : FGSS.FiniteGradedShellSeries
shiftFiniteGradedShellSeries =
  FGSS.seriesFromCounts
    (just 31)
    (length (OPCSP.shellList 1))
    (length (OPCSP.shellList 2))
