module DASHI.Physics.Moonshine.FiniteGradedShellSeriesRootSystemB4 where

open import Data.List.Base using (length)
open import Data.Maybe using (nothing)

open import DASHI.Physics.Moonshine.FiniteGradedShellSeries as FGSS
open import DASHI.Physics.RootSystemB4Carrier as B4

b4FiniteGradedShellSeries : FGSS.FiniteGradedShellSeries
b4FiniteGradedShellSeries =
  FGSS.seriesFromCounts
    nothing
    (length B4.shell1Points)
    (length B4.shell2Points)
