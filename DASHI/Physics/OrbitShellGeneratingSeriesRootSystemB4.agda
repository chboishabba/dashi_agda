module DASHI.Physics.OrbitShellGeneratingSeriesRootSystemB4 where

open import Data.Maybe using (nothing)

open import DASHI.Physics.OrbitProfileComputedRootSystemB4 as ORB4
open import DASHI.Physics.OrbitShellGeneratingSeries as OSG

b4Series : OSG.OrbitShellSeries
b4Series =
  OSG.seriesFromRaw nothing ORB4.b4-shell1-computed ORB4.b4-shell2-computed

