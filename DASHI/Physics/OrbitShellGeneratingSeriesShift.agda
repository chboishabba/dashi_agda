module DASHI.Physics.OrbitShellGeneratingSeriesShift where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.OrbitShellGeneratingSeries as OSG

shiftSeries : OSG.OrbitShellSeries
shiftSeries = OSG.seriesFromRaw (just 31) OPD.shell1_p3_q1 OPD.shell2_p3_q1

shiftSeries-shell1-source :
  OSG.OrbitShellSeries.shell1Terms shiftSeries
  ≡ OSG.compressSorted OPD.shell1_p3_q1
shiftSeries-shell1-source = refl

shiftSeries-shell2-source :
  OSG.OrbitShellSeries.shell2Terms shiftSeries
  ≡ OSG.compressSorted OPD.shell2_p3_q1
shiftSeries-shell2-source = refl

shiftSeries-orientation-source :
  OSG.OrbitShellSeries.orientationTag shiftSeries ≡ just 31
shiftSeries-orientation-source = refl

