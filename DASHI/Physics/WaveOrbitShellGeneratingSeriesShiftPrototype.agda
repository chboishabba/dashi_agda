module DASHI.Physics.WaveOrbitShellGeneratingSeriesShiftPrototype where

open import Data.Unit.Polymorphic using (⊤)

open import DASHI.Physics.OrbitShellGeneratingSeriesShift as OSGS
open import DASHI.Physics.WaveLiftEvenSubalgebra as WLE
open import DASHI.Physics.WaveOrbitShellGeneratingSeries as WOSG

gradedPrototype : WLE.Graded WOSG.WaveOrbitShellSeries
gradedPrototype =
  record
    { even = λ _ → ⊤
    ; odd = λ _ → ⊤
    }

liftPrototype : WLE.WaveLift WOSG.WaveOrbitShellSeries WOSG.WaveOrbitShellSeries
liftPrototype =
  record
    { lift = λ x → x }

shiftWaveSeriesPrototype : WOSG.WaveOrbitShellSeries
shiftWaveSeriesPrototype =
  WOSG.prototypeFromWaveLift gradedPrototype liftPrototype OSGS.shiftSeries

shiftWaveSeriesFactorsThroughEven :
  WLE.LiftFactorsThroughEven
    WOSG.WaveOrbitShellSeries
    WOSG.WaveOrbitShellSeries
shiftWaveSeriesFactorsThroughEven =
  WLE.waveLift⇒evenSubalgebra gradedPrototype liftPrototype

