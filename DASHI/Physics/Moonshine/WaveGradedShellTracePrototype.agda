module DASHI.Physics.Moonshine.WaveGradedShellTracePrototype where

open import Data.Unit.Polymorphic using (⊤)

open import DASHI.Physics.Moonshine.FiniteGradedShellSeriesShift as FGSSS
open import DASHI.Physics.Moonshine.WaveGradedShellModule as WGSM
open import DASHI.Physics.WaveLiftEvenSubalgebra as WLE

gradedPrototype : WLE.Graded WGSM.WaveGradedShellModule
gradedPrototype =
  record
    { even = λ _ → ⊤
    ; odd = λ _ → ⊤
    }

liftPrototype :
  WLE.WaveLift WGSM.WaveGradedShellModule WGSM.WaveGradedShellModule
liftPrototype =
  record { lift = λ x → x }

shiftWaveGradedShellModulePrototype : WGSM.WaveGradedShellModule
shiftWaveGradedShellModulePrototype =
  WGSM.fromFiniteSeries FGSSS.shiftFiniteGradedShellSeries

shiftWaveGradedShellPrototypeFactorsThroughEven :
  WLE.LiftFactorsThroughEven
    WGSM.WaveGradedShellModule
    WGSM.WaveGradedShellModule
shiftWaveGradedShellPrototypeFactorsThroughEven =
  WLE.waveLift⇒evenSubalgebra gradedPrototype liftPrototype
