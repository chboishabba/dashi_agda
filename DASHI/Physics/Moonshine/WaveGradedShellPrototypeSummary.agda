module DASHI.Physics.Moonshine.WaveGradedShellPrototypeSummary where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Moonshine.FiniteGradedShellSeries as FGSS
open import DASHI.Physics.Moonshine.FiniteGradedShellSeriesShift as FGSSS
open import DASHI.Physics.Moonshine.WaveGradedShellModule as WGSM
open import DASHI.Physics.Moonshine.WaveGradedShellTracePrototype as WGSTP

record WaveGradedShellPrototypeSummary : Set where
  field
    moduleValue : WGSM.WaveGradedShellModule
    grade0Preserved :
      WGSM.WaveGradedShellModule.grade0Count moduleValue
      ≡ FGSS.FiniteGradedShellSeries.grade0Count FGSSS.shiftFiniteGradedShellSeries
    grade1Preserved :
      WGSM.WaveGradedShellModule.grade1Count moduleValue
      ≡ FGSS.FiniteGradedShellSeries.grade1Count FGSSS.shiftFiniteGradedShellSeries
    grade2Preserved :
      WGSM.WaveGradedShellModule.grade2Count moduleValue
      ≡ FGSS.FiniteGradedShellSeries.grade2Count FGSSS.shiftFiniteGradedShellSeries

shiftWaveGradedShellPrototypeSummary : WaveGradedShellPrototypeSummary
shiftWaveGradedShellPrototypeSummary =
  record
    { moduleValue = WGSTP.shiftWaveGradedShellModulePrototype
    ; grade0Preserved = refl
    ; grade1Preserved = refl
    ; grade2Preserved = refl
    }
