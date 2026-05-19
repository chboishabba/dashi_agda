module DASHI.Physics.CLOCKPhaseSummaryBundle where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Sum using (_⊎_)

open import DASHI.Physics.CLOCKPhaseBridge using (step²)
open import DASHI.Physics.CLOCKPhaseInstance as CPI

record ClockSummaryBundle : Set₁ where
  field
    closure : CPI.EffectiveClockClosure
    cone    : CPI.EffectiveClockCone
    bridge  : CPI.PhasePhysicsBridgeStep²
    sector  : CPI.EffectiveClockSectorBridge

clockSummaryBundle : ClockSummaryBundle
clockSummaryBundle =
  record
    { closure = CPI.clockEffectiveClosure
    ; cone = CPI.clockEffectiveCone
    ; bridge = CPI.clockBridgeStep²
    ; sector = CPI.clockSectorBridge
    }

record ClockSectorEntryBundle : Set₁ where
  field
    normalize        : CPI.ClockState → CPI.ClockState
    normalize-inv    : ∀ x → CPI.strobeInv (normalize x)
    normalize-entry  :
      ∀ x →
      normalize x ≡ x ⊎ normalize x ≡ CPI.clockStep x
    normalize-step²  :
      ∀ x →
      step² CPI.clockLift (normalize x) ≡
      CPI.strobeEmbed (CPI.strobeStep (CPI.strobeProject (normalize x)))

clockSectorEntryBundle : ClockSectorEntryBundle
clockSectorEntryBundle =
  record
    { normalize = CPI.normalizeToStrobe
    ; normalize-inv = CPI.normalizeToStrobe-inv
    ; normalize-entry = CPI.normalizeToStrobe-is-step-if-needed
    ; normalize-step² = CPI.normalizeToStrobe-step²
    }

record ClockClosureConsumer : Set₁ where
  field
    summary : ClockSummaryBundle
    entry   : ClockSectorEntryBundle

clockClosureConsumer : ClockClosureConsumer
clockClosureConsumer =
  record
    { summary = clockSummaryBundle
    ; entry = clockSectorEntryBundle
    }
