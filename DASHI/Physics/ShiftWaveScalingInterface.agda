module DASHI.Physics.ShiftWaveScalingInterface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; -[1+_])
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS

------------------------------------------------------------------------
-- Theorem-thin scaling / refinement surface over the current shift-wave
-- carrier.
--
-- This is deliberately weaker than a continuum-limit claim. It only says
-- that the repo now has an explicit place to compare the same finite wave
-- dynamics across named scales, together with one discrete second-difference
-- operator over the existing Schrödinger-like step.

record ShiftWaveScalingInterface : Setω where
  field
    Scale : Set

    StateAt : Scale → Set

    embed :
      (σ τ : Scale) →
      StateAt σ → StateAt τ

    waveAt :
      (σ : Scale) →
      StateAt σ → SDWS.DiscreteWave

    stepAt :
      (σ : Scale) →
      StateAt σ → StateAt σ

    stepCompatibility : Set

    nonClaimBoundary : List String

data ShiftScale : Set where
  coarse fine : ShiftScale

StateAtShift : ShiftScale → Set
StateAtShift coarse = SPWSI.ShiftWavePhaseState
StateAtShift fine = SPWSI.ShiftWavePhaseState

embedShift :
  (σ τ : ShiftScale) →
  StateAtShift σ → StateAtShift τ
embedShift coarse coarse s = s
embedShift coarse fine s = s
embedShift fine coarse s = s
embedShift fine fine s = s

waveAtShift :
  (σ : ShiftScale) →
  StateAtShift σ → SDWS.DiscreteWave
waveAtShift coarse = SDWS.discreteWaveOf
waveAtShift fine = SDWS.discreteWaveOf

stepAtShift :
  (σ : ShiftScale) →
  StateAtShift σ → StateAtShift σ
stepAtShift coarse = SPWSI.advanceWavePhaseState
stepAtShift fine = SPWSI.advanceWavePhaseState

ShiftStepCompatibility : Set
ShiftStepCompatibility =
  (σ τ : ShiftScale) →
  (s : StateAtShift σ) →
  embedShift σ τ (stepAtShift σ s)
    ≡
  stepAtShift τ (embedShift σ τ s)

shiftStepCompatibility : ShiftStepCompatibility
shiftStepCompatibility coarse coarse s = refl
shiftStepCompatibility coarse fine s = refl
shiftStepCompatibility fine coarse s = refl
shiftStepCompatibility fine fine s = refl

shiftWaveScalingInterface : ShiftWaveScalingInterface
shiftWaveScalingInterface =
  record
    { Scale = ShiftScale
    ; StateAt = StateAtShift
    ; embed = embedShift
    ; waveAt = waveAtShift
    ; stepAt = stepAtShift
    ; stepCompatibility = ShiftStepCompatibility
    ; nonClaimBoundary =
        "Finite scaling interface only"
        ∷ "coarse/fine currently reuse the same carrier"
        ∷ "embed is identity packaging, not a geometric refinement theorem"
        ∷ "No limit, topology, derivative, or PDE claim is implied"
        ∷ []
    }

waveNeg : SDWS.DiscreteWave → SDWS.DiscreteWave
waveNeg ψ =
  SDWS.scaleWave (-[1+ 0 ]) ψ

waveSub :
  SDWS.DiscreteWave →
  SDWS.DiscreteWave →
  SDWS.DiscreteWave
waveSub ψ χ =
  SDWS.waveAdd ψ (waveNeg χ)

delta₁ :
  SDWS.DiscreteWave →
  SDWS.DiscreteWave →
  SDWS.DiscreteWave
delta₁ ψ ψ₁ = waveSub ψ₁ ψ

delta₂ :
  SDWS.DiscreteWave →
  SDWS.DiscreteWave →
  SDWS.DiscreteWave →
  SDWS.DiscreteWave
delta₂ ψ₀ ψ₁ ψ₂ =
  SDWS.waveAdd
    ψ₂
    (SDWS.waveAdd
      (SDWS.scaleWave (-[1+ 1 ]) ψ₁)
      ψ₀)

step1 :
  SPWSI.ShiftWavePhaseState →
  SDWS.DiscreteWave →
  SDWS.DiscreteWave
step1 w ψ = SDWS.shiftSchrodingerStep4 w ψ

step2 :
  SPWSI.ShiftWavePhaseState →
  SDWS.DiscreteWave →
  SDWS.DiscreteWave
step2 w ψ = step1 w (step1 w ψ)

discreteSecondDifference :
  SPWSI.ShiftWavePhaseState →
  SDWS.DiscreteWave →
  SDWS.DiscreteWave
discreteSecondDifference w ψ =
  delta₂ ψ (step1 w ψ) (step2 w ψ)
