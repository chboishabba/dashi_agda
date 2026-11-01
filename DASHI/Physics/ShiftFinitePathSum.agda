module DASHI.Physics.ShiftFinitePathSum where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Integer using (ℤ)

open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Bounded finite path-sum package over the current phase/discrete-wave
-- surfaces.
--
-- This is not a continuum path integral. It only sums two explicit finite
-- histories built from the current deterministic carrier advance.

step² :
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState
step² w =
  SPWSI.advanceWavePhaseState (SPWSI.advanceWavePhaseState w)

step³ :
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState
step³ w =
  SPWSI.advanceWavePhaseState (step² w)

record FinitePathHistory : Set where
  constructor mkFinitePathHistory
  field
    start : SPWSI.ShiftWavePhaseState
    middle : SPWSI.ShiftWavePhaseState
    end : SPWSI.ShiftWavePhaseState

primaryHistory :
  SPWSI.ShiftWavePhaseState →
  FinitePathHistory
primaryHistory w =
  mkFinitePathHistory w (SPWSI.advanceWavePhaseState w) (step² w)

shiftedHistory :
  SPWSI.ShiftWavePhaseState →
  FinitePathHistory
shiftedHistory w =
  mkFinitePathHistory
    (SPWSI.advanceWavePhaseState w)
    (step² w)
    (step³ w)

edgeWeight₀₁ :
  FinitePathHistory → ℤ
edgeWeight₀₁ h =
  SPTI4.phaseKernel4
    (SPTI4.phaseClass4 (FinitePathHistory.start h))
    (SPTI4.phaseClass4 (FinitePathHistory.middle h))

edgeWeight₁₂ :
  FinitePathHistory → ℤ
edgeWeight₁₂ h =
  SPTI4.phaseKernel4
    (SPTI4.phaseClass4 (FinitePathHistory.middle h))
    (SPTI4.phaseClass4 (FinitePathHistory.end h))

pathContribution :
  FinitePathHistory → SDWS.DiscreteWave
pathContribution h =
  SDWS.waveAdd
    (SDWS.scaleWave
      (edgeWeight₀₁ h)
      (SDWS.discreteWaveOf (FinitePathHistory.middle h)))
    (SDWS.scaleWave
      (edgeWeight₁₂ h)
      (SDWS.discreteWaveOf (FinitePathHistory.end h)))

boundedPathSum :
  SPWSI.ShiftWavePhaseState →
  SDWS.DiscreteWave
boundedPathSum w =
  SDWS.waveAdd
    (pathContribution (primaryHistory w))
    (pathContribution (shiftedHistory w))

record ShiftFinitePathSum : Setω where
  field
    History : Set
    primary :
      SPWSI.ShiftWavePhaseState → History
    shifted :
      SPWSI.ShiftWavePhaseState → History
    weight₀₁ :
      History → ℤ
    weight₁₂ :
      History → ℤ
    contribution :
      History → SDWS.DiscreteWave
    pathSum :
      SPWSI.ShiftWavePhaseState → SDWS.DiscreteWave
    nonClaimBoundary : List String

shiftFinitePathSum : ShiftFinitePathSum
shiftFinitePathSum =
  record
    { History = FinitePathHistory
    ; primary = primaryHistory
    ; shifted = shiftedHistory
    ; weight₀₁ = edgeWeight₀₁
    ; weight₁₂ = edgeWeight₁₂
    ; contribution = pathContribution
    ; pathSum = boundedPathSum
    ; nonClaimBoundary =
        "Finite path-sum package only"
        ∷ "path weights come from the four-class phase kernel on explicit finite histories"
        ∷ "the summed family contains exactly two bounded candidate histories"
        ∷ "No continuum path integral, measure theory, or analytic propagator claim is implied"
        ∷ []
    }
