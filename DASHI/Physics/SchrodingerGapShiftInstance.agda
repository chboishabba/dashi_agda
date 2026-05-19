module DASHI.Physics.SchrodingerGapShiftInstance where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_)
open import Data.List.Base using (_∷_; [])

open import DASHI.Physics.DashiDynamics as DD
open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.SchrodingerGap as SG
open import DASHI.Physics.SchrodingerAssumedTheorem as SAT
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- First non-placeholder Schrödinger-gap inhabitant over the shift lane.
--
-- This module still does not derive Schrödinger dynamics. It only exposes
-- one bounded pressure-ordered endomap on the existing three-point carrier
-- and proves monotonicity for density and amplitude proxies tied to that
-- order.

ShiftWaveState : Set
ShiftWaveState = SPTI.ShiftPressurePoint

shiftEvolve : ShiftWaveState → DD.State DDSI.shiftDashiDynamics
shiftEvolve = DDSI.shiftPressureAdvance

shiftDensity : ShiftWaveState → Nat
shiftDensity = DDSI.shiftPointDensity

shiftAmplitude : ShiftWaveState → Nat
shiftAmplitude = DDSI.shiftPressureRank

GapDensityLaw : Set
GapDensityLaw =
  (s : ShiftWaveState) → shiftDensity s ≤ shiftDensity (shiftEvolve s)

GapAmplitudeLaw : Set
GapAmplitudeLaw =
  (s : ShiftWaveState) → shiftAmplitude s ≤ shiftAmplitude (shiftEvolve s)

shiftDensityMonotone : GapDensityLaw
shiftDensityMonotone = DDSI.shiftPointDensityMonotone

shiftAmplitudeMonotone : GapAmplitudeLaw
shiftAmplitudeMonotone = DDSI.shiftPressureRankMonotone

ShiftSchrodingerForm : Set
ShiftSchrodingerForm = Σ GapDensityLaw (λ _ → GapAmplitudeLaw)

shiftSchrodingerFormWitness : ShiftSchrodingerForm
shiftSchrodingerFormWitness = shiftDensityMonotone , shiftAmplitudeMonotone

shiftSchrodingerGap :
  SG.SchrodingerGap Nat
shiftSchrodingerGap =
  record
    { dynamics = DDSI.shiftDashiDynamics
    ; WaveState = ShiftWaveState
    ; Hamiltonian = Nat
    ; evolve = shiftEvolve
    ; densityContinuity = GapDensityLaw
    ; amplitudeEvolution = GapAmplitudeLaw
    ; schrodingerForm = ShiftSchrodingerForm
    ; nonClaimBoundary =
        "Pressure-ordered shift inhabitant only"
        ∷ "evolve follows the bounded three-point pressure order"
        ∷ "density is empirical densityProxy plus pressure rank"
        ∷ "amplitude is a pressure-rank proxy only"
        ∷ "No physical Schrodinger equation derivation is claimed"
        ∷ DD.nonClaimBoundary DDSI.shiftDashiDynamics
    }

shiftSchrodingerAssumedTheorem :
  SAT.SchrodingerAssumedTheorem shiftSchrodingerGap
shiftSchrodingerAssumedTheorem =
  SAT.assumedTheoremFromGap
    shiftSchrodingerGap
    shiftSchrodingerFormWitness
