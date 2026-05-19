module DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_)
open import Data.List.Base using (_∷_; [])

open import DASHI.Physics.DashiDynamics as DD
open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.SchrodingerGap as SG
open import DASHI.Physics.SchrodingerAssumedTheorem as SAT
open import DASHI.Physics.ShiftPotentialQuadraticEnergy as SPQE
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Second Schrödinger-gap inhabitant with a structured wave carrier:
-- current pressure point + explicit amplitude + explicit phase proxy.
--
-- This still does not derive Schrödinger dynamics. It only lifts the wave
-- state above the raw pressure point so later wave-facing work no longer has
-- to start from a scalar-only carrier.

record ShiftWavePhaseState : Set where
  constructor mkShiftWavePhaseState
  field
    carrier : SPTI.ShiftPressurePoint
    amplitude : Nat
    phase : Nat
    amplitude-agrees : amplitude ≡ DDSI.shiftPointDensity carrier
    phase-agrees : phase ≡ DDSI.shiftHeldPotential carrier

canonicalWavePhaseState :
  SPTI.ShiftPressurePoint →
  ShiftWavePhaseState
canonicalWavePhaseState s =
  mkShiftWavePhaseState
    s
    (DDSI.shiftPointDensity s)
    (DDSI.shiftHeldPotential s)
    refl
    refl

advanceWavePhaseState :
  ShiftWavePhaseState →
  ShiftWavePhaseState
advanceWavePhaseState w =
  canonicalWavePhaseState
    (DDSI.shiftPressureAdvance (ShiftWavePhaseState.carrier w))

shiftPhaseWaveEvolve :
  ShiftWavePhaseState →
  DD.State DDSI.shiftDashiDynamics
shiftPhaseWaveEvolve w =
  DDSI.shiftPressureAdvance (ShiftWavePhaseState.carrier w)

shiftPhaseWaveDensity :
  ShiftWavePhaseState → Nat
shiftPhaseWaveDensity w =
  DDSI.shiftPointDensity (ShiftWavePhaseState.carrier w)

shiftPhaseWaveAmplitude :
  ShiftWavePhaseState → Nat
shiftPhaseWaveAmplitude =
  ShiftWavePhaseState.amplitude

shiftPhaseWavePhase :
  ShiftWavePhaseState → Nat
shiftPhaseWavePhase =
  ShiftWavePhaseState.phase

PhaseWaveDensityLaw : Set
PhaseWaveDensityLaw =
  (w : ShiftWavePhaseState) →
  shiftPhaseWaveDensity w ≤ shiftPhaseWaveDensity (advanceWavePhaseState w)

PhaseWaveAmplitudeLaw : Set
PhaseWaveAmplitudeLaw =
  (w : ShiftWavePhaseState) →
  shiftPhaseWaveAmplitude w ≤ shiftPhaseWaveAmplitude (advanceWavePhaseState w)

PhaseWavePhaseDescentLaw : Set
PhaseWavePhaseDescentLaw =
  (w : ShiftWavePhaseState) →
  shiftPhaseWavePhase (advanceWavePhaseState w) ≤ shiftPhaseWavePhase w

PhaseWaveInterferenceTransportLaw : Set
PhaseWaveInterferenceTransportLaw =
  (w : ShiftWavePhaseState) →
  shiftPhaseWaveAmplitude w + shiftPhaseWavePhase w
    ≡
  shiftPhaseWaveAmplitude (advanceWavePhaseState w)
    + shiftPhaseWavePhase (advanceWavePhaseState w)

shiftPhaseWaveDensityMonotone : PhaseWaveDensityLaw
shiftPhaseWaveDensityMonotone w =
  DDSI.shiftPointDensityMonotone (ShiftWavePhaseState.carrier w)

shiftPhaseWaveAmplitudeMonotone : PhaseWaveAmplitudeLaw
shiftPhaseWaveAmplitudeMonotone w
  rewrite ShiftWavePhaseState.amplitude-agrees w
        | ShiftWavePhaseState.amplitude-agrees (advanceWavePhaseState w) =
  DDSI.shiftPointDensityMonotone (ShiftWavePhaseState.carrier w)

shiftPhaseWavePhaseDescent : PhaseWavePhaseDescentLaw
shiftPhaseWavePhaseDescent w
  rewrite ShiftWavePhaseState.phase-agrees w
        | ShiftWavePhaseState.phase-agrees (advanceWavePhaseState w) =
  DDSI.shiftPotentialDescentWitness (ShiftWavePhaseState.carrier w)

shiftPhaseWaveInterferenceTransport : PhaseWaveInterferenceTransportLaw
shiftPhaseWaveInterferenceTransport w
  rewrite ShiftWavePhaseState.amplitude-agrees w
        | ShiftWavePhaseState.phase-agrees w
        | ShiftWavePhaseState.amplitude-agrees (advanceWavePhaseState w)
        | ShiftWavePhaseState.phase-agrees (advanceWavePhaseState w)
  with ShiftWavePhaseState.carrier w
... | SPTI.shiftStartPoint = refl
... | SPTI.shiftNextPoint = refl
... | SPTI.shiftHeldExitPoint = refl

ShiftPhaseWaveSchrodingerForm : Set
ShiftPhaseWaveSchrodingerForm =
  Σ PhaseWaveDensityLaw
    (λ _ →
      Σ PhaseWaveAmplitudeLaw
        (λ _ →
          Σ PhaseWavePhaseDescentLaw
            (λ _ → PhaseWaveInterferenceTransportLaw)))

shiftPhaseWaveSchrodingerWitness : ShiftPhaseWaveSchrodingerForm
shiftPhaseWaveSchrodingerWitness =
  shiftPhaseWaveDensityMonotone
  , (shiftPhaseWaveAmplitudeMonotone
     , (shiftPhaseWavePhaseDescent , shiftPhaseWaveInterferenceTransport))

shiftPhaseWaveSchrodingerGap :
  SG.SchrodingerGap Nat
shiftPhaseWaveSchrodingerGap =
  record
    { dynamics = DDSI.shiftDashiDynamics
    ; WaveState = ShiftWavePhaseState
    ; Hamiltonian = Nat
    ; evolve = shiftPhaseWaveEvolve
    ; densityContinuity = PhaseWaveDensityLaw
    ; amplitudeEvolution = PhaseWaveAmplitudeLaw
    ; schrodingerForm = ShiftPhaseWaveSchrodingerForm
    ; nonClaimBoundary =
        "Structured phase-wave shift inhabitant only"
        ∷ "WaveState carries carrier point, amplitude, and phase proxy"
        ∷ "amplitude is tied to empirical density-backed wave packaging"
        ∷ "phase is tied to held-potential descent on the current carrier"
        ∷ "interference transport is bounded by exact conservation of amplitude + phase on the current carrier"
        ∷ "Hamiltonian is still a finite scalar proxy"
        ∷ "No physical Schrodinger equation derivation is claimed"
        ∷ DD.nonClaimBoundary DDSI.shiftDashiDynamics
    }

shiftPhaseWaveHamiltonian :
  ShiftWavePhaseState → Nat
shiftPhaseWaveHamiltonian w =
  SPQE.shiftQuadraticEnergy (ShiftWavePhaseState.carrier w)

shiftPhaseWaveSchrodingerAssumedTheorem :
  SAT.SchrodingerAssumedTheorem shiftPhaseWaveSchrodingerGap
shiftPhaseWaveSchrodingerAssumedTheorem =
  SAT.assumedTheoremFromGap
    shiftPhaseWaveSchrodingerGap
    shiftPhaseWaveSchrodingerWitness
