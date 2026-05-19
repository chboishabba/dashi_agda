module DASHI.Physics.ShiftDiscreteContinuityCurrent where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
open import DASHI.Physics.ShiftDiscreteWaveEnergy as SDWE
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import DASHI.Physics.ShiftWaveGlobalUpdate as SWGU

------------------------------------------------------------------------
-- Finite continuity/current surface over the current discrete wave system.
--
-- This package intentionally mixes two exact finite stories:
--   * field-local energy and stencil-current magnitudes on the three-point
--     discrete wave field,
--   * a conserved amplitude+phase charge on the structured wave-state carrier.
--
-- It is a bookkeeping surface only. No PDE continuity equation, Noether
-- theorem, or conserved Hilbert current is claimed.

coarseLocalEnergy :
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  ℤ
coarseLocalEnergy ψ s =
  SDWE.waveNormSq (ψ s)

coarseUpdatedLocalEnergy :
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  ℤ
coarseUpdatedLocalEnergy ψ s =
  SDWE.waveNormSq (SWGU.coarseGlobalUpdate ψ s)

coarseLocalCurrentMagnitude :
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  ℤ
coarseLocalCurrentMagnitude ψ s =
  SDWE.waveNormSq (SSL.shiftSpatialLaplacian ψ s)

continuityCharge :
  SPWSI.ShiftWavePhaseState →
  Nat
continuityCharge w =
  SPWSI.shiftPhaseWaveAmplitude w + SPWSI.shiftPhaseWavePhase w

phaseInteractionCurrent :
  SPTI4.ShiftWavePairState →
  ℤ
phaseInteractionCurrent p =
  SPTI4.shiftPhaseInteraction4
    (SPTI4.ShiftWavePairState.left p)
    (SPTI4.ShiftWavePairState.right p)

interferenceCurrent :
  SPTI4.ShiftWavePairState →
  ℤ
interferenceCurrent p =
  SPTI4.shiftInterferenceIntensity4
    (SPTI4.ShiftWavePairState.left p)
    (SPTI4.ShiftWavePairState.right p)

ContinuityChargeLaw : Set
ContinuityChargeLaw =
  (w : SPWSI.ShiftWavePhaseState) →
  continuityCharge w
    ≡
  continuityCharge (SPWSI.advanceWavePhaseState w)

continuityChargeWitness :
  ContinuityChargeLaw
continuityChargeWitness =
  SPWSI.shiftPhaseWaveInterferenceTransport

record ShiftDiscreteContinuityCurrent : Setω where
  field
    WaveState : Set
    PairState : Set
    localEnergy :
      SSL.ShiftWaveField →
      SPTI.ShiftPressurePoint →
      ℤ
    updatedEnergy :
      SSL.ShiftWaveField →
      SPTI.ShiftPressurePoint →
      ℤ
    localCurrent :
      SSL.ShiftWaveField →
      SPTI.ShiftPressurePoint →
      ℤ
    pairInteractionCurrent :
      PairState → ℤ
    pairInterferenceCurrent :
      PairState → ℤ
    charge :
      WaveState → Nat
    chargeContinuity : Set
    nonClaimBoundary : List String

shiftDiscreteContinuityCurrent :
  ShiftDiscreteContinuityCurrent
shiftDiscreteContinuityCurrent =
  record
    { WaveState = SPWSI.ShiftWavePhaseState
    ; PairState = SPTI4.ShiftWavePairState
    ; localEnergy = coarseLocalEnergy
    ; updatedEnergy = coarseUpdatedLocalEnergy
    ; localCurrent = coarseLocalCurrentMagnitude
    ; pairInteractionCurrent = phaseInteractionCurrent
    ; pairInterferenceCurrent = interferenceCurrent
    ; charge = continuityCharge
    ; chargeContinuity = ContinuityChargeLaw
    ; nonClaimBoundary =
        "Finite discrete continuity/current package only"
        ∷ "field-local current is the square norm of the current three-point Laplacian stencil"
        ∷ "pair currents are finite phase-table observables on the structured carrier"
        ∷ "charge continuity is exact conservation of amplitude + phase under one finite advance step"
        ∷ "No PDE continuity equation, Noether theorem, or Hilbert-space probability current is implied"
        ∷ []
    }
