module DASHI.Physics.ShiftPhaseWaveContinuumStory where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Finite continuum-style story over the structured phase-wave shift carrier.
--
-- This is still not a differential equation or continuum-limit theorem.
-- It only packages the finite proxy coordinates that are now available:
--   * a coarse transport coordinate,
--   * amplitude and phase fields,
--   * a conserved interference charge,
--   * and one exact coordinate/phase balance law.

shiftContinuumCoordinate :
  SPWSI.ShiftWavePhaseState → Nat
shiftContinuumCoordinate w =
  DDSI.shiftPressureRank (SPWSI.ShiftWavePhaseState.carrier w)

shiftContinuumAmplitude :
  SPWSI.ShiftWavePhaseState → Nat
shiftContinuumAmplitude =
  SPWSI.shiftPhaseWaveAmplitude

shiftContinuumPhase :
  SPWSI.ShiftWavePhaseState → Nat
shiftContinuumPhase =
  SPWSI.shiftPhaseWavePhase

shiftContinuumInterferenceCharge :
  SPWSI.ShiftWavePhaseState → Nat
shiftContinuumInterferenceCharge w =
  shiftContinuumAmplitude w + shiftContinuumPhase w

ShiftContinuumInterferenceChargeTransportLaw : Set
ShiftContinuumInterferenceChargeTransportLaw =
  (w : SPWSI.ShiftWavePhaseState) →
  shiftContinuumInterferenceCharge w
    ≡
  shiftContinuumInterferenceCharge (SPWSI.advanceWavePhaseState w)

shiftContinuumInterferenceChargeTransport :
  ShiftContinuumInterferenceChargeTransportLaw
shiftContinuumInterferenceChargeTransport w
  rewrite SPWSI.ShiftWavePhaseState.amplitude-agrees w
        | SPWSI.ShiftWavePhaseState.phase-agrees w
        | SPWSI.ShiftWavePhaseState.amplitude-agrees (SPWSI.advanceWavePhaseState w)
        | SPWSI.ShiftWavePhaseState.phase-agrees (SPWSI.advanceWavePhaseState w)
  with SPWSI.ShiftWavePhaseState.carrier w
... | SPTI.shiftStartPoint = refl
... | SPTI.shiftNextPoint = refl
... | SPTI.shiftHeldExitPoint = refl

ShiftContinuumCoordinatePhaseBalanceLaw : Set
ShiftContinuumCoordinatePhaseBalanceLaw =
  (w : SPWSI.ShiftWavePhaseState) →
  shiftContinuumCoordinate w + shiftContinuumPhase w
    ≡
  shiftContinuumCoordinate (SPWSI.advanceWavePhaseState w)
    + shiftContinuumPhase (SPWSI.advanceWavePhaseState w)

shiftContinuumCoordinatePhaseBalance :
  ShiftContinuumCoordinatePhaseBalanceLaw
shiftContinuumCoordinatePhaseBalance w
  rewrite SPWSI.ShiftWavePhaseState.phase-agrees w
        | SPWSI.ShiftWavePhaseState.phase-agrees (SPWSI.advanceWavePhaseState w)
  with SPWSI.ShiftWavePhaseState.carrier w
... | SPTI.shiftStartPoint = refl
... | SPTI.shiftNextPoint = refl
... | SPTI.shiftHeldExitPoint = refl

record ShiftPhaseWaveContinuumStory : Set₁ where
  field
    continuumCoordinate :
      SPWSI.ShiftWavePhaseState → Nat
    continuumAmplitude :
      SPWSI.ShiftWavePhaseState → Nat
    continuumPhase :
      SPWSI.ShiftWavePhaseState → Nat
    interferenceCharge :
      SPWSI.ShiftWavePhaseState → Nat
    interferenceChargeTransportLaw :
      ShiftContinuumInterferenceChargeTransportLaw
    interferenceTransportLaw :
      SPWSI.PhaseWaveInterferenceTransportLaw
    coordinatePhaseBalanceLaw :
      ShiftContinuumCoordinatePhaseBalanceLaw
    nonClaimBoundary : List String

shiftPhaseWaveContinuumStory :
  ShiftPhaseWaveContinuumStory
shiftPhaseWaveContinuumStory =
  record
    { continuumCoordinate = shiftContinuumCoordinate
    ; continuumAmplitude = shiftContinuumAmplitude
    ; continuumPhase = shiftContinuumPhase
    ; interferenceCharge = shiftContinuumInterferenceCharge
    ; interferenceChargeTransportLaw = shiftContinuumInterferenceChargeTransport
    ; interferenceTransportLaw = SPWSI.shiftPhaseWaveInterferenceTransport
    ; coordinatePhaseBalanceLaw = shiftContinuumCoordinatePhaseBalance
    ; nonClaimBoundary =
        "Finite continuum-style story only"
        ∷ "continuumCoordinate is a bounded transport proxy, not a spatial continuum coordinate"
        ∷ "interferenceCharge is exactly preserved by advance on the current finite carrier only"
        ∷ "interferenceChargeTransportLaw is a finite exactness witness, not a PDE or scaling-limit theorem"
        ∷ "coordinatePhaseBalanceLaw is a finite transport balance, not a PDE or scaling-limit theorem"
        ∷ "No continuum-limit Schrodinger equation is implied"
        ∷ []
    }
