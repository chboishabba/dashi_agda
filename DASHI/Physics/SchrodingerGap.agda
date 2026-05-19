module DASHI.Physics.SchrodingerGap where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)

open import DASHI.Physics.DashiDynamics as DD
open import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS

------------------------------------------------------------------------
-- Theorem-thin Schrödinger-facing consumer over DashiDynamics.
--
-- This module does not claim a derived Schrödinger equation, Hamiltonian
-- proof, or Standard Model bridge. It only provides a bounded packaging
-- surface where a caller may supply:
--   * a wave-state carrier,
--   * a Hamiltonian carrier,
--   * an evolution map into the existing DashiDynamics state carrier,
--   * witness slots for density continuity, amplitude evolution, and
--     Schrödinger-form presentation.

record SchrodingerGap
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    dynamics : DD.DashiDynamics {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    WaveState : Set
    Hamiltonian : Set

    evolve : WaveState → DD.State dynamics

    densityContinuity : Set
    amplitudeEvolution : Set
    schrodingerForm : Set

    nonClaimBoundary : List String

open SchrodingerGap public

gapInterfaceLabel :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  SchrodingerGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  String
gapInterfaceLabel gap = DD.interfaceLabel (dynamics gap)

gapEmpiricalStatuses :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  SchrodingerGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  List PEVS.ValidationStatus
gapEmpiricalStatuses gap =
  DD.empiricalValidationStatuses (dynamics gap)

gapHeldControlPressureStatus :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  SchrodingerGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  OSPT.PhysicsPressureStatus
gapHeldControlPressureStatus gap =
  DD.heldControlPressureStatus (dynamics gap)

mkSchrodingerGap :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (dynamics : DD.DashiDynamics {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (WaveState : Set) →
  (Hamiltonian : Set) →
  (evolve : WaveState → DD.State dynamics) →
  Set →
  Set →
  Set →
  SchrodingerGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkSchrodingerGap dynamics WaveState Hamiltonian evolve
  densityContinuity amplitudeEvolution schrodingerForm =
  record
    { dynamics = dynamics
    ; WaveState = WaveState
    ; Hamiltonian = Hamiltonian
    ; evolve = evolve
    ; densityContinuity = densityContinuity
    ; amplitudeEvolution = amplitudeEvolution
    ; schrodingerForm = schrodingerForm
    ; nonClaimBoundary =
        "SchrodingerGap is interface packaging only"
        ∷ "schrodingerForm is a supplied witness slot, not a derived theorem"
        ∷ "densityContinuity and amplitudeEvolution are witness slots, not proofs"
        ∷ "No Standard Model or closure claim is implied"
        ∷ DD.nonClaimBoundary dynamics
    }
