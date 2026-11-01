module DASHI.Physics.DashiDynamics where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

open import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureConsumer as SOSPC

------------------------------------------------------------------------
-- Theorem-thin unifying interface over the current packaged carriers.
--
-- This module does not claim that action, density, amplitude, reduction,
-- or empirical packaging have already been derived from one another.
-- It only states the intended interface boundary:
--   * a dynamics-facing carrier with state/path/observable/scalar slots,
--   * one packaged empirical validation carrier,
--   * one packaged held/control pressure consumer,
--   * one bounded convergence law for the concrete dynamics witness,
--   * explicit non-claim boundary strings.

record DashiDynamics
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    ------------------------------------------------------------------
    -- Core dynamics-facing interfaces
    State      : Set ℓs
    Path       : State → State → Set ℓp
    Observable : Set ℓo
    Scalar     : Set ℓq

    ------------------------------------------------------------------
    -- Theorem-thin law surfaces
    Action     : ∀ {a b : State} → Path a b → Scalar
    Density    : State → Scalar
    Amplitude  : ∀ {a b : State} → Path a b → Scalar
    Reduction  : State → State → Set ℓr

    ActionLaw    : Set
    DensityLaw   : Set
    ReductionLaw : Set
    ConvergenceLaw : Set

    ------------------------------------------------------------------
    -- Packaged repo-facing carriers
    empiricalValidation :
      PEVS.PhotonuclearEmpiricalValidationSummary V

    pressureConsumer :
      SOSPC.ShiftObservableSignaturePressureConsumer

    ------------------------------------------------------------------
    -- Governance / non-claim boundary
    interfaceLabel : String
    nonClaimBoundary : List String

open DashiDynamics public

empiricalValidationStatuses :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  DashiDynamics {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  List PEVS.ValidationStatus
empiricalValidationStatuses dynamics =
  PEVS.PhotonuclearEmpiricalValidationSummary.statuses
    (empiricalValidation dynamics)

heldControlPressureStatus :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  DashiDynamics {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  OSPT.PhysicsPressureStatus
heldControlPressureStatus dynamics =
  SOSPC.ShiftObservableSignaturePressureConsumer.heldPressureStatus
    (pressureConsumer dynamics)
