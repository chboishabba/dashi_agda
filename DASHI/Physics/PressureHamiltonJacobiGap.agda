module DASHI.Physics.PressureHamiltonJacobiGap where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)

open import DASHI.Physics.DashiDynamics as DD
open import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS

------------------------------------------------------------------------
-- Theorem-thin least-action / Hamilton-Jacobi-facing consumer.
--
-- This module does not claim a continuous-limit theorem, a Schrödinger
-- derivation, or a completed physical Hamiltonian dynamics package.
-- It only provides a bounded surface where a caller may expose:
--   * a variational state carrier over an existing DashiDynamics package,
--   * an admissible-target relation and transition-action cost,
--   * a value / action-to-go presentation,
--   * a local optimality witness,
--   * and a Bellman / Hamilton-Jacobi-style presentation surface.

record PressureHamiltonJacobiGap
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    dynamics : DD.DashiDynamics {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    VariationalState : Set

    evolve : VariationalState → DD.State dynamics

    admissibleTarget :
      VariationalState →
      VariationalState →
      Set

    transitionAction :
      (s t : VariationalState) →
      admissibleTarget s t →
      DD.Scalar dynamics

    valueFunction :
      VariationalState →
      DD.Scalar dynamics

    localOptimality : Set
    bellmanPresentation : Set
    hamiltonJacobiPresentation : Set

    nonClaimBoundary : List String

open PressureHamiltonJacobiGap public

gapInterfaceLabel :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureHamiltonJacobiGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  String
gapInterfaceLabel gap = DD.interfaceLabel (dynamics gap)

gapEmpiricalStatuses :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureHamiltonJacobiGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  List PEVS.ValidationStatus
gapEmpiricalStatuses gap =
  DD.empiricalValidationStatuses (dynamics gap)

gapHeldControlPressureStatus :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureHamiltonJacobiGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  OSPT.PhysicsPressureStatus
gapHeldControlPressureStatus gap =
  DD.heldControlPressureStatus (dynamics gap)

mkPressureHamiltonJacobiGap :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (dynamics : DD.DashiDynamics {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (VariationalState : Set) →
  (evolve : VariationalState → DD.State dynamics) →
  (admissibleTarget : VariationalState → VariationalState → Set) →
  ((s t : VariationalState) →
   admissibleTarget s t →
   DD.Scalar dynamics) →
  (VariationalState → DD.Scalar dynamics) →
  Set →
  Set →
  Set →
  PressureHamiltonJacobiGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkPressureHamiltonJacobiGap dynamics VariationalState evolve
  admissibleTarget transitionAction valueFunction
  localOptimality bellmanPresentation hamiltonJacobiPresentation =
  record
    { dynamics = dynamics
    ; VariationalState = VariationalState
    ; evolve = evolve
    ; admissibleTarget = admissibleTarget
    ; transitionAction = transitionAction
    ; valueFunction = valueFunction
    ; localOptimality = localOptimality
    ; bellmanPresentation = bellmanPresentation
    ; hamiltonJacobiPresentation = hamiltonJacobiPresentation
    ; nonClaimBoundary =
        "PressureHamiltonJacobiGap is interface packaging only"
        ∷ "localOptimality is a supplied least-action witness slot"
        ∷ "bellmanPresentation is a supplied discrete presentation slot"
        ∷ "No continuous-limit PDE claim is implied"
        ∷ "No Schrodinger derivation claim is implied"
        ∷ DD.nonClaimBoundary dynamics
    }
