module DASHI.Physics.PressureHamiltonJacobiShiftInstance where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.List.Base using (_∷_; [])

open import DASHI.Physics.DashiDynamics as DD
open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.PressureHamiltonJacobiGap as PHJG
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- First theorem-thin Hamilton-Jacobi-facing inhabitant over the shift lane.
--
-- This module does not derive a continuous Hamilton-Jacobi PDE.
-- It only packages the existing least-action witness and one bounded
-- Bellman-style inequality on the three-point pressure carrier.

ShiftHJState : Set
ShiftHJState = SPTI.ShiftPressurePoint

shiftHJEvolve : ShiftHJState → ShiftHJState
shiftHJEvolve = DDSI.shiftPressureAdvance

shiftHJValue : ShiftHJState → Nat
shiftHJValue = DDSI.shiftPressureRank

ShiftHJLocalOptimality : Set
ShiftHJLocalOptimality = DDSI.ShiftLeastActionLaw

ShiftHJBellmanPresentation : Set
ShiftHJBellmanPresentation =
  (s t : ShiftHJState) →
  (target : DDSI.ShiftAdmissibleTarget s t) →
  shiftHJValue (shiftHJEvolve s)
    ≤
  DDSI.shiftTransitionAction s t target + shiftHJValue t

shiftHJBellmanWitness : ShiftHJBellmanPresentation
shiftHJBellmanWitness SPTI.shiftStartPoint SPTI.shiftNextPoint DDSI.start-next =
  s≤s z≤n
shiftHJBellmanWitness SPTI.shiftStartPoint SPTI.shiftHeldExitPoint DDSI.start-held =
  s≤s z≤n
shiftHJBellmanWitness SPTI.shiftNextPoint SPTI.shiftHeldExitPoint DDSI.next-held =
  s≤s (s≤s z≤n)
shiftHJBellmanWitness SPTI.shiftHeldExitPoint SPTI.shiftHeldExitPoint DDSI.held-held =
  NatP.≤-refl

ShiftHJPresentation : Set
ShiftHJPresentation =
  Σ ShiftHJLocalOptimality (λ _ → ShiftHJBellmanPresentation)

shiftHJPresentationWitness : ShiftHJPresentation
shiftHJPresentationWitness =
  DDSI.shiftLeastActionWitness , shiftHJBellmanWitness

shiftPressureHamiltonJacobiGap :
  PHJG.PressureHamiltonJacobiGap Nat
shiftPressureHamiltonJacobiGap =
  record
    { dynamics = DDSI.shiftDashiDynamics
    ; VariationalState = ShiftHJState
    ; evolve = shiftHJEvolve
    ; admissibleTarget = DDSI.ShiftAdmissibleTarget
    ; transitionAction = DDSI.shiftTransitionAction
    ; valueFunction = shiftHJValue
    ; localOptimality = ShiftHJLocalOptimality
    ; bellmanPresentation = ShiftHJBellmanPresentation
    ; hamiltonJacobiPresentation = ShiftHJPresentation
    ; nonClaimBoundary =
        "Shift least-action seam only"
        ∷ "valueFunction is a pressure-rank proxy, not a completed action-to-go theorem"
        ∷ "bellmanPresentation is a bounded discrete inequality, not a PDE limit"
        ∷ "No continuous Hamilton-Jacobi or Schrodinger derivation is claimed"
        ∷ DD.nonClaimBoundary DDSI.shiftDashiDynamics
    }

shiftHamiltonJacobiWitness :
  PHJG.hamiltonJacobiPresentation shiftPressureHamiltonJacobiGap
shiftHamiltonJacobiWitness = shiftHJPresentationWitness
