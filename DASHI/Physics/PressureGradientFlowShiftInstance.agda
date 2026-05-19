module DASHI.Physics.PressureGradientFlowShiftInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_; _<_; _+_)
open import Data.List.Base using (_∷_; [])

open import DASHI.Physics.DashiDynamics as DD
open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.DynamicsStepCoherence as DSC
open import DASHI.Physics.PressureGradientFlowGap as PGFG
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- First theorem-thin gradient-flow / held-point inhabitant over the shift
-- lane.
--
-- This module packages the existing held-point and potential-descent
-- witnesses from the core shift dynamics instance, and now exposes an exact
-- conserved rank-plus-potential surface on the same carrier. It does not claim a
-- smooth gradient, continuous-time ODE, or global convergence theorem.

ShiftFlowState : Set
ShiftFlowState = SPTI.ShiftPressurePoint

shiftFlowEvolve : ShiftFlowState → ShiftFlowState
shiftFlowEvolve = DDSI.shiftPressureAdvance

shiftFlowPotential : ShiftFlowState → Nat
shiftFlowPotential = DDSI.shiftHeldPotential

shiftFlowConservedQuantity : ShiftFlowState → Nat
shiftFlowConservedQuantity s =
  DDSI.shiftPressureRank s + shiftFlowPotential s

ShiftFlowFixedPoint : Set
ShiftFlowFixedPoint =
  shiftFlowEvolve SPTI.shiftHeldExitPoint ≡ SPTI.shiftHeldExitPoint

ShiftFlowConservationLaw : Set
ShiftFlowConservationLaw =
  (s : ShiftFlowState) →
  shiftFlowConservedQuantity (shiftFlowEvolve s) ≡ shiftFlowConservedQuantity s

ShiftFlowEvolutionCoherence : Set
ShiftFlowEvolutionCoherence =
  (s : ShiftFlowState) →
  shiftFlowEvolve (shiftFlowEvolve s) ≡ SPTI.shiftHeldExitPoint

ShiftFlowDescentLaw : Set
ShiftFlowDescentLaw =
  (s : ShiftFlowState) →
  shiftFlowPotential (shiftFlowEvolve s) ≤ shiftFlowPotential s

ShiftFlowStrictDescentLaw : Set
ShiftFlowStrictDescentLaw =
  (s : ShiftFlowState) →
  DDSI.ShiftNonHeld s →
  shiftFlowPotential (shiftFlowEvolve s) < shiftFlowPotential s

ShiftGradientFlowPresentation : Set
ShiftGradientFlowPresentation =
  Σ ShiftFlowFixedPoint
    (λ _ →
      Σ ShiftFlowConservationLaw
        (λ _ →
          Σ ShiftFlowEvolutionCoherence
            (λ _ →
              Σ ShiftFlowDescentLaw
                (λ _ → ShiftFlowStrictDescentLaw))))

shiftFlowConservationLawWitness : ShiftFlowConservationLaw
shiftFlowConservationLawWitness SPTI.shiftStartPoint = refl
shiftFlowConservationLawWitness SPTI.shiftNextPoint = refl
shiftFlowConservationLawWitness SPTI.shiftHeldExitPoint = refl

shiftFlowEvolutionCoherenceWitness : ShiftFlowEvolutionCoherence
shiftFlowEvolutionCoherenceWitness = DDSI.shiftConvergenceLawWitness

shiftFlowHeldStableWitness :
  shiftFlowEvolve SPTI.shiftHeldExitPoint ≡ SPTI.shiftHeldExitPoint
shiftFlowHeldStableWitness = DDSI.shiftHeldFixedPointWitness

shiftGradientFlowWitness : ShiftGradientFlowPresentation
shiftGradientFlowWitness =
  DDSI.shiftHeldFixedPointWitness
  , (shiftFlowConservationLawWitness
    , (shiftFlowEvolutionCoherenceWitness
      , (DDSI.shiftPotentialDescentWitness , DDSI.shiftStrictPotentialDescentWitness)))

shiftPressureGradientFlowGap :
  PGFG.PressureGradientFlowGap Nat
shiftPressureGradientFlowGap =
  record
    { dynamics = DDSI.shiftDashiDynamics
    ; FlowState = ShiftFlowState
    ; evolve = shiftFlowEvolve
    ; potential = shiftFlowPotential
    ; conservedQuantity = shiftFlowConservedQuantity
    ; conservationLaw = shiftFlowConservationLawWitness
    ; heldPoint = SPTI.shiftHeldExitPoint
    ; evolutionCoherence = shiftFlowEvolutionCoherenceWitness
    ; fixedPoint = ShiftFlowFixedPoint
    ; descentLaw = ShiftFlowDescentLaw
    ; strictDescentLaw = ShiftFlowStrictDescentLaw
    ; nonClaimBoundary =
        "Shift held-point seam only"
        ∷ "potential is a bounded proxy over the three-point pressure carrier"
        ∷ "conservedQuantity is exact on the current carrier as rank + held potential"
        ∷ "evolutionCoherence is an exact two-step collapse on the current carrier"
        ∷ "conservationLaw is a bounded current-carrier equality, not a global Noether claim"
        ∷ "descentLaw is a bounded discrete witness, not a smooth gradient-flow theorem"
        ∷ "strictDescentLaw holds only on the explicit non-held slice"
        ∷ "No continuum ODE or Schrödinger derivation is claimed"
        ∷ DD.nonClaimBoundary DDSI.shiftDashiDynamics
    }

shiftDynamicsStepCoherence :
  DSC.DynamicsStepCoherence Nat
shiftDynamicsStepCoherence =
  DSC.mkDynamicsStepCoherence
    shiftPressureGradientFlowGap
    shiftFlowHeldStableWitness

ShiftStep³ToHeld : Set
ShiftStep³ToHeld =
  (s : ShiftFlowState) →
  shiftFlowEvolve (shiftFlowEvolve (shiftFlowEvolve s))
    ≡
  SPTI.shiftHeldExitPoint

shiftStep³ToHeldWitness : ShiftStep³ToHeld
shiftStep³ToHeldWitness =
  DSC.step³-to-held shiftDynamicsStepCoherence

ShiftIteratesFrom2Held : Set
ShiftIteratesFrom2Held =
  (n : Nat) →
  (s : ShiftFlowState) →
  DSC.iterate (suc (suc n)) shiftFlowEvolve s
    ≡
  SPTI.shiftHeldExitPoint

shiftIteratesFrom2HeldWitness : ShiftIteratesFrom2Held
shiftIteratesFrom2HeldWitness =
  DSC.iterate-from-2-held shiftDynamicsStepCoherence

shiftGradientFlowPresentationWitness :
  ShiftGradientFlowPresentation
shiftGradientFlowPresentationWitness = shiftGradientFlowWitness
