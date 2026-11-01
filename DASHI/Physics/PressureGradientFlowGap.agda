module DASHI.Physics.PressureGradientFlowGap where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)

open import DASHI.Physics.DashiDynamics as DD
open import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS

------------------------------------------------------------------------
-- Theorem-thin gradient-flow / held-point consumer over DashiDynamics.
--
-- This module does not claim a continuous ODE, smooth gradient, or a
-- completed thermodynamic derivation. It only packages:
--   * a flow-state carrier,
--   * an evolution endomap,
--   * a potential function,
--   * a bounded conserved quantity surface,
--   * one held / fixed point,
--   * a bounded potential-descent witness,
--   * and an optional strict-descent witness off the held slice.

record PressureGradientFlowGap
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    dynamics : DD.DashiDynamics {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    FlowState : Set
    evolve : FlowState → FlowState
    potential : FlowState → DD.Scalar dynamics
    conservedQuantity : FlowState → DD.Scalar dynamics
    conservationLaw : (s : FlowState) →
      conservedQuantity (evolve s) ≡ conservedQuantity s
    heldPoint : FlowState
    evolutionCoherence : (s : FlowState) →
      evolve (evolve s) ≡ heldPoint

    fixedPoint : Set
    descentLaw : Set
    strictDescentLaw : Set

    nonClaimBoundary : List String

open PressureGradientFlowGap public

gapInterfaceLabel :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureGradientFlowGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  String
gapInterfaceLabel gap = DD.interfaceLabel (dynamics gap)

gapEmpiricalStatuses :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureGradientFlowGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  List PEVS.ValidationStatus
gapEmpiricalStatuses gap =
  DD.empiricalValidationStatuses (dynamics gap)

gapHeldControlPressureStatus :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureGradientFlowGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  OSPT.PhysicsPressureStatus
gapHeldControlPressureStatus gap =
  DD.heldControlPressureStatus (dynamics gap)

mkPressureGradientFlowGap :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (dynamics : DD.DashiDynamics {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (FlowState : Set) →
  (evolve : FlowState → FlowState) →
  (potential : FlowState → DD.Scalar dynamics) →
  (conservedQuantity : FlowState → DD.Scalar dynamics) →
  ((s : FlowState) →
    conservedQuantity (evolve s) ≡ conservedQuantity s) →
  (fixedPointState : FlowState) →
  ((s : FlowState) →
    evolve (evolve s) ≡ fixedPointState) →
  Set →
  Set →
  Set →
  PressureGradientFlowGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkPressureGradientFlowGap dynamics FlowState evolve potential conservedQuantity
  conservationLaw fixedPointState evolutionCoherence fixedPoint descentLaw
  strictDescentLaw =
  record
    { dynamics = dynamics
    ; FlowState = FlowState
    ; evolve = evolve
    ; potential = potential
    ; conservedQuantity = conservedQuantity
    ; conservationLaw = conservationLaw
    ; evolutionCoherence = evolutionCoherence
    ; heldPoint = fixedPointState
    ; fixedPoint = fixedPoint
    ; descentLaw = descentLaw
    ; strictDescentLaw = strictDescentLaw
    ; nonClaimBoundary =
        "PressureGradientFlowGap is interface packaging only"
        ∷ "conservedQuantity is a bounded exact current-carrier witness, not a global conservation theorem"
        ∷ "evolutionCoherence is an exact two-step collapse law on the finite carrier, not a continuum stability theorem"
        ∷ "descentLaw is a bounded supplied witness, not a smooth ODE claim"
        ∷ "strictDescentLaw is a bounded off-held witness, not a global convergence theorem"
        ∷ "heldPoint is a packaged fixed point, not a global attractor theorem"
        ∷ "No continuum gradient-flow or Schrödinger derivation is implied"
        ∷ DD.nonClaimBoundary dynamics
    }
