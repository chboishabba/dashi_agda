module DASHI.Physics.PressureGradientFlowTerminalityGap where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)

open import DASHI.Physics.Closure.Basin as Basin
open import DASHI.Physics.DynamicsFixedPointUniqueness as DFPU
open import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import DASHI.Physics.PressureGradientFlowGap as PGFG

------------------------------------------------------------------------
-- Theorem-thin terminality / attractor consumer over a gradient-flow gap.
--
-- This module still does not claim a general dynamical-systems theorem. It
-- only packages:
--   * eventual entry into the held shell,
--   * the current flow gap, including its exact conserved quantity surface,
--   * one bounded unique-fixed-point / global-attractor surface,
--   * and one unique minimal-potential surface.

record PressureGradientFlowTerminalityGap
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    flowGap :
      PGFG.PressureGradientFlowGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    eventualHeld : Set
    attractorSurface :
      DFPU.DynamicsFixedPointUniqueness {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
    uniquePotentialMinimum : Set

    nonClaimBoundary : List String

open PressureGradientFlowTerminalityGap public

terminalityGapInterfaceLabel :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureGradientFlowTerminalityGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  String
terminalityGapInterfaceLabel gap =
  PGFG.gapInterfaceLabel (flowGap gap)

terminalityGapEmpiricalStatuses :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureGradientFlowTerminalityGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  List PEVS.ValidationStatus
terminalityGapEmpiricalStatuses gap =
  PGFG.gapEmpiricalStatuses (flowGap gap)

terminalityGapHeldControlPressureStatus :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  PressureGradientFlowTerminalityGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  OSPT.PhysicsPressureStatus
terminalityGapHeldControlPressureStatus gap =
  PGFG.gapHeldControlPressureStatus (flowGap gap)

mkPressureGradientFlowTerminalityGap :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (flowGap : PGFG.PressureGradientFlowGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  Set →
  DFPU.DynamicsFixedPointUniqueness {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V →
  Set →
  PressureGradientFlowTerminalityGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkPressureGradientFlowTerminalityGap flowGap
  eventualHeld attractorSurface uniquePotentialMinimum =
  record
    { flowGap = flowGap
    ; eventualHeld = eventualHeld
    ; attractorSurface = attractorSurface
    ; uniquePotentialMinimum = uniquePotentialMinimum
    ; nonClaimBoundary =
        "PressureGradientFlowTerminalityGap is interface packaging only"
        ∷ "eventualHeld is a supplied eventual-stability witness on an explicit carrier"
        ∷ "attractorSurface is a bounded finite-carrier uniqueness / global-attractor witness"
        ∷ "uniquePotentialMinimum is a current-carrier surface only"
        ∷ "No continuum attractor or smooth gradient-flow claim is implied"
        ∷ PGFG.nonClaimBoundary flowGap
    }
