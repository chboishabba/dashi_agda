{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.ControlledPhysicalTransitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CONTROLLED PHYSICAL TRANSITION
--
-- Controls are not state variables, and a control path does not imply
-- equilibrium, reversibility, quasistatic operation or closed-cycle utility.
------------------------------------------------------------------------

record ControlCoordinate : Set where
  constructor control-coordinate
  field
    controlName : String
    controlValueReference : String
    calibrationReference : String

open ControlCoordinate public

record ControlledPhysicalTransition : Set where
  constructor controlled-physical-transition
  field
    initialStateId : String
    finalStateId : String
    controlCoordinate : ControlCoordinate
    pathReference : String
    domainDynamicsReceipt : String
    equilibriumReceiptPresent : Bool
    reversibilityReceiptPresent : Bool
    cycleClosureReceiptPresent : Bool

open ControlledPhysicalTransition public

record ControlledPhysicalPathBoundary : Set where
  constructor controlled-physical-path-boundary
  field
    controlIsNotStateIdentity : Bool
    controlPathDoesNotImplyEquilibrium : Bool
    controlPathDoesNotImplyReversibility : Bool
    closedParameterLoopDoesNotImplyThermodynamicCycle : Bool
    sameControlShapeDoesNotImplySameMechanism : Bool

open ControlledPhysicalPathBoundary public

canonicalControlBoundary : ControlledPhysicalPathBoundary
canonicalControlBoundary =
  controlled-physical-path-boundary true true true true true

canonicalControlCoordinate : ControlCoordinate
canonicalControlCoordinate =
  control-coordinate "fixture-control" "u(t)" "fixture-calibration"

canonicalControlledTransition : ControlledPhysicalTransition
canonicalControlledTransition =
  controlled-physical-transition
    "state-0" "state-1" canonicalControlCoordinate "fixture-path"
    "domain receipt required" false false false
