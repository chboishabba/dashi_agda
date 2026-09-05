module DASHI.Control.McCaslandFiniteFailureFamilyScoreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Executable finite failure-family scoring surface for McCasland placement.
-- This is a DASHI finite combinatorial compiler over source-shaped quantities;
-- it does not invent a numeric Gramian model absent source data.
------------------------------------------------------------------------

data PlacementNode : Set where
  sensorA sensorB sensorC actuatorA actuatorB actuatorC
  : PlacementNode

data FailureCase : Set where
  nominal
  failSensorA failSensorB failSensorC
  failActuatorA failActuatorB failActuatorC
  : FailureCase

record FinitePlacement : Set where
  constructor finite-placement
  field
    nodes : List PlacementNode
    label : String

open FinitePlacement public

record FailureScore : Set where
  constructor failure-score
  field
    placement : FinitePlacement
    failureCase : FailureCase
    controllabilityScore : Nat
    observabilityScore : Nat
    survivesRequiredThreshold : Bool
    evidenceReference : String

open FailureScore public

record FailureFamilyEvaluation : Set where
  constructor failure-family-evaluation
  field
    candidate : FinitePlacement
    cases : List FailureScore
    allRequiredCasesEnumerated : Bool
    allRequiredCasesEnumeratedIsTrue : allRequiredCasesEnumerated ≡ true
    scoreCoordinateSystemFixed : Bool
    scoreCoordinateSystemFixedIsTrue : scoreCoordinateSystemFixed ≡ true

open FailureFamilyEvaluation public

record WorstCaseWitness : Set where
  constructor worst-case-witness
  field
    evaluation : FailureFamilyEvaluation
    worstCase : FailureScore
    worstCaseIsEnumerated : Bool
    worstCaseIsEnumeratedIsTrue : worstCaseIsEnumerated ≡ true
    noUnevaluatedFailurePromoted : Bool
    noUnevaluatedFailurePromotedIsTrue : noUnevaluatedFailurePromoted ≡ true

open WorstCaseWitness public

record McCaslandFiniteFailureBoundary : Set where
  constructor mccasland-finite-failure-boundary
  field
    nominalScoreAloneClosesFaultTolerance : Bool
    nominalScoreAloneClosesFaultToleranceIsFalse : nominalScoreAloneClosesFaultTolerance ≡ false
    finiteEnumeratedFamilyEqualsAllPhysicallyPossibleFailures : Bool
    finiteEnumeratedFamilyEqualsAllPhysicallyPossibleFailuresIsFalse :
      finiteEnumeratedFamilyEqualsAllPhysicallyPossibleFailures ≡ false
    worstCaseWitnessRequiresEnumeratedDomain : Bool
    worstCaseWitnessRequiresEnumeratedDomainIsTrue :
      worstCaseWitnessRequiresEnumeratedDomain ≡ true

canonicalMcCaslandFiniteFailureBoundary : McCaslandFiniteFailureBoundary
canonicalMcCaslandFiniteFailureBoundary =
  mccasland-finite-failure-boundary false refl false refl true refl
