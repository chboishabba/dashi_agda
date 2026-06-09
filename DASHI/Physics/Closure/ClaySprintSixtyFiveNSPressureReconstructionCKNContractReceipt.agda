module DASHI.Physics.Closure.ClaySprintSixtyFiveNSPressureReconstructionCKNContractReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintSixtyFourNSSourceBudgetExhaustionCKNRouteReceipt
  as Sprint64NS

------------------------------------------------------------------------
-- Sprint 65 pressure reconstruction / CKN contract receipt.
--
-- dashiCFD reconstructs periodic zero-mean pressure snapshots from velocity
-- snapshots and reruns the Sprint 64 local critical concentration audit with
-- pressure present.  This receipt records that the artifact-level missing
-- pressure blocker is removed, but no CKN epsilon theorem or Clay/NS
-- promotion follows.

Scalar : Set
Scalar = String

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

data Sprint65RouteDecision : Set where
  pressureReconstructionImplementedDiagnostic :
    Sprint65RouteDecision
  pressurePoissonResidualRecorded :
    Sprint65RouteDecision
  pressureInclusiveLocalConcentrationMixed :
    Sprint65RouteDecision
  cknThresholdCalibrationOpen :
    Sprint65RouteDecision
  noClayPromotion :
    Sprint65RouteDecision

canonicalSprint65RouteDecisions :
  List Sprint65RouteDecision
canonicalSprint65RouteDecisions =
  pressureReconstructionImplementedDiagnostic
  ∷ pressurePoissonResidualRecorded
  ∷ pressureInclusiveLocalConcentrationMixed
  ∷ cknThresholdCalibrationOpen
  ∷ noClayPromotion
  ∷ []

data Sprint65OpenGate : Set where
  gateCKNEpsilonThresholdCalibration :
    Sprint65OpenGate
  gatePressureInclusiveLocalQuantityBridge :
    Sprint65OpenGate
  gateSuitableWeakSolutionBridge :
    Sprint65OpenGate
  gateContinuumUniformity :
    Sprint65OpenGate
  gateNoFiniteTimeBlowup :
    Sprint65OpenGate

canonicalSprint65OpenGates :
  List Sprint65OpenGate
canonicalSprint65OpenGates =
  gateCKNEpsilonThresholdCalibration
  ∷ gatePressureInclusiveLocalQuantityBridge
  ∷ gateSuitableWeakSolutionBridge
  ∷ gateContinuumUniformity
  ∷ gateNoFiniteTimeBlowup
  ∷ []

data Sprint65Promotion : Set where

sprint65PromotionImpossibleHere :
  Sprint65Promotion →
  ⊥
sprint65PromotionImpossibleHere ()

pressureEquationContract : String
pressureEquationContract =
  "Delta p = - sum_ij partial_i u_j partial_j u_i"

pressureGaugeContract : String
pressureGaugeContract =
  "periodic zero-mean pressure gauge per frame"

requiredCKNPressureTerm : String
requiredCKNPressureTerm =
  "r^-2 integral_Q |p|^(3/2) dx dt"

sprint65CFDContract : String
sprint65CFDContract =
  "ns_sprint65_pressure_reconstruction_manifest.json plus pressure-present ns_sprint64_local_critical_concentration_summary.json"

sprint65Boundary : String
sprint65Boundary =
  "Sprint 65 removes the artifact-level missing-pressure gate by reconstructing pressure snapshots. The pressure-inclusive local concentration audit routes mixed under the diagnostic epsilon; CKN threshold calibration, suitable-solution bridge, continuum uniformity, no-blowup, and Clay/NS promotion remain unproved."

record ClaySprintSixtyFiveNSPressureReconstructionCKNContractReceipt : Set₁ where
  field
    sprint64NoPromotion :
      Sprint64NS.clayNavierStokesPromoted ≡ false

    sourceBudgetRouteInheritedExhausted :
      Bool
    sourceBudgetRouteInheritedExhaustedIsTrue :
      sourceBudgetRouteInheritedExhausted ≡ true

    cknRouteInheritedOpen :
      Bool
    cknRouteInheritedOpenIsTrue :
      cknRouteInheritedOpen ≡ true

    velocityOnlyPreflightAvailable :
      Bool
    velocityOnlyPreflightAvailableIsTrue :
      velocityOnlyPreflightAvailable ≡ true

    pressureReconstructionImplemented :
      Bool
    pressureReconstructionImplementedIsTrue :
      pressureReconstructionImplemented ≡ true

    pressureGaugePinned :
      Bool
    pressureGaugePinnedIsTrue :
      pressureGaugePinned ≡ true

    pressureTermComputed :
      Bool
    pressureTermComputedIsTrue :
      pressureTermComputed ≡ true

    fullCKNQuantityComputed :
      Bool
    fullCKNQuantityComputedIsTrue :
      fullCKNQuantityComputed ≡ true

    cknEpsilonRegularityApplied :
      Bool
    cknEpsilonRegularityAppliedIsFalse :
      cknEpsilonRegularityApplied ≡ false

    cknThresholdCalibrated :
      Bool
    cknThresholdCalibratedIsFalse :
      cknThresholdCalibrated ≡ false

    suitableWeakSolutionBridgeProved :
      Bool
    suitableWeakSolutionBridgeProvedIsFalse :
      suitableWeakSolutionBridgeProved ≡ false

    continuumUniformityProved :
      Bool
    continuumUniformityProvedIsFalse :
      continuumUniformityProved ≡ false

    noFiniteTimeBlowup :
      Bool
    noFiniteTimeBlowupIsFalse :
      noFiniteTimeBlowup ≡ false

    pressureEquation :
      String
    pressureEquationIsCanonical :
      pressureEquation ≡ pressureEquationContract

    pressureGauge :
      String
    pressureGaugeIsCanonical :
      pressureGauge ≡ pressureGaugeContract

    cknPressureTerm :
      String
    cknPressureTermIsCanonical :
      cknPressureTerm ≡ requiredCKNPressureTerm

    outputContract :
      String
    outputContractIsCanonical :
      outputContract ≡ sprint65CFDContract

    routeDecisions :
      List Sprint65RouteDecision
    routeDecisionsAreCanonical :
      routeDecisions ≡ canonicalSprint65RouteDecisions

    openGates :
      List Sprint65OpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalSprint65OpenGates

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List Sprint65Promotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      Sprint65Promotion → ⊥

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint65Boundary

canonicalSprint65Receipt :
  ClaySprintSixtyFiveNSPressureReconstructionCKNContractReceipt
canonicalSprint65Receipt =
  record
    { sprint64NoPromotion = refl
    ; sourceBudgetRouteInheritedExhausted = true
    ; sourceBudgetRouteInheritedExhaustedIsTrue = refl
    ; cknRouteInheritedOpen = true
    ; cknRouteInheritedOpenIsTrue = refl
    ; velocityOnlyPreflightAvailable = true
    ; velocityOnlyPreflightAvailableIsTrue = refl
    ; pressureReconstructionImplemented = true
    ; pressureReconstructionImplementedIsTrue = refl
    ; pressureGaugePinned = true
    ; pressureGaugePinnedIsTrue = refl
    ; pressureTermComputed = true
    ; pressureTermComputedIsTrue = refl
    ; fullCKNQuantityComputed = true
    ; fullCKNQuantityComputedIsTrue = refl
    ; cknEpsilonRegularityApplied = false
    ; cknEpsilonRegularityAppliedIsFalse = refl
    ; cknThresholdCalibrated = false
    ; cknThresholdCalibratedIsFalse = refl
    ; suitableWeakSolutionBridgeProved = false
    ; suitableWeakSolutionBridgeProvedIsFalse = refl
    ; continuumUniformityProved = false
    ; continuumUniformityProvedIsFalse = refl
    ; noFiniteTimeBlowup = false
    ; noFiniteTimeBlowupIsFalse = refl
    ; pressureEquation = pressureEquationContract
    ; pressureEquationIsCanonical = refl
    ; pressureGauge = pressureGaugeContract
    ; pressureGaugeIsCanonical = refl
    ; cknPressureTerm = requiredCKNPressureTerm
    ; cknPressureTermIsCanonical = refl
    ; outputContract = sprint65CFDContract
    ; outputContractIsCanonical = refl
    ; routeDecisions = canonicalSprint65RouteDecisions
    ; routeDecisionsAreCanonical = refl
    ; openGates = canonicalSprint65OpenGates
    ; openGatesAreCanonical = refl
    ; clayNavierStokesPromotedIsFalse = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = sprint65PromotionImpossibleHere
    ; boundary = sprint65Boundary
    ; boundaryIsCanonical = refl
    }
