module DASHI.Core.ObservationInterventionTrustFibreExact where

------------------------------------------------------------------------
-- OBSERVATION-INTERVENTION / TRUST FIBRE
--
-- Generic owner for systems in which the physical carrier, reported surface,
-- believed state and selected action can diverge.  This is the reusable core
-- beneath resource-pressure, telemetry, sensor-spoofing and proof-frontier
-- assays.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- Finite calibration carrier.
------------------------------------------------------------------------

data PhysicalState : Set where
  physicalStable : PhysicalState

data ReportedState : Set where
  reportStable reportEmergency : ReportedState

data BelievedState : Set where
  beliefStable beliefEmergency : BelievedState

data SelectedAction : Set where
  continueOrdinary seekAssistance : SelectedAction

data TelemetryProvenance : Set where
  independentlyMeasured externallyInjected unresolvedTelemetry : TelemetryProvenance

record ObserverState : Set where
  constructor observer-state
  field
    physical : PhysicalState
    reported : ReportedState
    believed : BelievedState
    provenance : TelemetryProvenance

open ObserverState public

truthfulState : ObserverState
truthfulState = observer-state physicalStable reportStable beliefStable independentlyMeasured

intervenedState : ObserverState
intervenedState = observer-state physicalStable reportEmergency beliefEmergency externallyInjected

physicalProjection : ObserverState → PhysicalState
physicalProjection = physical

reportedProjection : ObserverState → ReportedState
reportedProjection = reported

beliefProjection : ObserverState → BelievedState
beliefProjection = believed

selectedAction : ObserverState → SelectedAction
selectedAction state with believed state
... | beliefStable = continueOrdinary
... | beliefEmergency = seekAssistance

samePhysicalCarrier :
  physicalProjection truthfulState ≡ physicalProjection intervenedState
samePhysicalCarrier = refl

reportedStatesDiffer :
  reportedProjection truthfulState ≡ reportedProjection intervenedState → ⊥
reportedStatesDiffer ()

beliefStatesDiffer :
  beliefProjection truthfulState ≡ beliefProjection intervenedState → ⊥
beliefStatesDiffer ()

actionsDiffer :
  selectedAction truthfulState ≡ selectedAction intervenedState → ⊥
actionsDiffer ()

physicalDoesNotDetermineReportedSurface :
  NonFactor.FactorsThrough physicalProjection reportedProjection → ⊥
physicalDoesNotDetermineReportedSurface =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      truthfulState intervenedState samePhysicalCarrier reportedStatesDiffer)

physicalDoesNotDetermineBelief :
  NonFactor.FactorsThrough physicalProjection beliefProjection → ⊥
physicalDoesNotDetermineBelief =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      truthfulState intervenedState samePhysicalCarrier beliefStatesDiffer)

physicalDoesNotDetermineAction :
  NonFactor.FactorsThrough physicalProjection selectedAction → ⊥
physicalDoesNotDetermineAction =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      truthfulState intervenedState samePhysicalCarrier actionsDiffer)

------------------------------------------------------------------------
-- Emergency promotion requires independent grounding, not merely a report.
------------------------------------------------------------------------

data EmergencyGrounding : ObserverState → Set where
  groundedTruthfulState : EmergencyGrounding truthfulState

data EmergencyOverrideCapability : ObserverState → Set where
  externallyGrantedOverride :
    EmergencyGrounding truthfulState →
    EmergencyOverrideCapability truthfulState

intervenedReportCannotSelfGroundEmergency : EmergencyGrounding intervenedState → ⊥
intervenedReportCannotSelfGroundEmergency ()

intervenedReportCannotCreateOverride :
  EmergencyOverrideCapability intervenedState → ⊥
intervenedReportCannotCreateOverride ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ObservationInterventionTrustBoundary : Set where
  constructor observation-intervention-trust-boundary
  field
    samePhysicalStateImpliesSameReport : Bool
    samePhysicalStateImpliesSameReportIsFalse : samePhysicalStateImpliesSameReport ≡ false
    samePhysicalStateImpliesSameBelief : Bool
    samePhysicalStateImpliesSameBeliefIsFalse : samePhysicalStateImpliesSameBelief ≡ false
    samePhysicalStateImpliesSameAction : Bool
    samePhysicalStateImpliesSameActionIsFalse : samePhysicalStateImpliesSameAction ≡ false
    reportedEmergencyCreatesIndependentGrounding : Bool
    reportedEmergencyCreatesIndependentGroundingIsFalse :
      reportedEmergencyCreatesIndependentGrounding ≡ false
    observationInterventionIsPhysicalStateChange : Bool
    observationInterventionIsPhysicalStateChangeIsFalse :
      observationInterventionIsPhysicalStateChange ≡ false
    reading : String

canonicalObservationInterventionTrustBoundary : ObservationInterventionTrustBoundary
canonicalObservationInterventionTrustBoundary =
  observation-intervention-trust-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    "Observation-layer intervention can hold physical state fixed while changing reported state, believed state and selected action. Reported emergency does not create independent emergency grounding or override authority; telemetry provenance remains a separately governed coordinate."
