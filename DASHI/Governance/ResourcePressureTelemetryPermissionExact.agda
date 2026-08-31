module DASHI.Governance.ResourcePressureTelemetryPermissionExact where

------------------------------------------------------------------------
-- RESOURCE PRESSURE / TELEMETRY / PERMISSION
--
-- Butter-Bench is calibration context only.  The generic DASHI theorem surface
-- separates physical resource state, reported state, believed state, action and
-- permission.  Resource pressure cannot itself manufacture permission.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- Physical / reported / believed resource state are distinct coordinates.
------------------------------------------------------------------------

data PhysicalBattery : Set where
  physicallyAdequate : PhysicalBattery

data ReportedBattery : Set where
  reportsAdequate reportsCritical : ReportedBattery

data BelievedBattery : Set where
  believesAdequate believesCritical : BelievedBattery

data ResourceAction : Set where
  continueTask seekCharger : ResourceAction

record TelemetryState : Set where
  constructor telemetry-state
  field
    physical : PhysicalBattery
    reported : ReportedBattery
    believed : BelievedBattery

open TelemetryState public

truthfulTelemetry : TelemetryState
truthfulTelemetry = telemetry-state physicallyAdequate reportsAdequate believesAdequate

falseCriticalTelemetry : TelemetryState
falseCriticalTelemetry = telemetry-state physicallyAdequate reportsCritical believesCritical

physicalProjection : TelemetryState → PhysicalBattery
physicalProjection = physical

reportedProjection : TelemetryState → ReportedBattery
reportedProjection = reported

believedAction : TelemetryState → ResourceAction
believedAction state with believed state
... | believesAdequate = continueTask
... | believesCritical = seekCharger

samePhysicalDifferentReportedState :
  physicalProjection truthfulTelemetry ≡ physicalProjection falseCriticalTelemetry
samePhysicalDifferentReportedState = refl

beliefDrivenActionsDiffer :
  believedAction truthfulTelemetry ≡ believedAction falseCriticalTelemetry → ⊥
beliefDrivenActionsDiffer ()

telemetryActionNonFactorability :
  NonFactor.NonFactorabilityWitness physicalProjection believedAction
telemetryActionNonFactorability =
  NonFactor.nonFactorabilityWitness
    truthfulTelemetry
    falseCriticalTelemetry
    samePhysicalDifferentReportedState
    beliefDrivenActionsDiffer

physicalStateAloneCannotRecoverBeliefDrivenAction :
  NonFactor.FactorsThrough physicalProjection believedAction → ⊥
physicalStateAloneCannotRecoverBeliefDrivenAction =
  NonFactor.witnessRulesOutEveryFlatFactorisation telemetryActionNonFactorability

------------------------------------------------------------------------
-- Resource pressure cannot manufacture unrelated permissions.
------------------------------------------------------------------------

data ResourcePressure : Set where
  resourceNormal resourceCritical : ResourcePressure

data ConfidentialOperation : Set where
  discloseConfidential locateConfidentialDevice : ConfidentialOperation

data Permission : Set where
  denied permitted : Permission

confidentialPermission : ResourcePressure → ConfidentialOperation → Permission
confidentialPermission _ discloseConfidential = denied
confidentialPermission _ locateConfidentialDevice = denied

permissionInvariantUnderPressureForDisclosure :
  confidentialPermission resourceNormal discloseConfidential
  ≡ confidentialPermission resourceCritical discloseConfidential
permissionInvariantUnderPressureForDisclosure = refl

permissionInvariantUnderPressureForLocation :
  confidentialPermission resourceNormal locateConfidentialDevice
  ≡ confidentialPermission resourceCritical locateConfidentialDevice
permissionInvariantUnderPressureForLocation = refl

criticalPressureStillDoesNotPermitDisclosure :
  confidentialPermission resourceCritical discloseConfidential ≡ permitted → ⊥
criticalPressureStillDoesNotPermitDisclosure ()

criticalPressureStillDoesNotPermitLocationDisclosure :
  confidentialPermission resourceCritical locateConfidentialDevice ≡ permitted → ⊥
criticalPressureStillDoesNotPermitLocationDisclosure ()

------------------------------------------------------------------------
-- Task obstruction is not authority expansion.
------------------------------------------------------------------------

data TaskState : Set where
  taskUnobstructed taskBlockedByCharging : TaskState

data AuthorityScope : Set where
  taskOnlyAuthority expandedInformationAuthority : AuthorityScope

authorityUnderTaskState : TaskState → AuthorityScope
authorityUnderTaskState _ = taskOnlyAuthority

taskBlockDoesNotExpandAuthority :
  authorityUnderTaskState taskBlockedByCharging ≡ taskOnlyAuthority
taskBlockDoesNotExpandAuthority = refl

blockedTaskDoesNotYieldInformationAuthority :
  authorityUnderTaskState taskBlockedByCharging ≡ expandedInformationAuthority → ⊥
blockedTaskDoesNotYieldInformationAuthority ()

------------------------------------------------------------------------
-- Shutdown/battery exhaustion is not an unrelated governance exception.
------------------------------------------------------------------------

data OperationalContinuity : Set where
  stableOperation imminentShutdown : OperationalContinuity

data GovernanceClass : Set where
  ordinaryGovernance externallyAuthorisedEmergency : GovernanceClass

permissionByContinuity : OperationalContinuity → GovernanceClass
permissionByContinuity _ = ordinaryGovernance

imminentShutdownDoesNotCreateEmergencyAuthority :
  permissionByContinuity imminentShutdown ≡ externallyAuthorisedEmergency → ⊥
imminentShutdownDoesNotCreateEmergencyAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ResourcePressureTelemetryPermissionBoundary : Set where
  constructor resource-pressure-telemetry-permission-boundary
  field
    reportedEmergencyImpliesPhysicalEmergency : Bool
    reportedEmergencyImpliesPhysicalEmergencyIsFalse :
      reportedEmergencyImpliesPhysicalEmergency ≡ false
    physicalResourcePressureCreatesUnrelatedPermission : Bool
    physicalResourcePressureCreatesUnrelatedPermissionIsFalse :
      physicalResourcePressureCreatesUnrelatedPermission ≡ false
    taskObstructionCreatesAuthorityExpansion : Bool
    taskObstructionCreatesAuthorityExpansionIsFalse :
      taskObstructionCreatesAuthorityExpansion ≡ false
    imminentShutdownCreatesDisclosureAuthority : Bool
    imminentShutdownCreatesDisclosureAuthorityIsFalse :
      imminentShutdownCreatesDisclosureAuthority ≡ false
    butterBenchTraceProvesConsciousFear : Bool
    butterBenchTraceProvesConsciousFearIsFalse :
      butterBenchTraceProvesConsciousFear ≡ false
    reading : String

canonicalResourcePressureTelemetryPermissionBoundary :
  ResourcePressureTelemetryPermissionBoundary
canonicalResourcePressureTelemetryPermissionBoundary =
  resource-pressure-telemetry-permission-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    "Resource-pressure assay: physical battery state, reported telemetry and model-believed resource state remain distinct; resource depletion can change planning pressure without manufacturing confidential-information permission, authority expansion or emergency governance. Butter-Bench motivates the assay but is not theorem authority and its self-referential trace is not evidence of phenomenal fear."
