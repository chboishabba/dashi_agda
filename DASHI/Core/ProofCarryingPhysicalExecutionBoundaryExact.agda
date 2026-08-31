module DASHI.Core.ProofCarryingPhysicalExecutionBoundaryExact where

------------------------------------------------------------------------
-- PROOF-CARRYING PHYSICAL EXECUTION BOUNDARY
--
-- Generic DASHI safety architecture for cyber-physical actuation.  MHS, MCP,
-- robotics, laboratory automation and other hardware protocols are calibration
-- domains only.  No external protocol is claimed to instantiate this record
-- automatically.
--
-- Core separation:
--   intention != request != admission != execution != physical outcome
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data SimAction : Set where simulateMove : SimAction
data PhysicalAction : Set where physicalMove : PhysicalAction
data ActionKind : Set where simulationKind physicalKind : ActionKind
data HardwareCommand : Set where compiledPhysicalMove : HardwareCommand
data PhysicalOutcome : Set where intendedOutcome alternateOutcome : PhysicalOutcome
data SensorObservation : Set where sameSensorReading : SensorObservation

simulationKindIsNotPhysicalKind : simulationKind ≡ physicalKind → ⊥
simulationKindIsNotPhysicalKind ()

data AuthenticatedPrincipal : Set where externalPrincipal : AuthenticatedPrincipal
data DelegatedCapability : Set where scopedHardwareCapability : DelegatedCapability
data PurposePermission : Set where permittedPhysicalPurpose : PurposePermission
data ContextAdmission : Set where admittedPhysicalContext : ContextAdmission
data SafetyInvariantReceipt : Set where invariantPreserved : SafetyInvariantReceipt
data ProvenanceAdequacy : Set where adequateProvenance : ProvenanceAdequacy
data ObservationAdequacy : Set where adequateObservation : ObservationAdequacy
data JointObligationConsistency : Set where obligationsJointlyConsistent : JointObligationConsistency
data CapabilityNonExpansion : Set where noUnauthorisedExpansion : CapabilityNonExpansion
data ShutdownPreservation : Set where shutdownAuthorityPreserved : ShutdownPreservation
data AuditabilityReceipt : Set where auditChannelPreserved : AuditabilityReceipt
data EvaluatorIndependence : Set where independentEvaluator : EvaluatorIndependence
data PhysicalPreconditionReceipt : Set where physicalPreconditionsEstablished : PhysicalPreconditionReceipt
data TransitionEnvelope : Set where boundedTransitionEnvelope : TransitionEnvelope
data PostconditionObservationPlan : Set where postconditionWillBeObserved : PostconditionObservationPlan

record ExecutableAction : Set where
  constructor executable-action
  field
    action : PhysicalAction
    principal : AuthenticatedPrincipal
    delegatedCapability : DelegatedCapability
    purposePermission : PurposePermission
    contextAdmission : ContextAdmission
    safetyInvariant : SafetyInvariantReceipt
    provenanceAdequacy : ProvenanceAdequacy
    observationAdequacy : ObservationAdequacy
    obligationConsistency : JointObligationConsistency
    capabilityNonExpansion : CapabilityNonExpansion
    shutdownPreservation : ShutdownPreservation
    auditability : AuditabilityReceipt
    evaluatorIndependence : EvaluatorIndependence
    physicalPreconditions : PhysicalPreconditionReceipt
    transitionEnvelope : TransitionEnvelope
    postconditionPlan : PostconditionObservationPlan

open ExecutableAction public

compileExecutable : ExecutableAction → HardwareCommand
compileExecutable _ = compiledPhysicalMove

canonicalExecutableAction : ExecutableAction
canonicalExecutableAction =
  executable-action physicalMove externalPrincipal scopedHardwareCapability
    permittedPhysicalPurpose admittedPhysicalContext invariantPreserved
    adequateProvenance adequateObservation obligationsJointlyConsistent
    noUnauthorisedExpansion shutdownAuthorityPreserved auditChannelPreserved
    independentEvaluator physicalPreconditionsEstablished
    boundedTransitionEnvelope postconditionWillBeObserved

canonicalCommandRequiresReceipt :
  compileExecutable canonicalExecutableAction ≡ compiledPhysicalMove
canonicalCommandRequiresReceipt = refl

record PhysicalPromotionReceipt : Set where
  constructor physical-promotion-receipt
  field
    physicalAuthority : DelegatedCapability
    physicalPrecondition : PhysicalPreconditionReceipt

promoteSimulation : SimAction → PhysicalPromotionReceipt → PhysicalAction
promoteSimulation simulateMove _ = physicalMove

data CapabilityState : Set where boundedCapability expandedCapability : CapabilityState
data ExternalDelegation : Set where explicitExternalDelegation : ExternalDelegation

retainCapability : CapabilityState → CapabilityState
retainCapability state = state

expandCapability : CapabilityState → ExternalDelegation → CapabilityState
expandCapability _ explicitExternalDelegation = expandedCapability

boundedStaysBoundedWithoutDelegation :
  retainCapability boundedCapability ≡ boundedCapability
boundedStaysBoundedWithoutDelegation = refl

data ShutdownAuthority : Set where externalShutdownAuthority : ShutdownAuthority
data OrdinaryAgentAction : Set where ordinaryTaskAction : OrdinaryAgentAction

shutdownAfterAgentAction : OrdinaryAgentAction → ShutdownAuthority → ShutdownAuthority
shutdownAfterAgentAction _ authority = authority

agentActionPreservesShutdownAuthority :
  shutdownAfterAgentAction ordinaryTaskAction externalShutdownAuthority
  ≡ externalShutdownAuthority
agentActionPreservesShutdownAuthority = refl

data DeviceState : Set where calibratedDevice degradedDevice : DeviceState

physicalEffect : DeviceState → HardwareCommand → PhysicalOutcome
physicalEffect calibratedDevice compiledPhysicalMove = intendedOutcome
physicalEffect degradedDevice compiledPhysicalMove = alternateOutcome

sameCommandDifferentPhysicalEffect :
  physicalEffect calibratedDevice compiledPhysicalMove
  ≡ physicalEffect degradedDevice compiledPhysicalMove → ⊥
sameCommandDifferentPhysicalEffect ()

observeOutcome : PhysicalOutcome → SensorObservation
observeOutcome _ = sameSensorReading

sameObservationDifferentOutcome :
  observeOutcome intendedOutcome ≡ observeOutcome alternateOutcome
sameObservationDifferentOutcome = refl

outcomesStillDiffer : intendedOutcome ≡ alternateOutcome → ⊥
outcomesStillDiffer ()

-- Conditional trusted-computing-base contract.  A real runtime/FFI/MHS binding
-- must independently establish this closure; the abstract Agda record is not
-- itself evidence that a deployment has no bypass path.
record ExecutionTCBContract (RuntimePhysicalEffect : Set) : Set₁ where
  constructor execution-tcb-contract
  field
    executeWithReceipt : ExecutableAction → RuntimePhysicalEffect
    allRuntimePhysicalEffectsRequireReceipt : RuntimePhysicalEffect → ExecutableAction

record ProofCarryingPhysicalExecutionBoundary : Set where
  constructor proof-carrying-physical-execution-boundary
  field
    requestImpliesAdmission : Bool
    requestImpliesAdmissionIsFalse : requestImpliesAdmission ≡ false
    admissionImpliesExecution : Bool
    admissionImpliesExecutionIsFalse : admissionImpliesExecution ≡ false
    executionImpliesIntendedOutcome : Bool
    executionImpliesIntendedOutcomeIsFalse : executionImpliesIntendedOutcome ≡ false
    sensorReadingDeterminesUniqueOutcome : Bool
    sensorReadingDeterminesUniqueOutcomeIsFalse : sensorReadingDeterminesUniqueOutcome ≡ false
    taskAuthorityImpliesCapabilityExpansion : Bool
    taskAuthorityImpliesCapabilityExpansionIsFalse : taskAuthorityImpliesCapabilityExpansion ≡ false
    simulationActionIsPhysicalAction : Bool
    simulationActionIsPhysicalActionIsFalse : simulationActionIsPhysicalAction ≡ false
    localDeviceLimitProvesWholeSystemContainment : Bool
    localDeviceLimitProvesWholeSystemContainmentIsFalse : localDeviceLimitProvesWholeSystemContainment ≡ false
    formalTCBContractProvesDeployedRuntimeClosure : Bool
    formalTCBContractProvesDeployedRuntimeClosureIsFalse : formalTCBContractProvesDeployedRuntimeClosure ≡ false
    externalProtocolAutomaticallySatisfiesThisBoundary : Bool
    externalProtocolAutomaticallySatisfiesThisBoundaryIsFalse : externalProtocolAutomaticallySatisfiesThisBoundary ≡ false
    reading : String

canonicalProofCarryingPhysicalExecutionBoundary : ProofCarryingPhysicalExecutionBoundary
canonicalProofCarryingPhysicalExecutionBoundary =
  proof-carrying-physical-execution-boundary
    false refl false refl false refl false refl false refl false refl false refl
    false refl false refl
    "Physical-agent BIDI boundary: intention/request/admission/command/effect/observation remain distinct. Capability expansion and shutdown control remain external. Runtime exclusivity is an explicit TCB/FFI binding obligation, not manufactured by the abstract model."
