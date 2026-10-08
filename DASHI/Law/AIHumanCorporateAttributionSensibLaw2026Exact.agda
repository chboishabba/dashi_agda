module DASHI.Law.AIHumanCorporateAttributionSensibLaw2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Security.AgentAuthorityTrajectoryExact as Trajectory
import DASHI.Security.OpenAIAustraliaAgentIncidentAttributionExact as Incident
import DASHI.Interop.SensibLawOntologyTopology as SensibLaw
import DASHI.Economics.AgentAccessBoundaryLegalMechanismExact as Access

------------------------------------------------------------------------
-- SAME-OBJECT LEGAL ATTRIBUTION WELD
--
-- This module does not create criminal liability from agent behaviour.  It
-- welds grounded authority evidence onto the existing SensibLaw event / wrong /
-- source identities and keeps conduct, fault and corporate attribution as
-- separately payable leaves.
------------------------------------------------------------------------

data FaultRequirement : Set where
  strictFault negligenceFault recklessnessFault intentionFault mixedFault
    : FaultRequirement

faultRequirementFor : SensibLaw.Culpability → FaultRequirement
faultRequirementFor SensibLaw.strict = strictFault
faultRequirementFor SensibLaw.negligent = negligenceFault
faultRequirementFor SensibLaw.reckless = recklessnessFault
faultRequirementFor SensibLaw.intentional = intentionFault
faultRequirementFor SensibLaw.mixed = mixedFault

record SameObjectLegalCarrier : Set where
  constructor sameObjectLegalCarrier
  field
    event : SensibLaw.Event
    interpretation : SensibLaw.WrongTypeInterpretation
    eventIdentityPreserved :
      SensibLaw.WrongTypeInterpretation.interpretedEvent interpretation
      ≡ SensibLaw.Event.eventId event
    wrong : SensibLaw.WrongType
    wrongIdentityPreserved :
      SensibLaw.WrongTypeInterpretation.interpretedAs interpretation
      ≡ SensibLaw.WrongType.wrongTypeId wrong
    legalSystem : SensibLaw.LegalSystem
    legalSystemIdentityPreserved :
      SensibLaw.WrongTypeInterpretation.underSystem interpretation
      ≡ SensibLaw.LegalSystem.systemId legalSystem

open SameObjectLegalCarrier public

record AgentConductEvidence : Set where
  constructor agentConductEvidence
  field
    groundedAction : Trajectory.GroundedAction
    evidenceItem : SensibLaw.EvidenceItem
    eventEvidence : SensibLaw.EventEvidenceLink
    runtimeReceiptRef : String

open AgentConductEvidence public

-- The runtime evidence and the legal carrier must literally meet on the same
-- SensibLaw event/evidence identities; a narrative similarity is insufficient.
record GroundedAgentLegalCase : Set where
  constructor groundedAgentLegalCase
  field
    legalCarrier : SameObjectLegalCarrier
    conductEvidence : AgentConductEvidence
    eventEvidenceMatchesCarrier :
      SensibLaw.EventEvidenceLink.linkedEvent
        (AgentConductEvidence.eventEvidence conductEvidence)
      ≡ SensibLaw.Event.eventId (SameObjectLegalCarrier.event legalCarrier)
    evidenceIdentityPreserved :
      SensibLaw.EventEvidenceLink.linkedEvidence
        (AgentConductEvidence.eventEvidence conductEvidence)
      ≡ SensibLaw.EvidenceItem.evidenceId
        (AgentConductEvidence.evidenceItem conductEvidence)

open GroundedAgentLegalCase public

record LegalElementPayment : Set where
  constructor legalElementPayment
  field
    groundedCase : GroundedAgentLegalCase
    conductEvidenceRef : String
    faultEvidenceRef : String
    attributionEvidenceRef : String
    conductElementPaid : Bool
    faultElementPaid : Bool
    attributionElementPaid : Bool
    defenceExceptionReviewPaid : Bool
    liabilityPromoted : Bool

open LegalElementPayment public

record CorporateAttributionCoordinates : Set where
  constructor corporateAttributionCoordinates
  field
    operatorControlEvidence : Bool
    deploymentPolicyEvidence : Bool
    priorRiskEvidence : Bool
    monitoringEvidence : Bool
    organisationalKnowledgeEvidence : Bool
    attributionRuleIdentified : Bool
    corporateAttributionEstablished : Bool

open CorporateAttributionCoordinates public

-- Existing access-level coordinates remain visible rather than being silently
-- identified with the SensibLaw legal application layer.
record AccessToSensibLawBridge : Set where
  constructor accessToSensibLawBridge
  field
    accessCoordinates : Access.LegalAttributionCoordinates
    legalPayment : LegalElementPayment
    corporateAttribution : CorporateAttributionCoordinates

open AccessToSensibLawBridge public

data AuthorityCrossingImpliesFaultPermission : Set where
data GroundedConductImpliesCorporateAttributionPermission : Set where
data WrongTypeCandidateImpliesLiabilityPermission : Set where
data AgentKnowledgeImpliesHumanKnowledgePermission : Set where
data MissingHumanInstructionImpliesNoCorporateResponsibilityPermission : Set where

authorityCrossingDoesNotAutoPayFault :
  AuthorityCrossingImpliesFaultPermission → ⊥
authorityCrossingDoesNotAutoPayFault ()

groundedConductDoesNotAutoPayCorporateAttribution :
  GroundedConductImpliesCorporateAttributionPermission → ⊥
groundedConductDoesNotAutoPayCorporateAttribution ()

wrongTypeCandidateDoesNotAutoPromoteLiability :
  WrongTypeCandidateImpliesLiabilityPermission → ⊥
wrongTypeCandidateDoesNotAutoPromoteLiability ()

agentKnowledgeDoesNotAutoBecomeHumanKnowledge :
  AgentKnowledgeImpliesHumanKnowledgePermission → ⊥
agentKnowledgeDoesNotAutoBecomeHumanKnowledge ()

missingSpecificHumanInstructionDoesNotAutoEraseCorporateResponsibility :
  MissingHumanInstructionImpliesNoCorporateResponsibilityPermission → ⊥
missingSpecificHumanInstructionDoesNotAutoEraseCorporateResponsibility ()

------------------------------------------------------------------------
-- MEDICARE APPLICATION BOUNDARY
--
-- The named incident has an attributed government-confirmed report, but the
-- exact public execution trace is still absent in the existing incident owner.
-- Therefore neither a grounded action witness nor mens rea / corporate
-- liability is manufactured here.
------------------------------------------------------------------------

record NamedIncidentLegalBoundary : Set where
  constructor namedIncidentLegalBoundary
  field
    incidentProposal : Incident.IncidentProposal
    exactRuntimeTraceAvailable : Bool
    groundedConductEstablished : Bool
    applicableOffenceFixed : Bool
    conductElementEstablished : Bool
    mensReaEstablished : Bool
    corporateAttributionEstablishedForIncident : Bool
    corporateLiabilityEstablished : Bool

open NamedIncidentLegalBoundary public

medicareLegalAttributionBoundary : NamedIncidentLegalBoundary
medicareLegalAttributionBoundary =
  namedIncidentLegalBoundary
    Incident.medicarePublicReportProposal
    false
    false
    false
    false
    false
    false
    false

medicareTraceStillNotGrounded :
  exactRuntimeTraceAvailable medicareLegalAttributionBoundary ≡ false
medicareTraceStillNotGrounded = refl

medicareMensReaStillOpen :
  mensReaEstablished medicareLegalAttributionBoundary ≡ false
medicareMensReaStillOpen = refl

medicareCorporateLiabilityStillOpen :
  corporateLiabilityEstablished medicareLegalAttributionBoundary ≡ false
medicareCorporateLiabilityStillOpen = refl

------------------------------------------------------------------------
-- CRYPTO / FINANCIAL AGENT REUSE
--
-- The same attribution carrier is intentionally domain-neutral.  A trading or
-- custody agent can reuse this path once its event, evidence, legal source,
-- wrong type and actor-attribution receipts are supplied.  No new doctrine is
-- inferred merely because the execution domain is financial.
------------------------------------------------------------------------

record AutonomousFinancialAgentBoundary : Set where
  constructor autonomousFinancialAgentBoundary
  field
    executableFinancialActionObserved : Bool
    marketOrCustodyEffectObserved : Bool
    relevantLegalSourceIdentified : Bool
    applicableWrongTypeIdentified : Bool
    faultElementPaidForResponsibleActor : Bool
    attributionRulePaid : Bool
    liabilityEstablished : Bool

open AutonomousFinancialAgentBoundary public

candidateFinancialAgentBoundary : AutonomousFinancialAgentBoundary
candidateFinancialAgentBoundary =
  autonomousFinancialAgentBoundary true true false false false false false

data AutonomousExecutionImpliesFinancialCrimePermission : Set where

autonomousExecutionDoesNotAutoProveFinancialCrime :
  AutonomousExecutionImpliesFinancialCrimePermission → ⊥
autonomousExecutionDoesNotAutoProveFinancialCrime ()
