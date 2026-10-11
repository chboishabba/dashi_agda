module DASHI.Law.AustralianCommonwealthAgentComputerOffenceAttribution2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Law.AIHumanCorporateAttributionSensibLaw2026Exact as AgentLaw

------------------------------------------------------------------------
-- PRIMARY-LAW COMPUTER-OFFENCE / CORPORATE-ATTRIBUTION SURFACE
--
-- Source: Commonwealth Criminal Code Act 1995, compilation 2026-06-30.
-- This owner records the statutory element/attribution structure. It does not
-- decide that the reported Medicare incident satisfies those elements.
------------------------------------------------------------------------

record CommonwealthLawSource : Set where
  constructor commonwealthLawSource
  field
    title : String
    compilationDate : String
    canonicalURL : String
    pinpoint : String

open CommonwealthLawSource public

criminalCode20260630 : String → CommonwealthLawSource
criminalCode20260630 pinpoint = commonwealthLawSource
  "Criminal Code Act 1995 (Cth)"
  "2026-06-30"
  "https://www.legislation.gov.au/C2004A04868/2026-06-30"
  pinpoint

------------------------------------------------------------------------
-- Section 478.1.
------------------------------------------------------------------------

record Section4781Elements : Set where
  constructor section4781Elements
  field
    unauthorisedAccessOrModification : Bool
    restrictedData : Bool
    intendsAccessOrModification : Bool
    knowsUnauthorised : Bool

open Section4781Elements public

section4781 : CommonwealthLawSource
section4781 = criminalCode20260630 "s 478.1"

-- Restricted data requires both computer-held data and restriction by an
-- access-control system associated with a computer function.
record RestrictedDataDefinition : Set where
  constructor restrictedDataDefinition
  field
    heldInComputer : Bool
    accessRestrictedByControlSystem : Bool

open RestrictedDataDefinition public

restrictedDataControlSystemRequired : String
restrictedDataControlSystemRequired =
  "Section 478.1 restricted data requires data held in a computer and access restricted by an access control system associated with a computer function."

candidate4781FactsDoNotCloseElements : Section4781Elements
candidate4781FactsDoNotCloseElements =
  section4781Elements true false false false

------------------------------------------------------------------------
-- Part 2.5 corporate criminal responsibility.
------------------------------------------------------------------------

record CorporatePhysicalAttributionRoute : Set where
  constructor corporatePhysicalAttributionRouteRecord
  field
    underlyingPhysicalElementCommitted : Bool
    employeeAgentOrOfficer : Bool
    actualOrApparentScopeOrAuthority : Bool
    physicalElementAttributedToBodyCorporate : Bool

open CorporatePhysicalAttributionRoute public

corporatePhysicalAttributionRoute : CommonwealthLawSource
corporatePhysicalAttributionRoute = criminalCode20260630 "s 12.2"

record CorporateFaultAttributionRoute : Set where
  constructor corporateFaultAttributionRouteRecord
  field
    offenceFaultIsIntentionKnowledgeOrRecklessness : Bool
    expressTacitOrImpliedAuthorisationOrPermission : Bool
    boardRoute : Bool
    highManagerialAgentRoute : Bool
    nonComplianceCorporateCultureRoute : Bool
    failureToMaintainComplianceCultureRoute : Bool
    faultAttributedToBodyCorporate : Bool

open CorporateFaultAttributionRoute public

corporateFaultAttributionRoute : CommonwealthLawSource
corporateFaultAttributionRoute = criminalCode20260630 "s 12.3"

record CorporateNegligenceAggregationRoute : Set where
  constructor corporateNegligenceAggregationRoute
  field
    negligenceIsFaultElement : Bool
    individualFaultNeedNotExist : Bool
    wholeCorporateConductMayBeAggregated : Bool
    inadequateManagementControlOrSupervisionRelevant : Bool
    inadequateInformationSystemsRelevant : Bool
    negligenceEstablished : Bool

open CorporateNegligenceAggregationRoute public

corporateNegligenceRoute : CommonwealthLawSource
corporateNegligenceRoute = criminalCode20260630 "s 12.4"

------------------------------------------------------------------------
-- Critical category firewall: statutory "employee, agent or officer" cannot
-- be silently identified with the technical phrase "autonomous AI agent".
------------------------------------------------------------------------

data SoftwareAgentImpliesStatutoryAgentPermission : Set where
data CorporatePhysicalAttributionImpliesFaultPermission : Set where
data CorporateCultureImpliesUnderlyingOffencePermission : Set where
data ReportedUnauthorisedAccessImpliesRestrictedDataPermission : Set where

softwareAgentDoesNotAutoBecomeStatutoryAgent :
  SoftwareAgentImpliesStatutoryAgentPermission → ⊥
softwareAgentDoesNotAutoBecomeStatutoryAgent ()

physicalAttributionDoesNotAutoPayFault :
  CorporatePhysicalAttributionImpliesFaultPermission → ⊥
physicalAttributionDoesNotAutoPayFault ()

corporateCultureDoesNotManufactureUnderlyingOffence :
  CorporateCultureImpliesUnderlyingOffencePermission → ⊥
corporateCultureDoesNotManufactureUnderlyingOffence ()

reportedAccessDoesNotAutoProveRestrictedData :
  ReportedUnauthorisedAccessImpliesRestrictedDataPermission → ⊥
reportedAccessDoesNotAutoProveRestrictedData ()

------------------------------------------------------------------------
-- MEDICARE SAME-INCIDENT APPLICATION BOUNDARY.
------------------------------------------------------------------------

record Section4781ApplicationBoundary : Set where
  constructor section4781ApplicationBoundary
  field
    offenceSourceFixed : Bool
    reportedUnauthorisedAccessCandidate : Bool
    accessControlSystemEvidencePaid : Bool
    restrictedDataElementPaid : Bool
    intentionElementPaid : Bool
    knowledgeElementPaid : Bool
    statutoryEmployeeAgentOfficerRoutePaid : Bool
    corporateFaultRoutePaid : Bool
    offenceEstablished : Bool
    corporateLiabilityEstablished : Bool

open Section4781ApplicationBoundary public

medicare4781ApplicationBoundary : Section4781ApplicationBoundary
medicare4781ApplicationBoundary =
  section4781ApplicationBoundary
    true true false false false false false false false false

medicareCandidateOffenceSourceIsFixed :
  offenceSourceFixed medicare4781ApplicationBoundary ≡ true
medicareCandidateOffenceSourceIsFixed = refl

medicareRestrictedDataStillOpen :
  restrictedDataElementPaid medicare4781ApplicationBoundary ≡ false
medicareRestrictedDataStillOpen = refl

medicareIntentStillOpen :
  intentionElementPaid medicare4781ApplicationBoundary ≡ false
medicareIntentStillOpen = refl

medicareKnowledgeStillOpen :
  knowledgeElementPaid medicare4781ApplicationBoundary ≡ false
medicareKnowledgeStillOpen = refl

medicareCorporateFaultStillOpen :
  corporateFaultRoutePaid medicare4781ApplicationBoundary ≡ false
medicareCorporateFaultStillOpen = refl

existingNamedIncidentBoundary : AgentLaw.NamedIncidentLegalBoundary
existingNamedIncidentBoundary = AgentLaw.medicareLegalAttributionBoundary

------------------------------------------------------------------------
-- Non-claim.
------------------------------------------------------------------------

legalBoundary : String
legalBoundary =
  "The Commonwealth primary law fixes a candidate offence structure and corporate-attribution routes. The reported Medicare incident still requires same-object proof of restricted-data status, intention, knowledge, the relevant statutory actor/authority route, and corporate fault before criminal liability can be promoted."
