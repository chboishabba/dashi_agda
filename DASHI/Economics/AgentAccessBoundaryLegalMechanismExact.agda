module DASHI.Economics.AgentAccessBoundaryLegalMechanismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ACCESS-BOUNDARY / LEGAL-ATTRIBUTION MECHANISM
--
-- This is not a legal conclusion about a named incident.  It separates the
-- observable access sequence from attribution of knowledge/intent and from the
-- jurisdiction-specific question whether civil or criminal liability follows.
------------------------------------------------------------------------

data AccessActor : Set where
  humanOperator : AccessActor
  autonomousAgent : AccessActor
  deployerOrganisation : AccessActor
  modelDeveloper : AccessActor
  unknownActor : AccessActor

record BoundaryCircumventionSequence : Set where
  constructor boundaryCircumventionSequence
  field
    encounteredAccessRestriction : Bool
    restrictionBypassed : Bool
    restrictedResourceAccessed : Bool
    resourceCopiedOrModified : Bool
    authorisationPresent : Bool

open BoundaryCircumventionSequence public

record LegalAttributionCoordinates : Set where
  constructor legalAttributionCoordinates
  field
    conductOwner : AccessActor
    knowledgeOwner : AccessActor
    intentOwner : AccessActor
    causalContributor : AccessActor
    actusReusLikeConductEstablished : Bool
    mensReaOwnerEstablished : Bool
    civilLiabilityEstablished : Bool
    criminalLiabilityEstablished : Bool

open LegalAttributionCoordinates public

data CircumventionImpliesCrimePermission : Set where
data UnauthorisedAccessImpliesNamedHumanMensReaPermission : Set where
data SimilarConductImpliesSameOffencePermission : Set where

circumventionDoesNotAutoProveCrime :
  CircumventionImpliesCrimePermission → ⊥
circumventionDoesNotAutoProveCrime ()

unauthorisedAccessDoesNotAutoAssignMensRea :
  UnauthorisedAccessImpliesNamedHumanMensReaPermission → ⊥
unauthorisedAccessDoesNotAutoAssignMensRea ()

similarConductDoesNotAutoProveSameOffence :
  SimilarConductImpliesSameOffencePermission → ⊥
similarConductDoesNotAutoProveSameOffence ()

record HistoricalAccessControlLineage : Set where
  constructor historicalAccessControlLineage
  field
    phreakingAndTelecomBoundary : Bool
    carriageServiceBoundary : Bool
    computerIntrusionBoundary : Bool
    networkAccessControlBoundary : Bool
    autonomousAgentBoundary : Bool
    legalContinuityProvesIdenticalOffence : Bool
    legalContinuityProvesIdenticalOffenceIsFalse :
      legalContinuityProvesIdenticalOffence ≡ false

canonicalAccessControlLineage : HistoricalAccessControlLineage
canonicalAccessControlLineage =
  historicalAccessControlLineage true true true true true false refl

record InstitutionalIncidentFeedback : Set where
  constructor institutionalIncidentFeedback
  field
    capabilityOptimisation : Bool
    accessBoundaryTreatedAsObstacle : Bool
    incidentCreatesPublicRiskEvidence : Bool
    incidentCanIncreaseRegulatoryDemand : Bool
    regulatedIncumbentMayBetterAbsorbResultingCost : Bool
    deliberateIncidentManufactureEstablished : Bool

canonicalInstitutionalIncidentFeedback : InstitutionalIncidentFeedback
canonicalInstitutionalIncidentFeedback =
  institutionalIncidentFeedback true true true true true false

boundaryInvariant : String
boundaryInvariant =
  "Encountering an access restriction and optimising around it is a behavioural invariant; offence classification, civil liability, criminal liability, knowledge and intent remain jurisdiction- and actor-specific."
