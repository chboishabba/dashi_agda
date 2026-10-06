module DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo
import DASHI.Governance.OccupyConsensusEvidenceAtlasExact as Occupy
import DASHI.Governance.OccupyArchivalIncidenceEvidenceExact as Archive
import DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact as LibraryGraph
import DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact as Longitudinal
import DASHI.Governance.OccupyLibraryMeetingDurationEvidenceExact as Duration
import DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact as BurdenDesign
import DASHI.Governance.OccupyHeldOutMeetingValidationExact as HeldOut
import DASHI.Governance.GeneralGroupDecisionQuantitativeEvidenceAtlasExact as General
import DASHI.Governance.BookchinConfederalismAuthorityBridgeExact as Bookchin
import DASHI.Governance.IPCCSR15TransitionViabilityBridgeExact as SR15

------------------------------------------------------------------------
-- CROSS-SOURCE EVIDENCE INSTANTIATION CAPSTONE.
--
-- Attribution rule: agreement or structural similarity never collapses source
-- provenance. Each lane retains its own author/institution, evidentiary role,
-- and claim ceiling. The capstone merely assembles already-typed lanes.
------------------------------------------------------------------------

data EvidenceProvenanceClass : Set where
  primaryPoliticalDesignSource : EvidenceProvenanceClass
  primaryArchivalRecord : EvidenceProvenanceClass
  empiricalSocialMovementStudy : EvidenceProvenanceClass
  externalGroupDecisionExperiment : EvidenceProvenanceClass
  primaryAssessmentSource : EvidenceProvenanceClass
  dashiDerivedBridge : EvidenceProvenanceClass

data EvidenceLane : Set where
  boloPrimaryLane : EvidenceLane
  occupyArchivalLane : EvidenceLane
  occupyEmpiricalLane : EvidenceLane
  generalGroupDecisionLane : EvidenceLane
  bookchinPrimaryLane : EvidenceLane
  sr15PrimaryLane : EvidenceLane

laneClass : EvidenceLane → EvidenceProvenanceClass
laneClass boloPrimaryLane = primaryPoliticalDesignSource
laneClass occupyArchivalLane = primaryArchivalRecord
laneClass occupyEmpiricalLane = empiricalSocialMovementStudy
laneClass generalGroupDecisionLane = externalGroupDecisionExperiment
laneClass bookchinPrimaryLane = primaryPoliticalDesignSource
laneClass sr15PrimaryLane = primaryAssessmentSource

record FederatedGovernanceEvidenceInstantiation : Set where
  constructor federatedGovernanceEvidenceInstantiation
  field
    boloAtlas : Bolo.BoloBoloPrimarySourceAtlas
    occupyArchiveCandidate : Archive.ArchivalIncidenceCandidate
    occupyLibraryObservedEdges : List LibraryGraph.ObservedEdge
    occupyLongitudinalObservedEdges : List Longitudinal.LongitudinalEdge
    oct15Duration : Duration.MeetingDurationObservation
    oct22Duration : Duration.MeetingDurationObservation
    prospectiveHeldOutPlan : HeldOut.ProspectiveHeldOutPlan
    occupySynthesis : Occupy.OccupyEvidenceSynthesis
    generalGroupDecisionSources : List General.GeneralGroupDecisionSource
    bookchinSource : Bookchin.BookchinConfederalismSourceBoundary
    bookchinBridge : Bookchin.BookchinDASHIAlignment
    sr15Source : SR15.SR15SourceBoundary

    nestedCommunityArchitectureEvidencePresent : Bool
    boundedArchivalInteractionEvidencePresent : Bool
    boundedFiniteArchivalIncidenceGraphPresent : Bool
    longitudinalArchivalIncidenceFamilyPresent : Bool
    archivalProcessBurdenObservationsPresent : Bool
    measuredMeetingDurationEvidencePresent : Bool
    coordinationBurdenExperimentDesignPresent : Bool
    prospectiveHeldOutProtocolPresent : Bool
    consensusBurdenBenefitPluralEvidencePresent : Bool
    generalGroupDecisionQuantitativeEvidencePresent : Bool
    recallableConfederalCoordinationEvidencePresent : Bool
    transitionViabilityConstraintEvidencePresent : Bool

open FederatedGovernanceEvidenceInstantiation public

canonicalFederatedGovernanceEvidenceInstantiation :
  FederatedGovernanceEvidenceInstantiation
canonicalFederatedGovernanceEvidenceInstantiation =
  federatedGovernanceEvidenceInstantiation
    Bolo.canonicalBoloBoloPrimarySourceAtlas
    Archive.adashSpokesCouncilCandidate
    LibraryGraph.canonicalObservedEdges
    Longitudinal.longitudinalObservedEdges
    Duration.oct15FirstFormalMeeting
    Duration.oct22Meeting
    HeldOut.canonicalProspectiveHeldOutPlan
    Occupy.canonicalOccupyEvidenceSynthesis
    General.canonicalGeneralGroupDecisionSources
    Bookchin.canonicalBookchinConfederalismSourceBoundary
    Bookchin.canonicalBookchinDASHIAlignment
    SR15.canonicalSR15SourceBoundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- What is now paid, and what is not.
------------------------------------------------------------------------

record FederatedGovernanceEvidenceBoundary : Set where
  constructor federatedGovernanceEvidenceBoundary
  field
    crossSourceAgreementCollapsesProvenance : Bool
    boloArchitectureAttributedToBookchin : Bool
    bookchinConfederalismAttributedToPM : Bool
    ipccTransitionEvidenceCreatesPoliticalDoctrine : Bool
    occupyEvidencePaysQuantitativeScalingLaw : Bool
    generalGroupDecisionEvidenceDirectlyValidatesOccupyScaling : Bool

    boloSourcePaysNestedArchitecture : Bool
    occupyArchivePaysBoundedNamedInteraction : Bool
    occupyArchivePaysBoundedFiniteIncidenceGraph : Bool
    occupyArchivePaysLongitudinalIncidenceFamily : Bool
    occupyArchivePaysProcessBurdenObservations : Bool
    occupyArchivePaysMeasuredMeetingDurations : Bool
    dashiPaysCoordinationBurdenExperimentDesign : Bool
    dashiPaysProspectiveHeldOutProtocol : Bool
    occupyLiteraturePaysPluralProcessEvidence : Bool
    generalGroupDecisionEvidencePaysMechanismPlausibility : Bool
    bookchinSourcePaysRecallableConfederalCoordination : Bool
    sr15PaysSystemTransitionConstraintSurface : Bool

    actualPolityLegitimacyPaid : Bool
    actualParticipantIssueIncidencePaid : Bool
    empiricalCoordinationCostFunctionalPaid : Bool
    quantitativeIncidenceBurdenRelationshipPaid : Bool
    prospectiveHeldOutValidationPaid : Bool
    concreteClimateViabilityOfFederationPaid : Bool

open FederatedGovernanceEvidenceBoundary public

canonicalFederatedGovernanceEvidenceBoundary :
  FederatedGovernanceEvidenceBoundary
canonicalFederatedGovernanceEvidenceBoundary =
  federatedGovernanceEvidenceBoundary
    false
    false
    false
    false
    false
    false
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false

canonicalFederatedGovernanceEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalFederatedGovernanceEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated governance evidence instantiation capstone"
    "DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact"
    "canonicalFederatedGovernanceEvidenceBoundary"
    "assembles independently attributed bolo'bolo, bounded and longitudinal Occupy archival incidence, archival process-strain and measured-duration observations, Occupy scholarship, external quantitative group-decision evidence, Bookchin confederalism, IPCC SR1.5 evidence, a DASHI-derived burden experiment-design frontier and a prospective held-out protocol while preserving source class and claim ceilings"
    "two real meeting durations and a prospective validation protocol are paid, but external experiments do not directly validate Occupy scaling; complete real-institution incidence, an empirical coordination-cost functional, a quantitative OWS incidence-to-burden relationship and actual prospective held-out validation remain unpaid"
    "agda -i . DASHI/Governance/FederatedGovernanceEvidenceInstantiationRegression.agda"
