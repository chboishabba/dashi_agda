module DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo
import DASHI.Governance.OccupyConsensusEvidenceAtlasExact as Occupy
import DASHI.Governance.OccupyArchivalIncidenceEvidenceExact as Archive
import DASHI.Governance.OccupyArchivalObservationModelExact as Observation
import DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact as LibraryGraph
import DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact as Longitudinal
import DASHI.Governance.OccupyLibraryMeetingDurationEvidenceExact as Duration
import DASHI.Governance.OccupyMeetingPanelExact as Panel
import DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact as BurdenDesign
import DASHI.Governance.OccupyHeldOutMeetingValidationExact as HeldOut
import DASHI.Governance.OccupyCoordinationCausalPromotionExact as Causal
import DASHI.Governance.GeneralGroupDecisionQuantitativeEvidenceAtlasExact as General
import DASHI.Governance.BookchinConfederalismAuthorityBridgeExact as Bookchin
import DASHI.Governance.IPCCSR15TransitionViabilityBridgeExact as SR15

data EvidenceProvenanceClass : Set where
  primaryPoliticalDesignSource primaryArchivalRecord empiricalSocialMovementStudy externalGroupDecisionExperiment primaryAssessmentSource dashiDerivedBridge : EvidenceProvenanceClass

data EvidenceLane : Set where
  boloPrimaryLane occupyArchivalLane occupyEmpiricalLane generalGroupDecisionLane bookchinPrimaryLane sr15PrimaryLane : EvidenceLane

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
    occupyDevelopmentMeetingPanel : List Panel.MeetingPanelRow
    oct15Duration : Duration.MeetingDurationObservation
    oct22Duration : Duration.MeetingDurationObservation
    prospectiveHeldOutPlan : HeldOut.ProspectiveHeldOutPlan
    candidateCausalGraph : List Causal.CandidateCausalEdge
    occupySynthesis : Occupy.OccupyEvidenceSynthesis
    generalGroupDecisionSources : List General.GeneralGroupDecisionSource
    bookchinSource : Bookchin.BookchinConfederalismSourceBoundary
    bookchinBridge : Bookchin.BookchinDASHIAlignment
    sr15Source : SR15.SR15SourceBoundary
    nestedCommunityArchitectureEvidencePresent boundedArchivalInteractionEvidencePresent boundedFiniteArchivalIncidenceGraphPresent longitudinalArchivalIncidenceFamilyPresent sourceExplicitMeetingPanelPresent archivalObservationModelPresent archivalProcessBurdenObservationsPresent measuredMeetingDurationEvidencePresent coordinationBurdenExperimentDesignPresent prospectiveHeldOutProtocolPresent causalPromotionObligationSurfacePresent consensusBurdenBenefitPluralEvidencePresent generalGroupDecisionQuantitativeEvidencePresent recallableConfederalCoordinationEvidencePresent transitionViabilityConstraintEvidencePresent : Bool

open FederatedGovernanceEvidenceInstantiation public

canonicalFederatedGovernanceEvidenceInstantiation : FederatedGovernanceEvidenceInstantiation
canonicalFederatedGovernanceEvidenceInstantiation =
  federatedGovernanceEvidenceInstantiation
    Bolo.canonicalBoloBoloPrimarySourceAtlas
    Archive.adashSpokesCouncilCandidate
    LibraryGraph.canonicalObservedEdges
    Longitudinal.longitudinalObservedEdges
    Panel.canonicalDevelopmentPanel
    Duration.oct15FirstFormalMeeting
    Duration.oct22Meeting
    HeldOut.canonicalProspectiveHeldOutPlan
    Causal.candidateCausalGraph
    Occupy.canonicalOccupyEvidenceSynthesis
    General.canonicalGeneralGroupDecisionSources
    Bookchin.canonicalBookchinConfederalismSourceBoundary
    Bookchin.canonicalBookchinDASHIAlignment
    SR15.canonicalSR15SourceBoundary
    true true true true true true true true true true true true true true true

record FederatedGovernanceEvidenceBoundary : Set where
  constructor federatedGovernanceEvidenceBoundary
  field
    crossSourceAgreementCollapsesProvenance boloArchitectureAttributedToBookchin bookchinConfederalismAttributedToPM ipccTransitionEvidenceCreatesPoliticalDoctrine occupyEvidencePaysQuantitativeScalingLaw generalGroupDecisionEvidenceDirectlyValidatesOccupyScaling : Bool
    boloSourcePaysNestedArchitecture occupyArchivePaysBoundedNamedInteraction occupyArchivePaysBoundedFiniteIncidenceGraph occupyArchivePaysLongitudinalIncidenceFamily occupyArchivePaysSourceExplicitMeetingPanel dashiPaysArchivalObservationModel occupyArchivePaysProcessBurdenObservations occupyArchivePaysMeasuredMeetingDurations dashiPaysCoordinationBurdenExperimentDesign dashiPaysProspectiveHeldOutProtocol dashiPaysCausalPromotionObligationSurface occupyLiteraturePaysPluralProcessEvidence generalGroupDecisionEvidencePaysMechanismPlausibility bookchinSourcePaysRecallableConfederalCoordination sr15PaysSystemTransitionConstraintSurface : Bool
    actualPolityLegitimacyPaid actualParticipantIssueIncidencePaid empiricalCoordinationCostFunctionalPaid quantitativeIncidenceBurdenRelationshipPaid incidenceBurdenCausalEffectPromoted prospectiveHeldOutValidationPaid concreteClimateViabilityOfFederationPaid : Bool

open FederatedGovernanceEvidenceBoundary public

canonicalFederatedGovernanceEvidenceBoundary : FederatedGovernanceEvidenceBoundary
canonicalFederatedGovernanceEvidenceBoundary =
  federatedGovernanceEvidenceBoundary
    false false false false false false
    true true true true true true true true true true true true true true true
    false false false false false false false

canonicalFederatedGovernanceEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalFederatedGovernanceEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated governance evidence instantiation capstone"
    "DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact"
    "canonicalFederatedGovernanceEvidenceBoundary"
    "assembles independently attributed political-design, archival, empirical and assessment lanes with a source-explicit meeting panel, deterministic held-out protocol, causal-promotion surface and a DASHI archival event-record-coding observation model"
    "coding fidelity, documentary soundness and documentary completeness remain distinct; missingness is not zero, posted agenda count is not the observed issue set, and complete incidence, empirical cost, causal effect and prospective held-out validation remain unpaid"
    "agda -i . DASHI/Governance/FederatedGovernanceEvidenceInstantiationRegression.agda"
