module DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo
import DASHI.Governance.OccupyConsensusEvidenceAtlasExact as Occupy
import DASHI.Governance.OccupyArchivalIncidenceEvidenceExact as Archive
import DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact as LibraryGraph
import DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact as Longitudinal
import DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact as BurdenDesign
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
  primaryAssessmentSource : EvidenceProvenanceClass
  dashiDerivedBridge : EvidenceProvenanceClass

data EvidenceLane : Set where
  boloPrimaryLane : EvidenceLane
  occupyArchivalLane : EvidenceLane
  occupyEmpiricalLane : EvidenceLane
  bookchinPrimaryLane : EvidenceLane
  sr15PrimaryLane : EvidenceLane

laneClass : EvidenceLane → EvidenceProvenanceClass
laneClass boloPrimaryLane = primaryPoliticalDesignSource
laneClass occupyArchivalLane = primaryArchivalRecord
laneClass occupyEmpiricalLane = empiricalSocialMovementStudy
laneClass bookchinPrimaryLane = primaryPoliticalDesignSource
laneClass sr15PrimaryLane = primaryAssessmentSource

record FederatedGovernanceEvidenceInstantiation : Set where
  constructor federatedGovernanceEvidenceInstantiation
  field
    boloAtlas : Bolo.BoloBoloPrimarySourceAtlas
    occupyArchiveCandidate : Archive.ArchivalIncidenceCandidate
    occupyLibraryObservedEdges : List LibraryGraph.ObservedEdge
    occupyLongitudinalObservedEdges : List Longitudinal.LongitudinalEdge
    occupySynthesis : Occupy.OccupyEvidenceSynthesis
    bookchinSource : Bookchin.BookchinConfederalismSourceBoundary
    bookchinBridge : Bookchin.BookchinDASHIAlignment
    sr15Source : SR15.SR15SourceBoundary

    nestedCommunityArchitectureEvidencePresent : Bool
    boundedArchivalInteractionEvidencePresent : Bool
    boundedFiniteArchivalIncidenceGraphPresent : Bool
    longitudinalArchivalIncidenceFamilyPresent : Bool
    archivalProcessBurdenObservationsPresent : Bool
    coordinationBurdenExperimentDesignPresent : Bool
    consensusBurdenBenefitPluralEvidencePresent : Bool
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
    Occupy.canonicalOccupyEvidenceSynthesis
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

    boloSourcePaysNestedArchitecture : Bool
    occupyArchivePaysBoundedNamedInteraction : Bool
    occupyArchivePaysBoundedFiniteIncidenceGraph : Bool
    occupyArchivePaysLongitudinalIncidenceFamily : Bool
    occupyArchivePaysProcessBurdenObservations : Bool
    dashiPaysCoordinationBurdenExperimentDesign : Bool
    occupyLiteraturePaysPluralProcessEvidence : Bool
    bookchinSourcePaysRecallableConfederalCoordination : Bool
    sr15PaysSystemTransitionConstraintSurface : Bool

    actualPolityLegitimacyPaid : Bool
    actualParticipantIssueIncidencePaid : Bool
    empiricalCoordinationCostFunctionalPaid : Bool
    quantitativeIncidenceBurdenRelationshipPaid : Bool
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

canonicalFederatedGovernanceEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalFederatedGovernanceEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated governance evidence instantiation capstone"
    "DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact"
    "canonicalFederatedGovernanceEvidenceBoundary"
    "assembles independently attributed bolo'bolo, bounded and longitudinal Occupy archival incidence, archival process-strain observations, Occupy scholarship, Bookchin confederalism, IPCC SR1.5 evidence and a DASHI-derived experiment-design frontier while preserving source class and claim ceilings"
    "fifty-two admitted archival rows and qualitative process-strain co-occurrences are descriptive only; complete real-institution incidence, an empirical coordination-cost functional, a quantitative incidence-to-burden relationship, actual legitimacy and concrete climate viability remain unpaid"
    "agda -i . DASHI/Governance/FederatedGovernanceEvidenceInstantiationRegression.agda"
