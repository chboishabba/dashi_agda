module DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo
import DASHI.Governance.OccupyConsensusEvidenceAtlasExact as Occupy
import DASHI.Governance.OccupyParticipantPseudonymisationExact as Privacy
import DASHI.Governance.OccupyArchivalIncidenceEvidenceExact as Archive
import DASHI.Governance.OccupyArchivalObservationModelExact as Observation
import DASHI.Governance.OccupyFilesCorpusReceiptExact as Corpus
import DASHI.Governance.OccupyOWSManifestExact as Manifest
import DASHI.Governance.OccupyOWSDevelopmentDurationPanelExact as OWSDuration
import DASHI.Governance.OccupyOWSDevelopmentTextProcessPanelExact as OWSText
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
  primaryPoliticalDesignSource primaryArchivalRecord curatedArchiveMetadata empiricalSocialMovementStudy externalGroupDecisionExperiment primaryAssessmentSource dashiDerivedBridge : EvidenceProvenanceClass

data EvidenceLane : Set where
  boloPrimaryLane occupyArchivalLane occupyCuratedCorpusLane occupyEmpiricalLane generalGroupDecisionLane bookchinPrimaryLane sr15PrimaryLane : EvidenceLane

laneClass : EvidenceLane → EvidenceProvenanceClass
laneClass boloPrimaryLane = primaryPoliticalDesignSource
laneClass occupyArchivalLane = primaryArchivalRecord
laneClass occupyCuratedCorpusLane = curatedArchiveMetadata
laneClass occupyEmpiricalLane = empiricalSocialMovementStudy
laneClass generalGroupDecisionLane = externalGroupDecisionExperiment
laneClass bookchinPrimaryLane = primaryPoliticalDesignSource
laneClass sr15PrimaryLane = primaryAssessmentSource

record FederatedGovernanceEvidenceInstantiation : Set where
  constructor federatedGovernanceEvidenceInstantiation
  field
    boloAtlas : Bolo.BoloBoloPrimarySourceAtlas
    participantPrivacyBoundary : Privacy.PseudonymisationBoundary
    occupyCorpusReceipt : Corpus.OccupyFilesCorpusReceipt
    occupyOWSManifest : List Manifest.OWSRecord
    occupyOWSDevelopmentDurations : List OWSDuration.OWSDurationRow
    occupyOWSDevelopmentTextProcess : List OWSText.TextProcessRow
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
    participantPseudonymisationPresent materialisedOccupyCorpusPresent checksumPinnedOWSManifestPresent protectedHoldoutAssignmentPresent owsDevelopmentDurationPanelPresent owsDevelopmentTextProcessPanelPresent nestedCommunityArchitectureEvidencePresent boundedArchivalInteractionEvidencePresent boundedFiniteArchivalIncidenceGraphPresent longitudinalArchivalIncidenceFamilyPresent sourceExplicitMeetingPanelPresent archivalObservationModelPresent archivalProcessBurdenObservationsPresent measuredMeetingDurationEvidencePresent coordinationBurdenExperimentDesignPresent prospectiveHeldOutProtocolPresent causalPromotionObligationSurfacePresent consensusBurdenBenefitPluralEvidencePresent generalGroupDecisionQuantitativeEvidencePresent recallableConfederalCoordinationEvidencePresent transitionViabilityConstraintEvidencePresent : Bool

open FederatedGovernanceEvidenceInstantiation public

canonicalFederatedGovernanceEvidenceInstantiation : FederatedGovernanceEvidenceInstantiation
canonicalFederatedGovernanceEvidenceInstantiation =
  federatedGovernanceEvidenceInstantiation
    Bolo.canonicalBoloBoloPrimarySourceAtlas
    Privacy.canonicalPseudonymisationBoundary
    Corpus.canonicalOccupyFilesCorpusReceipt
    Manifest.canonicalOWSRecords
    OWSDuration.canonicalOWSDurationRows
    OWSText.canonicalTextProcessRows
    Archive.boundedSpeakerProposalCandidate
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
    true true true true true true
    true true true true true true true true true true true true true true true true

record FederatedGovernanceEvidenceBoundary : Set where
  constructor federatedGovernanceEvidenceBoundary
  field
    crossSourceAgreementCollapsesProvenance boloArchitectureAttributedToBookchin bookchinConfederalismAttributedToPM ipccTransitionEvidenceCreatesPoliticalDoctrine occupyEvidencePaysQuantitativeScalingLaw generalGroupDecisionEvidenceDirectlyValidatesOccupyScaling curatedArchiveMetadataBecomesUnderlyingMinuteAuthorship rawParticipantNamesRequiredForCorrelation : Bool
    dashiPaysParticipantPseudonymisation occupyCorpusMaterialisationPaid occupyOWSManifestFreezePaid occupyProtectedHoldoutAssignmentPaid occupyOWSDevelopmentDurationPanelPaid occupyOWSDevelopmentTextProcessPanelPaid boloSourcePaysNestedArchitecture occupyArchivePaysBoundedNamedInteraction occupyArchivePaysBoundedFiniteIncidenceGraph occupyArchivePaysLongitudinalIncidenceFamily occupyArchivePaysSourceExplicitMeetingPanel dashiPaysArchivalObservationModel occupyArchivePaysProcessBurdenObservations occupyArchivePaysMeasuredMeetingDurations dashiPaysCoordinationBurdenExperimentDesign dashiPaysProspectiveHeldOutProtocol dashiPaysCausalPromotionObligationSurface occupyLiteraturePaysPluralProcessEvidence generalGroupDecisionEvidencePaysMechanismPlausibility bookchinSourcePaysRecallableConfederalCoordination sr15PaysSystemTransitionConstraintSurface : Bool
    actualPolityLegitimacyPaid actualParticipantIssueIncidencePaid empiricalCoordinationCostFunctionalPaid quantitativeIncidenceBurdenRelationshipPaid incidenceBurdenCausalEffectPromoted prospectiveHeldOutValidationPaid concreteClimateViabilityOfFederationPaid : Bool

open FederatedGovernanceEvidenceBoundary public

canonicalFederatedGovernanceEvidenceBoundary : FederatedGovernanceEvidenceBoundary
canonicalFederatedGovernanceEvidenceBoundary =
  federatedGovernanceEvidenceBoundary
    false false false false false false false false
    true true true true true true
    true true true true true true true true true true true true true true true
    false false false false false false false

canonicalFederatedGovernanceEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalFederatedGovernanceEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated governance evidence instantiation capstone"
    "DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact"
    "canonicalFederatedGovernanceEvidenceBoundary"
    "assembles independently attributed political-design, archival, curated-corpus, empirical and assessment lanes with keyed-HMAC participant pseudonyms, materialised/checksum-pinned OWS corpus, protected holdout, development duration/lexical panels and causal-promotion obligations"
    "raw participant names are not required for longitudinal correlation and are not propagated in derived incidence tables; private key/map are not committed, aliases are not silently merged, and corpus evidence still does not pay complete incidence, empirical coordination cost, causal effect or held-out validation"
    "agda -i . DASHI/Governance/FederatedGovernanceEvidenceInstantiationRegression.agda"
