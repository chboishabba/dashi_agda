module DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo
import DASHI.Governance.BoloBoloIncidenceCompressionExact as Compression
import DASHI.Governance.BoloBoloIncidenceCompressionCostBridgeExact as CompressionBridge
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Robust
import DASHI.Governance.BoloBoloNestedCostBoundCompilerExact as ComponentCompiler
import DASHI.Governance.BoloBoloPracticalSignificanceExact as Significance
import DASHI.Governance.BoloBoloLinearCalibrationBoundCompilerExact as LinearCompiler
import DASHI.Governance.BoloBoloCalibrationTransferExact as Transfer
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as PairedExperiment
import DASHI.Governance.BoloBoloEmpiricalPromotionGateExact as Promotion
import DASHI.Governance.BoloBoloModelClassRobustnessExact as ModelRobustness
import DASHI.Governance.OccupyConsensusEvidenceAtlasExact as Occupy
import DASHI.Governance.OccupyParticipantPseudonymisationExact as Privacy
import DASHI.Governance.OccupyArchivalIncidenceEvidenceExact as Archive
import DASHI.Governance.OccupyArchivalObservationModelExact as Observation
import DASHI.Governance.OccupyFilesCorpusReceiptExact as Corpus
import DASHI.Governance.OccupyOWSManifestExact as Manifest
import DASHI.Governance.OccupyOWSDevelopmentDurationPanelExact as OWSDuration
import DASHI.Governance.OccupyOWSDevelopmentTextProcessPanelExact as OWSText
import DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelExact as OWSInterface
import DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact as LibraryGraph
import DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact as Longitudinal
import DASHI.Governance.OccupyPseudonymousNetworkFeaturesExact as Network
import DASHI.Governance.OccupyLibraryMeetingDurationEvidenceExact as Duration
import DASHI.Governance.OccupyMeetingPanelExact as Panel
import DASHI.Governance.OccupyMeetingLevelProcessPanelExact as ProcessPanel
import DASHI.Governance.OccupyPanelMissingnessAuditExact as Missingness
import DASHI.Governance.OccupyDevelopmentDiagnosticsExact as Diagnostics
import DASHI.Governance.OccupyHoldoutPromotionGateExact as HoldoutGate
import DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact as BurdenDesign
import DASHI.Governance.OccupyHeldOutMeetingValidationExact as HeldOut
import DASHI.Governance.OccupyCoordinationCausalPromotionExact as Causal
import DASHI.Governance.GeneralGroupDecisionQuantitativeEvidenceAtlasExact as General
import DASHI.Governance.BookchinConfederalismAuthorityBridgeExact as Bookchin
import DASHI.Governance.IPCCSR15TransitionViabilityBridgeExact as SR15

data EvidenceProvenanceClass : Set where
  primaryPoliticalDesignSource : EvidenceProvenanceClass
  primaryArchivalRecord : EvidenceProvenanceClass
  curatedArchiveMetadata : EvidenceProvenanceClass
  empiricalSocialMovementStudy : EvidenceProvenanceClass
  externalGroupDecisionExperiment : EvidenceProvenanceClass
  primaryAssessmentSource : EvidenceProvenanceClass
  dashiDerivedBridge : EvidenceProvenanceClass

data EvidenceLane : Set where
  boloPrimaryLane : EvidenceLane
  occupyArchivalLane : EvidenceLane
  occupyCuratedCorpusLane : EvidenceLane
  occupyEmpiricalLane : EvidenceLane
  generalGroupDecisionLane : EvidenceLane
  bookchinPrimaryLane : EvidenceLane
  sr15PrimaryLane : EvidenceLane

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
    boloCompressionBoundary : Compression.IncidenceCompressionBoundary
    boloCompressionCostBridgeBoundary : CompressionBridge.CompressionCostBridgeBoundary
    robustBoloBoundTargets : Robust.NestedCostBoundTargets
    nestedCostBoundCompilerBoundary : ComponentCompiler.NestedCostBoundCompilerBoundary
    practicalSignificanceBoundary : Significance.PracticalSignificanceBoundary
    linearCalibrationCompilerBoundary : LinearCompiler.LinearCalibrationCompilerBoundary
    boloTransferBoundary : Transfer.CalibrationTransferBoundary
    directBoloExperimentMapping : PairedExperiment.CounterfactualTermMappingPlan
    boloPromotionBoundary : Promotion.EmpiricalPromotionBoundary
    boloMeaningfulPromotionBoundary : Promotion.MeaningfulPromotionBoundary
    boloModelClassRobustnessBoundary : ModelRobustness.ModelClassRobustnessBoundary

    participantPrivacyBoundary : Privacy.PseudonymisationBoundary
    occupyCorpusReceipt : Corpus.OccupyFilesCorpusReceipt
    occupyOWSManifest : List Manifest.OWSRecord
    occupyOWSDevelopmentDurations : List OWSDuration.OWSDurationRow
    occupyOWSDevelopmentTextProcess : List OWSText.TextProcessRow
    occupyOWSDevelopmentInterfaceProcess : List OWSInterface.InterfaceProcessRow
    occupyArchiveCandidate : Archive.ArchivalIncidenceCandidate
    occupyLibraryObservedEdges : List LibraryGraph.ObservedEdge
    occupyLongitudinalObservedEdges : List Longitudinal.LongitudinalEdge
    occupyPseudonymousNetworkFeatures : List Network.NetworkFeatureRow
    occupyDevelopmentMeetingPanel : List Panel.MeetingPanelRow
    occupyMeetingLevelProcessPanel : ProcessPanel.MeetingLevelProcessPanel
    occupyMissingnessAudit : Missingness.PanelMissingnessAudit
    occupyDevelopmentDiagnosticBoundary : Diagnostics.DevelopmentDiagnosticBoundary
    occupyHoldoutPromotionBoundary : HoldoutGate.HoldoutPromotionBoundary
    oct15Duration : Duration.MeetingDurationObservation
    oct22Duration : Duration.MeetingDurationObservation
    prospectiveHeldOutPlan : HeldOut.ProspectiveHeldOutPlan
    candidateCausalGraph : List Causal.CandidateCausalEdge
    occupySynthesis : Occupy.OccupyEvidenceSynthesis
    generalGroupDecisionSources : List General.GeneralGroupDecisionSource
    bookchinSource : Bookchin.BookchinConfederalismSourceBoundary
    bookchinBridge : Bookchin.BookchinDASHIAlignment
    sr15Source : SR15.SR15SourceBoundary

    participantPseudonymisationPresent : Bool
    materialisedOccupyCorpusPresent : Bool
    checksumPinnedOWSManifestPresent : Bool
    protectedHoldoutAssignmentPresent : Bool
    owsDevelopmentDurationPanelPresent : Bool
    owsDevelopmentTextProcessPanelPresent : Bool
    owsDevelopmentInterfaceProcessPanelPresent : Bool
    pseudonymousNetworkFeaturesPresent : Bool
    meetingLevelProcessPanelPresent : Bool
    panelMissingnessAuditPresent : Bool
    developmentDiagnosticsPresent : Bool
    holdoutPromotionGatePresent : Bool
    nestedCommunityArchitectureEvidencePresent : Bool
    boundedArchivalInteractionEvidencePresent : Bool
    boundedFiniteArchivalIncidenceGraphPresent : Bool
    longitudinalArchivalIncidenceFamilyPresent : Bool
    sourceExplicitMeetingPanelPresent : Bool
    archivalObservationModelPresent : Bool
    archivalProcessBurdenObservationsPresent : Bool
    measuredMeetingDurationEvidencePresent : Bool
    coordinationBurdenExperimentDesignPresent : Bool
    prospectiveHeldOutProtocolPresent : Bool
    causalPromotionObligationSurfacePresent : Bool
    incidenceCompressionScenarioPresent : Bool
    incidenceCompressionCostBridgePresent : Bool
    robustCostBoundTheoremPresent : Bool
    componentwiseCostBoundCompilerPresent : Bool
    practicalSignificanceGatePresent : Bool
    linearCalibrationBoundCompilerPresent : Bool
    calibrationTransferFirewallPresent : Bool
    directFlatNestedExperimentDesignPresent : Bool
    empiricalBoloPromotionGatePresent : Bool
    meaningfulBoloPromotionGatePresent : Bool
    modelClassRobustnessGatePresent : Bool
    consensusBurdenBenefitPluralEvidencePresent : Bool
    generalGroupDecisionQuantitativeEvidencePresent : Bool
    recallableConfederalCoordinationEvidencePresent : Bool
    transitionViabilityConstraintEvidencePresent : Bool

open FederatedGovernanceEvidenceInstantiation public

canonicalFederatedGovernanceEvidenceInstantiation : FederatedGovernanceEvidenceInstantiation
canonicalFederatedGovernanceEvidenceInstantiation = record
  { boloAtlas = Bolo.canonicalBoloBoloPrimarySourceAtlas
  ; boloCompressionBoundary = Compression.canonicalIncidenceCompressionBoundary
  ; boloCompressionCostBridgeBoundary = CompressionBridge.canonicalCompressionCostBridgeBoundary
  ; robustBoloBoundTargets = Robust.canonicalNestedCostBoundTargets
  ; nestedCostBoundCompilerBoundary = ComponentCompiler.canonicalNestedCostBoundCompilerBoundary
  ; practicalSignificanceBoundary = Significance.canonicalPracticalSignificanceBoundary
  ; linearCalibrationCompilerBoundary = LinearCompiler.canonicalLinearCalibrationCompilerBoundary
  ; boloTransferBoundary = Transfer.canonicalCalibrationTransferBoundary
  ; directBoloExperimentMapping = PairedExperiment.canonicalCounterfactualTermMappingPlan
  ; boloPromotionBoundary = Promotion.canonicalEmpiricalPromotionBoundary
  ; boloMeaningfulPromotionBoundary = Promotion.canonicalMeaningfulPromotionBoundary
  ; boloModelClassRobustnessBoundary = ModelRobustness.canonicalModelClassRobustnessBoundary
  ; participantPrivacyBoundary = Privacy.canonicalPseudonymisationBoundary
  ; occupyCorpusReceipt = Corpus.canonicalOccupyFilesCorpusReceipt
  ; occupyOWSManifest = Manifest.canonicalOWSRecords
  ; occupyOWSDevelopmentDurations = OWSDuration.canonicalOWSDurationRows
  ; occupyOWSDevelopmentTextProcess = OWSText.canonicalTextProcessRows
  ; occupyOWSDevelopmentInterfaceProcess = OWSInterface.canonicalInterfaceProcessRows
  ; occupyArchiveCandidate = Archive.boundedSpeakerProposalCandidate
  ; occupyLibraryObservedEdges = LibraryGraph.canonicalObservedEdges
  ; occupyLongitudinalObservedEdges = Longitudinal.longitudinalObservedEdges
  ; occupyPseudonymousNetworkFeatures = Network.canonicalNetworkFeatureRows
  ; occupyDevelopmentMeetingPanel = Panel.canonicalDevelopmentPanel
  ; occupyMeetingLevelProcessPanel = ProcessPanel.canonicalMeetingLevelProcessPanel
  ; occupyMissingnessAudit = Missingness.canonicalMissingnessAudit
  ; occupyDevelopmentDiagnosticBoundary = Diagnostics.canonicalDevelopmentDiagnosticBoundary
  ; occupyHoldoutPromotionBoundary = HoldoutGate.canonicalHoldoutPromotionBoundary
  ; oct15Duration = Duration.oct15FirstFormalMeeting
  ; oct22Duration = Duration.oct22Meeting
  ; prospectiveHeldOutPlan = HeldOut.canonicalProspectiveHeldOutPlan
  ; candidateCausalGraph = Causal.candidateCausalGraph
  ; occupySynthesis = Occupy.canonicalOccupyEvidenceSynthesis
  ; generalGroupDecisionSources = General.canonicalGeneralGroupDecisionSources
  ; bookchinSource = Bookchin.canonicalBookchinConfederalismSourceBoundary
  ; bookchinBridge = Bookchin.canonicalBookchinDASHIAlignment
  ; sr15Source = SR15.canonicalSR15SourceBoundary
  ; participantPseudonymisationPresent = true
  ; materialisedOccupyCorpusPresent = true
  ; checksumPinnedOWSManifestPresent = true
  ; protectedHoldoutAssignmentPresent = true
  ; owsDevelopmentDurationPanelPresent = true
  ; owsDevelopmentTextProcessPanelPresent = true
  ; owsDevelopmentInterfaceProcessPanelPresent = true
  ; pseudonymousNetworkFeaturesPresent = true
  ; meetingLevelProcessPanelPresent = true
  ; panelMissingnessAuditPresent = true
  ; developmentDiagnosticsPresent = true
  ; holdoutPromotionGatePresent = true
  ; nestedCommunityArchitectureEvidencePresent = true
  ; boundedArchivalInteractionEvidencePresent = true
  ; boundedFiniteArchivalIncidenceGraphPresent = true
  ; longitudinalArchivalIncidenceFamilyPresent = true
  ; sourceExplicitMeetingPanelPresent = true
  ; archivalObservationModelPresent = true
  ; archivalProcessBurdenObservationsPresent = true
  ; measuredMeetingDurationEvidencePresent = true
  ; coordinationBurdenExperimentDesignPresent = true
  ; prospectiveHeldOutProtocolPresent = true
  ; causalPromotionObligationSurfacePresent = true
  ; incidenceCompressionScenarioPresent = true
  ; incidenceCompressionCostBridgePresent = true
  ; robustCostBoundTheoremPresent = true
  ; componentwiseCostBoundCompilerPresent = true
  ; practicalSignificanceGatePresent = true
  ; linearCalibrationBoundCompilerPresent = true
  ; calibrationTransferFirewallPresent = true
  ; directFlatNestedExperimentDesignPresent = true
  ; empiricalBoloPromotionGatePresent = true
  ; meaningfulBoloPromotionGatePresent = true
  ; modelClassRobustnessGatePresent = true
  ; consensusBurdenBenefitPluralEvidencePresent = true
  ; generalGroupDecisionQuantitativeEvidencePresent = true
  ; recallableConfederalCoordinationEvidencePresent = true
  ; transitionViabilityConstraintEvidencePresent = true
  }

record FederatedGovernanceEvidenceBoundary : Set where
  constructor federatedGovernanceEvidenceBoundary
  field
    crossSourceAgreementCollapsesProvenance : Bool
    boloArchitectureAttributedToBookchin : Bool
    bookchinConfederalismAttributedToPM : Bool
    ipccTransitionEvidenceCreatesPoliticalDoctrine : Bool
    occupyEvidencePaysQuantitativeScalingLaw : Bool
    generalGroupDecisionEvidenceDirectlyValidatesOccupyScaling : Bool
    curatedArchiveMetadataBecomesUnderlyingMinuteAuthorship : Bool
    rawParticipantNamesRequiredForCorrelation : Bool
    completeNamedParticipantIssueMatrixRequired : Bool

    dashiPaysParticipantPseudonymisation : Bool
    occupyCorpusMaterialisationPaid : Bool
    occupyOWSManifestFreezePaid : Bool
    occupyProtectedHoldoutAssignmentPaid : Bool
    occupyOWSDevelopmentDurationPanelPaid : Bool
    occupyOWSDevelopmentTextProcessPanelPaid : Bool
    dashiPaysOWSInterfaceProcessPanel : Bool
    dashiPaysPseudonymousNetworkFeatures : Bool
    dashiPaysMeetingLevelProcessPanel : Bool
    dashiPaysPanelMissingnessAudit : Bool
    dashiPaysDevelopmentDiagnostics : Bool
    dashiPaysHoldoutPromotionGate : Bool
    boloSourcePaysNestedArchitecture : Bool
    occupyArchivePaysBoundedNamedInteraction : Bool
    occupyArchivePaysBoundedFiniteIncidenceGraph : Bool
    occupyArchivePaysLongitudinalIncidenceFamily : Bool
    occupyArchivePaysSourceExplicitMeetingPanel : Bool
    dashiPaysArchivalObservationModel : Bool
    occupyArchivePaysProcessBurdenObservations : Bool
    occupyArchivePaysMeasuredMeetingDurations : Bool
    dashiPaysCoordinationBurdenExperimentDesign : Bool
    dashiPaysProspectiveHeldOutProtocol : Bool
    dashiPaysCausalPromotionObligationSurface : Bool
    dashiPaysIncidenceCompressionScenario : Bool
    dashiPaysIncidenceCompressionCostBridge : Bool
    dashiPaysRobustCostBoundTheorem : Bool
    dashiPaysComponentwiseCostBoundCompiler : Bool
    dashiPaysPracticalSignificanceGate : Bool
    dashiPaysLinearCalibrationBoundCompiler : Bool
    dashiPaysCalibrationTransferFirewall : Bool
    dashiPaysDirectFlatNestedExperimentDesign : Bool
    dashiPaysEmpiricalBoloPromotionGate : Bool
    dashiPaysMeaningfulBoloPromotionGate : Bool
    dashiPaysModelClassRobustnessGate : Bool
    occupyLiteraturePaysPluralProcessEvidence : Bool
    generalGroupDecisionEvidencePaysMechanismPlausibility : Bool
    bookchinSourcePaysRecallableConfederalCoordination : Bool
    sr15PaysSystemTransitionConstraintSurface : Bool

    targetQualifiedBoloCostBoundsPaid : Bool
    minimumMeaningfulThresholdPaid : Bool
    admissibleTargetModelFamilyPaid : Bool
    robustBoloCoordinationWinPaid : Bool
    validatedBoloCoordinationAdvantagePaid : Bool
    validatedBoloCoordinationDisadvantagePaid : Bool
    validatedMeaningfulBoloAdvantagePaid : Bool
    validatedMeaningfulBoloDisadvantagePaid : Bool
    uniformModelFamilyAdvantagePaid : Bool
    uniformModelFamilyDisadvantagePaid : Bool
    directFlatNestedExperimentRun : Bool
    actualPolityLegitimacyPaid : Bool
    actualParticipantIssueIncidencePaid : Bool
    empiricalCoordinationCostFunctionalPaid : Bool
    quantitativeIncidenceBurdenRelationshipPaid : Bool
    incidenceBurdenCausalEffectPromoted : Bool
    prospectiveHeldOutValidationPaid : Bool
    concreteClimateViabilityOfFederationPaid : Bool

open FederatedGovernanceEvidenceBoundary public

canonicalFederatedGovernanceEvidenceBoundary : FederatedGovernanceEvidenceBoundary
canonicalFederatedGovernanceEvidenceBoundary = record
  { crossSourceAgreementCollapsesProvenance = false
  ; boloArchitectureAttributedToBookchin = false
  ; bookchinConfederalismAttributedToPM = false
  ; ipccTransitionEvidenceCreatesPoliticalDoctrine = false
  ; occupyEvidencePaysQuantitativeScalingLaw = false
  ; generalGroupDecisionEvidenceDirectlyValidatesOccupyScaling = false
  ; curatedArchiveMetadataBecomesUnderlyingMinuteAuthorship = false
  ; rawParticipantNamesRequiredForCorrelation = false
  ; completeNamedParticipantIssueMatrixRequired = false
  ; dashiPaysParticipantPseudonymisation = true
  ; occupyCorpusMaterialisationPaid = true
  ; occupyOWSManifestFreezePaid = true
  ; occupyProtectedHoldoutAssignmentPaid = true
  ; occupyOWSDevelopmentDurationPanelPaid = true
  ; occupyOWSDevelopmentTextProcessPanelPaid = true
  ; dashiPaysOWSInterfaceProcessPanel = true
  ; dashiPaysPseudonymousNetworkFeatures = true
  ; dashiPaysMeetingLevelProcessPanel = true
  ; dashiPaysPanelMissingnessAudit = true
  ; dashiPaysDevelopmentDiagnostics = true
  ; dashiPaysHoldoutPromotionGate = true
  ; boloSourcePaysNestedArchitecture = true
  ; occupyArchivePaysBoundedNamedInteraction = true
  ; occupyArchivePaysBoundedFiniteIncidenceGraph = true
  ; occupyArchivePaysLongitudinalIncidenceFamily = true
  ; occupyArchivePaysSourceExplicitMeetingPanel = true
  ; dashiPaysArchivalObservationModel = true
  ; occupyArchivePaysProcessBurdenObservations = true
  ; occupyArchivePaysMeasuredMeetingDurations = true
  ; dashiPaysCoordinationBurdenExperimentDesign = true
  ; dashiPaysProspectiveHeldOutProtocol = true
  ; dashiPaysCausalPromotionObligationSurface = true
  ; dashiPaysIncidenceCompressionScenario = true
  ; dashiPaysIncidenceCompressionCostBridge = true
  ; dashiPaysRobustCostBoundTheorem = true
  ; dashiPaysComponentwiseCostBoundCompiler = true
  ; dashiPaysPracticalSignificanceGate = true
  ; dashiPaysLinearCalibrationBoundCompiler = true
  ; dashiPaysCalibrationTransferFirewall = true
  ; dashiPaysDirectFlatNestedExperimentDesign = true
  ; dashiPaysEmpiricalBoloPromotionGate = true
  ; dashiPaysMeaningfulBoloPromotionGate = true
  ; dashiPaysModelClassRobustnessGate = true
  ; occupyLiteraturePaysPluralProcessEvidence = true
  ; generalGroupDecisionEvidencePaysMechanismPlausibility = true
  ; bookchinSourcePaysRecallableConfederalCoordination = true
  ; sr15PaysSystemTransitionConstraintSurface = true
  ; targetQualifiedBoloCostBoundsPaid = false
  ; minimumMeaningfulThresholdPaid = false
  ; admissibleTargetModelFamilyPaid = false
  ; robustBoloCoordinationWinPaid = false
  ; validatedBoloCoordinationAdvantagePaid = false
  ; validatedBoloCoordinationDisadvantagePaid = false
  ; validatedMeaningfulBoloAdvantagePaid = false
  ; validatedMeaningfulBoloDisadvantagePaid = false
  ; uniformModelFamilyAdvantagePaid = false
  ; uniformModelFamilyDisadvantagePaid = false
  ; directFlatNestedExperimentRun = false
  ; actualPolityLegitimacyPaid = false
  ; actualParticipantIssueIncidencePaid = false
  ; empiricalCoordinationCostFunctionalPaid = false
  ; quantitativeIncidenceBurdenRelationshipPaid = false
  ; incidenceBurdenCausalEffectPromoted = false
  ; prospectiveHeldOutValidationPaid = false
  ; concreteClimateViabilityOfFederationPaid = false
  }

canonicalFederatedGovernanceEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalFederatedGovernanceEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated governance evidence instantiation capstone"
    "DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact"
    "canonicalFederatedGovernanceEvidenceBoundary"
    "assembles independently attributed political-design, archival, curated-corpus, empirical and assessment lanes with privacy-preserving longitudinal features, meeting-level process data, OWS interface-process lexical surfaces, explicit missingness and holdout gates, incidence-compression accounting, robust bolo cost-bound theorems, componentwise and count-times-weight bound compilers, a practical-significance gate, cross-context transfer firewall, direct flat-vs-nested experiment design, symmetric meaningful promotion/falsification and predeclared model-class robustness"
    "the evidence still does not supply target-qualified primitive cost bounds, a target-study meaningful threshold or admissible model family, a robust/validated meaningful target coordination classification, a completed flat-vs-nested experiment, an empirical coordination-cost functional, an incidence-to-burden causal effect, political legitimacy or concrete federation viability"
    "agda -i . DASHI/Governance/FederatedGovernanceEvidenceInstantiationRegression.agda"
