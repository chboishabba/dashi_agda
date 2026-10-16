module DASHI.Culture.PowersPlantationParadiseEmpiricalRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical
import DASHI.Culture.PowersPlantationParadiseArchiveModalityExact as ArchiveModality
import DASHI.Culture.PowersPlantationParadiseInvestigationParetoExact as Routing
import DASHI.Culture.PowersPlantationParadiseHistoricalDiscriminatorExact as Discriminator
import DASHI.Culture.ColonialTheatreSensoryAccessExact as Sensory
import DASHI.Culture.PowersPlantationParadiseEvidenceGraphExact as Graph
import DASHI.Culture.PowersPlantationParadiseMobilityRegimeTransitionExact as Mobility
import DASHI.Culture.PowersPlantationParadiseResearchThroughPerformanceExact as PerformanceProbe

------------------------------------------------------------------------
-- TERMINAL EMPIRICAL ROADMAP
------------------------------------------------------------------------

data ResearchPhase : Set where
  formalNonCollapse : ResearchPhase
  sourceProvenanceAtlas : ResearchPhase
  sameObjectMicrohistory : ResearchPhase
  primaryCorpusReconstruction : ResearchPhase
  actorDistributionReconstruction : ResearchPhase
  institutionalRuleReconstruction : ResearchPhase
  archiveModalityReconstruction : ResearchPhase
  historicalDiscrimination : ResearchPhase
  causalIdentification : ResearchPhase
  comparativeTemporalTransport : ResearchPhase
  scholarlyPublicSynthesis : ResearchPhase

data PhaseStatus : Set where
  closed : PhaseStatus
  closedReopenable : PhaseStatus
  substantiallyPaid : PhaseStatus
  activeFrontier : PhaseStatus
  ready : PhaseStatus
  causalityGated : PhaseStatus
  nextHorizon : PhaseStatus
  parallelReady : PhaseStatus

phaseStatus : ResearchPhase → PhaseStatus
phaseStatus formalNonCollapse = closed
phaseStatus sourceProvenanceAtlas = closedReopenable
phaseStatus sameObjectMicrohistory = substantiallyPaid
phaseStatus primaryCorpusReconstruction = activeFrontier
phaseStatus actorDistributionReconstruction = activeFrontier
phaseStatus institutionalRuleReconstruction = activeFrontier
phaseStatus archiveModalityReconstruction = activeFrontier
phaseStatus historicalDiscrimination = ready
phaseStatus causalIdentification = causalityGated
phaseStatus comparativeTemporalTransport = nextHorizon
phaseStatus scholarlyPublicSynthesis = parallelReady

data ProgrammeDeliverable : Set where
  saintDomingueEvidenceGraphV2 : ProgrammeDeliverable
  namedActorDistributionAtlas : ProgrammeDeliverable
  theatreRulesArchitecturePracticeAtlas : ProgrammeDeliverable
  minetteCompensationDossier : ProgrammeDeliverable
  sourceProductionModalityAtlas : ProgrammeDeliverable
  historicalDiscriminatorCatalogue : ProgrammeDeliverable
  canonicalFiveAxisAcquisitionFrontier : ProgrammeDeliverable
  sensoryAccessibilityExtension : ProgrammeDeliverable
  multilingualMobilityRegimeAtlas : ProgrammeDeliverable
  revolutionaryDiasporaTransitionAtlas : ProgrammeDeliverable
  scholarlyDigitalSynthesis : ProgrammeDeliverable
  researchThroughPerformanceProbeSet : ProgrammeDeliverable

data DeliverableStatus : Set where
  implementedCore : DeliverableStatus
  activeBuild : DeliverableStatus
  partialEvidence : DeliverableStatus
  futureAfterCoreFibres : DeliverableStatus

statusOfDeliverable : ProgrammeDeliverable → DeliverableStatus
statusOfDeliverable saintDomingueEvidenceGraphV2 = implementedCore
statusOfDeliverable namedActorDistributionAtlas = activeBuild
statusOfDeliverable theatreRulesArchitecturePracticeAtlas = activeBuild
statusOfDeliverable minetteCompensationDossier = partialEvidence
statusOfDeliverable sourceProductionModalityAtlas = implementedCore
statusOfDeliverable historicalDiscriminatorCatalogue = implementedCore
statusOfDeliverable canonicalFiveAxisAcquisitionFrontier = implementedCore
statusOfDeliverable sensoryAccessibilityExtension = implementedCore
statusOfDeliverable multilingualMobilityRegimeAtlas = partialEvidence
statusOfDeliverable revolutionaryDiasporaTransitionAtlas = futureAfterCoreFibres
statusOfDeliverable scholarlyDigitalSynthesis = activeBuild
statusOfDeliverable researchThroughPerformanceProbeSet = implementedCore

nextPriorityReference : String
nextPriorityReference =
  "primary manifestation saturation plus named actor x venue x time contribution/benefit/burden/voice joins; source genre/producer/purpose stays attached to every assertion; rule-producing instruments and residual settlement are discriminating follow-ups; causal identification remains gated"

empiricalProgrammeBoundary : Empirical.PowersEmpiricalProgrammeBoundary
empiricalProgrammeBoundary = Empirical.canonicalPowersEmpiricalProgrammeBoundary

archiveModalityBoundary : ArchiveModality.PowersArchiveModalityBoundary
archiveModalityBoundary = ArchiveModality.canonicalPowersArchiveModalityBoundary

routingBoundary : Routing.PowersInvestigationRoutingBoundary
routingBoundary = Routing.canonicalPowersInvestigationRoutingBoundary

discriminatorBoundary : Discriminator.PowersHistoricalDiscriminatorBoundary
discriminatorBoundary = Discriminator.canonicalPowersHistoricalDiscriminatorBoundary

sensoryBoundary : Sensory.ColonialTheatreSensoryAccessBoundary
sensoryBoundary = Sensory.canonicalColonialTheatreSensoryAccessBoundary

graphBoundary : Graph.PowersEvidenceGraphBoundary
graphBoundary = Graph.canonicalPowersEvidenceGraphBoundary

mobilityBoundary : Mobility.PowersMobilityRegimeBoundary
mobilityBoundary = Mobility.canonicalPowersMobilityRegimeBoundary

performanceProbeBoundary : PerformanceProbe.PowersResearchThroughPerformanceBoundary
performanceProbeBoundary = PerformanceProbe.canonicalPowersResearchThroughPerformanceBoundary

record PowersEmpiricalRoadmapBoundary : Set where
  constructor powers-empirical-roadmap-boundary
  field
    genericFormalTheoryIsCurrentBottleneck : Bool
    genericFormalTheoryIsCurrentBottleneckIsFalse :
      genericFormalTheoryIsCurrentBottleneck ≡ false
    sameObjectEmpiricalAcquisitionIsCurrentBottleneck : Bool
    sameObjectEmpiricalAcquisitionIsCurrentBottleneckIsTrue :
      sameObjectEmpiricalAcquisitionIsCurrentBottleneck ≡ true
    corpusDistributionRulesAndModalityAreActiveFrontier : Bool
    corpusDistributionRulesAndModalityAreActiveFrontierIsTrue :
      corpusDistributionRulesAndModalityAreActiveFrontier ≡ true
    causalEffectMayBeEstimatedFromCurrentDescriptiveFibres : Bool
    causalEffectMayBeEstimatedFromCurrentDescriptiveFibresIsFalse :
      causalEffectMayBeEstimatedFromCurrentDescriptiveFibres ≡ false
    sourceSilenceMayBeComparedWithoutProductionContext : Bool
    sourceSilenceMayBeComparedWithoutProductionContextIsFalse :
      sourceSilenceMayBeComparedWithoutProductionContext ≡ false
    revolutionaryDiasporaTransportRequiresScopeReceipts : Bool
    revolutionaryDiasporaTransportRequiresScopeReceiptsIsTrue :
      revolutionaryDiasporaTransportRequiresScopeReceipts ≡ true
    publicSynthesisMayProceedWithExplicitUncertainty : Bool
    publicSynthesisMayProceedWithExplicitUncertaintyIsTrue :
      publicSynthesisMayProceedWithExplicitUncertainty ≡ true

canonicalPowersEmpiricalRoadmapBoundary : PowersEmpiricalRoadmapBoundary
canonicalPowersEmpiricalRoadmapBoundary =
  powers-empirical-roadmap-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
