module DASHI.Culture.PowersPlantationParadiseEmpiricalRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical
import DASHI.Culture.PowersPlantationParadiseInvestigationParetoExact as Routing
import DASHI.Culture.PowersPlantationParadiseHistoricalDiscriminatorExact as Discriminator
import DASHI.Culture.ColonialTheatreSensoryAccessExact as Sensory
import DASHI.Culture.PowersPlantationParadiseEvidenceGraphExact as Graph
import DASHI.Culture.PowersPlantationParadiseResearchThroughPerformanceExact as PerformanceProbe

------------------------------------------------------------------------
-- TERMINAL EMPIRICAL ROADMAP
------------------------------------------------------------------------

data ResearchPhase : Set where
  formalNonCollapse : ResearchPhase
  sourceProvenanceAtlas : ResearchPhase
  sameObjectMicrohistory : ResearchPhase
  corpusDistributionReconstruction : ResearchPhase
  historicalDiscriminationIdentification : ResearchPhase
  comparativeTemporalTransport : ResearchPhase
  scholarlyPublicSynthesis : ResearchPhase

data PhaseStatus : Set where
  closed : PhaseStatus
  closedReopenable : PhaseStatus
  substantiallyPaid : PhaseStatus
  activeFrontier : PhaseStatus
  readyButCausalityGated : PhaseStatus
  nextHorizon : PhaseStatus
  parallelReady : PhaseStatus

phaseStatus : ResearchPhase → PhaseStatus
phaseStatus formalNonCollapse = closed
phaseStatus sourceProvenanceAtlas = closedReopenable
phaseStatus sameObjectMicrohistory = substantiallyPaid
phaseStatus corpusDistributionReconstruction = activeFrontier
phaseStatus historicalDiscriminationIdentification = readyButCausalityGated
phaseStatus comparativeTemporalTransport = nextHorizon
phaseStatus scholarlyPublicSynthesis = parallelReady

data ProgrammeDeliverable : Set where
  saintDomingueEvidenceGraphV1 : ProgrammeDeliverable
  namedActorDistributionAtlas : ProgrammeDeliverable
  theatreRulesArchitecturePracticeAtlas : ProgrammeDeliverable
  minetteCompensationDossier : ProgrammeDeliverable
  historicalDiscriminatorCatalogue : ProgrammeDeliverable
  canonicalFiveAxisAcquisitionFrontier : ProgrammeDeliverable
  sensoryAccessibilityExtension : ProgrammeDeliverable
  revolutionaryDiasporaTransitionAtlas : ProgrammeDeliverable
  scholarlyDigitalSynthesis : ProgrammeDeliverable
  researchThroughPerformanceProbeSet : ProgrammeDeliverable

data DeliverableStatus : Set where
  implementedCore : DeliverableStatus
  activeBuild : DeliverableStatus
  partialEvidence : DeliverableStatus
  futureAfterCoreFibres : DeliverableStatus

statusOfDeliverable : ProgrammeDeliverable → DeliverableStatus
statusOfDeliverable saintDomingueEvidenceGraphV1 = implementedCore
statusOfDeliverable namedActorDistributionAtlas = activeBuild
statusOfDeliverable theatreRulesArchitecturePracticeAtlas = activeBuild
statusOfDeliverable minetteCompensationDossier = partialEvidence
statusOfDeliverable historicalDiscriminatorCatalogue = implementedCore
statusOfDeliverable canonicalFiveAxisAcquisitionFrontier = implementedCore
statusOfDeliverable sensoryAccessibilityExtension = implementedCore
statusOfDeliverable revolutionaryDiasporaTransitionAtlas = futureAfterCoreFibres
statusOfDeliverable scholarlyDigitalSynthesis = activeBuild
statusOfDeliverable researchThroughPerformanceProbeSet = implementedCore

nextPriorityReference : String
nextPriorityReference =
  "primary issue/page/image saturation plus actor x venue x time contribution/benefit/burden/voice joins; rule-producing instruments and residual settlement follow as discriminators reopen specific fibres"

empiricalProgrammeBoundary : Empirical.PowersEmpiricalProgrammeBoundary
empiricalProgrammeBoundary = Empirical.canonicalPowersEmpiricalProgrammeBoundary

routingBoundary : Routing.PowersInvestigationRoutingBoundary
routingBoundary = Routing.canonicalPowersInvestigationRoutingBoundary

discriminatorBoundary : Discriminator.PowersHistoricalDiscriminatorBoundary
discriminatorBoundary = Discriminator.canonicalPowersHistoricalDiscriminatorBoundary

sensoryBoundary : Sensory.ColonialTheatreSensoryAccessBoundary
sensoryBoundary = Sensory.canonicalColonialTheatreSensoryAccessBoundary

graphBoundary : Graph.PowersEvidenceGraphBoundary
graphBoundary = Graph.canonicalPowersEvidenceGraphBoundary

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
    corpusAndDistributionAreActiveFrontier : Bool
    corpusAndDistributionAreActiveFrontierIsTrue :
      corpusAndDistributionAreActiveFrontier ≡ true
    causalEffectMayBeEstimatedFromCurrentDescriptiveFibres : Bool
    causalEffectMayBeEstimatedFromCurrentDescriptiveFibresIsFalse :
      causalEffectMayBeEstimatedFromCurrentDescriptiveFibres ≡ false
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
    true refl
    true refl
