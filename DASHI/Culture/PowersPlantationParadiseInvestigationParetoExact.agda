module DASHI.Culture.PowersPlantationParadiseInvestigationParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ITIRInvestigationAcquisitionParetoExact as ITIR
import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical

------------------------------------------------------------------------
-- POWERS EMPIRICAL ACQUISITION ON THE CANONICAL ITIR FIVE-AXIS SURFACE
--
-- Coordinates are routing calibration only.  They are not probabilities,
-- truth values, historical-importance scores or welfare/culpability measures.
------------------------------------------------------------------------

primaryCorpusCandidate : ITIR.InvestigationCandidate
primaryCorpusCandidate =
  ITIR.investigation-candidate
    "powers:primary-corpus-saturation"
    "leaf:primaryCorpusSaturationLeaf"
    "Affiches/ANOM issue-page-image rooting and event-row expansion"
    "public/institutional/archive access subject to lawful availability"
    "Powers -> Prest/St-Andrews -> Affiches/ANOM"
    "axis calibration: broad event/person/rule dependency reopening"
    10 10 10 9 4
    true refl false refl false refl

actorDistributionCandidate : ITIR.InvestigationCandidate
actorDistributionCandidate =
  ITIR.investigation-candidate
    "powers:actor-distribution-incidence"
    "leaf:distributionalIncidenceLeaf"
    "join contribution/benefit/burden/voice/status at actor x venue x time"
    "public scholarly/archival sources; no unlawful private-record acquisition"
    "Prest 2023 -> named enslaved-musician notices -> venue/person records"
    "axis calibration: high residual coverage and direct substantive discrimination"
    10 9 10 8 5
    true refl false refl false refl

compensationSettlementCandidate : ITIR.InvestigationCandidate
compensationSettlementCandidate =
  ITIR.investigation-candidate
    "powers:minette-compensation-settlement"
    "leaf:compensationPaymentLeaf"
    "Saint-Martin estate/executor transfer plus benefit-night receipts/proceeds"
    "notarial/archive access"
    "Prest 2019 -> 9 June 1784 testament -> estate/account follow-up"
    "axis calibration: high same-object specificity, narrower residual coverage"
    8 7 5 9 7
    true refl false refl false refl

seatingRuleCandidate : ITIR.InvestigationCandidate
seatingRuleCandidate =
  ITIR.investigation-candidate
    "powers:saint-domingue-seating-rule"
    "leaf:legalStatusSeatingRuleLeaf"
    "ordinance/police/theatre rule plus enforcement and price schedule recovery"
    "archive/publication access"
    "observed seating geometry -> rule-producing instrument search"
    "axis calibration: separates architecture/custom/practice/formal rule"
    9 8 7 10 6
    true refl false refl false refl

causalIdentificationCandidate : ITIR.InvestigationCandidate
causalIdentificationCandidate =
  ITIR.investigation-candidate
    "powers:theatre-status-causal-identification"
    "leaf:causalMobilityLeaf"
    "case-specific identification family after comparable trajectory fibres exist"
    "requires sufficient observational fibres and admissible design"
    "Minette/Lise and later comparable trajectories -> identification gate"
    "axis calibration: potentially high downstream value but prerequisite-heavy"
    7 5 6 7 9
    true refl false refl false refl

primaryCorpusLeaf : Empirical.EmpiricalProgrammeLeaf
primaryCorpusLeaf = Empirical.primaryCorpusSaturationLeaf

actorDistributionLeaf : Empirical.EmpiricalProgrammeLeaf
actorDistributionLeaf = Empirical.distributionalIncidenceLeaf

compensationLeaf : Empirical.EmpiricalProgrammeLeaf
compensationLeaf = Empirical.compensationPaymentLeaf

seatingRuleLeaf : Empirical.EmpiricalProgrammeLeaf
seatingRuleLeaf = Empirical.legalStatusSeatingRuleLeaf

causalLeaf : Empirical.EmpiricalProgrammeLeaf
causalLeaf = Empirical.causalMobilityLeaf

canonicalITIRBoundary : ITIR.InvestigationAcquisitionBoundary
canonicalITIRBoundary = ITIR.canonicalInvestigationAcquisitionBoundary

------------------------------------------------------------------------
-- Selective reopening: acquisition only reopens declared dependent consumers.
------------------------------------------------------------------------

data AcquisitionArtifact : Set where
  primaryIssueImage : AcquisitionArtifact
  july1790ChronologyConsumer : AcquisitionArtifact
  performanceEventLedgerConsumer : AcquisitionArtifact
  seatingRuleInstrument : AcquisitionArtifact
  seatingRuleConsumer : AcquisitionArtifact
  namedActorCompensationRecord : AcquisitionArtifact
  actorDistributionConsumer : AcquisitionArtifact
  estateSettlementRecord : AcquisitionArtifact
  compensationSettlementConsumer : AcquisitionArtifact

data PowersDepends : AcquisitionArtifact → AcquisitionArtifact → Set where
  issueReopensChronology : PowersDepends primaryIssueImage july1790ChronologyConsumer
  issueReopensEventLedger : PowersDepends primaryIssueImage performanceEventLedgerConsumer
  ruleInstrumentReopensSeating : PowersDepends seatingRuleInstrument seatingRuleConsumer
  actorCompensationDependency : PowersDepends namedActorCompensationRecord actorDistributionConsumer
  estateRecordReopensSettlement : PowersDepends estateSettlementRecord compensationSettlementConsumer

powersAcquisitionDependencyGraph :
  Acquisition.AcquisitionDependencyGraph AcquisitionArtifact
powersAcquisitionDependencyGraph =
  Acquisition.acquisition-dependency-graph
    PowersDepends
    "Powers empirical dependency graph: evidence acquisition reopens only explicitly dependent chronology/event/rule/distribution/settlement consumers"

PrimaryIssueChronologyReopening : Set
PrimaryIssueChronologyReopening =
  Acquisition.SelectiveAcquisitionReopening
    powersAcquisitionDependencyGraph
    primaryIssueImage
    july1790ChronologyConsumer

primaryIssueReopensChronology : PrimaryIssueChronologyReopening
primaryIssueReopensChronology =
  Acquisition.oneEdgeAcquisitionReopening issueReopensChronology

PrimaryIssueEventLedgerReopening : Set
PrimaryIssueEventLedgerReopening =
  Acquisition.SelectiveAcquisitionReopening
    powersAcquisitionDependencyGraph
    primaryIssueImage
    performanceEventLedgerConsumer

primaryIssueReopensEventLedger : PrimaryIssueEventLedgerReopening
primaryIssueReopensEventLedger =
  Acquisition.oneEdgeAcquisitionReopening issueReopensEventLedger

ActorCompensationDistributionReopening : Set
ActorCompensationDistributionReopening =
  Acquisition.SelectiveAcquisitionReopening
    powersAcquisitionDependencyGraph
    namedActorCompensationRecord
    actorDistributionConsumer

actorCompensationReopensDistribution : ActorCompensationDistributionReopening
actorCompensationReopensDistribution =
  Acquisition.oneEdgeAcquisitionReopening actorCompensationDependency

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record PowersInvestigationRoutingBoundary : Set where
  constructor powers-investigation-routing-boundary
  field
    usesFiveMixedOrientationAxes : Bool
    usesFiveMixedOrientationAxesIsTrue : usesFiveMixedOrientationAxes ≡ true
    scalarTruthScoreUsed : Bool
    scalarTruthScoreUsedIsFalse : scalarTruthScoreUsed ≡ false
    acquisitionPriorityCreatesHistoricalTruth : Bool
    acquisitionPriorityCreatesHistoricalTruthIsFalse :
      acquisitionPriorityCreatesHistoricalTruth ≡ false
    notLocatedMeansKnownAbsent : Bool
    notLocatedMeansKnownAbsentIsFalse : notLocatedMeansKnownAbsent ≡ false
    corpusAndDistributionRemainImmediateHighCoverageRoutes : Bool
    corpusAndDistributionRemainImmediateHighCoverageRoutesIsTrue :
      corpusAndDistributionRemainImmediateHighCoverageRoutes ≡ true
    compensationSettlementStillRequiredEvenIfNarrower : Bool
    compensationSettlementStillRequiredEvenIfNarrowerIsTrue :
      compensationSettlementStillRequiredEvenIfNarrower ≡ true
    causalIdentificationRequiresPrerequisiteFibres : Bool
    causalIdentificationRequiresPrerequisiteFibresIsTrue :
      causalIdentificationRequiresPrerequisiteFibres ≡ true
    acquisitionReopensOnlyDeclaredDependentConsumers : Bool
    acquisitionReopensOnlyDeclaredDependentConsumersIsTrue :
      acquisitionReopensOnlyDeclaredDependentConsumers ≡ true

canonicalPowersInvestigationRoutingBoundary : PowersInvestigationRoutingBoundary
canonicalPowersInvestigationRoutingBoundary =
  powers-investigation-routing-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
