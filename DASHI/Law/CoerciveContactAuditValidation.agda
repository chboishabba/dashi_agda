module DASHI.Law.CoerciveContactAuditValidation where

open import DASHI.Core.Prelude

import DASHI.Law.QueenslandWandingReachabilityBidiExact as Wand
import DASHI.Law.LowTraceCoerciveForceNonReconstructionExact as Force
import DASHI.Law.CoerciveContactAuditHyperfabricCrossPollinationExact as Cross
import DASHI.Law.CoerciveEncounterTrajectoryBidiExact as Trajectory
import DASHI.Law.CoerciveEncounterLawfulnessBidiExact as Law
import DASHI.Law.CoerciveEncounterLawfulnessProductExact as Product
import DASHI.Law.TemporalAuthorityNonRetroactivityExact as Temporal
import DASHI.Law.IndependentEvidenceProvenanceExact as Provenance
import DASHI.Law.EvidenceProvenanceDependencyDagExact as Dag
import DASHI.Law.CoerciveEncounterFixtureCompilerExact as Fixture
import DASHI.Law.CoerciveEncounterGenericReceiptBridgeExact as Receipt
import DASHI.Law.CoerciveEncounterPopulationAggregationExact as Population
import DASHI.Law.SystemicCoercivePracticePromotionGateExact as Systemic
import DASHI.Law.CoerciveEncounterDenominatorIntegrityExact as Denom
import DASHI.Law.SelectionEligibilityDisparityBidiExact as Disparity

firewallAndReachabilityCoexist :
  Wand.FirewallWithReachability Wand.canonicalFirewallBoundary
firewallAndReachabilityCoexist = Wand.canonicalFirewallReachability

forceRecordNonReconstruction :
  Force.NF.FactorsThrough Force.observe Force.actualForce → ⊥
forceRecordNonReconstruction =
  Force.postEncounterRecordCannotReconstructForceHistory

firstOpenEdgeRegression :
  Trajectory.firstUnsupported
    (Trajectory.canonicalEncounterTrajectory
      Trajectory.supported Trajectory.supported
      Trajectory.unsupported Trajectory.unsupported)
  ≡ Trajectory.firstOpen (Trajectory.responsePredicateEdge Trajectory.unsupported)
firstOpenEdgeRegression = Trajectory.canonicalFirstGapAtTransition

coarseEndpointDoesNotCloseResidual :
  Trajectory.Residual.DependencyCodeDescendsAt
    Trajectory.trajectoryResidualObserver
    Trajectory.coarseOutcome
    Trajectory.inspectTransitionTable → ⊥
coarseEndpointDoesNotCloseResidual =
  Trajectory.coarseOutcomeCannotRecoverTransitionResidual

crossPollinatedAsymmetry :
  Cross.ReachabilityObservabilityAsymmetry
    (Cross.coerciveContactHypervoxel
      Wand.canonicalFirewallBoundary
      Force.contactElectricalLowRecord
      (Wand.noDirectConferral Wand.canonicalFirewallReachability)
      (Wand.searchStillReachable Wand.canonicalFirewallReachability)
      "validation")
crossPollinatedAsymmetry = Cross.canonicalAsymmetry

occurrenceCannotCloseLawfulness :
  Law.NF.FactorsThrough Law.occurrenceProjection Law.legalOutcomeProjection → ⊥
occurrenceCannotCloseLawfulness = Law.occurrenceCannotReconstructLawfulness

missingEvidenceDoesNotBecomeNegativeEvidence :
  Law.closureOf Law.missingReceipt ≡ Law.openMissing
missingEvidenceDoesNotBecomeNegativeEvidence = Law.missingReceiptRemainsOpen

physicalReachabilityDoesNotEstablishLawfulReachability :
  Law.legalReachability Law.canonicalReachableButNotLawfullyClosed ≡ Law.unreachable
physicalReachabilityDoesNotEstablishLawfulReachability =
  Law.notYetLawfullyReachable Law.canonicalReachableButNotLawfullyClosed

sameEvidenceContentDoesNotEstablishIndependence :
  Provenance.NF.FactorsThrough
    Provenance.contentProjection Provenance.provenanceStrength → ⊥
sameEvidenceContentDoesNotEstablishIndependence =
  Provenance.sameContentCannotReconstructIndependence

lowAuditSurfaceHasReconstructionDeficit :
  Provenance.AccountabilityReconstructionDeficit Provenance.canonicalLowAuditSurface
lowAuditSurfaceHasReconstructionDeficit = Provenance.canonicalAccountabilityDeficit

missingSafeguardBlocksLawfulnessClosure :
  Product.firstOpenLawfulness
    (Product.lawfulnessObligationVector
      Product.coordinateClosed Product.coordinateClosed
      Product.coordinateClosed Product.coordinateClosed
      Product.coordinateClosed Product.coordinateOpen
      Product.coordinateClosed Product.coordinateClosed)
  ≡ Product.firstOpenLawfulnessCoordinate Product.safeguardCoordinate
missingSafeguardBlocksLawfulnessClosure = Product.missingSafeguardStopsClosure

laterContrabandCannotBeEarlierSearchProducer :
  Temporal.RetroactiveProducer Temporal.contrabandAfterSearch
laterContrabandCannotBeEarlierSearchProducer = Temporal.contrabandAfterSearchIsRetroactive

downstreamDoesNotRetroactivelyCloseUpstream :
  Temporal.downstreamClosesUpstream Temporal.canonicalDownstreamCannotRetroactivelyCloseUpstream ≡ false
downstreamDoesNotRetroactivelyCloseUpstream =
  Temporal.downstreamClosesUpstreamIsFalse Temporal.canonicalDownstreamCannotRetroactivelyCloseUpstream

multipleInstitutionalRecordsMayShareProducer : Dag.SharedUltimateProducer
multipleInstitutionalRecordsMayShareProducer = Dag.canonicalSharedProducer

independenceConsumerRequiresIndependentProducer :
  Dag.reverseProvenance Dag.independentCorroborationConsumer ≡ Dag.independentProducerReceipt
independenceConsumerRequiresIndependentProducer =
  Dag.independenceConsumerRequiresProducerReceipt

empiricalFixtureStopsAtFirstLegalGap :
  Fixture.firstLawfulnessResidual Fixture.canonicalMissingSafeguardFixture
  ≡ Product.firstOpenLawfulnessCoordinate Product.safeguardCoordinate
empiricalFixtureStopsAtFirstLegalGap = Fixture.canonicalFixtureStopsAtSafeguard

downstreamSearchCannotLeapfrogFixtureGap :
  Fixture.searchOccurred Fixture.canonicalMissingSafeguardFixture ≡ Fixture.observedTrue
downstreamSearchCannotLeapfrogFixtureGap = Fixture.canonicalFixtureSearchCannotLeapfrogSafeguard

downstreamContrabandCannotLeapfrogFixtureGap :
  Fixture.otherContrabandFound Fixture.canonicalMissingSafeguardFixture ≡ Fixture.observedTrue
downstreamContrabandCannotLeapfrogFixtureGap = Fixture.canonicalFixtureContrabandCannotLeapfrogSafeguard

genericFixtureReceiptRemainsNonPromoting :
  Receipt.Generic.promotesClaim Receipt.canonicalFixtureGenericReceipt ≡ false
genericFixtureReceiptRemainsNonPromoting = Receipt.canonicalFixtureReceiptNonPromoting

populationGatewayCountsPreserveTypedDenominator :
  Population.numerator (Population.gatewayRateCounts Population.canonicalPopulation) ≡ 2
populationGatewayCountsPreserveTypedDenominator = Population.canonicalGatewayNumerator

populationLawfulnessDoesNotFollowFromSearchCount :
  Population.numerator (Population.lawfulnessClosureRateCounts Population.canonicalPopulation) ≡ 0
populationLawfulnessDoesNotFollowFromSearchCount = Population.canonicalLawfulnessClosedNumerator

pretextClaimStillRequiresIntentProducer :
  Systemic.firstSystemicResidual
    Systemic.pretextualIntent
    Systemic.canonicalDescriptiveOnlyCutset
  ≡ Systemic.intentResidual
pretextClaimStillRequiresIntentProducer = Systemic.canonicalPretextStopsAtIntent

deterrenceClaimStillRequiresCounterfactual :
  Systemic.firstSystemicResidual
    Systemic.causalDeterrence
    Systemic.canonicalDescriptiveOnlyCutset
  ≡ Systemic.counterfactualResidual
deterrenceClaimStillRequiresCounterfactual = Systemic.canonicalDeterrenceStillNeedsCounterfactual

encounterCountDoesNotCollapseToUniquePersons :
  Denom.encounterCount Denom.canonicalDenominatorLedger ≡ 4
encounterCountDoesNotCollapseToUniquePersons = Denom.canonicalEncounterCount

uniquePersonDenominatorRetainsDeduplication :
  Denom.uniquePersonCount Denom.canonicalDenominatorLedger ≡ 2
uniquePersonDenominatorRetainsDeduplication = Denom.canonicalUniquePersonCount

missingStatusRemainsUnresolved :
  Denom.interpretStatus Denom.statusMissing ≡ Denom.unresolvedStatus
missingStatusRemainsUnresolved = Denom.missingStatusIsNotNegative

scanShareDoesNotCloseSelectionDisparity :
  Disparity.firstDisparityResidual
    Disparity.descriptiveSelectionDisparity
    Disparity.canonicalScanShareOnly
  ≡ Disparity.eligibilityResidual
scanShareDoesNotCloseSelectionDisparity = Disparity.scanShareDoesNotCloseSelectionDisparity

causalDiscriminationNeedsCausalSelectionModel :
  Disparity.firstDisparityResidual
    Disparity.causalDiscrimination
    (Disparity.selectionDisparityCutset true true true true true false "descriptive selection surface closed")
  ≡ Disparity.causalModelResidual
causalDiscriminationNeedsCausalSelectionModel = Disparity.causalClaimRequiresCausalModel
