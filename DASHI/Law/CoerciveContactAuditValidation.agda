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
