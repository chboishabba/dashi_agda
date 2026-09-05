module DASHI.Law.CoerciveContactAuditValidation where

open import DASHI.Core.Prelude

import DASHI.Law.QueenslandWandingReachabilityBidiExact as Wand
import DASHI.Law.LowTraceCoerciveForceNonReconstructionExact as Force
import DASHI.Law.CoerciveContactAuditHyperfabricCrossPollinationExact as Cross
import DASHI.Law.CoerciveEncounterTrajectoryBidiExact as Trajectory
import DASHI.Law.CoerciveEncounterLawfulnessBidiExact as Law
import DASHI.Law.IndependentEvidenceProvenanceExact as Provenance

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
