module DASHI.Law.CoerciveContactAuditValidation where

open import DASHI.Core.Prelude

import DASHI.Law.QueenslandWandingReachabilityBidiExact as Wand
import DASHI.Law.LowTraceCoerciveForceNonReconstructionExact as Force
import DASHI.Law.CoerciveContactAuditHyperfabricCrossPollinationExact as Cross
import DASHI.Law.CoerciveEncounterTrajectoryBidiExact as Trajectory

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
