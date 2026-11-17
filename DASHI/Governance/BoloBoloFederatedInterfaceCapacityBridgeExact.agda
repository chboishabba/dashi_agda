module DASHI.Governance.BoloBoloFederatedInterfaceCapacityBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Planning.NetworkFlowCapacityCongestionExact as Capacity

------------------------------------------------------------------------
-- FEDERATED GOVERNANCE INTERFACE CAPACITY / BOTTLENECK BRIDGE.
--
-- This is a DASHI cross-domain theorem-pattern reuse.  The planning module's
-- finite shared-capacity witness is reused abstractly for coordination channels
-- such as delegate/reportback or inter-community council interfaces.
--
-- No claim is made that political coordination is literally road/transit flow,
-- that p.m. supplied a queueing/capacity model, or that the toy 2+2>3 witness
-- is an empirical governance law.  The transferable logical point is narrower:
-- individual/local feasibility does not imply joint feasibility on a shared
-- finite-capacity interface.
------------------------------------------------------------------------

data CoordinationInterfaceLayer : Set where
  boloBoundaryInterface : CoordinationInterfaceLayer
  tegaBoundaryInterface : CoordinationInterfaceLayer
  widerFederationInterface : CoordinationInterfaceLayer

data GovernanceLoadKind : Set where
  issueEscalationLoad : GovernanceLoadKind
  delegateReportbackLoad : GovernanceLoadKind
  conflictResolutionLoad : GovernanceLoadKind
  sharedInfrastructureLoad : GovernanceLoadKind

record FederatedInterfaceCapacityBoundary : Set where
  constructor federatedInterfaceCapacityBoundary
  field
    localityReductionEliminatesAllUpperInterfaceLoad : Bool
    individuallyFeasibleCommunitiesGuaranteeJointInterfaceFeasibility : Bool
    aggregateLowCoordinationCostGuaranteesNoBottleneck : Bool
    sharedInterfaceCapacityMustBeAudited : Bool
    concurrentBoundaryDemandMustBeAudited : Bool
    overloadCanCreateBacklogOrUnresolvedBurden : Bool
    capacityConstraintAutomaticallyIdentifiesEmpiricalCost : Bool
    planningNetworkSemanticsArePoliticalGovernanceSemantics : Bool
    pMSourceProvidesThisCapacityModel : Bool

open FederatedInterfaceCapacityBoundary public

canonicalFederatedInterfaceCapacityBoundary : FederatedInterfaceCapacityBoundary
canonicalFederatedInterfaceCapacityBoundary =
  federatedInterfaceCapacityBoundary
    false false false
    true true true
    false false false

------------------------------------------------------------------------
-- Exact finite witness inherited from the generic capacity owner.
------------------------------------------------------------------------

canonicalCoordinationInterfaceOverloadAnalogue :
  Capacity.OverCapacity
    Capacity.individualDemandA
    Capacity.individualDemandB
    Capacity.sharedCapacity
canonicalCoordinationInterfaceOverloadAnalogue =
  Capacity.canonicalSharedOverCapacity

localFeasibilityCannotAutoPromoteToJointInterfaceFeasibility :
  Capacity.IndividualFeasibilityImpliesJointFeasibilityPermission → ⊥
localFeasibilityCannotAutoPromoteToJointInterfaceFeasibility =
  Capacity.individualFeasibilityCannotAutoPromoteToJoint

record InterfaceCapacityCalibrationObligations : Set where
  constructor interfaceCapacityCalibrationObligations
  field
    TargetInterfaceSetDeclared : Set
    targetInterfaceSetWitness : TargetInterfaceSetDeclared

    InterfaceCapacityMeasureDeclared : Set
    interfaceCapacityMeasureWitness : InterfaceCapacityMeasureDeclared

    ConcurrentDemandMeasureDeclared : Set
    concurrentDemandMeasureWitness : ConcurrentDemandMeasureDeclared

    BacklogOrUnresolvedMappingDeclared : Set
    backlogOrUnresolvedMappingWitness : BacklogOrUnresolvedMappingDeclared

open InterfaceCapacityCalibrationObligations public

record InterfaceCapacityResearchBoundary : Set where
  constructor interfaceCapacityResearchBoundary
  field
    incidenceCompressionAlonePaysInterfaceCapacity : Bool
    comparatorMeetingCadencePaysTargetCapacity : Bool
    observedSpokesVocabularyPaysTargetCapacity : Bool
    targetCapacityAndDemandRequireDirectOrQualifiedEvidence : Bool
    capacityCanEnterUnresolvedOverheadModel : Bool
    capacityBottleneckCanFalsifyNaiveFederationAdvantage : Bool

open InterfaceCapacityResearchBoundary public

canonicalInterfaceCapacityResearchBoundary : InterfaceCapacityResearchBoundary
canonicalInterfaceCapacityResearchBoundary =
  interfaceCapacityResearchBoundary false false false true true true

canonicalFederatedInterfaceCapacityReceipt : GenericReceipt.GenericReceipt
canonicalFederatedInterfaceCapacityReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo federated interface capacity bottleneck bridge"
    "DASHI.Governance.BoloBoloFederatedInterfaceCapacityBridgeExact"
    "canonicalFederatedInterfaceCapacityBoundary / canonicalCoordinationInterfaceOverloadAnalogue / canonicalInterfaceCapacityResearchBoundary"
    "reuses DASHI's generic finite shared-capacity counterexample to expose a distinct bolo counterfactual failure mode: local or individual feasibility and aggregate incidence reduction do not imply that shared delegate/reportback or inter-community interfaces can absorb concurrent boundary demand"
    "the capacity analogy supplies no empirical governance capacity, queueing law or cost coefficient and is not attributed to p.m.; target interface capacity, concurrent demand and backlog-to-unresolved-burden mapping remain direct-measurement or explicitly transported evidence obligations"
    "agda -i . DASHI/Governance/BoloBoloFederatedInterfaceCapacityBridgeRegression.agda"
