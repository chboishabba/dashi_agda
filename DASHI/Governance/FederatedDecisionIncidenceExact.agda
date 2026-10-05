module DASHI.Governance.FederatedDecisionIncidenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base

------------------------------------------------------------------------
-- Decision-incidence graph for federated governance.
--
-- An edge is an actual participation witness between one agent and one issue.
-- The graph does not assume that every agent participates in every issue.
------------------------------------------------------------------------

record DecisionIncidenceGraph
  {Agent Community Issue : Set}
  (governance : Base.FederatedGovernance Agent Community Issue) : Set₁ where
  field
    Edge : Set
    edgeAgent : Edge → Agent
    edgeIssue : Edge → Issue
    edgeParticipation :
      ∀ edge →
      Base.participates governance (edgeAgent edge) (edgeIssue edge)

open DecisionIncidenceGraph public

------------------------------------------------------------------------
-- Locality theorem.
------------------------------------------------------------------------

localEdgeAgentMember :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  (subsidiarity : Base.SubsidiarityWitness governance) →
  (graph : DecisionIncidenceGraph governance) →
  ∀ edge community →
  Base.scopeOf governance (edgeIssue graph edge) ≡ Base.localTo community →
  Base.memberOf governance (edgeAgent graph edge) community
localEdgeAgentMember subsidiarity graph edge community localScope =
  Base.localParticipationScoped
    subsidiarity
    localScope
    (edgeParticipation graph edge)

------------------------------------------------------------------------
-- Global-coupling predicates.
------------------------------------------------------------------------

GloballyCoupledIssue :
  ∀ {Agent Community Issue : Set} →
  Base.FederatedGovernance Agent Community Issue →
  Issue →
  Set
GloballyCoupledIssue governance issue =
  ∀ agent → Base.participates governance agent issue

GloballyCoupledGovernance :
  ∀ {Agent Community Issue : Set} →
  Base.FederatedGovernance Agent Community Issue →
  Set
GloballyCoupledGovernance governance =
  ∀ issue → GloballyCoupledIssue governance issue

localIssueWithOutsiderNotGloballyCoupled :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  (subsidiarity : Base.SubsidiarityWitness governance) →
  ∀ {issue community} →
  Base.scopeOf governance issue ≡ Base.localTo community →
  Σ Agent (λ agent → ¬ Base.memberOf governance agent community) →
  ¬ GloballyCoupledIssue governance issue
localIssueWithOutsiderNotGloballyCoupled
  subsidiarity
  {issue}
  {community}
  localScope
  (outsider , outsiderNotMember)
  globalCoupling =
    outsiderNotMember
      (Base.localParticipationScoped
        subsidiarity
        localScope
        (globalCoupling outsider))

subsidiarityObstructsTotalGlobalCoupling :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  (subsidiarity : Base.SubsidiarityWitness governance) →
  ∀ {issue community} →
  Base.scopeOf governance issue ≡ Base.localTo community →
  Σ Agent (λ agent → ¬ Base.memberOf governance agent community) →
  ¬ GloballyCoupledGovernance governance
subsidiarityObstructsTotalGlobalCoupling
  subsidiarity
  {issue}
  localScope
  outsiderWitness
  globallyCoupled =
    localIssueWithOutsiderNotGloballyCoupled
      subsidiarity
      localScope
      outsiderWitness
      (globallyCoupled issue)

------------------------------------------------------------------------
-- Proof-carrying finite incidence accounting.
--
-- Counts are supplied by an external finite enumeration/audit.  This record
-- certifies only that the supplied total has been partitioned into local,
-- boundary and federation-wide edge counts.  It does not derive those counts
-- from the abstract graph and it is not an empirical complexity law.
------------------------------------------------------------------------

record IncidenceAccounting : Set where
  constructor incidenceAccounting
  field
    localEdges : Nat
    boundaryEdges : Nat
    federationWideEdges : Nat
    totalEdges : Nat
    exactPartition :
      totalEdges ≡ localEdges + boundaryEdges + federationWideEdges

open IncidenceAccounting public

totalEdgesPartition :
  ∀ accounting →
  totalEdges accounting ≡
    localEdges accounting
      + boundaryEdges accounting
      + federationWideEdges accounting
totalEdgesPartition accounting = exactPartition accounting

nonLocalEdges : IncidenceAccounting → Nat
nonLocalEdges accounting =
  boundaryEdges accounting + federationWideEdges accounting

------------------------------------------------------------------------
-- Interpretation / authority firewall.
------------------------------------------------------------------------

record DecisionIncidenceBoundary : Set where
  constructor decisionIncidenceBoundary
  field
    graphEdgesCreatePoliticalLegitimacy : Bool
    localityProvesEmpiricalEfficiency : Bool
    absenceOfGlobalCouplingImpliesDemocracy : Bool
    quantitativeScalingLawEmpiricallyEstablished : Bool
    suppliedCountsNeedExternalJustification : Bool
    boundaryIssuesMayCrossCommunities : Bool
    federationWideIssuesRemainRepresentable : Bool

open DecisionIncidenceBoundary public

canonicalDecisionIncidenceBoundary : DecisionIncidenceBoundary
canonicalDecisionIncidenceBoundary =
  decisionIncidenceBoundary
    false
    false
    false
    false
    true
    true
    true

canonicalFederatedDecisionIncidenceReceipt :
  GenericReceipt.GenericReceipt
canonicalFederatedDecisionIncidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated decision-incidence locality core"
    "DASHI.Governance.FederatedDecisionIncidenceExact"
    "canonicalDecisionIncidenceBoundary"
    "represents participation as agent-issue incidence, proves that subsidiarity localises local-issue edges, and proves that any local issue with an outsider obstructs total global coupling"
    "finite incidence counts remain externally supplied and no empirical efficiency, democracy, legitimacy or quantitative social-scaling law is promoted"
    "agda -i . DASHI/Governance/FederatedDecisionIncidenceRegression.agda"
