module DASHI.Governance.FederatedDecisionIncidenceRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.FederatedDecisionIncidenceExact as Incidence

------------------------------------------------------------------------
-- RED-first regression surface for decision-incidence locality.
------------------------------------------------------------------------

localEdgeRequiresMembership :
  ∀ {A C I : Set}
    {g : Base.FederatedGovernance A C I} →
  (s : Base.SubsidiarityWitness g) →
  (graph : Incidence.DecisionIncidenceGraph g) →
  ∀ edge community →
  Base.scopeOf g (Incidence.edgeIssue graph edge) ≡ Base.localTo community →
  Base.memberOf g (Incidence.edgeAgent graph edge) community
localEdgeRequiresMembership =
  Incidence.localEdgeAgentMember

localIssueWithOutsiderCannotBeGloballyCoupled :
  ∀ {A C I : Set}
    {g : Base.FederatedGovernance A C I} →
  (s : Base.SubsidiarityWitness g) →
  ∀ {issue community} →
  Base.scopeOf g issue ≡ Base.localTo community →
  Σ A (λ agent → ¬ Base.memberOf g agent community) →
  ¬ Incidence.GloballyCoupledIssue g issue
localIssueWithOutsiderCannotBeGloballyCoupled =
  Incidence.localIssueWithOutsiderNotGloballyCoupled

subsidiarityBlocksTotalGlobalCoupling :
  ∀ {A C I : Set}
    {g : Base.FederatedGovernance A C I} →
  (s : Base.SubsidiarityWitness g) →
  ∀ {issue community} →
  Base.scopeOf g issue ≡ Base.localTo community →
  Σ A (λ agent → ¬ Base.memberOf g agent community) →
  ¬ Incidence.GloballyCoupledGovernance g
subsidiarityBlocksTotalGlobalCoupling =
  Incidence.subsidiarityObstructsTotalGlobalCoupling

accountingExample : Incidence.IncidenceAccounting
accountingExample =
  Incidence.incidenceAccounting
    7
    2
    1
    10
    refl

accountingExamplePartition :
  Incidence.totalEdges accountingExample ≡
  Incidence.localEdges accountingExample
    + Incidence.boundaryEdges accountingExample
    + Incidence.federationWideEdges accountingExample
accountingExamplePartition =
  Incidence.totalEdgesPartition accountingExample

quantitativeLawStillExternal :
  Incidence.quantitativeScalingLawEmpiricallyEstablished
    Incidence.canonicalDecisionIncidenceBoundary
  ≡ false
quantitativeLawStillExternal = refl
