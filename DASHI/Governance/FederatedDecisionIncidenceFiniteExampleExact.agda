module DASHI.Governance.FederatedDecisionIncidenceFiniteExampleExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.FederatedDecisionIncidenceExact as Incidence

------------------------------------------------------------------------
-- Concrete finite specimen.
--
-- This is a synthetic proof witness only.  It exercises the generic incidence
-- and subsidiarity interfaces without claiming to model any real population.
------------------------------------------------------------------------

data ExampleCommunity : Set where
  communityA : ExampleCommunity
  communityB : ExampleCommunity

data ExampleAgent : Set where
  agentAOne : ExampleAgent
  agentATwo : ExampleAgent
  agentBOne : ExampleAgent

data ExampleIssue : Set where
  localAIssue : ExampleIssue
  federationIssue : ExampleIssue

data ExampleMembership : ExampleAgent → ExampleCommunity → Set where
  agentAOneInA : ExampleMembership agentAOne communityA
  agentATwoInA : ExampleMembership agentATwo communityA
  agentBOneInB : ExampleMembership agentBOne communityB

data ExampleParticipation : ExampleAgent → ExampleIssue → Set where
  agentAOneLocalA : ExampleParticipation agentAOne localAIssue
  agentATwoLocalA : ExampleParticipation agentATwo localAIssue
  agentAOneFederation : ExampleParticipation agentAOne federationIssue
  agentATwoFederation : ExampleParticipation agentATwo federationIssue
  agentBOneFederation : ExampleParticipation agentBOne federationIssue

exampleScope : ExampleIssue → Base.IssueScope ExampleCommunity
exampleScope localAIssue = Base.localTo communityA
exampleScope federationIssue = Base.federationWide

exampleGovernance :
  Base.FederatedGovernance ExampleAgent ExampleCommunity ExampleIssue
exampleGovernance = record
  { memberOf = ExampleMembership
  ; participates = ExampleParticipation
  ; scopeOf = exampleScope
  }

exampleLocalParticipationScoped :
  ∀ {agent community issue} →
  exampleScope issue ≡ Base.localTo community →
  ExampleParticipation agent issue →
  ExampleMembership agent community
exampleLocalParticipationScoped {issue = localAIssue} refl agentAOneLocalA =
  agentAOneInA
exampleLocalParticipationScoped {issue = localAIssue} refl agentATwoLocalA =
  agentATwoInA
exampleLocalParticipationScoped {issue = federationIssue} () participation

exampleSubsidiarity : Base.SubsidiarityWitness exampleGovernance
exampleSubsidiarity = record
  { localParticipationScoped = exampleLocalParticipationScoped }

agentBOneOutsideA : ¬ ExampleMembership agentBOne communityA
agentBOneOutsideA ()

exampleFederationCoupled :
  Incidence.GloballyCoupledIssue exampleGovernance federationIssue
exampleFederationCoupled agentAOne = agentAOneFederation
exampleFederationCoupled agentATwo = agentATwoFederation
exampleFederationCoupled agentBOne = agentBOneFederation

exampleLocalIssueNotGloballyCoupled :
  ¬ Incidence.GloballyCoupledIssue exampleGovernance localAIssue
exampleLocalIssueNotGloballyCoupled =
  Incidence.localIssueWithOutsiderNotGloballyCoupled
    exampleSubsidiarity
    refl
    (agentBOne , agentBOneOutsideA)

exampleStrictParticipationContraction :
  Incidence.StrictParticipationContraction
    exampleGovernance
    localAIssue
    federationIssue
exampleStrictParticipationContraction =
  Incidence.localToGlobalStrictParticipationContraction
    exampleSubsidiarity
    refl
    (agentBOne , agentBOneOutsideA)
    exampleFederationCoupled

------------------------------------------------------------------------
-- Explicit incidence-edge specimen.
------------------------------------------------------------------------

data ExampleEdge : Set where
  edgeAOneLocal : ExampleEdge
  edgeATwoLocal : ExampleEdge
  edgeAOneFederation : ExampleEdge
  edgeATwoFederation : ExampleEdge
  edgeBOneFederation : ExampleEdge

exampleEdgeAgent : ExampleEdge → ExampleAgent
exampleEdgeAgent edgeAOneLocal = agentAOne
exampleEdgeAgent edgeATwoLocal = agentATwo
exampleEdgeAgent edgeAOneFederation = agentAOne
exampleEdgeAgent edgeATwoFederation = agentATwo
exampleEdgeAgent edgeBOneFederation = agentBOne

exampleEdgeIssue : ExampleEdge → ExampleIssue
exampleEdgeIssue edgeAOneLocal = localAIssue
exampleEdgeIssue edgeATwoLocal = localAIssue
exampleEdgeIssue edgeAOneFederation = federationIssue
exampleEdgeIssue edgeATwoFederation = federationIssue
exampleEdgeIssue edgeBOneFederation = federationIssue

exampleEdgeParticipation :
  ∀ edge →
  ExampleParticipation (exampleEdgeAgent edge) (exampleEdgeIssue edge)
exampleEdgeParticipation edgeAOneLocal = agentAOneLocalA
exampleEdgeParticipation edgeATwoLocal = agentATwoLocalA
exampleEdgeParticipation edgeAOneFederation = agentAOneFederation
exampleEdgeParticipation edgeATwoFederation = agentATwoFederation
exampleEdgeParticipation edgeBOneFederation = agentBOneFederation

exampleIncidenceGraph : Incidence.DecisionIncidenceGraph exampleGovernance
exampleIncidenceGraph = record
  { Edge = ExampleEdge
  ; edgeAgent = exampleEdgeAgent
  ; edgeIssue = exampleEdgeIssue
  ; edgeParticipation = exampleEdgeParticipation
  }

exampleIncidenceAccounting : Incidence.IncidenceAccounting
exampleIncidenceAccounting =
  Incidence.incidenceAccounting
    2
    0
    3
    5
    refl

record FiniteExampleBoundary : Set where
  constructor finiteExampleBoundary
  field
    finiteExampleIsEmpiricalPopulationLaw : Bool
    edgeEnumerationProvesRealCoordinationCost : Bool
    syntheticGlobalIssueIsRealGeneralAssembly : Bool
    exampleExercisesStrictContraction : Bool

open FiniteExampleBoundary public

canonicalFiniteExampleBoundary : FiniteExampleBoundary
canonicalFiniteExampleBoundary =
  finiteExampleBoundary
    false
    false
    false
    true

canonicalFederatedDecisionIncidenceFiniteExampleReceipt :
  GenericReceipt.GenericReceipt
canonicalFederatedDecisionIncidenceFiniteExampleReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "finite federated decision-incidence specimen"
    "DASHI.Governance.FederatedDecisionIncidenceFiniteExampleExact"
    "canonicalFiniteExampleBoundary"
    "constructs two communities, three agents, a two-participant local issue and a three-participant federation-wide issue, proving the local participant fibre is a strict contraction of the global comparison fibre"
    "the finite specimen is synthetic and does not establish population-level coordination cost, Occupy dynamics, Bolo Bolo viability or empirical superiority"
    "agda -i . DASHI/Governance/FederatedDecisionIncidenceFiniteExampleRegression.agda"
