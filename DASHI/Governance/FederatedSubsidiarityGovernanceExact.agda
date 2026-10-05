module DASHI.Governance.FederatedSubsidiarityGovernanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.SituatedConstituency as Situated

------------------------------------------------------------------------
-- Federated subsidiarity governance core.
--
-- Source motivation: the attached 2026-10-05 transcript contrasts the
-- coordination burden of a growing globally-coupled consensus process with
-- a proposed architecture of locally autonomous communities connected by
-- federation.  The transcript motivates the problem statement only.  It does
-- not itself supply a quantitative scaling law, empirical superiority result,
-- ecological threshold, or political-legitimacy theorem.
--
-- This module therefore proves only structural consequences of explicit
-- witnesses.  Existing authority and constituency semantics are imported
-- rather than recreated.
------------------------------------------------------------------------

data IssueScope (Community : Set) : Set where
  localTo : Community → IssueScope Community
  boundaryBetween : Community → Community → IssueScope Community
  federationWide : IssueScope Community

record FederatedGovernance
  (Agent Community Issue : Set) : Set₁ where
  field
    memberOf : Agent → Community → Set
    participates : Agent → Issue → Set
    scopeOf : Issue → IssueScope Community

open FederatedGovernance public

record SubsidiarityWitness
  {Agent Community Issue : Set}
  (governance : FederatedGovernance Agent Community Issue) : Set₁ where
  field
    localParticipationScoped :
      ∀ {agent community issue} →
      scopeOf governance issue ≡ localTo community →
      participates governance agent issue →
      memberOf governance agent community

open SubsidiarityWitness public

nonMemberCannotParticipateLocal :
  ∀ {Agent Community Issue : Set} →
  (governance : FederatedGovernance Agent Community Issue) →
  (subsidiarity : SubsidiarityWitness governance) →
  ∀ {agent community issue} →
  ¬ memberOf governance agent community →
  scopeOf governance issue ≡ localTo community →
  participates governance agent issue →
  ⊥
nonMemberCannotParticipateLocal governance subsidiarity notMember localScope participation =
  notMember
    (localParticipationScoped subsidiarity localScope participation)

------------------------------------------------------------------------
-- Existing authority/constituency cross-pollination.
--
-- These records attach the already-existing semantics.  They deliberately do
-- not define a new notion of mandate, legitimacy, representation, place, time
-- or intersectional constituency.
------------------------------------------------------------------------

record FederationAuthorityAttachment
  {Agent Community Issue : Set}
  (governance : FederatedGovernance Agent Community Issue) : Set₁ where
  field
    mandate : Authority.Mandate
    mandateIsNonAlienating : Authority.NonAlienatingMandate mandate
    constituencyOf : Community → Situated.SituatedConstituency

open FederationAuthorityAttachment public

------------------------------------------------------------------------
-- Coordination-load decomposition.
--
-- `federatedLoad` is a definition, not an empirical complexity law.  Concrete
-- applications must separately justify what their local/boundary load numbers
-- mean and how they were measured.
------------------------------------------------------------------------

federatedLoad : Nat → Nat → Nat
federatedLoad localLoad boundaryLoad =
  localLoad + boundaryLoad

federatedLoadDecomposes :
  ∀ localLoad boundaryLoad →
  federatedLoad localLoad boundaryLoad ≡ localLoad + boundaryLoad
federatedLoadDecomposes localLoad boundaryLoad = refl

federatedLoadUpperBound :
  ∀ localLoad boundaryLoad →
  federatedLoad localLoad boundaryLoad ≤ localLoad + boundaryLoad
federatedLoadUpperBound localLoad boundaryLoad = ≤-refl

------------------------------------------------------------------------
-- Explicit composition carrier.
--
-- Compatibility is supplied, never inferred.  The theorem only packages the
-- two already-proved local guarantees.
------------------------------------------------------------------------

record ComposablePair
  {LeftState RightState Interface : Set}
  (LeftGuarantee : LeftState → Set)
  (RightGuarantee : RightState → Set)
  (Compatible : LeftState → RightState → Interface → Set) : Set₁ where
  field
    leftState : LeftState
    rightState : RightState
    interface : Interface
    compatibilityWitness : Compatible leftState rightState interface
    leftGuaranteeWitness : LeftGuarantee leftState
    rightGuaranteeWitness : RightGuarantee rightState

open ComposablePair public

pairGuarantees :
  ∀ {LeftState RightState Interface : Set}
    {LeftGuarantee : LeftState → Set}
    {RightGuarantee : RightState → Set}
    {Compatible : LeftState → RightState → Interface → Set} →
  (pair : ComposablePair LeftGuarantee RightGuarantee Compatible) →
  LeftGuarantee (leftState pair) × RightGuarantee (rightState pair)
pairGuarantees pair =
  leftGuaranteeWitness pair , rightGuaranteeWitness pair

------------------------------------------------------------------------
-- Transition system for gradual institutional change.
------------------------------------------------------------------------

data TransitionKind : Set where
  createCommunity : TransitionKind
  joinCommunity : TransitionKind
  exitCommunity : TransitionKind
  splitCommunity : TransitionKind
  federateCommunities : TransitionKind
  shareInfrastructure : TransitionKind

record TransitionSystem (State : Set) : Set₁ where
  field
    step : TransitionKind → State → State → Set

open TransitionSystem public

_↝_ :
  ∀ {State : Set} →
  TransitionSystem State →
  State →
  State →
  Set
_↝_ transitionSystem source target =
  Σ TransitionKind (λ kind → step transitionSystem kind source target)

infix 4 _↝_

data Reachable
  {State : Set}
  (transitionSystem : TransitionSystem State) :
  State → State → Set where
  reachableRefl :
    ∀ {state} →
    Reachable transitionSystem state state

  reachableByStep :
    ∀ {kind source target} →
    step transitionSystem kind source target →
    Reachable transitionSystem source target

  reachableTrans :
    ∀ {source middle target} →
    Reachable transitionSystem source middle →
    Reachable transitionSystem middle target →
    Reachable transitionSystem source target

reachableStep :
  ∀ {State : Set}
    {transitionSystem : TransitionSystem State}
    {source target} →
  transitionSystem ↝ source →
  Reachable transitionSystem source target
reachableStep {target = target} (kind , witness) =
  reachableByStep witness

------------------------------------------------------------------------
-- Independent viability dimensions.
------------------------------------------------------------------------

record ViabilityEnvelope (State : Set) : Set₁ where
  field
    governanceViable : State → Set
    ecologicalViable : State → Set
    resourceViable : State → Set
    basicNeedsAccessible : State → Set

open ViabilityEnvelope public

Viable :
  ∀ {State : Set} →
  ViabilityEnvelope State →
  State →
  Set
Viable envelope state =
  governanceViable envelope state
  × ecologicalViable envelope state
  × resourceViable envelope state
  × basicNeedsAccessible envelope state

------------------------------------------------------------------------
-- Claim/authority firewalls.
------------------------------------------------------------------------

record FederatedGovernanceBoundary : Set where
  constructor federatedGovernanceBoundary
  field
    formalModelCreatesLegitimacy : Bool
    consensusDefinitionallyDemocracy : Bool
    federationDefinitionallyLegitimate : Bool
    decentralisationEmpiricallySuperior : Bool
    governanceFormImpliesEcologicalViability : Bool
    quantitativeScalingLawProvedFromTranscript : Bool
    compatibilityMustBeSupplied : Bool
    localAuthorityRemainsScoped : Bool

open FederatedGovernanceBoundary public

canonicalFederatedGovernanceBoundary : FederatedGovernanceBoundary
canonicalFederatedGovernanceBoundary =
  federatedGovernanceBoundary
    false
    false
    false
    false
    false
    false
    true
    true

canonicalFederatedSubsidiarityGovernanceReceipt :
  GenericReceipt.GenericReceipt
canonicalFederatedSubsidiarityGovernanceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated subsidiarity governance structural core"
    "DASHI.Governance.FederatedSubsidiarityGovernanceExact"
    "canonicalFederatedGovernanceBoundary"
    "formalises local issue scope, explicit subsidiarity, local-plus-boundary coordination decomposition, witness-gated composition, transition reachability and independent viability predicates"
    "the transcript motivates the architecture but does not prove empirical superiority, political legitimacy, quantitative scaling laws, ecological thresholds or concrete viability"
    "agda -i . DASHI/Governance/FederatedSubsidiarityGovernanceRegression.agda"
