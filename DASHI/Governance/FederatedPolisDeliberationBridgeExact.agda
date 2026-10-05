module DASHI.Governance.FederatedPolisDeliberationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Interop.PolisITIRDeliberationBoundary as Polis
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base

------------------------------------------------------------------------
-- Pol.is vote-row -> federated participation incidence adapter.
--
-- The mapping from participant IDs and statement IDs into typed governance
-- agents/issues is explicit input.  A vote row can then witness participation
-- in that mapped issue.  The adapter does not infer issue scope, legitimacy,
-- agreement, truth or authority from Pol.is output.
------------------------------------------------------------------------

record PolisIncidenceAdapter
  {Agent Community Issue : Set}
  (governance : Base.FederatedGovernance Agent Community Issue) : Set₁ where
  field
    agentFromParticipantId : String → Agent
    issueFromStatementId : String → Issue
    rowParticipation :
      (row : Polis.PolisVoteRow) →
      Base.participates
        governance
        (agentFromParticipantId (Polis.participantId row))
        (issueFromStatementId (Polis.votedStatementId row))

open PolisIncidenceAdapter public

agentOfRow :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  PolisIncidenceAdapter governance →
  Polis.PolisVoteRow →
  Agent
agentOfRow adapter row =
  agentFromParticipantId adapter (Polis.participantId row)

issueOfRow :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  PolisIncidenceAdapter governance →
  Polis.PolisVoteRow →
  Issue
issueOfRow adapter row =
  issueFromStatementId adapter (Polis.votedStatementId row)

polisLocalVoteRequiresMembership :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  (subsidiarity : Base.SubsidiarityWitness governance) →
  (adapter : PolisIncidenceAdapter governance) →
  ∀ row community →
  Base.scopeOf governance (issueOfRow adapter row) ≡ Base.localTo community →
  Base.memberOf governance (agentOfRow adapter row) community
polisLocalVoteRequiresMembership subsidiarity adapter row community localScope =
  Base.localParticipationScoped
    subsidiarity
    localScope
    (rowParticipation adapter row)

------------------------------------------------------------------------
-- Existing Pol.is authority firewalls are retained.
------------------------------------------------------------------------

polisHasNoNormativeAuthority :
  Polis.ownsNormativeAuthority Polis.canonicalPolisAuthorityBits ≡ false
polisHasNoNormativeAuthority =
  Polis.ownsNormativeAuthorityIsFalse Polis.canonicalPolisAuthorityBits

communitySupportIsNotNormativeTruth :
  Polis.communitySupportIsNormativeTruth
    Polis.canonicalITIRDeliberationAuthorityBits
  ≡ false
communitySupportIsNotNormativeTruth =
  Polis.communitySupportIsNormativeTruthIsFalse
    Polis.canonicalITIRDeliberationAuthorityBits

communitySupportIsNotLegalAuthority :
  Polis.communitySupportIsLegalAuthority
    Polis.canonicalITIRDeliberationAuthorityBits
  ≡ false
communitySupportIsNotLegalAuthority =
  Polis.communitySupportIsLegalAuthorityIsFalse
    Polis.canonicalITIRDeliberationAuthorityBits

------------------------------------------------------------------------
-- Bridge-specific boundary.
------------------------------------------------------------------------

record FederatedPolisBoundary : Set where
  constructor federatedPolisBoundary
  field
    voteMatrixMayWitnessParticipationIncidence : Bool
    statementScopeMappingMustBeSupplied : Bool
    participantIdentityMappingMustBeSupplied : Bool
    passRowStillRecordsDeliberationPresence : Bool
    voteRowMeansSubstantiveAgreement : Bool
    consensusScoreCreatesTruth : Bool
    voteMatrixCreatesPoliticalLegitimacy : Bool
    clusteringCreatesRepresentativeAuthority : Bool
    bridgeReimplementsPolisConsensusEngine : Bool

open FederatedPolisBoundary public

canonicalFederatedPolisBoundary : FederatedPolisBoundary
canonicalFederatedPolisBoundary =
  federatedPolisBoundary
    true
    true
    true
    true
    false
    false
    false
    false
    false

canonicalFederatedPolisDeliberationBridgeReceipt :
  GenericReceipt.GenericReceipt
canonicalFederatedPolisDeliberationBridgeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated Pol.is deliberation incidence bridge"
    "DASHI.Governance.FederatedPolisDeliberationBridgeExact"
    "canonicalFederatedPolisBoundary"
    "maps explicit Pol.is participant/statement identifiers into typed governance agents/issues so vote rows can witness participation incidence and local rows inherit the existing subsidiarity membership theorem"
    "scope and identity mappings remain supplied inputs; votes, clusters and consensus statistics create no truth, legal authority, political legitimacy or representative mandate, and the Pol.is engine is not reimplemented"
    "agda -i . DASHI/Governance/FederatedPolisDeliberationBridgeRegression.agda"
