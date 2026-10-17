module DASHI.Governance.FederatedPolisDeliberationBridgeRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.FederatedPolisDeliberationBridgeExact as Bridge

localMappedVoteRequiresCommunityMembership :
  ∀ {A C I : Set}
    {g : Base.FederatedGovernance A C I} →
  (s : Base.SubsidiarityWitness g) →
  (adapter : Bridge.PolisIncidenceAdapter g) →
  ∀ row community →
  Base.scopeOf g (Bridge.issueOfRow adapter row) ≡ Base.localTo community →
  Base.memberOf g (Bridge.agentOfRow adapter row) community
localMappedVoteRequiresCommunityMembership =
  Bridge.polisLocalVoteRequiresMembership

consensusScoreDoesNotCreateTruth :
  Bridge.consensusScoreCreatesTruth
    Bridge.canonicalFederatedPolisBoundary
  ≡ false
consensusScoreDoesNotCreateTruth = refl

voteMatrixDoesNotCreateLegitimacy :
  Bridge.voteMatrixCreatesPoliticalLegitimacy
    Bridge.canonicalFederatedPolisBoundary
  ≡ false
voteMatrixDoesNotCreateLegitimacy = refl

scopeMappingMustBeSupplied :
  Bridge.statementScopeMappingMustBeSupplied
    Bridge.canonicalFederatedPolisBoundary
  ≡ true
scopeMappingMustBeSupplied = refl
