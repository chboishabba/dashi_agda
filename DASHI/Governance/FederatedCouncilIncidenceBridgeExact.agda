module DASHI.Governance.FederatedCouncilIncidenceBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.StageValuationBundleAtlas as Stage
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.FederatedDecisionIncidenceExact as Incidence
import DASHI.Governance.LocalGlobalCouncilGluing as Gluing
import DASHI.Governance.CouncilDelegationGraph as Council

------------------------------------------------------------------------
-- Cross-pollination of three already-separated structures:
--   1. agent/issue participation locality;
--   2. compatibility-gated local/global council gluing;
--   3. directed upward delegation and downward accountability.
--
-- None of these structures is identified with either of the others.
------------------------------------------------------------------------

record CouncilIncidenceBridge
  {Agent Community Issue : Set}
  (governance : Base.FederatedGovernance Agent Community Issue) : Set₁ where
  field
    subsidiarity : Base.SubsidiarityWitness governance
    incidenceGraph : Incidence.DecisionIncidenceGraph governance
    canonicalCouncilFamilyCompatible :
      Gluing.CompatibleCouncilFamily Gluing.canonicalLocalCouncilFamily

open CouncilIncidenceBridge public

bridgeLocalEdgeAgentMember :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  (bridge : CouncilIncidenceBridge governance) →
  ∀ edge community →
  Base.scopeOf governance
      (Incidence.edgeIssue (incidenceGraph bridge) edge)
    ≡ Base.localTo community →
  Base.memberOf governance
    (Incidence.edgeAgent (incidenceGraph bridge) edge)
    community
bridgeLocalEdgeAgentMember bridge =
  Incidence.localEdgeAgentMember
    (subsidiarity bridge)
    (incidenceGraph bridge)

canonicalGlobalStillRestrictsToNeighbourhood :
  Stage.BundleSheaf.restrict
    Gluing.rceppCouncilBundleSheaf
    Gluing.canonicalGlobalCouncilSection
    Gluing.neighbourhoodPoint
  ≡ Gluing.canonicalLocalCouncilFamily Gluing.neighbourhoodPoint
canonicalGlobalStillRestrictsToNeighbourhood =
  Gluing.canonicalGlobalRestrictsToNeighbourhood

canonicalGlobalStillRestrictsToIDPCamp :
  Stage.BundleSheaf.restrict
    Gluing.rceppCouncilBundleSheaf
    Gluing.canonicalGlobalCouncilSection
    Gluing.idpCampPoint
  ≡ Gluing.canonicalLocalCouncilFamily Gluing.idpCampPoint
canonicalGlobalStillRestrictsToIDPCamp =
  Gluing.canonicalGlobalRestrictsToIDPCamp

upwardDelegationDirectionPreserved :
  Council.edgeDirection Council.neighbourhoodDelegatesToLocality
  ≡ Council.upwardDelegationDirection
upwardDelegationDirectionPreserved =
  Council.upwardAndDownwardEdgesRemainDistinct

downwardAccountabilityDirectionPreserved :
  Council.edgeDirection Council.localityAccountsToNeighbourhood
  ≡ Council.downwardAccountabilityDirection
downwardAccountabilityDirectionPreserved = refl

record CouncilIncidenceBridgeBoundary : Set where
  constructor councilIncidenceBridgeBoundary
  field
    localIncidenceCollapsedIntoGlobalParticipation : Bool
    gluingErasesLocalSections : Bool
    delegationErasesDownwardAccountability : Bool
    compatibilityStillRequiredForGluing : Bool
    politicalAuthorityCreatedByBridge : Bool

open CouncilIncidenceBridgeBoundary public

canonicalCouncilIncidenceBridgeBoundary : CouncilIncidenceBridgeBoundary
canonicalCouncilIncidenceBridgeBoundary =
  councilIncidenceBridgeBoundary
    false
    false
    false
    true
    false

canonicalFederatedCouncilIncidenceBridgeReceipt :
  GenericReceipt.GenericReceipt
canonicalFederatedCouncilIncidenceBridgeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated decision-incidence / council-gluing bridge"
    "DASHI.Governance.FederatedCouncilIncidenceBridgeExact"
    "canonicalCouncilIncidenceBridgeBoundary"
    "combines local participation locality with compatibility-gated council gluing and distinct upward-delegation/downward-accountability directions while preserving each structure's existing theorem boundary"
    "the bridge neither identifies participation with representation nor turns finite compatibility, delegation or graph structure into real political legitimacy"
    "agda -i . DASHI/Governance/FederatedCouncilIncidenceBridgeExact.agda"
