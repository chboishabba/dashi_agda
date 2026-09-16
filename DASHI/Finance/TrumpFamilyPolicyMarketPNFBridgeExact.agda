module DASHI.Finance.TrumpFamilyPolicyMarketPNFBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Finance.TrumpFamilyTradePNFBridgeExact as TradePNF
import DASHI.Finance.TrumpFamilyPolicyMarketSourceAtlasExact as Policy

------------------------------------------------------------------------
-- POLICY / MARKET SOURCE -> PNF
--
-- Ownership, policy proposal and independent synthesis remain separate events.
-- A PNF composition may retain their temporal/relational adjacency, but it does
-- not construct prior knowledge, influence, causation, realized benefit or a
-- trade recommendation.
------------------------------------------------------------------------

record PolicyEvidencePNFBinding (evidence : Policy.PolicyMarketEvidence) : Set₁ where
  constructor policy-evidence-pnf-binding
  field
    event : PNF.EventPNF
    sourceEventSameObject : Set
    sourceEventSameObjectReceipt : sourceEventSameObject
    eventTimeReference : String
    publicationTimeReference : String
    propositionScopeReference : String

open PolicyEvidencePNFBinding public

record PolicyMarketTriadPNFBinding
    (triad : Policy.PolicyMarketTriad) : Set₁ where
  constructor policy-market-triad-pnf-binding
  field
    ownershipBinding :
      TradePNF.TradeClaimPNFBinding (Policy.ownershipEvidence triad)
    policyBinding :
      PolicyEvidencePNFBinding (Policy.policyEvidence triad)
    independentBinding :
      PolicyEvidencePNFBinding (Policy.independentEvidence triad)
    relationReference : String
    knowledgeClaimPromoted : Bool
    knowledgeClaimPromotedIsFalse : knowledgeClaimPromoted ≡ false
    influenceClaimPromoted : Bool
    influenceClaimPromotedIsFalse : influenceClaimPromoted ≡ false
    realizedBenefitPromoted : Bool
    realizedBenefitPromotedIsFalse : realizedBenefitPromoted ≡ false

open PolicyMarketTriadPNFBinding public

------------------------------------------------------------------------
-- Point-in-time discipline.
------------------------------------------------------------------------

record PolicyMarketInformationCut : Set₁ where
  constructor policy-market-information-cut
  field
    ownershipKnownAt : String
    policyTextKnownAt : String
    independentReportKnownAt : String
    laterEvidenceMayRevise : Bool
    laterEvidenceMayReviseIsTrue : laterEvidenceMayRevise ≡ true
    cutReference : String

open PolicyMarketInformationCut public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PNFTimingMeansAdvanceKnowledgePermission : Set where
data PNFPolicyExposureMeansInfluencePermission : Set where
data PNFBusinessExposureMeansRealizedProfitPermission : Set where
data PNFPolicyMarketTriadMeansTradeSignalPermission : Set where

pnfTimingDoesNotCreateAdvanceKnowledge : PNFTimingMeansAdvanceKnowledgePermission → ⊥
pnfTimingDoesNotCreateAdvanceKnowledge ()

pnfExposureDoesNotCreateInfluence : PNFPolicyExposureMeansInfluencePermission → ⊥
pnfExposureDoesNotCreateInfluence ()

pnfExposureDoesNotCreateRealizedProfit : PNFBusinessExposureMeansRealizedProfitPermission → ⊥
pnfExposureDoesNotCreateRealizedProfit ()

pnfTriadDoesNotCreateTradeSignal : PNFPolicyMarketTriadMeansTradeSignalPermission → ⊥
pnfTriadDoesNotCreateTradeSignal ()

record PolicyMarketPNFBoundary : Set where
  constructor policy-market-pnf-boundary
  field
    ownershipPolicyAndReportingRemainDistinctEvents : Bool
    sourceToPNFRequiresSameObjectBinding : Bool
    timingDoesNotCreateAdvanceKnowledge : Bool
    structuralExposureDoesNotCreateInfluence : Bool
    structuralExposureDoesNotCreateRealizedProfit : Bool
    triadDoesNotCreateTradeSignal : Bool

canonicalPolicyMarketPNFBoundary : PolicyMarketPNFBoundary
canonicalPolicyMarketPNFBoundary =
  policy-market-pnf-boundary true true true true true true
