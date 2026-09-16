module DASHI.Finance.TrumpTradeDecisionProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradePrimarySourceRound3Exact as Round3
import DASHI.Finance.TrumpPortfolioManagementAttributionExact as Management
import DASHI.Finance.TrumpTradePointInTimeInformationExact as PIT

------------------------------------------------------------------------
-- TRADE-EVENT / DECISION-PROVENANCE SEPARATION
--
-- A filed transaction pays an event edge.  It need not identify the human or
-- automated decision-maker, funding source, information set, instruction path,
-- or execution mechanism.  Conversely an attributed management statement is a
-- source-backed representation of those mechanisms, not independent audit.
------------------------------------------------------------------------

data DecisionEvidenceStatus : Set where
  paidPrimary : DecisionEvidenceStatus
  paidAttributed : DecisionEvidenceStatus
  unresolved : DecisionEvidenceStatus

data InformationStatus : Set where
  publicAtCut : InformationStatus
  unavailableAtPublicCut : InformationStatus
  sourceUnknown : InformationStatus
  nonpublicEstablished : InformationStatus

record TradeDecisionProvenance : Set₁ where
  constructor trade-decision-provenance
  field
    transactionClaim : Atlas.TradeEvidenceClaim
    beneficialOwnerReference : String
    transactionEventStatus : DecisionEvidenceStatus
    decisionMakerStatus : DecisionEvidenceStatus
    fundingSourceStatus : DecisionEvidenceStatus
    executionMechanismStatus : DecisionEvidenceStatus
    managementRepresentationStatus : DecisionEvidenceStatus
    informationStatusAtDecision : InformationStatus
    transactionEventReference : String
    decisionMakerReference : String
    fundingSourceReference : String
    executionReference : String
    informationReference : String

open TradeDecisionProvenance public

------------------------------------------------------------------------
-- Concrete President-level OGE event.
--
-- The Coinbase sale event itself is primary-source paid.  Reuters separately
-- pays an attributed Trump Organization representation of third-party,
-- automated/discretionary management.  The public record used here does not
-- independently identify the manager for this transaction, the funding path,
-- or the decision-time information state.
------------------------------------------------------------------------

coinbaseDecisionProvenance : TradeDecisionProvenance
coinbaseDecisionProvenance =
  trade-decision-provenance
    Round3.trumpCoinbaseSale20260212
    "Donald J. Trump is the filer/beneficial-interest subject of the OGE 278-T event"
    paidPrimary
    unresolved
    unresolved
    paidAttributed
    paidAttributed
    sourceUnknown
    "OGE Form 278-T pays sale/date/value-band"
    "specific decision-maker not identified by the OGE transaction row"
    "specific source of capital / portfolio funding not identified by the OGE transaction row"
    "Reuters attributes a spokesperson statement describing independently managed discretionary accounts and automated execution/rebalancing"
    "no source in this carrier establishes the information available to the decision-maker at the decision time"

managementDefenseClaim : Atlas.TradeEvidenceClaim
managementDefenseClaim = Management.thirdPartyManagementDefense

coinbaseDelayedPublicEvidence : PIT.DelayedPublicEvidence
coinbaseDelayedPublicEvidence = PIT.coinbaseSaleDelayedPublicEvidence

------------------------------------------------------------------------
-- The actual decision provenance remains a product, not a promoted scalar.
------------------------------------------------------------------------

data TransactionEventAutomaticallyIdentifiesDecisionMaker : Set where
data AttributedManagerStatementAutomaticallyAuditsMandate : Set where
data FamilyRelationAutomaticallySharesInformation : Set where
data PublicPolicyRoleAutomaticallyCreatesTradeInformation : Set where
data LaterDisclosureAutomaticallyRevealsEarlierInformationSet : Set where

eventDoesNotIdentifyDecisionMaker :
  TransactionEventAutomaticallyIdentifiesDecisionMaker → ⊥
eventDoesNotIdentifyDecisionMaker ()

attributedStatementDoesNotAuditMandate :
  AttributedManagerStatementAutomaticallyAuditsMandate → ⊥
attributedStatementDoesNotAuditMandate ()

familyRelationDoesNotTransportInformation :
  FamilyRelationAutomaticallySharesInformation → ⊥
familyRelationDoesNotTransportInformation ()

publicRoleDoesNotCreateTradeInformation :
  PublicPolicyRoleAutomaticallyCreatesTradeInformation → ⊥
publicRoleDoesNotCreateTradeInformation ()

laterDisclosureDoesNotRevealEarlierInformationSet :
  LaterDisclosureAutomaticallyRevealsEarlierInformationSet → ⊥
laterDisclosureDoesNotRevealEarlierInformationSet ()

record DecisionProvenanceBoundary : Set where
  constructor decision-provenance-boundary
  field
    transactionEventIsIndependentCoordinate : Bool
    decisionMakerIsIndependentCoordinate : Bool
    fundingSourceIsIndependentCoordinate : Bool
    executionMechanismIsIndependentCoordinate : Bool
    informationStateIsIndependentCoordinate : Bool
    attributedManagementIsNotAudit : Bool
    kinshipDoesNotTransportKnowledge : Bool

canonicalDecisionProvenanceBoundary : DecisionProvenanceBoundary
canonicalDecisionProvenanceBoundary =
  decision-provenance-boundary true true true true true true true
