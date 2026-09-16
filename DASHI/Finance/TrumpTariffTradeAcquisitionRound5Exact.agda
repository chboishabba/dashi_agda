module DASHI.Finance.TrumpTariffTradeAcquisitionRound5Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpTariffMarketSignalSourceExact as Tariff
import DASHI.Finance.TrumpTradeDecisionProvenanceExact as Decision

data AcquisitionCoordinate : Set where
  firstPartyPostArtifact : AcquisitionCoordinate
  enforcementOutcomeArtifact : AcquisitionCoordinate
  contemporaneousTradeArtifact : AcquisitionCoordinate
  namedPortfolioManagerArtifact : AcquisitionCoordinate
  portfolioMandateArtifact : AcquisitionCoordinate
  decisionTimeInformationArtifact : AcquisitionCoordinate
  transactionFundingArtifact : AcquisitionCoordinate
  truthAPIContractArtifact : AcquisitionCoordinate
  truthAPILatencyMeasurementArtifact : AcquisitionCoordinate

data DebtStatus : Set where
  unpaid partiallyPaid paid : DebtStatus

record AcquisitionDebt : Set where
  constructor acquisition-debt
  field
    coordinate : AcquisitionCoordinate
    status : DebtStatus
    propositionNeeded preferredSource currentBoundary acquisitionReference : String
open AcquisitionDebt public

originalBuyPostDebt : AcquisitionDebt
originalBuyPostDebt = acquisition-debt firstPartyPostArtifact partiallyPaid
  "recover the original/permalink-grade Truth Social artifact for the 09:37 ET April 9 2025 buy post"
  "first-party Truth Social record or authenticated archival capture"
  "official Senate correspondence pays quotation/timestamp but is not the originating platform artifact"
  "public-signal same-object strengthening"

enforcementOutcomeDebt : AcquisitionDebt
enforcementOutcomeDebt = acquisition-debt enforcementOutcomeArtifact unpaid
  "determine whether SEC, OGE, DOJ or another competent body publicly issued a disposition specifically resolving the April 9 2025 tariff-trading requests"
  "official agency enforcement, closing, inspector-general, ethics or litigation record"
  "congressional requests are paid; no adjudicated/enforcement conclusion is promoted here"
  "regulatory-outcome acquisition"

april9TradeIdentityDebt : AcquisitionDebt
april9TradeIdentityDebt = acquisition-debt contemporaneousTradeArtifact unpaid
  "recover source-identified Trump/family/administration transaction records, if any, specifically tied by date to the April 9 2025 window"
  "OGE transaction disclosures, SEC ownership filings, broker/court/regulatory records or other competent primary records"
  "public signal/policy/market sequence is paid; beneficiary trade identity is not"
  "trade-identity acquisition"

managerIdentityDebt : AcquisitionDebt
managerIdentityDebt = acquisition-debt namedPortfolioManagerArtifact unpaid
  "identify the third-party financial institution(s) or manager(s) responsible for disclosed President-level securities transactions"
  "account mandate, manager disclosure, OGE attachment, institutional confirmation or competent regulatory record"
  "Reuters pays an attributed independent-management representation; named manager identity is not independently paid"
  "decision-provenance acquisition"

mandateTermsDebt : AcquisitionDebt
mandateTermsDebt = acquisition-debt portfolioMandateArtifact unpaid
  "recover mandate terms showing discretion, automation, information barriers and any permitted client/family input"
  "executed investment-management agreement or competent audited/regulatory description"
  "attributed automation/discretion statements are not an audit of actual mandate terms"
  "execution-authority acquisition"

decisionInformationDebt : AcquisitionDebt
decisionInformationDebt = acquisition-debt decisionTimeInformationArtifact unpaid
  "identify what information was available to the actual decision-maker when a specific disclosed trade was selected"
  "contemporaneous communication, manager system log, regulatory finding, sworn evidence or comparable primary record"
  "transaction event and later disclosure do not reconstruct the earlier decision-time information set"
  "Bayesian-information-state acquisition"

fundingSourceDebt : AcquisitionDebt
fundingSourceDebt = acquisition-debt transactionFundingArtifact unpaid
  "bind a specific reported securities transaction to its actual source of capital"
  "account ledger, cash-flow record, audited statement or equivalent primary source"
  "aggregate crypto/business income does not automatically fund any specific trade"
  "capital-provenance acquisition"

truthAPIContractDebt : AcquisitionDebt
truthAPIContractDebt = acquisition-debt truthAPIContractArtifact partiallyPaid
  "recover identified Truth API customer contracts / terms rather than issuer-reported agreement counts"
  "executed customer contract, customer confirmation, litigation exhibit or competent regulatory record"
  "launch/customer-count/revenue claims are paid; counterparty identity/terms remain proposition-local"
  "market-data-counterparty acquisition"

truthAPILatencyDebt : AcquisitionDebt
truthAPILatencyDebt = acquisition-debt truthAPILatencyMeasurementArtifact unpaid
  "measure realised end-to-end latency advantage relative to ordinary public access"
  "independent timestamped measurement or reproducible market-data capture"
  "issuer low-latency language does not establish realised trading advantage"
  "market-microstructure acquisition"

publicSequenceAnchor : Tariff.PublicSequence
publicSequenceAnchor = Tariff.canonicalApril9Sequence
decisionProvenanceAnchor : Decision.TradeDecisionProvenance
decisionProvenanceAnchor = Decision.coinbaseDecisionProvenance

data PaidNeighborAutomaticallyPaysDebt : Set where
data SearchFailureAutomaticallyProvesAbsence : Set where
data AcquisitionPriorityAutomaticallyMeansWrongdoing : Set where
neighboringEvidenceDoesNotPayDebt : PaidNeighborAutomaticallyPaysDebt → ⊥
neighboringEvidenceDoesNotPayDebt ()
failureToLocateDoesNotProveAbsence : SearchFailureAutomaticallyProvesAbsence → ⊥
failureToLocateDoesNotProveAbsence ()
priorityDoesNotMeanWrongdoing : AcquisitionPriorityAutomaticallyMeansWrongdoing → ⊥
priorityDoesNotMeanWrongdoing ()

record Round5AcquisitionBoundary : Set where
  constructor round5-acquisition-boundary
  field
    debtIsPropositionIndexed tradeIdentityStillSeparateFromPublicSignal decisionMakerStillSeparateFromTransaction informationSetStillSeparateFromDecisionMaker investigationRequestStillSeparateFromOutcome searchAbsenceIsNotEvidenceOfAbsence acquisitionPriorityIsNotAccusation : Bool
canonicalRound5AcquisitionBoundary : Round5AcquisitionBoundary
canonicalRound5AcquisitionBoundary = round5-acquisition-boundary true true true true true true true
