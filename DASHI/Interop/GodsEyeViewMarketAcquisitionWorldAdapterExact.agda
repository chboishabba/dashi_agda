module DASHI.Interop.GodsEyeViewMarketAcquisitionWorldAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewRuntimeNeutralAcquisitionABIExact as ABI
import DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact as Assessment

------------------------------------------------------------------------
-- BOUNDED MARKET ACQUISITION -> WORLD ACQUISITION ABI
--
-- Market-data transport is provider work, not an insider-trading / manipulation
-- classifier.  This adapter preserves the exact live consumer/prerequisite and
-- the no-lookahead / identity / mechanism coordinates already required by the
-- GEV market lane, then returns the ordinary runtime-neutral acquisition result.
-- Semantic disposition remains owned by the generic assessment/return loop.
------------------------------------------------------------------------

record BoundMarketWorldRequest
    (request : ABI.RuntimeNeutralAcquisitionRequest) : Set where
  constructor bound-market-world-request
  field
    providerIsMarketData :
      ABI.providerKind request ≡ ABI.marketDataProvider
    requestedCarrierIsMarketEvent :
      ABI.requestedCarrier request ≡ ABI.marketEventCarrier

    venueReference : String
    marketTickerOrContractReference : String
    boundedQueryReference : String
    requestedStartTimeReference : String
    requestedEndTimeReference : String
    informationCutoffReference : String
    accountOrWalletScopeReference : String
    publicInformationSetReference : String
    mechanismDiscriminatorReference : String
    noLookaheadReference : String
    bindingReference : String

open BoundMarketWorldRequest public

data MarketAcquisitionOutcome : Set where
  executedWithBoundedMarketOutput : MarketAcquisitionOutcome
  executedNoMarketMatch : MarketAcquisitionOutcome
  marketAcquisitionBlocked : MarketAcquisitionOutcome
  marketProviderUnavailable : MarketAcquisitionOutcome
  marketAcquisitionFailed : MarketAcquisitionOutcome

executionStatusFor : MarketAcquisitionOutcome → ABI.AcquisitionExecutionStatus
executionStatusFor executedWithBoundedMarketOutput = ABI.executedWithOutput
executionStatusFor executedNoMarketMatch = ABI.executedNoMatch
executionStatusFor marketAcquisitionBlocked = ABI.blockedBeforeExecution
executionStatusFor marketProviderUnavailable = ABI.providerUnavailable
executionStatusFor marketAcquisitionFailed = ABI.executionFailed

marketOutcomeAllowsSemanticAssessment : MarketAcquisitionOutcome → Bool
marketOutcomeAllowsSemanticAssessment executedWithBoundedMarketOutput = true
marketOutcomeAllowsSemanticAssessment executedNoMarketMatch = false
marketOutcomeAllowsSemanticAssessment marketAcquisitionBlocked = false
marketOutcomeAllowsSemanticAssessment marketProviderUnavailable = false
marketOutcomeAllowsSemanticAssessment marketAcquisitionFailed = false

genericAssessmentAdmissionAgrees :
  (outcome : MarketAcquisitionOutcome) →
  Assessment.executionAllowsSemanticAssessment (executionStatusFor outcome)
  ≡ marketOutcomeAllowsSemanticAssessment outcome
genericAssessmentAdmissionAgrees executedWithBoundedMarketOutput = refl
genericAssessmentAdmissionAgrees executedNoMarketMatch = refl
genericAssessmentAdmissionAgrees marketAcquisitionBlocked = refl
genericAssessmentAdmissionAgrees marketProviderUnavailable = refl
genericAssessmentAdmissionAgrees marketAcquisitionFailed = refl

record MarketWorldAcquisitionReceipt
    {request : ABI.RuntimeNeutralAcquisitionRequest}
    (bound : BoundMarketWorldRequest request) : Set₁ where
  constructor market-world-acquisition-receipt
  field
    outcome : MarketAcquisitionOutcome
    providerExecutionReference : String
    observationTimeOrRevisionReference : String
    exactTradeOrderbookOrChainLocatorReference : String
    contentIdentityOrHashReference : String
    coverageReference : String
    uncertaintyReference : String
    provenanceReference : String
    acquisitionAuthorityReference : String
    rawEvidenceReference : String
    providerInterpretationReference : String
    resultIdentityReference : String

    eventTimeAssessmentReference : String
    informationReleaseTimeAssessmentReference : String
    entityResolutionReference : String
    crossVenueLinkageReference : String
    sourceOfFundsReference : String
    mechanismAlternativeReference : String
    validationReference : String

open MarketWorldAcquisitionReceipt public

marketReceiptToRuntimeResult :
  ∀ {request}
    {bound : BoundMarketWorldRequest request} →
  MarketWorldAcquisitionReceipt bound →
  ABI.RuntimeNeutralAcquisitionResult request
marketReceiptToRuntimeResult {bound = bound} receipt =
  ABI.runtime-neutral-acquisition-result
    (executionStatusFor (outcome receipt))
    (providerExecutionReference receipt)
    ABI.marketEventCarrier
    "market adapter returns the market-event carrier required by the bound request"
    (venueReference bound)
    (observationTimeOrRevisionReference receipt)
    (exactTradeOrderbookOrChainLocatorReference receipt)
    (contentIdentityOrHashReference receipt)
    (coverageReference receipt)
    (uncertaintyReference receipt)
    (provenanceReference receipt)
    (acquisitionAuthorityReference receipt)
    (rawEvidenceReference receipt)
    (providerInterpretationReference receipt)
    false refl
    false refl
    false refl
    (resultIdentityReference receipt)

------------------------------------------------------------------------
-- Introspective firewalls.
------------------------------------------------------------------------

data MarketOutputCreatesTraderIdentity : Set where
data MarketAnomalyCreatesMNPI : Set where
data MarketAnomalyCreatesDuty : Set where
data MarketAnomalyCreatesLiability : Set where
data WalletClusterCreatesPersonIdentity : Set where
data ProfitablePatternCreatesManipulationFinding : Set where
data NoMarketMatchMeansNoRelevantConduct : Set where
data MarketRuntimeResultCreatesTradeAuthority : Set where

marketOutputDoesNotCreateTraderIdentity : MarketOutputCreatesTraderIdentity → ⊥
marketOutputDoesNotCreateTraderIdentity ()

marketAnomalyDoesNotCreateMNPI : MarketAnomalyCreatesMNPI → ⊥
marketAnomalyDoesNotCreateMNPI ()

marketAnomalyDoesNotCreateDuty : MarketAnomalyCreatesDuty → ⊥
marketAnomalyDoesNotCreateDuty ()

marketAnomalyDoesNotCreateLiability : MarketAnomalyCreatesLiability → ⊥
marketAnomalyDoesNotCreateLiability ()

walletClusterDoesNotCreatePersonIdentity : WalletClusterCreatesPersonIdentity → ⊥
walletClusterDoesNotCreatePersonIdentity ()

profitablePatternDoesNotCreateManipulationFinding :
  ProfitablePatternCreatesManipulationFinding → ⊥
profitablePatternDoesNotCreateManipulationFinding ()

noMarketMatchDoesNotMeanNoRelevantConduct : NoMarketMatchMeansNoRelevantConduct → ⊥
noMarketMatchDoesNotMeanNoRelevantConduct ()

marketRuntimeResultDoesNotCreateTradeAuthority :
  MarketRuntimeResultCreatesTradeAuthority → ⊥
marketRuntimeResultDoesNotCreateTradeAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record MarketWorldAdapterBoundary : Set where
  constructor market-world-adapter-boundary
  field
    requestMustRemainLiveResidualBound : Bool
    requestMustRemainLiveResidualBoundIsTrue :
      requestMustRemainLiveResidualBound ≡ true
    timeAndInformationCutoffRemainDistinct : Bool
    timeAndInformationCutoffRemainDistinctIsTrue :
      timeAndInformationCutoffRemainDistinct ≡ true
    entityResolutionRemainsDownstream : Bool
    entityResolutionRemainsDownstreamIsTrue :
      entityResolutionRemainsDownstream ≡ true
    competingMarketMechanismsRemainVisible : Bool
    competingMarketMechanismsRemainVisibleIsTrue :
      competingMarketMechanismsRemainVisible ≡ true
    executedOutputMayEnterGenericAssessment : Bool
    executedOutputMayEnterGenericAssessmentIsTrue :
      executedOutputMayEnterGenericAssessment ≡ true
    noMatchMayEnterGenericAssessment : Bool
    noMatchMayEnterGenericAssessmentIsFalse :
      noMatchMayEnterGenericAssessment ≡ false
    adapterOwnsSemanticDisposition : Bool
    adapterOwnsSemanticDispositionIsFalse :
      adapterOwnsSemanticDisposition ≡ false
    adapterCreatesLegalOrTradeAuthority : Bool
    adapterCreatesLegalOrTradeAuthorityIsFalse :
      adapterCreatesLegalOrTradeAuthority ≡ false

canonicalMarketWorldAdapterBoundary : MarketWorldAdapterBoundary
canonicalMarketWorldAdapterBoundary =
  market-world-adapter-boundary
    true refl true refl true refl true refl true refl false refl false refl false refl
