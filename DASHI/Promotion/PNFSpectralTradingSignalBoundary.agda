module DASHI.Promotion.PNFSpectralTradingSignalBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Core.FiniteReceiptList using (listCount)

------------------------------------------------------------------------
-- PNF spectral trading/news application boundary.
--
-- This module records a consumer-facing Nashi/Mirror-style vocabulary for
-- market/news use of PNF spectral fields.  It is intentionally non-promoting:
-- the records below may describe candidate packets and proposal-only signal
-- envelopes, but they do not assert financial validity, market prediction,
-- production trading authority, or empirical adequacy.

------------------------------------------------------------------------
-- Consumer concepts.

data MarketInformationSurface : Set where
  priceTapeSurface : MarketInformationSurface
  orderBookSurface : MarketInformationSurface
  corporateNewsSurface : MarketInformationSurface
  macroNewsSurface : MarketInformationSurface
  socialNarrativeSurface : MarketInformationSurface
  regulatoryFilingSurface : MarketInformationSurface
  analystResearchSurface : MarketInformationSurface
  receiptBackedReplaySurface : MarketInformationSurface

data PNFSpectralTradingConsumerConcept : Set where
  incomingEvidenceBraidConcept :
    PNFSpectralTradingConsumerConcept
  historicalAdverseBraidNeighborhoodConcept :
    PNFSpectralTradingConsumerConcept
  historicalFavorableBraidNeighborhoodConcept :
    PNFSpectralTradingConsumerConcept
  volatilityBurstCandidateConcept :
    PNFSpectralTradingConsumerConcept
  falseHoldCandidateConcept :
    PNFSpectralTradingConsumerConcept
  missedOpportunityCandidateConcept :
    PNFSpectralTradingConsumerConcept
  supportPacketDeformationConcept :
    PNFSpectralTradingConsumerConcept

canonicalConsumerConcepts :
  List PNFSpectralTradingConsumerConcept
canonicalConsumerConcepts =
  incomingEvidenceBraidConcept
  ∷ historicalAdverseBraidNeighborhoodConcept
  ∷ historicalFavorableBraidNeighborhoodConcept
  ∷ volatilityBurstCandidateConcept
  ∷ falseHoldCandidateConcept
  ∷ missedOpportunityCandidateConcept
  ∷ supportPacketDeformationConcept
  ∷ []

data BraidPolarity : Set where
  adverseBraidPolarity : BraidPolarity
  favorableBraidPolarity : BraidPolarity
  mixedBraidPolarity : BraidPolarity
  unknownBraidPolarity : BraidPolarity

data CandidateDecisionSurface : Set where
  holdCandidateSurface : CandidateDecisionSurface
  watchCandidateSurface : CandidateDecisionSurface
  reduceExposureCandidateSurface : CandidateDecisionSurface
  increaseExposureCandidateSurface : CandidateDecisionSurface
  exitCandidateSurface : CandidateDecisionSurface
  noActionCandidateSurface : CandidateDecisionSurface

data SupportDeformationKind : Set where
  supportExpansionCandidate : SupportDeformationKind
  supportContractionCandidate : SupportDeformationKind
  supportRotationCandidate : SupportDeformationKind
  supportFragmentationCandidate : SupportDeformationKind
  supportStabilizationCandidate : SupportDeformationKind

record IncomingEvidenceBraid : Set where
  field
    braidId : String
    sourceSurfaces : List MarketInformationSurface
    pnfSpectralVectorIndexAnchor : String
    pnfBraidTransportFieldAnchor : String
    eventWindow : String
    evidenceDigest : String
    narrativeDigest : String
    receiptId : String
    receiptSupplied : Bool
    receiptSuppliedIsFalseByDefault :
      receiptSupplied ≡ false
    marketFactClaimed : Bool
    marketFactClaimedIsFalse :
      marketFactClaimed ≡ false

record HistoricalBraidNeighborhood : Set where
  field
    neighborhoodId : String
    targetBraid : IncomingEvidenceBraid
    polarity : BraidPolarity
    historicalWindow : String
    similarityMetric : String
    neighborhoodDigest : String
    replayReceiptId : String
    replayReceiptSupplied : Bool
    replayReceiptSuppliedIsFalseByDefault :
      replayReceiptSupplied ≡ false
    adverseOrFavorableOutcomeAsserted : Bool
    adverseOrFavorableOutcomeAssertedIsFalse :
      adverseOrFavorableOutcomeAsserted ≡ false

record VolatilityBurstCandidate : Set where
  field
    candidateId : String
    incomingBraid : IncomingEvidenceBraid
    adverseNeighborhood : HistoricalBraidNeighborhood
    favorableNeighborhood : HistoricalBraidNeighborhood
    burstWindow : String
    spectralBurstFeature : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    volatilityPredicted : Bool
    volatilityPredictedIsFalse : volatilityPredicted ≡ false

record FalseHoldMissedOpportunityCandidate : Set where
  field
    candidateId : String
    candidateDecisionSurface : CandidateDecisionSurface
    incomingBraid : IncomingEvidenceBraid
    referenceNeighborhood : HistoricalBraidNeighborhood
    counterfactualLabel : String
    counterfactualEvidenceDigest : String
    falseHoldCandidate : Bool
    missedOpportunityCandidate : Bool
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    counterfactualProfitClaimed : Bool
    counterfactualProfitClaimedIsFalse :
      counterfactualProfitClaimed ≡ false

record SupportPacketDeformation : Set where
  field
    deformationId : String
    incomingBraid : IncomingEvidenceBraid
    deformationKind : SupportDeformationKind
    priorSupportPacketDigest : String
    deformedSupportPacketDigest : String
    deformationOperatorDigest : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    tradableSupportClaimed : Bool
    tradableSupportClaimedIsFalse :
      tradableSupportClaimed ≡ false

------------------------------------------------------------------------
-- Signal proposals and validation requirements.

data TradingSignalStatus : Set where
  candidateOnlySignal : TradingSignalStatus
  proposalOnlySignal : TradingSignalStatus
  resolverPendingSignal : TradingSignalStatus
  selectorPendingSignal : TradingSignalStatus
  itirValidationPendingSignal : TradingSignalStatus
  replayReceiptPendingSignal : TradingSignalStatus

data TradingSignalValidationRequirement : Set where
  resolverRequirement :
    TradingSignalValidationRequirement
  selectorRequirement :
    TradingSignalValidationRequirement
  itirValidationRequirement :
    TradingSignalValidationRequirement
  historicalReplayRequirement :
    TradingSignalValidationRequirement
  receiptBindingRequirement :
    TradingSignalValidationRequirement
  slippageAndCostsRequirement :
    TradingSignalValidationRequirement
  holdoutRegimeRequirement :
    TradingSignalValidationRequirement
  riskLimitReviewRequirement :
    TradingSignalValidationRequirement
  humanGovernanceReviewRequirement :
    TradingSignalValidationRequirement

canonicalTradingSignalValidationRequirements :
  List TradingSignalValidationRequirement
canonicalTradingSignalValidationRequirements =
  resolverRequirement
  ∷ selectorRequirement
  ∷ itirValidationRequirement
  ∷ historicalReplayRequirement
  ∷ receiptBindingRequirement
  ∷ slippageAndCostsRequirement
  ∷ holdoutRegimeRequirement
  ∷ riskLimitReviewRequirement
  ∷ humanGovernanceReviewRequirement
  ∷ []

record ResolverSelectorITIRValidationEnvelope : Set where
  field
    resolverId : String
    selectorId : String
    itirValidationLaneId : String
    resolverRequired : Bool
    resolverRequiredIsTrue : resolverRequired ≡ true
    selectorRequired : Bool
    selectorRequiredIsTrue : selectorRequired ≡ true
    itirValidationRequired : Bool
    itirValidationRequiredIsTrue :
      itirValidationRequired ≡ true
    resolverReceiptSupplied : Bool
    resolverReceiptSuppliedIsFalseByDefault :
      resolverReceiptSupplied ≡ false
    selectorReceiptSupplied : Bool
    selectorReceiptSuppliedIsFalseByDefault :
      selectorReceiptSupplied ≡ false
    itirValidationReceiptSupplied : Bool
    itirValidationReceiptSuppliedIsFalseByDefault :
      itirValidationReceiptSupplied ≡ false

record TradingSignalProposal : Set where
  field
    signalId : String
    signalStatus : TradingSignalStatus
    incomingBraid : IncomingEvidenceBraid
    adverseNeighborhood : HistoricalBraidNeighborhood
    favorableNeighborhood : HistoricalBraidNeighborhood
    volatilityBurstCandidate :
      VolatilityBurstCandidate
    falseHoldOrMissedOpportunityCandidate :
      FalseHoldMissedOpportunityCandidate
    supportPacketDeformation :
      SupportPacketDeformation
    validationEnvelope :
      ResolverSelectorITIRValidationEnvelope
    validationRequirements :
      List TradingSignalValidationRequirement
    proposedActionSurface :
      CandidateDecisionSurface
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    proposalOnly : Bool
    proposalOnlyIsTrue : proposalOnly ≡ true
    executableTradingSignal : Bool
    executableTradingSignalIsFalse :
      executableTradingSignal ≡ false
    predictionClaim : Bool
    predictionClaimIsFalse :
      predictionClaim ≡ false
    financialAdviceClaim : Bool
    financialAdviceClaimIsFalse :
      financialAdviceClaim ≡ false

------------------------------------------------------------------------
-- Governance gates.

data TradingBoundaryGovernanceGate : Set where
  noFinancialAdviceGate :
    TradingBoundaryGovernanceGate
  noMarketPredictionGuaranteeGate :
    TradingBoundaryGovernanceGate
  noProductionTradingAuthorityGate :
    TradingBoundaryGovernanceGate
  noEmpiricalAdequacyWithoutReplayReceiptGate :
    TradingBoundaryGovernanceGate
  resolverRequiredBeforeSelectionGate :
    TradingBoundaryGovernanceGate
  selectorRequiredBeforeExecutionGate :
    TradingBoundaryGovernanceGate
  itirValidationRequiredBeforePromotionGate :
    TradingBoundaryGovernanceGate
  replayAndReceiptRequiredBeforeAdequacyGate :
    TradingBoundaryGovernanceGate

canonicalTradingBoundaryGovernanceGates :
  List TradingBoundaryGovernanceGate
canonicalTradingBoundaryGovernanceGates =
  noFinancialAdviceGate
  ∷ noMarketPredictionGuaranteeGate
  ∷ noProductionTradingAuthorityGate
  ∷ noEmpiricalAdequacyWithoutReplayReceiptGate
  ∷ resolverRequiredBeforeSelectionGate
  ∷ selectorRequiredBeforeExecutionGate
  ∷ itirValidationRequiredBeforePromotionGate
  ∷ replayAndReceiptRequiredBeforeAdequacyGate
  ∷ []

data TradingSignalPromotion : Set where

tradingSignalPromotionImpossible :
  TradingSignalPromotion →
  ⊥
tradingSignalPromotionImpossible ()

------------------------------------------------------------------------
-- Canonical non-promoting packet.

canonicalIncomingEvidenceBraid : IncomingEvidenceBraid
canonicalIncomingEvidenceBraid =
  record
    { braidId =
        "canonical incoming evidence braid placeholder"
    ; sourceSurfaces =
        priceTapeSurface
        ∷ corporateNewsSurface
        ∷ macroNewsSurface
        ∷ receiptBackedReplaySurface
        ∷ []
    ; pnfSpectralVectorIndexAnchor =
        "DASHI.Interop.PNFSpectralVectorIndex"
    ; pnfBraidTransportFieldAnchor =
        "DASHI.Interop.PNFBraidTransportField"
    ; eventWindow =
        "unvalidated candidate event window"
    ; evidenceDigest =
        "no digest accepted without receipt"
    ; narrativeDigest =
        "news narrative digest is candidate-only"
    ; receiptId =
        "missing runtime/replay receipt"
    ; receiptSupplied =
        false
    ; receiptSuppliedIsFalseByDefault =
        refl
    ; marketFactClaimed =
        false
    ; marketFactClaimedIsFalse =
        refl
    }

canonicalAdverseBraidNeighborhood :
  HistoricalBraidNeighborhood
canonicalAdverseBraidNeighborhood =
  record
    { neighborhoodId =
        "canonical adverse braid neighborhood placeholder"
    ; targetBraid =
        canonicalIncomingEvidenceBraid
    ; polarity =
        adverseBraidPolarity
    ; historicalWindow =
        "historical adverse window pending replay"
    ; similarityMetric =
        "spectral-braid similarity metric pending selector"
    ; neighborhoodDigest =
        "adverse neighborhood digest pending receipt"
    ; replayReceiptId =
        "missing adverse replay receipt"
    ; replayReceiptSupplied =
        false
    ; replayReceiptSuppliedIsFalseByDefault =
        refl
    ; adverseOrFavorableOutcomeAsserted =
        false
    ; adverseOrFavorableOutcomeAssertedIsFalse =
        refl
    }

canonicalFavorableBraidNeighborhood :
  HistoricalBraidNeighborhood
canonicalFavorableBraidNeighborhood =
  record
    { neighborhoodId =
        "canonical favorable braid neighborhood placeholder"
    ; targetBraid =
        canonicalIncomingEvidenceBraid
    ; polarity =
        favorableBraidPolarity
    ; historicalWindow =
        "historical favorable window pending replay"
    ; similarityMetric =
        "spectral-braid similarity metric pending selector"
    ; neighborhoodDigest =
        "favorable neighborhood digest pending receipt"
    ; replayReceiptId =
        "missing favorable replay receipt"
    ; replayReceiptSupplied =
        false
    ; replayReceiptSuppliedIsFalseByDefault =
        refl
    ; adverseOrFavorableOutcomeAsserted =
        false
    ; adverseOrFavorableOutcomeAssertedIsFalse =
        refl
    }

canonicalVolatilityBurstCandidate :
  VolatilityBurstCandidate
canonicalVolatilityBurstCandidate =
  record
    { candidateId =
        "canonical volatility burst candidate"
    ; incomingBraid =
        canonicalIncomingEvidenceBraid
    ; adverseNeighborhood =
        canonicalAdverseBraidNeighborhood
    ; favorableNeighborhood =
        canonicalFavorableBraidNeighborhood
    ; burstWindow =
        "candidate burst window pending replay"
    ; spectralBurstFeature =
        "candidate spectral energy concentration"
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; volatilityPredicted =
        false
    ; volatilityPredictedIsFalse =
        refl
    }

canonicalFalseHoldMissedOpportunityCandidate :
  FalseHoldMissedOpportunityCandidate
canonicalFalseHoldMissedOpportunityCandidate =
  record
    { candidateId =
        "canonical false-hold missed-opportunity candidate"
    ; candidateDecisionSurface =
        holdCandidateSurface
    ; incomingBraid =
        canonicalIncomingEvidenceBraid
    ; referenceNeighborhood =
        canonicalFavorableBraidNeighborhood
    ; counterfactualLabel =
        "counterfactual candidate pending replay"
    ; counterfactualEvidenceDigest =
        "counterfactual digest pending receipt"
    ; falseHoldCandidate =
        true
    ; missedOpportunityCandidate =
        true
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; counterfactualProfitClaimed =
        false
    ; counterfactualProfitClaimedIsFalse =
        refl
    }

canonicalSupportPacketDeformation :
  SupportPacketDeformation
canonicalSupportPacketDeformation =
  record
    { deformationId =
        "canonical support packet deformation candidate"
    ; incomingBraid =
        canonicalIncomingEvidenceBraid
    ; deformationKind =
        supportRotationCandidate
    ; priorSupportPacketDigest =
        "prior support packet digest pending receipt"
    ; deformedSupportPacketDigest =
        "deformed support packet digest pending receipt"
    ; deformationOperatorDigest =
        "support deformation operator pending resolver"
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; tradableSupportClaimed =
        false
    ; tradableSupportClaimedIsFalse =
        refl
    }

canonicalResolverSelectorITIRValidationEnvelope :
  ResolverSelectorITIRValidationEnvelope
canonicalResolverSelectorITIRValidationEnvelope =
  record
    { resolverId =
        "resolver required before any signal interpretation"
    ; selectorId =
        "selector required before ranking or action choice"
    ; itirValidationLaneId =
        "ITIR replay and receipt validation required"
    ; resolverRequired =
        true
    ; resolverRequiredIsTrue =
        refl
    ; selectorRequired =
        true
    ; selectorRequiredIsTrue =
        refl
    ; itirValidationRequired =
        true
    ; itirValidationRequiredIsTrue =
        refl
    ; resolverReceiptSupplied =
        false
    ; resolverReceiptSuppliedIsFalseByDefault =
        refl
    ; selectorReceiptSupplied =
        false
    ; selectorReceiptSuppliedIsFalseByDefault =
        refl
    ; itirValidationReceiptSupplied =
        false
    ; itirValidationReceiptSuppliedIsFalseByDefault =
        refl
    }

canonicalTradingSignalProposal :
  TradingSignalProposal
canonicalTradingSignalProposal =
  record
    { signalId =
        "canonical PNF spectral trading/news candidate proposal"
    ; signalStatus =
        proposalOnlySignal
    ; incomingBraid =
        canonicalIncomingEvidenceBraid
    ; adverseNeighborhood =
        canonicalAdverseBraidNeighborhood
    ; favorableNeighborhood =
        canonicalFavorableBraidNeighborhood
    ; volatilityBurstCandidate =
        canonicalVolatilityBurstCandidate
    ; falseHoldOrMissedOpportunityCandidate =
        canonicalFalseHoldMissedOpportunityCandidate
    ; supportPacketDeformation =
        canonicalSupportPacketDeformation
    ; validationEnvelope =
        canonicalResolverSelectorITIRValidationEnvelope
    ; validationRequirements =
        canonicalTradingSignalValidationRequirements
    ; proposedActionSurface =
        watchCandidateSurface
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; proposalOnly =
        true
    ; proposalOnlyIsTrue =
        refl
    ; executableTradingSignal =
        false
    ; executableTradingSignalIsFalse =
        refl
    ; predictionClaim =
        false
    ; predictionClaimIsFalse =
        refl
    ; financialAdviceClaim =
        false
    ; financialAdviceClaimIsFalse =
        refl
    }

canonicalBoundaryStatement : String
canonicalBoundaryStatement =
  "PNF spectral trading/news packets are candidate/proposal-only consumer artifacts. They require resolver, selector, ITIR validation, replay, and receipt binding before any empirical adequacy discussion. They provide no financial advice, no market prediction guarantee, and no production trading authority."

record PNFSpectralTradingSignalBoundaryReceipt : Set where
  field
    consumerConcepts :
      List PNFSpectralTradingConsumerConcept
    consumerConceptsAreCanonical :
      consumerConcepts ≡ canonicalConsumerConcepts
    governanceGates :
      List TradingBoundaryGovernanceGate
    governanceGatesAreCanonical :
      governanceGates ≡ canonicalTradingBoundaryGovernanceGates
    signalProposal :
      TradingSignalProposal
    signalProposalIsCanonical :
      signalProposal ≡ canonicalTradingSignalProposal
    validationRequirements :
      List TradingSignalValidationRequirement
    validationRequirementsAreCanonical :
      validationRequirements
      ≡
      canonicalTradingSignalValidationRequirements
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ canonicalBoundaryStatement
    financialAdviceAuthority :
      Bool
    financialAdviceAuthorityIsFalse :
      financialAdviceAuthority ≡ false
    marketPredictionGuarantee :
      Bool
    marketPredictionGuaranteeIsFalse :
      marketPredictionGuarantee ≡ false
    productionTradingAuthority :
      Bool
    productionTradingAuthorityIsFalse :
      productionTradingAuthority ≡ false
    empiricalAdequacy :
      Bool
    empiricalAdequacyIsFalseWithoutReplayReceipt :
      empiricalAdequacy ≡ false
    replayReceiptSupplied :
      Bool
    replayReceiptSuppliedIsFalse :
      replayReceiptSupplied ≡ false
    resolverValidationSupplied :
      Bool
    resolverValidationSuppliedIsFalse :
      resolverValidationSupplied ≡ false
    selectorValidationSupplied :
      Bool
    selectorValidationSuppliedIsFalse :
      selectorValidationSupplied ≡ false
    itirValidationSupplied :
      Bool
    itirValidationSuppliedIsFalse :
      itirValidationSupplied ≡ false
    tradingSignalPromoted :
      Bool
    tradingSignalPromotedIsFalse :
      tradingSignalPromoted ≡ false
    promotionFlags :
      List TradingSignalPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open PNFSpectralTradingSignalBoundaryReceipt public

canonicalPNFSpectralTradingSignalBoundaryReceipt :
  PNFSpectralTradingSignalBoundaryReceipt
canonicalPNFSpectralTradingSignalBoundaryReceipt =
  record
    { consumerConcepts =
        canonicalConsumerConcepts
    ; consumerConceptsAreCanonical =
        refl
    ; governanceGates =
        canonicalTradingBoundaryGovernanceGates
    ; governanceGatesAreCanonical =
        refl
    ; signalProposal =
        canonicalTradingSignalProposal
    ; signalProposalIsCanonical =
        refl
    ; validationRequirements =
        canonicalTradingSignalValidationRequirements
    ; validationRequirementsAreCanonical =
        refl
    ; boundaryStatement =
        canonicalBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; financialAdviceAuthority =
        false
    ; financialAdviceAuthorityIsFalse =
        refl
    ; marketPredictionGuarantee =
        false
    ; marketPredictionGuaranteeIsFalse =
        refl
    ; productionTradingAuthority =
        false
    ; productionTradingAuthorityIsFalse =
        refl
    ; empiricalAdequacy =
        false
    ; empiricalAdequacyIsFalseWithoutReplayReceipt =
        refl
    ; replayReceiptSupplied =
        false
    ; replayReceiptSuppliedIsFalse =
        refl
    ; resolverValidationSupplied =
        false
    ; resolverValidationSuppliedIsFalse =
        refl
    ; selectorValidationSupplied =
        false
    ; selectorValidationSuppliedIsFalse =
        refl
    ; itirValidationSupplied =
        false
    ; itirValidationSuppliedIsFalse =
        refl
    ; tradingSignalPromoted =
        false
    ; tradingSignalPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

canonicalConsumerConceptCountIs7 :
  listCount
    (consumerConcepts
      canonicalPNFSpectralTradingSignalBoundaryReceipt)
  ≡ 7
canonicalConsumerConceptCountIs7 =
  refl

canonicalGovernanceGateCountIs8 :
  listCount
    (governanceGates
      canonicalPNFSpectralTradingSignalBoundaryReceipt)
  ≡ 8
canonicalGovernanceGateCountIs8 =
  refl

canonicalValidationRequirementCountIs9 :
  listCount
    (validationRequirements
      canonicalPNFSpectralTradingSignalBoundaryReceipt)
  ≡ 9
canonicalValidationRequirementCountIs9 =
  refl

canonicalTradingSignalNoFinancialAdvice :
  financialAdviceAuthority
    canonicalPNFSpectralTradingSignalBoundaryReceipt
  ≡ false
canonicalTradingSignalNoFinancialAdvice =
  refl

canonicalTradingSignalNoMarketPredictionGuarantee :
  marketPredictionGuarantee
    canonicalPNFSpectralTradingSignalBoundaryReceipt
  ≡ false
canonicalTradingSignalNoMarketPredictionGuarantee =
  refl

canonicalTradingSignalNoProductionAuthority :
  productionTradingAuthority
    canonicalPNFSpectralTradingSignalBoundaryReceipt
  ≡ false
canonicalTradingSignalNoProductionAuthority =
  refl

canonicalTradingSignalNoEmpiricalAdequacy :
  empiricalAdequacy
    canonicalPNFSpectralTradingSignalBoundaryReceipt
  ≡ false
canonicalTradingSignalNoEmpiricalAdequacy =
  refl

canonicalTradingSignalNoPromotion :
  tradingSignalPromoted
    canonicalPNFSpectralTradingSignalBoundaryReceipt
  ≡ false
canonicalTradingSignalNoPromotion =
  refl
