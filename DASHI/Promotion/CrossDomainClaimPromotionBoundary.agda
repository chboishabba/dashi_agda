module DASHI.Promotion.CrossDomainClaimPromotionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
import DASHI.Promotion.AuthorityGateCore as AuthorityGateCore
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.BridgeRequirementCore as BridgeReq
import DASHI.Core.CandidateOnlyCore as CandidateOnly
open import DASHI.Core.FiniteReceiptList using (listCount)

------------------------------------------------------------------------
-- Cross-domain claim promotion boundary.
--
-- This module records a fail-closed receipt surface for mathematical or
-- structural analogies.  Analogies, graph shapes, vectors, proximity
-- scores, and product candidates may be catalogued as candidate structure,
-- but they do not promote into empirical, political, economic, clinical, or
-- trading claims unless an explicit bridge receipt is supplied.

------------------------------------------------------------------------
-- Claim and bridge vocabularies.

data ClaimKind : Set where
  mathematicalClaim : ClaimKind
  structuralAnalogyClaim : ClaimKind
  evidenceGraphClaim : ClaimKind
  spatialPracticeInterpretationClaim : ClaimKind
  empiricalFactClaim : ClaimKind
  environmentalAuthorityClaim : ClaimKind
  politicalClaim : ClaimKind
  economicClaim : ClaimKind
  clinicalClaim : ClaimKind
  spiritualAuthorityClaim : ClaimKind
  legalAuthorityClaim : ClaimKind
  tradingClaim : ClaimKind
  supportClaim : ClaimKind
  admissibilityClaim : ClaimKind

data BridgeReceiptKind : Set where
  measurementAuthorityBridgeReceipt : BridgeReceiptKind
  empiricalReplayBridgeReceipt : BridgeReceiptKind
  territoryObservationBridgeReceipt : BridgeReceiptKind
  policyAuthorityBridgeReceipt : BridgeReceiptKind
  economicDataAuthorityBridgeReceipt : BridgeReceiptKind
  clinicalEvidenceAuthorityBridgeReceipt : BridgeReceiptKind
  governedSpatialPracticeValidationReceipt : BridgeReceiptKind
  tradingValidationBridgeReceipt : BridgeReceiptKind
  supportAdmissibilityBridgeReceipt : BridgeReceiptKind
  governanceReviewBridgeReceipt : BridgeReceiptKind

data PromotionBlockReason : Set where
  analogyOnlyReason : PromotionBlockReason
  missingMeasurementAuthorityReason : PromotionBlockReason
  missingTerritoryObservationReason : PromotionBlockReason
  missingDomainAuthorityReason : PromotionBlockReason
  missingClinicalEvidenceReason : PromotionBlockReason
  missingGovernedSpatialPracticeValidationReason : PromotionBlockReason
  missingTradingValidationReason : PromotionBlockReason
  missingSupportAdmissibilityReason : PromotionBlockReason

canonicalBlockedTargetClaims : List ClaimKind
canonicalBlockedTargetClaims =
  empiricalFactClaim
  ∷ environmentalAuthorityClaim
  ∷ politicalClaim
  ∷ economicClaim
  ∷ clinicalClaim
  ∷ spiritualAuthorityClaim
  ∷ legalAuthorityClaim
  ∷ tradingClaim
  ∷ supportClaim
  ∷ admissibilityClaim
  ∷ []

canonicalRequiredBridgeReceiptKinds : List BridgeReceiptKind
canonicalRequiredBridgeReceiptKinds =
  measurementAuthorityBridgeReceipt
  ∷ empiricalReplayBridgeReceipt
  ∷ territoryObservationBridgeReceipt
  ∷ policyAuthorityBridgeReceipt
  ∷ economicDataAuthorityBridgeReceipt
  ∷ clinicalEvidenceAuthorityBridgeReceipt
  ∷ governedSpatialPracticeValidationReceipt
  ∷ tradingValidationBridgeReceipt
  ∷ supportAdmissibilityBridgeReceipt
  ∷ governanceReviewBridgeReceipt
  ∷ []

------------------------------------------------------------------------
-- Authority-gate adapter rows.
--
-- The adapter below maps this module's public promotion flags and local
-- claim/bridge vocabulary onto the qualified generic authority gate core.
-- The local target and bridge fields remain because the core authority kinds
-- are intentionally coarser than this boundary's domain-specific claims.

data CrossDomainPromotionFlagName : Set where
  mathematicalAnalogyEmpiricalFlag :
    CrossDomainPromotionFlagName
  evidenceGraphTerritoryFlag :
    CrossDomainPromotionFlagName
  vectorProximitySupportFlag :
    CrossDomainPromotionFlagName
  vectorProximityAdmissibilityFlag :
    CrossDomainPromotionFlagName
  empiricalPromotionFlag :
    CrossDomainPromotionFlagName
  politicalPromotionFlag :
    CrossDomainPromotionFlagName
  economicPromotionFlag :
    CrossDomainPromotionFlagName
  clinicalPromotionFlag :
    CrossDomainPromotionFlagName
  environmentalAuthorityPromotionFlag :
    CrossDomainPromotionFlagName
  spiritualAuthorityPromotionFlag :
    CrossDomainPromotionFlagName
  legalAuthorityPromotionFlag :
    CrossDomainPromotionFlagName
  tradingPromotionFlag :
    CrossDomainPromotionFlagName
  supportPromotionFlag :
    CrossDomainPromotionFlagName
  admissibilityPromotionFlag :
    CrossDomainPromotionFlagName
  anyCrossDomainPromotionFlagName :
    CrossDomainPromotionFlagName

record CrossDomainAuthorityGateAdapterRow : Set where
  field
    authorityGateLabel : String
    promotionFlagName : CrossDomainPromotionFlagName
    coreAuthorityGate : AuthorityGateCore.PromotionGate
    coreAuthorityGateReceipt : AuthorityGateCore.AuthorityGateReceipt
    guardedTargetClaims : List ClaimKind
    requiredAuthorityBridgeReceipts : List BridgeReceiptKind

    promotionFlagValue : Bool
    promotionFlagValueIsFalse :
      promotionFlagValue ≡ false

    bridgeReceiptsRequired : Bool
    bridgeReceiptsRequiredIsTrue :
      bridgeReceiptsRequired ≡ true

    promotionWithoutBridgeBlockedFlag : Bool
    promotionWithoutBridgeBlockedFlagIsTrue :
      promotionWithoutBridgeBlockedFlag ≡ true

open CrossDomainAuthorityGateAdapterRow public

mkFailClosedAuthorityGateAdapterRow :
  String →
  CrossDomainPromotionFlagName →
  AuthorityGateCore.AuthorityKind →
  List ClaimKind →
  List BridgeReceiptKind →
  CrossDomainAuthorityGateAdapterRow
mkFailClosedAuthorityGateAdapterRow label flag kind targets bridges =
  record
    { authorityGateLabel = label
    ; promotionFlagName = flag
    ; coreAuthorityGate =
        AuthorityGateCore.mkClosedGate kind label
    ; coreAuthorityGateReceipt =
        AuthorityGateCore.mkClosedReceipt
          label
          (AuthorityGateCore.mkClosedGate kind label)
    ; guardedTargetClaims = targets
    ; requiredAuthorityBridgeReceipts = bridges
    ; promotionFlagValue =
        AuthorityGateCore.promoted
          (AuthorityGateCore.mkClosedGate kind label)
    ; promotionFlagValueIsFalse =
        AuthorityGateCore.promotedIsFalse
          (AuthorityGateCore.mkClosedGate kind label)
    ; bridgeReceiptsRequired = true
    ; bridgeReceiptsRequiredIsTrue = refl
    ; promotionWithoutBridgeBlockedFlag = true
    ; promotionWithoutBridgeBlockedFlagIsTrue = refl
    }

canonicalCrossDomainAuthorityGateAdapterRows :
  List CrossDomainAuthorityGateAdapterRow
canonicalCrossDomainAuthorityGateAdapterRows =
  mkFailClosedAuthorityGateAdapterRow
    "mathematical analogy to empirical fact gate"
    mathematicalAnalogyEmpiricalFlag
    AuthorityGateCore.empiricalAuthority
    (empiricalFactClaim ∷ [])
    (measurementAuthorityBridgeReceipt ∷ empiricalReplayBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "evidence graph to territory truth gate"
    evidenceGraphTerritoryFlag
    AuthorityGateCore.empiricalAuthority
    (empiricalFactClaim ∷ environmentalAuthorityClaim ∷ [])
    (territoryObservationBridgeReceipt ∷ empiricalReplayBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "vector proximity to support gate"
    vectorProximitySupportFlag
    AuthorityGateCore.supportAuthority
    (supportClaim ∷ [])
    (supportAdmissibilityBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "vector proximity to admissibility gate"
    vectorProximityAdmissibilityFlag
    AuthorityGateCore.admissibilityAuthority
    (admissibilityClaim ∷ [])
    (supportAdmissibilityBridgeReceipt ∷ governanceReviewBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "empirical claim promotion gate"
    empiricalPromotionFlag
    AuthorityGateCore.empiricalAuthority
    (empiricalFactClaim ∷ [])
    (measurementAuthorityBridgeReceipt ∷ empiricalReplayBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "political claim promotion gate"
    politicalPromotionFlag
    AuthorityGateCore.legalAuthority
    (politicalClaim ∷ [])
    (policyAuthorityBridgeReceipt ∷ governanceReviewBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "economic claim promotion gate"
    economicPromotionFlag
    AuthorityGateCore.scientificAuthority
    (economicClaim ∷ [])
    (economicDataAuthorityBridgeReceipt ∷ governanceReviewBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "clinical claim promotion gate"
    clinicalPromotionFlag
    AuthorityGateCore.clinicalAuthority
    (clinicalClaim ∷ [])
    (clinicalEvidenceAuthorityBridgeReceipt ∷ governanceReviewBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "environmental authority promotion gate"
    environmentalAuthorityPromotionFlag
    AuthorityGateCore.scientificAuthority
    (environmentalAuthorityClaim ∷ [])
    (territoryObservationBridgeReceipt ∷ governedSpatialPracticeValidationReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "spiritual authority promotion gate"
    spiritualAuthorityPromotionFlag
    AuthorityGateCore.spiritualAuthority
    (spiritualAuthorityClaim ∷ [])
    (governedSpatialPracticeValidationReceipt ∷ governanceReviewBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "legal authority promotion gate"
    legalAuthorityPromotionFlag
    AuthorityGateCore.legalAuthority
    (legalAuthorityClaim ∷ [])
    (policyAuthorityBridgeReceipt ∷ governanceReviewBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "trading claim promotion gate"
    tradingPromotionFlag
    AuthorityGateCore.tradingAuthority
    (tradingClaim ∷ [])
    (tradingValidationBridgeReceipt ∷ governanceReviewBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "support claim promotion gate"
    supportPromotionFlag
    AuthorityGateCore.supportAuthority
    (supportClaim ∷ [])
    (supportAdmissibilityBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "admissibility claim promotion gate"
    admissibilityPromotionFlag
    AuthorityGateCore.admissibilityAuthority
    (admissibilityClaim ∷ [])
    (supportAdmissibilityBridgeReceipt ∷ governanceReviewBridgeReceipt ∷ [])
  ∷ mkFailClosedAuthorityGateAdapterRow
    "any cross-domain promotion gate"
    anyCrossDomainPromotionFlagName
    AuthorityGateCore.runtimeAuthority
    canonicalBlockedTargetClaims
    canonicalRequiredBridgeReceiptKinds
  ∷ []

------------------------------------------------------------------------
-- Canonical examples.

record CrossDomainPromotionExample : Set where
  field
    exampleLabel : String
    sourceClaimKind : ClaimKind
    targetClaimKind : ClaimKind
    deniedAuthorityTargets : List ClaimKind
    requiredBridgeReceipt : BridgeReceiptKind
    blockReason : PromotionBlockReason
    analogyOrStructureAccepted : Bool
    analogyOrStructureAcceptedIsTrue :
      analogyOrStructureAccepted ≡ true
    explicitBridgeReceiptSupplied : Bool
    explicitBridgeReceiptSuppliedIsFalse :
      explicitBridgeReceiptSupplied ≡ false
    targetClaimPromoted : Bool
    targetClaimPromotedIsFalse :
      targetClaimPromoted ≡ false
    exampleNote : String

open CrossDomainPromotionExample public

mkBlockedExample :
  String →
  ClaimKind →
  ClaimKind →
  BridgeReceiptKind →
  PromotionBlockReason →
  String →
  CrossDomainPromotionExample
mkBlockedExample label source target bridge reason note =
  record
    { exampleLabel = label
    ; sourceClaimKind = source
    ; targetClaimKind = target
    ; deniedAuthorityTargets = target ∷ []
    ; requiredBridgeReceipt = bridge
    ; blockReason = reason
    ; analogyOrStructureAccepted = true
    ; analogyOrStructureAcceptedIsTrue = refl
    ; explicitBridgeReceiptSupplied = false
    ; explicitBridgeReceiptSuppliedIsFalse = refl
    ; targetClaimPromoted = false
    ; targetClaimPromotedIsFalse = refl
    ; exampleNote = note
    }

mathematicalAnalogyEmpiricalExample :
  CrossDomainPromotionExample
mathematicalAnalogyEmpiricalExample =
  mkBlockedExample
    "mathematical analogy does not imply empirical fact"
    structuralAnalogyClaim
    empiricalFactClaim
    measurementAuthorityBridgeReceipt
    missingMeasurementAuthorityReason
    "a formal resemblance is retained as analogy only until a measurement authority bridge is supplied"

evidenceGraphTerritoryExample :
  CrossDomainPromotionExample
evidenceGraphTerritoryExample =
  mkBlockedExample
    "evidence graph structure does not imply territory truth"
    evidenceGraphClaim
    empiricalFactClaim
    territoryObservationBridgeReceipt
    missingTerritoryObservationReason
    "nodes, edges, and replayable graph shape do not assert that the territory has the described property"

vectorProximitySupportExample :
  CrossDomainPromotionExample
vectorProximitySupportExample =
  mkBlockedExample
    "vector and proximity candidates do not imply support"
    mathematicalClaim
    supportClaim
    supportAdmissibilityBridgeReceipt
    missingSupportAdmissibilityReason
    "embedding distance, neighborhood membership, or score proximity remains a support candidate only"

productCandidateAdmissibilityExample :
  CrossDomainPromotionExample
productCandidateAdmissibilityExample =
  mkBlockedExample
    "product candidate does not imply admissibility"
    structuralAnalogyClaim
    admissibilityClaim
    supportAdmissibilityBridgeReceipt
    missingSupportAdmissibilityReason
    "a constructed product, packet, or witness candidate is not an admissibility receipt"

structuralAnalogyPoliticalExample :
  CrossDomainPromotionExample
structuralAnalogyPoliticalExample =
  mkBlockedExample
    "structural analogy does not imply political claim"
    structuralAnalogyClaim
    politicalClaim
    policyAuthorityBridgeReceipt
    missingDomainAuthorityReason
    "formal governance shape does not decide political fact or policy validity"

structuralAnalogyEconomicExample :
  CrossDomainPromotionExample
structuralAnalogyEconomicExample =
  mkBlockedExample
    "structural analogy does not imply economic claim"
    structuralAnalogyClaim
    economicClaim
    economicDataAuthorityBridgeReceipt
    missingDomainAuthorityReason
    "market or macro analogy requires economic data authority before promotion"

structuralAnalogyClinicalExample :
  CrossDomainPromotionExample
structuralAnalogyClinicalExample =
  mkBlockedExample
    "structural analogy does not imply clinical claim"
    structuralAnalogyClaim
    clinicalClaim
    clinicalEvidenceAuthorityBridgeReceipt
    missingClinicalEvidenceReason
    "clinical interpretation requires clinical evidence and governance receipts"

structuralAnalogyTradingExample :
  CrossDomainPromotionExample
structuralAnalogyTradingExample =
  mkBlockedExample
    "structural analogy does not imply trading claim"
    structuralAnalogyClaim
    tradingClaim
    tradingValidationBridgeReceipt
    missingTradingValidationReason
    "signal-like structure requires replay, slippage, risk, and governance receipts before trading promotion"

spatialPracticeInterpretationExample :
  CrossDomainPromotionExample
spatialPracticeInterpretationExample =
  record
    { exampleLabel =
        "Feng Shui-style spatial practice reading is interpretation-only"
    ; sourceClaimKind =
        spatialPracticeInterpretationClaim
    ; targetClaimKind =
        environmentalAuthorityClaim
    ; deniedAuthorityTargets =
        environmentalAuthorityClaim
        ∷ clinicalClaim
        ∷ spiritualAuthorityClaim
        ∷ legalAuthorityClaim
        ∷ empiricalFactClaim
        ∷ []
    ; requiredBridgeReceipt =
        governedSpatialPracticeValidationReceipt
    ; blockReason =
        missingGovernedSpatialPracticeValidationReason
    ; analogyOrStructureAccepted =
        true
    ; analogyOrStructureAcceptedIsTrue =
        refl
    ; explicitBridgeReceiptSupplied =
        false
    ; explicitBridgeReceiptSuppliedIsFalse =
        refl
    ; targetClaimPromoted =
        false
    ; targetClaimPromotedIsFalse =
        refl
    ; exampleNote =
        "culturally mediated spatial-practice interpretation is allowed as non-promoting meaning-making, but grants no environmental, clinical, spiritual, legal, or empirical authority without governed receipts and validation"
    }

canonicalCrossDomainPromotionExamples :
  List CrossDomainPromotionExample
canonicalCrossDomainPromotionExamples =
  mathematicalAnalogyEmpiricalExample
  ∷ evidenceGraphTerritoryExample
  ∷ vectorProximitySupportExample
  ∷ productCandidateAdmissibilityExample
  ∷ structuralAnalogyPoliticalExample
  ∷ structuralAnalogyEconomicExample
  ∷ structuralAnalogyClinicalExample
  ∷ structuralAnalogyTradingExample
  ∷ spatialPracticeInterpretationExample
  ∷ []

------------------------------------------------------------------------
-- Reusable core adapters.
--
-- These adapter receipts consume the shared cores without replacing the
-- local claim, bridge, example, or AuthorityGateCore adapter rows above.

authorityNonPromotionCoreAdapter :
  AuthorityNA.AuthorityNonPromotionBundle
authorityNonPromotionCoreAdapter =
  AuthorityNA.canonicalAuthorityNonPromotionBundle

authorityNonPromotionCoreAdapterIsCanonical :
  authorityNonPromotionCoreAdapter
  ≡
  AuthorityNA.canonicalAuthorityNonPromotionBundle
authorityNonPromotionCoreAdapterIsCanonical =
  refl

authorityNonPromotionCoreAdapterCanonicalKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    authorityNonPromotionCoreAdapter
    AuthorityNA.canonicalAuthorityKinds
authorityNonPromotionCoreAdapterCanonicalKindsFalse =
  AuthorityNA.proveAllAuthorityKindsFalse
    authorityNonPromotionCoreAdapter
    AuthorityNA.canonicalAuthorityKinds

crossDomainAdapterEmpiricalAuthorityFalse :
  AuthorityNA.empiricalAuthorityFlag authorityNonPromotionCoreAdapter
  ≡ false
crossDomainAdapterEmpiricalAuthorityFalse =
  AuthorityNA.bundleEmpiricalAuthorityIsFalse
    authorityNonPromotionCoreAdapter

crossDomainAdapterTradingAuthorityFalse :
  AuthorityNA.tradingAuthorityFlag authorityNonPromotionCoreAdapter
  ≡ false
crossDomainAdapterTradingAuthorityFalse =
  AuthorityNA.bundleTradingAuthorityIsFalse
    authorityNonPromotionCoreAdapter

crossDomainAdapterSupportAuthorityFalse :
  AuthorityNA.supportAuthorityFlag authorityNonPromotionCoreAdapter
  ≡ false
crossDomainAdapterSupportAuthorityFalse =
  AuthorityNA.bundleSupportAuthorityIsFalse
    authorityNonPromotionCoreAdapter

crossDomainAdapterAdmissibilityAuthorityFalse :
  AuthorityNA.admissibilityAuthorityFlag authorityNonPromotionCoreAdapter
  ≡ false
crossDomainAdapterAdmissibilityAuthorityFalse =
  AuthorityNA.bundleAdmissibilityAuthorityIsFalse
    authorityNonPromotionCoreAdapter

crossDomainAdapterAnyAuthorityPromotionFalse :
  AuthorityNA.promotesAnyAuthority authorityNonPromotionCoreAdapter
  ≡ false
crossDomainAdapterAnyAuthorityPromotionFalse =
  AuthorityNA.bundlePromotesAnyAuthorityIsFalse
    authorityNonPromotionCoreAdapter

bridgeRequirementCoreAdapter :
  BridgeReq.BridgeRequirementCoreReceipt
bridgeRequirementCoreAdapter =
  BridgeReq.canonicalBridgeRequirementCoreReceipt

bridgeRequirementCoreAdapterIsCanonical :
  bridgeRequirementCoreAdapter
  ≡
  BridgeReq.canonicalBridgeRequirementCoreReceipt
bridgeRequirementCoreAdapterIsCanonical =
  refl

bridgeRequirementCoreAdapterAuthorityPromotionFalse :
  BridgeReq.receiptAuthorityPromotion bridgeRequirementCoreAdapter
  ≡ false
bridgeRequirementCoreAdapterAuthorityPromotionFalse =
  BridgeReq.receiptAuthorityPromotionFalse
    bridgeRequirementCoreAdapter

bridgeRequirementCoreAdapterTransportMapAuthorityFalse :
  BridgeReq.receiptTransportMapAuthority bridgeRequirementCoreAdapter
  ≡ false
bridgeRequirementCoreAdapterTransportMapAuthorityFalse =
  BridgeReq.receiptTransportMapAuthorityFalse
    bridgeRequirementCoreAdapter

bridgeRequirementCoreAdapterBackgroundBridgeAuthorityFalse :
  BridgeReq.receiptBackgroundBridgeAuthority bridgeRequirementCoreAdapter
  ≡ false
bridgeRequirementCoreAdapterBackgroundBridgeAuthorityFalse =
  BridgeReq.receiptBackgroundBridgeAuthorityFalse
    bridgeRequirementCoreAdapter

bridgeRequirementCoreAdapterBridgeRequired :
  BridgeReq.statusRequiresBridge BridgeReq.bridgeRequired
  ≡ true
bridgeRequirementCoreAdapterBridgeRequired =
  refl

candidateOnlyCoreAdapter :
  CandidateOnly.CandidateOnlyRow
candidateOnlyCoreAdapter =
  CandidateOnly.canonicalBridgeCandidateOnlyRow

candidateOnlyCoreAdapterIsCanonical :
  candidateOnlyCoreAdapter
  ≡
  CandidateOnly.canonicalBridgeCandidateOnlyRow
candidateOnlyCoreAdapterIsCanonical =
  refl

candidateOnlyCoreAdapterReceipt :
  CandidateOnly.CandidateOnlyReceipt candidateOnlyCoreAdapter
candidateOnlyCoreAdapterReceipt =
  CandidateOnly.canonicalBridgeCandidateOnlyReceipt

candidateOnlyCoreAdapterCandidateOnlyTrue :
  CandidateOnly.candidateOnly candidateOnlyCoreAdapter
  ≡ true
candidateOnlyCoreAdapterCandidateOnlyTrue =
  CandidateOnly.candidateOnlyIsTrue
    candidateOnlyCoreAdapterReceipt

candidateOnlyCoreAdapterPromotedFalse :
  CandidateOnly.promoted candidateOnlyCoreAdapter
  ≡ false
candidateOnlyCoreAdapterPromotedFalse =
  CandidateOnly.candidatePromotedIsFalse
    candidateOnlyCoreAdapterReceipt

candidateOnlyCoreAdapterSupportAuthorityFalse :
  CandidateOnly.carriesSupportAuthority candidateOnlyCoreAdapter
  ≡ false
candidateOnlyCoreAdapterSupportAuthorityFalse =
  CandidateOnly.candidateNoSupportAuthority
    candidateOnlyCoreAdapterReceipt

candidateOnlyCoreAdapterAdmissibilityAuthorityFalse :
  CandidateOnly.carriesAdmissibilityAuthority candidateOnlyCoreAdapter
  ≡ false
candidateOnlyCoreAdapterAdmissibilityAuthorityFalse =
  CandidateOnly.candidateNoAdmissibilityAuthority
    candidateOnlyCoreAdapterReceipt

candidateOnlyCoreAdapterTradingAuthorityFalse :
  CandidateOnly.carriesTradingAuthority candidateOnlyCoreAdapter
  ≡ false
candidateOnlyCoreAdapterTradingAuthorityFalse =
  CandidateOnly.candidateNoTradingAuthority
    candidateOnlyCoreAdapterReceipt

------------------------------------------------------------------------
-- Canonical fail-closed receipt.

record CrossDomainClaimPromotionBoundary : Set where
  field
    receiptLabel : String
    blockedTargetClaims : List ClaimKind
    requiredBridgeReceiptKinds : List BridgeReceiptKind
    examples : List CrossDomainPromotionExample
    authorityGateAdapterRows : List CrossDomainAuthorityGateAdapterRow
    authorityGateAdapterRowsAreCanonical :
      authorityGateAdapterRows ≡ canonicalCrossDomainAuthorityGateAdapterRows

    mathematicalAnalogyImpliesEmpiricalFact : Bool
    mathematicalAnalogyImpliesEmpiricalFactIsFalse :
      mathematicalAnalogyImpliesEmpiricalFact ≡ false

    evidenceGraphStructureImpliesTerritoryTruth : Bool
    evidenceGraphStructureImpliesTerritoryTruthIsFalse :
      evidenceGraphStructureImpliesTerritoryTruth ≡ false

    vectorProximityProductCandidatesImplySupport : Bool
    vectorProximityProductCandidatesImplySupportIsFalse :
      vectorProximityProductCandidatesImplySupport ≡ false

    vectorProximityProductCandidatesImplyAdmissibility : Bool
    vectorProximityProductCandidatesImplyAdmissibilityIsFalse :
      vectorProximityProductCandidatesImplyAdmissibility ≡ false

    empiricalClaimPromoted : Bool
    empiricalClaimPromotedIsFalse :
      empiricalClaimPromoted ≡ false

    politicalClaimPromoted : Bool
    politicalClaimPromotedIsFalse :
      politicalClaimPromoted ≡ false

    economicClaimPromoted : Bool
    economicClaimPromotedIsFalse :
      economicClaimPromoted ≡ false

    clinicalClaimPromoted : Bool
    clinicalClaimPromotedIsFalse :
      clinicalClaimPromoted ≡ false

    environmentalAuthorityPromoted : Bool
    environmentalAuthorityPromotedIsFalse :
      environmentalAuthorityPromoted ≡ false

    spiritualAuthorityPromoted : Bool
    spiritualAuthorityPromotedIsFalse :
      spiritualAuthorityPromoted ≡ false

    legalAuthorityPromoted : Bool
    legalAuthorityPromotedIsFalse :
      legalAuthorityPromoted ≡ false

    tradingClaimPromoted : Bool
    tradingClaimPromotedIsFalse :
      tradingClaimPromoted ≡ false

    supportClaimPromoted : Bool
    supportClaimPromotedIsFalse :
      supportClaimPromoted ≡ false

    admissibilityClaimPromoted : Bool
    admissibilityClaimPromotedIsFalse :
      admissibilityClaimPromoted ≡ false

    anyCrossDomainPromotionFlag : Bool
    anyCrossDomainPromotionFlagIsFalse :
      anyCrossDomainPromotionFlag ≡ false

    explicitBridgeReceiptsRequired : Bool
    explicitBridgeReceiptsRequiredIsTrue :
      explicitBridgeReceiptsRequired ≡ true

    promotionWithoutBridgeBlocked : Bool
    promotionWithoutBridgeBlockedIsTrue :
      promotionWithoutBridgeBlocked ≡ true

    validationCommand : String
    boundaryNotes : List String

open CrossDomainClaimPromotionBoundary public

canonicalCrossDomainClaimPromotionBoundary :
  CrossDomainClaimPromotionBoundary
canonicalCrossDomainClaimPromotionBoundary =
  record
    { receiptLabel =
        "cross-domain claim promotion boundary"
    ; blockedTargetClaims =
        canonicalBlockedTargetClaims
    ; requiredBridgeReceiptKinds =
        canonicalRequiredBridgeReceiptKinds
    ; examples =
        canonicalCrossDomainPromotionExamples
    ; authorityGateAdapterRows =
        canonicalCrossDomainAuthorityGateAdapterRows
    ; authorityGateAdapterRowsAreCanonical =
        refl
    ; mathematicalAnalogyImpliesEmpiricalFact =
        false
    ; mathematicalAnalogyImpliesEmpiricalFactIsFalse =
        refl
    ; evidenceGraphStructureImpliesTerritoryTruth =
        false
    ; evidenceGraphStructureImpliesTerritoryTruthIsFalse =
        refl
    ; vectorProximityProductCandidatesImplySupport =
        false
    ; vectorProximityProductCandidatesImplySupportIsFalse =
        refl
    ; vectorProximityProductCandidatesImplyAdmissibility =
        false
    ; vectorProximityProductCandidatesImplyAdmissibilityIsFalse =
        refl
    ; empiricalClaimPromoted =
        false
    ; empiricalClaimPromotedIsFalse =
        refl
    ; politicalClaimPromoted =
        false
    ; politicalClaimPromotedIsFalse =
        refl
    ; economicClaimPromoted =
        false
    ; economicClaimPromotedIsFalse =
        refl
    ; clinicalClaimPromoted =
        false
    ; clinicalClaimPromotedIsFalse =
        refl
    ; environmentalAuthorityPromoted =
        false
    ; environmentalAuthorityPromotedIsFalse =
        refl
    ; spiritualAuthorityPromoted =
        false
    ; spiritualAuthorityPromotedIsFalse =
        refl
    ; legalAuthorityPromoted =
        false
    ; legalAuthorityPromotedIsFalse =
        refl
    ; tradingClaimPromoted =
        false
    ; tradingClaimPromotedIsFalse =
        refl
    ; supportClaimPromoted =
        false
    ; supportClaimPromotedIsFalse =
        refl
    ; admissibilityClaimPromoted =
        false
    ; admissibilityClaimPromotedIsFalse =
        refl
    ; anyCrossDomainPromotionFlag =
        false
    ; anyCrossDomainPromotionFlagIsFalse =
        refl
    ; explicitBridgeReceiptsRequired =
        true
    ; explicitBridgeReceiptsRequiredIsTrue =
        refl
    ; promotionWithoutBridgeBlocked =
        true
    ; promotionWithoutBridgeBlockedIsTrue =
        refl
    ; validationCommand =
        "agda -i . DASHI/Promotion/CrossDomainClaimPromotionBoundary.agda"
    ; boundaryNotes =
        "math and structure may organize hypotheses but do not assert territory truth"
        ∷ "empirical, political, economic, clinical, and trading claims require explicit bridge receipts"
        ∷ "culturally mediated spatial-practice readings are interpretation-only unless governed validation receipts are supplied"
        ∷ "support and admissibility claims require their own support/admissibility bridge receipts"
        ∷ "canonical surface keeps all promotion flags false"
        ∷ []
    }

------------------------------------------------------------------------
-- Projection lemmas for the canonical receipt.

canonicalBlockedTargetClaimCountIs10 :
  listCount
    (blockedTargetClaims canonicalCrossDomainClaimPromotionBoundary)
  ≡ suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
canonicalBlockedTargetClaimCountIs10 = refl

canonicalRequiredBridgeReceiptKindCountIs10 :
  listCount
    (requiredBridgeReceiptKinds canonicalCrossDomainClaimPromotionBoundary)
  ≡ suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
canonicalRequiredBridgeReceiptKindCountIs10 = refl

canonicalCrossDomainExampleCountIs9 :
  listCount
    (examples canonicalCrossDomainClaimPromotionBoundary)
  ≡ suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
canonicalCrossDomainExampleCountIs9 = refl

canonicalAuthorityGateAdapterRowsAreCanonical :
  authorityGateAdapterRows canonicalCrossDomainClaimPromotionBoundary
  ≡ canonicalCrossDomainAuthorityGateAdapterRows
canonicalAuthorityGateAdapterRowsAreCanonical = refl

canonicalMathematicalAnalogyDoesNotImplyEmpiricalFact :
  mathematicalAnalogyImpliesEmpiricalFact
    canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalMathematicalAnalogyDoesNotImplyEmpiricalFact = refl

canonicalEvidenceGraphStructureDoesNotImplyTerritoryTruth :
  evidenceGraphStructureImpliesTerritoryTruth
    canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalEvidenceGraphStructureDoesNotImplyTerritoryTruth = refl

canonicalVectorProximityProductCandidatesDoNotImplySupport :
  vectorProximityProductCandidatesImplySupport
    canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalVectorProximityProductCandidatesDoNotImplySupport = refl

canonicalVectorProximityProductCandidatesDoNotImplyAdmissibility :
  vectorProximityProductCandidatesImplyAdmissibility
    canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalVectorProximityProductCandidatesDoNotImplyAdmissibility = refl

canonicalEmpiricalPromotionFlagIsFalse :
  empiricalClaimPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalEmpiricalPromotionFlagIsFalse = refl

canonicalPoliticalPromotionFlagIsFalse :
  politicalClaimPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalPoliticalPromotionFlagIsFalse = refl

canonicalEconomicPromotionFlagIsFalse :
  economicClaimPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalEconomicPromotionFlagIsFalse = refl

canonicalClinicalPromotionFlagIsFalse :
  clinicalClaimPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalClinicalPromotionFlagIsFalse = refl

canonicalEnvironmentalAuthorityPromotionFlagIsFalse :
  environmentalAuthorityPromoted
    canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalEnvironmentalAuthorityPromotionFlagIsFalse = refl

canonicalSpiritualAuthorityPromotionFlagIsFalse :
  spiritualAuthorityPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalSpiritualAuthorityPromotionFlagIsFalse = refl

canonicalLegalAuthorityPromotionFlagIsFalse :
  legalAuthorityPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalLegalAuthorityPromotionFlagIsFalse = refl

canonicalTradingPromotionFlagIsFalse :
  tradingClaimPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalTradingPromotionFlagIsFalse = refl

canonicalSupportPromotionFlagIsFalse :
  supportClaimPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalSupportPromotionFlagIsFalse = refl

canonicalAdmissibilityPromotionFlagIsFalse :
  admissibilityClaimPromoted canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalAdmissibilityPromotionFlagIsFalse = refl

canonicalAnyCrossDomainPromotionFlagIsFalse :
  anyCrossDomainPromotionFlag canonicalCrossDomainClaimPromotionBoundary
  ≡ false
canonicalAnyCrossDomainPromotionFlagIsFalse = refl

canonicalExplicitBridgeReceiptsRequired :
  explicitBridgeReceiptsRequired
    canonicalCrossDomainClaimPromotionBoundary
  ≡ true
canonicalExplicitBridgeReceiptsRequired = refl

canonicalPromotionWithoutBridgeBlocked :
  promotionWithoutBridgeBlocked
    canonicalCrossDomainClaimPromotionBoundary
  ≡ true
canonicalPromotionWithoutBridgeBlocked = refl

canonicalMathematicalExampleDoesNotPromote :
  targetClaimPromoted mathematicalAnalogyEmpiricalExample ≡ false
canonicalMathematicalExampleDoesNotPromote = refl

canonicalEvidenceGraphExampleDoesNotPromote :
  targetClaimPromoted evidenceGraphTerritoryExample ≡ false
canonicalEvidenceGraphExampleDoesNotPromote = refl

canonicalVectorSupportExampleDoesNotPromote :
  targetClaimPromoted vectorProximitySupportExample ≡ false
canonicalVectorSupportExampleDoesNotPromote = refl

canonicalProductAdmissibilityExampleDoesNotPromote :
  targetClaimPromoted productCandidateAdmissibilityExample ≡ false
canonicalProductAdmissibilityExampleDoesNotPromote = refl

canonicalSpatialPracticeInterpretationExampleDoesNotPromote :
  targetClaimPromoted spatialPracticeInterpretationExample ≡ false
canonicalSpatialPracticeInterpretationExampleDoesNotPromote = refl

canonicalSpatialPracticeDeniedAuthorityTargetCountIs5 :
  listCount (deniedAuthorityTargets spatialPracticeInterpretationExample)
  ≡ suc (suc (suc (suc (suc zero))))
canonicalSpatialPracticeDeniedAuthorityTargetCountIs5 = refl
