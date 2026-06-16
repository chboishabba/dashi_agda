module DASHI.Promotion.CrossDomainClaimPromotionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
import DASHI.Promotion.AuthorityGateCore as AuthorityGateCore
import DASHI.Core.AdapterCanonicalityCore as AdapterCanon
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.BridgeRequirementCore as BridgeReq
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.FormalLensQualificationCore as FormalLens
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary
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
-- Authority-boundary adapter.
--
-- The cross-domain boundary keeps its local claim vocabulary, but the
-- blocked-authority and boundary-promoted plumbing now projects through the
-- reusable authority-boundary core so the closed false surface is shared.

record CrossDomainAuthorityBoundaryAdapterRow : Set where
  constructor crossDomainAuthorityBoundaryAdapterRow
  field
    authorityBoundaryLabel :
      String
    authorityBoundaryReceipt :
      AuthorityBoundary.AuthorityBoundaryReceipt
    authorityBoundaryReceiptIsCanonical :
      authorityBoundaryReceipt ≡
      AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    authorityBoundaryBlockedClaimKinds :
      List AuthorityBoundary.AuthorityBoundaryClaimKind
    authorityBoundaryBlockedClaimKindsAreCanonical :
      authorityBoundaryBlockedClaimKinds ≡
      AuthorityBoundary.canonicalBlockedAuthorityClaims
    authorityBoundaryBlockedKinds :
      List AuthorityNA.AuthorityKind
    authorityBoundaryBlockedKindsAreCanonical :
      authorityBoundaryBlockedKinds ≡
      AuthorityBoundary.canonicalBlockedAuthorityKinds
    authorityBoundaryCandidateOnly :
      Bool
    authorityBoundaryCandidateOnlyIsTrue :
      authorityBoundaryCandidateOnly ≡ true
    authorityBoundaryCandidatePromoted :
      Bool
    authorityBoundaryCandidatePromotedIsFalse :
      authorityBoundaryCandidatePromoted ≡ false
    authorityBoundaryBundlePromotesAnyAuthority :
      Bool
    authorityBoundaryBundlePromotesAnyAuthorityIsFalse :
      authorityBoundaryBundlePromotesAnyAuthority ≡ false
    authorityBoundaryPromoted :
      Bool
    authorityBoundaryPromotedIsFalse :
      authorityBoundaryPromoted ≡ false
    authorityBoundaryBlockedKindsFalse :
      AuthorityNA.AllAuthorityKindsFalse
        (AuthorityBoundary.receiptAuthorityBundle
          authorityBoundaryReceipt)
        authorityBoundaryBlockedKinds
    authorityBoundaryBlockedKindsCount :
      Nat
    authorityBoundaryBlockedKindsCountIsCanonical :
      authorityBoundaryBlockedKindsCount ≡
      AuthorityBoundary.canonicalBlockedAuthorityKindCount
    authorityBoundaryAdapterNote :
      String

open CrossDomainAuthorityBoundaryAdapterRow public

canonicalCrossDomainAuthorityBoundaryAdapterRow :
  CrossDomainAuthorityBoundaryAdapterRow
canonicalCrossDomainAuthorityBoundaryAdapterRow =
  record
    { authorityBoundaryLabel =
        "cross-domain authority boundary adapter"
    ; authorityBoundaryReceipt =
        AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    ; authorityBoundaryReceiptIsCanonical =
        refl
    ; authorityBoundaryBlockedClaimKinds =
        AuthorityBoundary.canonicalBlockedAuthorityClaims
    ; authorityBoundaryBlockedClaimKindsAreCanonical =
        refl
    ; authorityBoundaryBlockedKinds =
        AuthorityBoundary.canonicalBlockedAuthorityKinds
    ; authorityBoundaryBlockedKindsAreCanonical =
        refl
    ; authorityBoundaryCandidateOnly =
        CandidateOnly.candidateOnly
          (AuthorityBoundary.receiptCandidateRow
            AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt)
    ; authorityBoundaryCandidateOnlyIsTrue =
        AuthorityBoundary.authorityBoundaryCandidateOnlyIsTrue
          AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    ; authorityBoundaryCandidatePromoted =
        CandidateOnly.promoted
          (AuthorityBoundary.receiptCandidateRow
            AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt)
    ; authorityBoundaryCandidatePromotedIsFalse =
        AuthorityBoundary.authorityBoundaryCandidatePromotedIsFalse
          AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    ; authorityBoundaryBundlePromotesAnyAuthority =
        AuthorityNA.promotesAnyAuthority
          (AuthorityBoundary.receiptAuthorityBundle
            AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt)
    ; authorityBoundaryBundlePromotesAnyAuthorityIsFalse =
        AuthorityBoundary.authorityBoundaryBundlePromotesAnyAuthorityIsFalse
          AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    ; authorityBoundaryPromoted =
        AuthorityBoundary.receiptBoundaryPromoted
          AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    ; authorityBoundaryPromotedIsFalse =
        AuthorityBoundary.receiptBoundaryPromotedIsFalse
          AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    ; authorityBoundaryBlockedKindsFalse =
        AuthorityBoundary.authorityBoundaryBlockedAuthorityKindsFalse
          AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    ; authorityBoundaryBlockedKindsCount =
        AuthorityBoundary.canonicalBlockedAuthorityKindCount
    ; authorityBoundaryBlockedKindsCountIsCanonical =
        refl
    ; authorityBoundaryAdapterNote =
        "cross-domain claim promotion keeps the generic authority-boundary core blocked and candidate-only"
    }

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
-- Formal-lens qualification adapter.
--
-- Cross-domain vocabulary may be read through formal lenses, but the
-- reading is candidate-only and does not supply claim truth, support,
-- admissibility, bridge authority, external authority, theorem authority,
-- Clay authority, or promotion.

data CrossDomainFormalLensReading : Set where
  crossDomainSymbolicRationalReading :
    CrossDomainFormalLensReading
  crossDomainCategoryReading :
    CrossDomainFormalLensReading
  crossDomainBridgeReading :
    CrossDomainFormalLensReading
  crossDomainFunctionalReading :
    CrossDomainFormalLensReading

crossDomainFormalLens :
  CrossDomainFormalLensReading →
  FormalLens.FormalLens
crossDomainFormalLens crossDomainSymbolicRationalReading =
  FormalLens.SymbolicRational
crossDomainFormalLens crossDomainCategoryReading =
  FormalLens.Category
crossDomainFormalLens crossDomainBridgeReading =
  FormalLens.NamedFormalLens "Bridge"
crossDomainFormalLens crossDomainFunctionalReading =
  FormalLens.Functional

record CrossDomainFormalLensQualificationAdapterRow : Set where
  constructor crossDomainFormalLensQualificationAdapterRow
  field
    formalLensReading :
      CrossDomainFormalLensReading
    formalLensConstructor :
      FormalLens.FormalLens
    formalLensConstructorComputes :
      crossDomainFormalLens formalLensReading
      ≡
      formalLensConstructor
    formalLensQualificationSurface :
      FormalLens.FormalLensQualificationSurface
    formalLensQualificationReceipt :
      FormalLens.FormalLensQualificationReceipt
        formalLensQualificationSurface
    formalLensCandidateOnly :
      Bool
    formalLensCandidateOnlyIsTrue :
      formalLensCandidateOnly ≡ true
    formalLensPromoted :
      Bool
    formalLensPromotedIsFalse :
      formalLensPromoted ≡ false
    formalLensTruthAuthority :
      Bool
    formalLensTruthAuthorityIsFalse :
      formalLensTruthAuthority ≡ false
    formalLensSupportAuthority :
      Bool
    formalLensSupportAuthorityIsFalse :
      formalLensSupportAuthority ≡ false
    formalLensAdmissibilityAuthority :
      Bool
    formalLensAdmissibilityAuthorityIsFalse :
      formalLensAdmissibilityAuthority ≡ false
    formalLensAnalyticAuthority :
      Bool
    formalLensAnalyticAuthorityIsFalse :
      formalLensAnalyticAuthority ≡ false
    formalLensEmpiricalAuthority :
      Bool
    formalLensEmpiricalAuthorityIsFalse :
      formalLensEmpiricalAuthority ≡ false
    formalLensClinicalAuthority :
      Bool
    formalLensClinicalAuthorityIsFalse :
      formalLensClinicalAuthority ≡ false
    formalLensTheoremAuthority :
      Bool
    formalLensTheoremAuthorityIsFalse :
      formalLensTheoremAuthority ≡ false
    formalLensClayAuthority :
      Bool
    formalLensClayAuthorityIsFalse :
      formalLensClayAuthority ≡ false
    formalLensExternalAuthority :
      Bool
    formalLensExternalAuthorityIsFalse :
      formalLensExternalAuthority ≡ false
    formalLensGovernanceAuthority :
      Bool
    formalLensGovernanceAuthorityIsFalse :
      formalLensGovernanceAuthority ≡ false
    formalLensPromotionAuthority :
      Bool
    formalLensPromotionAuthorityIsFalse :
      formalLensPromotionAuthority ≡ false
    formalLensBridgeAuthority :
      Bool
    formalLensBridgeAuthorityIsFalse :
      formalLensBridgeAuthority ≡ false
    formalLensTransportMapAuthority :
      Bool
    formalLensTransportMapAuthorityIsFalse :
      formalLensTransportMapAuthority ≡ false
    formalLensBackgroundBridgeAuthority :
      Bool
    formalLensBackgroundBridgeAuthorityIsFalse :
      formalLensBackgroundBridgeAuthority ≡ false
    formalLensAuthorityBundlePromotion :
      Bool
    formalLensAuthorityBundlePromotionIsFalse :
      formalLensAuthorityBundlePromotion ≡ false
    formalLensReadingNote :
      String

open CrossDomainFormalLensQualificationAdapterRow public

mkCrossDomainFormalLensQualificationSurface :
  CrossDomainFormalLensReading →
  String →
  FormalLens.FormalLensQualificationSurface
mkCrossDomainFormalLensQualificationSurface reading note =
  FormalLens.mkFormalLensQualificationSurface
    "cross-domain claim formal-lens qualification"
    "DASHI.Promotion.CrossDomainClaimPromotionBoundary"
    "CrossDomainFormalLensQualificationAdapterRow"
    (crossDomainFormalLens reading)
    FormalLens.Information
    FormalLens.adapterConsumerRole
    FormalLens.canonicalRequiredThresholdRow
    FormalLens.canonicalRequiredThresholdRowReceipt
    FormalLens.explicitBridgeResidualBoundary
    FormalLens.genericFormalLensCandidateRow
    FormalLens.genericFormalLensCandidateReceipt
    FormalLens.genericFormalLensBridgeRow
    FormalLens.genericFormalLensBridgeReceipt
    note
    "formal-lens qualification is candidate-only; domain authority, bridge authority, theorem authority, external acceptance, Clay authority, and promotion remain absent"

mkCrossDomainFormalLensQualificationReceipt :
  (reading : CrossDomainFormalLensReading) →
  (note : String) →
  FormalLens.FormalLensQualificationReceipt
    (mkCrossDomainFormalLensQualificationSurface reading note)
mkCrossDomainFormalLensQualificationReceipt reading note =
  FormalLens.mkFormalLensQualificationReceipt
    (mkCrossDomainFormalLensQualificationSurface reading note)
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

mkCrossDomainFormalLensQualificationAdapterRow :
  CrossDomainFormalLensReading →
  String →
  CrossDomainFormalLensQualificationAdapterRow
mkCrossDomainFormalLensQualificationAdapterRow reading note =
  record
    { formalLensReading =
        reading
    ; formalLensConstructor =
        crossDomainFormalLens reading
    ; formalLensConstructorComputes =
        refl
    ; formalLensQualificationSurface =
        mkCrossDomainFormalLensQualificationSurface reading note
    ; formalLensQualificationReceipt =
        mkCrossDomainFormalLensQualificationReceipt
          reading
          note
    ; formalLensCandidateOnly =
        FormalLens.qualificationCandidateOnly
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensCandidateOnlyIsTrue =
        FormalLens.qualificationIsCandidateOnly
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensPromoted =
        FormalLens.qualificationPromoted
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensPromotedIsFalse =
        FormalLens.qualificationPromotedFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensTruthAuthority =
        AuthorityNA.truthAuthorityFlag
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensTruthAuthorityIsFalse =
        AuthorityNA.bundleTruthAuthorityIsFalse
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensSupportAuthority =
        AuthorityNA.supportAuthorityFlag
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensSupportAuthorityIsFalse =
        AuthorityNA.bundleSupportAuthorityIsFalse
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensAdmissibilityAuthority =
        AuthorityNA.admissibilityAuthorityFlag
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensAdmissibilityAuthorityIsFalse =
        AuthorityNA.bundleAdmissibilityAuthorityIsFalse
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensAnalyticAuthority =
        FormalLens.analyticAuthority
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensAnalyticAuthorityIsFalse =
        FormalLens.qualificationAnalyticAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensEmpiricalAuthority =
        FormalLens.empiricalAuthority
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensEmpiricalAuthorityIsFalse =
        FormalLens.qualificationEmpiricalAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensClinicalAuthority =
        FormalLens.clinicalAuthority
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensClinicalAuthorityIsFalse =
        FormalLens.qualificationClinicalAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensTheoremAuthority =
        FormalLens.theoremAuthority
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensTheoremAuthorityIsFalse =
        FormalLens.qualificationTheoremAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensClayAuthority =
        AuthorityNA.clayAuthorityFlag
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensClayAuthorityIsFalse =
        AuthorityNA.bundleClayAuthorityIsFalse
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensExternalAuthority =
        FormalLens.externalAuthority
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensExternalAuthorityIsFalse =
        FormalLens.qualificationExternalAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensGovernanceAuthority =
        FormalLens.governanceAuthority
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensGovernanceAuthorityIsFalse =
        FormalLens.qualificationGovernanceAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensPromotionAuthority =
        FormalLens.promotionAuthority
          (mkCrossDomainFormalLensQualificationSurface reading note)
    ; formalLensPromotionAuthorityIsFalse =
        FormalLens.qualificationPromotionAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensBridgeAuthority =
        BridgeReq.rowAuthorityPromotion
          (FormalLens.bridgeRow
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensBridgeAuthorityIsFalse =
        FormalLens.receiptBridgeAuthorityPromotionFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensTransportMapAuthority =
        BridgeReq.rowTransportMapAuthority
          (FormalLens.bridgeRow
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensTransportMapAuthorityIsFalse =
        FormalLens.receiptBridgeTransportMapAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensBackgroundBridgeAuthority =
        BridgeReq.rowBackgroundBridgeAuthority
          (FormalLens.bridgeRow
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensBackgroundBridgeAuthorityIsFalse =
        FormalLens.receiptBridgeBackgroundAuthorityFalse
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensAuthorityBundlePromotion =
        AuthorityNA.promotesAnyAuthority
          (FormalLens.authorityBundle
            (mkCrossDomainFormalLensQualificationSurface reading note))
    ; formalLensAuthorityBundlePromotionIsFalse =
        FormalLens.receiptAuthorityBundleNonPromoting
          (mkCrossDomainFormalLensQualificationReceipt
            reading
            note)
    ; formalLensReadingNote =
        note
    }

crossDomainSymbolicRationalFormalLensQualificationRow :
  CrossDomainFormalLensQualificationAdapterRow
crossDomainSymbolicRationalFormalLensQualificationRow =
  mkCrossDomainFormalLensQualificationAdapterRow
    crossDomainSymbolicRationalReading
    "scores, proximity, ratios, and symbolic thresholds are read only as SymbolicRational formal-lens candidates."

crossDomainCategoryFormalLensQualificationRow :
  CrossDomainFormalLensQualificationAdapterRow
crossDomainCategoryFormalLensQualificationRow =
  mkCrossDomainFormalLensQualificationAdapterRow
    crossDomainCategoryReading
    "claim kinds, bridge receipt kinds, examples, and blocked-target lists are read only as Category formal-lens candidates."

crossDomainBridgeFormalLensQualificationRow :
  CrossDomainFormalLensQualificationAdapterRow
crossDomainBridgeFormalLensQualificationRow =
  mkCrossDomainFormalLensQualificationAdapterRow
    crossDomainBridgeReading
    "required bridge vocabulary is read only as a named Bridge formal-lens candidate, not bridge authority."

crossDomainFunctionalFormalLensQualificationRow :
  CrossDomainFormalLensQualificationAdapterRow
crossDomainFunctionalFormalLensQualificationRow =
  mkCrossDomainFormalLensQualificationAdapterRow
    crossDomainFunctionalReading
    "promotion gates and boolean projections are read only as Functional formal-lens candidates."

canonicalCrossDomainFormalLensQualificationRows :
  List CrossDomainFormalLensQualificationAdapterRow
canonicalCrossDomainFormalLensQualificationRows =
  crossDomainSymbolicRationalFormalLensQualificationRow
  ∷ crossDomainCategoryFormalLensQualificationRow
  ∷ crossDomainBridgeFormalLensQualificationRow
  ∷ crossDomainFunctionalFormalLensQualificationRow
  ∷ []

crossDomainFormalLensAdapterCanonicality :
  AdapterCanon.AdapterCanonicalityReceipt
    (List CrossDomainFormalLensQualificationAdapterRow)
    canonicalCrossDomainFormalLensQualificationRows
crossDomainFormalLensAdapterCanonicality =
  AdapterCanon.mkCanonicalAdapterReceipt
    "cross-domain formal-lens qualification adapter"
    "DASHI.Promotion.CrossDomainClaimPromotionBoundary"
    "canonicalCrossDomainFormalLensQualificationRows"
    (AdapterCanon.namedAdapterKind "formal-lens-qualification")
    canonicalCrossDomainFormalLensQualificationRows

crossDomainFormalLensAdapterIsCanonical :
  AdapterCanon.adapter crossDomainFormalLensAdapterCanonicality
  ≡
  canonicalCrossDomainFormalLensQualificationRows
crossDomainFormalLensAdapterIsCanonical =
  AdapterCanon.adapterCanonical
    crossDomainFormalLensAdapterCanonicality

crossDomainFormalLensAdapterPromotesAuthorityFalse :
  AdapterCanon.adapterPromotesAuthority
    crossDomainFormalLensAdapterCanonicality
  ≡ false
crossDomainFormalLensAdapterPromotesAuthorityFalse =
  AdapterCanon.adapterAuthorityPromotionFalse
    crossDomainFormalLensAdapterCanonicality

crossDomainSymbolicRationalFormalLensCandidateOnly :
  formalLensCandidateOnly
    crossDomainSymbolicRationalFormalLensQualificationRow
  ≡ true
crossDomainSymbolicRationalFormalLensCandidateOnly =
  formalLensCandidateOnlyIsTrue
    crossDomainSymbolicRationalFormalLensQualificationRow

crossDomainCategoryFormalLensCandidateOnly :
  formalLensCandidateOnly
    crossDomainCategoryFormalLensQualificationRow
  ≡ true
crossDomainCategoryFormalLensCandidateOnly =
  formalLensCandidateOnlyIsTrue
    crossDomainCategoryFormalLensQualificationRow

crossDomainBridgeFormalLensBridgeAuthorityFalse :
  formalLensBridgeAuthority
    crossDomainBridgeFormalLensQualificationRow
  ≡ false
crossDomainBridgeFormalLensBridgeAuthorityFalse =
  formalLensBridgeAuthorityIsFalse
    crossDomainBridgeFormalLensQualificationRow

crossDomainFunctionalFormalLensPromotionAuthorityFalse :
  formalLensPromotionAuthority
    crossDomainFunctionalFormalLensQualificationRow
  ≡ false
crossDomainFunctionalFormalLensPromotionAuthorityFalse =
  formalLensPromotionAuthorityIsFalse
    crossDomainFunctionalFormalLensQualificationRow

------------------------------------------------------------------------
-- Canonical fail-closed receipt.

record CrossDomainClaimPromotionBoundary : Set where
  field
    receiptLabel : String
    authorityBoundaryAdapterRow :
      CrossDomainAuthorityBoundaryAdapterRow
    authorityBoundaryAdapterRowIsCanonical :
      authorityBoundaryAdapterRow ≡
      canonicalCrossDomainAuthorityBoundaryAdapterRow
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
    ; authorityBoundaryAdapterRow =
        canonicalCrossDomainAuthorityBoundaryAdapterRow
    ; authorityBoundaryAdapterRowIsCanonical =
        refl
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

canonicalAuthorityBoundaryAdapterRowIsCanonical :
  authorityBoundaryAdapterRow
    canonicalCrossDomainClaimPromotionBoundary
  ≡ canonicalCrossDomainAuthorityBoundaryAdapterRow
canonicalAuthorityBoundaryAdapterRowIsCanonical = refl

canonicalAuthorityBoundaryReceiptIsCanonical :
  authorityBoundaryReceipt
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)
  ≡
  AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
canonicalAuthorityBoundaryReceiptIsCanonical = refl

canonicalAuthorityBoundaryBlockedClaimKindsAreCanonical :
  authorityBoundaryBlockedClaimKinds
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)
  ≡ AuthorityBoundary.canonicalBlockedAuthorityClaims
canonicalAuthorityBoundaryBlockedClaimKindsAreCanonical = refl

canonicalAuthorityBoundaryBlockedKindsAreCanonical :
  authorityBoundaryBlockedKinds
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)
  ≡ AuthorityBoundary.canonicalBlockedAuthorityKinds
canonicalAuthorityBoundaryBlockedKindsAreCanonical = refl

canonicalAuthorityBoundaryBlockedKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    (AuthorityBoundary.receiptAuthorityBundle
      (authorityBoundaryReceipt
        (authorityBoundaryAdapterRow
          canonicalCrossDomainClaimPromotionBoundary)))
    (authorityBoundaryBlockedKinds
      (authorityBoundaryAdapterRow
        canonicalCrossDomainClaimPromotionBoundary))
canonicalAuthorityBoundaryBlockedKindsFalse =
  authorityBoundaryBlockedKindsFalse
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)

canonicalAuthorityBoundaryPromotedIsFalse :
  authorityBoundaryPromoted
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)
  ≡ false
canonicalAuthorityBoundaryPromotedIsFalse = refl

canonicalAuthorityBoundaryCandidateOnlyIsTrue :
  authorityBoundaryCandidateOnly
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)
  ≡ true
canonicalAuthorityBoundaryCandidateOnlyIsTrue = refl

canonicalAuthorityBoundaryCandidatePromotedIsFalse :
  authorityBoundaryCandidatePromoted
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)
  ≡ false
canonicalAuthorityBoundaryCandidatePromotedIsFalse = refl

canonicalAuthorityBoundaryBundlePromotesAnyAuthorityIsFalse :
  authorityBoundaryBundlePromotesAnyAuthority
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)
  ≡ false
canonicalAuthorityBoundaryBundlePromotesAnyAuthorityIsFalse = refl

canonicalAuthorityBoundaryBlockedKindsCountIsCanonical :
  authorityBoundaryBlockedKindsCount
    (authorityBoundaryAdapterRow
      canonicalCrossDomainClaimPromotionBoundary)
  ≡ AuthorityBoundary.canonicalBlockedAuthorityKindCount
canonicalAuthorityBoundaryBlockedKindsCountIsCanonical = refl

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
