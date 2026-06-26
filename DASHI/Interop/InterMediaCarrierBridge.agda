module DASHI.Interop.InterMediaCarrierBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.BridgeRequirementCore as BridgeReq
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.EmptyPromotionCore as EmptyPromotion
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Generic inter-media bridge.
--
-- A row in this module records that one carrier medium can be read through
-- another medium as an interpretive adapter.  The adapter is candidate-only:
-- it does not promote truth, support, admissibility, clinical authority,
-- metaphysical authority, or Clay/physics authority.

data InterMediaBridgeStatus : Set where
  interMediaBridge_candidateOnly :
    InterMediaBridgeStatus

data MediaKind : Set where
  spatialMedium :
    MediaKind

  movingBodyMedium :
    MediaKind

  attentionalMedium :
    MediaKind

  relationalMedium :
    MediaKind

  textualMedium :
    MediaKind

  namedMedium :
    String →
    MediaKind

canonicalMediaKinds : List MediaKind
canonicalMediaKinds =
  spatialMedium
  ∷ movingBodyMedium
  ∷ attentionalMedium
  ∷ relationalMedium
  ∷ []

data CarrierKind : Set where
  roomCarrier :
    CarrierKind

  landscapeCarrier :
    CarrierKind

  thresholdCarrier :
    CarrierKind

  bodyCarrier :
    CarrierKind

  breathCarrier :
    CarrierKind

  postureCarrier :
    CarrierKind

  forceCarrier :
    CarrierKind

  movementCarrier :
    CarrierKind

  attentionCarrier :
    CarrierKind

  perceptionCarrier :
    CarrierKind

  affectCarrier :
    CarrierKind

  memoryCarrier :
    CarrierKind

  selfModelCarrier :
    CarrierKind

  residualCarrier :
    CarrierKind

  namedCarrier :
    String →
    CarrierKind

canonicalSpatialCarriers : List CarrierKind
canonicalSpatialCarriers =
  roomCarrier
  ∷ landscapeCarrier
  ∷ thresholdCarrier
  ∷ relationalCarrier
  ∷ []
  where
    relationalCarrier : CarrierKind
    relationalCarrier =
      namedCarrier "relation"

canonicalMovingBodyCarriers : List CarrierKind
canonicalMovingBodyCarriers =
  bodyCarrier
  ∷ breathCarrier
  ∷ postureCarrier
  ∷ forceCarrier
  ∷ movementCarrier
  ∷ []

canonicalAttentionalCarriers : List CarrierKind
canonicalAttentionalCarriers =
  attentionCarrier
  ∷ breathCarrier
  ∷ perceptionCarrier
  ∷ affectCarrier
  ∷ memoryCarrier
  ∷ selfModelCarrier
  ∷ residualCarrier
  ∷ []

data InterMediaBridgePromotion : Set where

interMediaBridgePromotionImpossible :
  InterMediaBridgePromotion →
  ⊥
interMediaBridgePromotionImpossible ()

record InterMediaBridgeRow : Set where
  constructor interMediaBridgeRow
  field
    sourceMedium :
      MediaKind

    targetMedium :
      MediaKind

    sourceCarrier :
      CarrierKind

    targetCarrier :
      CarrierKind

    bridgeIndex :
      Nat

    bridgeProfile :
      String

    bridgeStatement :
      String

    candidateOnly :
      Bool

    carriesTruthAuthority :
      Bool

    carriesSupportAuthority :
      Bool

    carriesAdmissibilityAuthority :
      Bool

    carriesClinicalAuthority :
      Bool

    carriesMetaphysicalAuthority :
      Bool

    carriesClayAuthority :
      Bool

open InterMediaBridgeRow public

record InterMediaBridgeRowReceipt
  (row : InterMediaBridgeRow) :
  Set where
  constructor interMediaBridgeRowReceipt
  field
    rowCandidateOnly :
      candidateOnly row ≡ true

    rowTruthAuthorityFalse :
      carriesTruthAuthority row ≡ false

    rowSupportAuthorityFalse :
      carriesSupportAuthority row ≡ false

    rowAdmissibilityAuthorityFalse :
      carriesAdmissibilityAuthority row ≡ false

    rowClinicalAuthorityFalse :
      carriesClinicalAuthority row ≡ false

    rowMetaphysicalAuthorityFalse :
      carriesMetaphysicalAuthority row ≡ false

    rowClayAuthorityFalse :
      carriesClayAuthority row ≡ false

open InterMediaBridgeRowReceipt public

spatialToAttentionBridgeRow : InterMediaBridgeRow
spatialToAttentionBridgeRow =
  interMediaBridgeRow
    spatialMedium
    attentionalMedium
    roomCarrier
    attentionCarrier
    zero
    "feng-shui-to-meditation-carrier-adapter"
    "Space carrier readings may inform attentional carrier hypotheses only."
    true
    false
    false
    false
    false
    false
    false

movingBodyToAttentionBridgeRow : InterMediaBridgeRow
movingBodyToAttentionBridgeRow =
  interMediaBridgeRow
    movingBodyMedium
    attentionalMedium
    movementCarrier
    attentionCarrier
    zero
    "tai-chi-to-meditation-carrier-adapter"
    "Moving body-force readings may inform attentional carrier hypotheses only."
    true
    false
    false
    false
    false
    false
    false

attentionToRelationBridgeRow : InterMediaBridgeRow
attentionToRelationBridgeRow =
  interMediaBridgeRow
    attentionalMedium
    relationalMedium
    attentionCarrier
    (namedCarrier "reciprocal-practice")
    zero
    "attention-to-reciprocal-relation-adapter"
    "Meditation-state readings may inform reciprocal-practice questions only."
    true
    false
    false
    false
    false
    false
    false

spatialToAttentionBridgeRowReceipt :
  InterMediaBridgeRowReceipt spatialToAttentionBridgeRow
spatialToAttentionBridgeRowReceipt =
  interMediaBridgeRowReceipt refl refl refl refl refl refl refl

movingBodyToAttentionBridgeRowReceipt :
  InterMediaBridgeRowReceipt movingBodyToAttentionBridgeRow
movingBodyToAttentionBridgeRowReceipt =
  interMediaBridgeRowReceipt refl refl refl refl refl refl refl

attentionToRelationBridgeRowReceipt :
  InterMediaBridgeRowReceipt attentionToRelationBridgeRow
attentionToRelationBridgeRowReceipt =
  interMediaBridgeRowReceipt refl refl refl refl refl refl refl

canonicalInterMediaBridgeRows : List InterMediaBridgeRow
canonicalInterMediaBridgeRows =
  spatialToAttentionBridgeRow
  ∷ movingBodyToAttentionBridgeRow
  ∷ attentionToRelationBridgeRow
  ∷ []

record InterMediaCarrierBridgeReceipt : Set where
  constructor interMediaCarrierBridgeReceipt
  field
    authorityNonPromotionCoreAdapter :
      AuthorityNA.AuthorityNonPromotionBundle

    authorityNonPromotionCoreAdapterIsCanonical :
      authorityNonPromotionCoreAdapter
      ≡
      AuthorityNA.canonicalAuthorityNonPromotionBundle

    candidateOnlyCoreAdapter :
      CandidateOnly.CandidateOnlyReceipt
        CandidateOnly.canonicalBridgeCandidateOnlyRow

    candidateOnlyCoreAdapterIsCanonical :
      candidateOnlyCoreAdapter
      ≡
      CandidateOnly.canonicalBridgeCandidateOnlyReceipt

    bridgeRequirementCoreAdapter :
      BridgeReq.BridgeRequirementCoreReceipt

    bridgeRequirementCoreAdapterIsCanonical :
      bridgeRequirementCoreAdapter
      ≡
      BridgeReq.canonicalBridgeRequirementCoreReceipt

    emptyPromotionCoreAdapter :
      EmptyPromotion.EmptyPromotionReceipt

    emptyPromotionCoreAdapterIsCanonical :
      emptyPromotionCoreAdapter
      ≡
      EmptyPromotion.canonicalEmptyPromotionReceipt

    authorityBoundaryCoreAdapter :
      AuthorityBoundary.AuthorityBoundaryReceipt

    authorityBoundaryCoreAdapterIsCanonical :
      authorityBoundaryCoreAdapter
      ≡
      AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt

    authorityBoundaryCoreAdapterCandidateReceipt :
      CandidateOnly.CandidateOnlyReceipt
        (AuthorityBoundary.receiptCandidateRow
          authorityBoundaryCoreAdapter)

    authorityBoundaryCoreAdapterCandidateReceiptIsCanonical :
      authorityBoundaryCoreAdapterCandidateReceipt
      ≡
      AuthorityBoundary.receiptCandidateReceipt
        authorityBoundaryCoreAdapter

    authorityBoundaryCoreAdapterGenericReceipt :
      GenericReceipt.GenericReceipt

    authorityBoundaryCoreAdapterGenericReceiptIsCanonical :
      authorityBoundaryCoreAdapterGenericReceipt
      ≡
      AuthorityBoundary.authorityBoundaryGenericReceipt
        authorityBoundaryCoreAdapter

    authorityBoundaryCoreAdapterBlockedAuthorityKinds :
      List AuthorityNA.AuthorityKind

    authorityBoundaryCoreAdapterBlockedAuthorityKindsAreCanonical :
      authorityBoundaryCoreAdapterBlockedAuthorityKinds
      ≡
      AuthorityBoundary.canonicalBlockedAuthorityKinds

    authorityBoundaryCoreAdapterBlockedAuthorityKindsCount :
      Nat

    authorityBoundaryCoreAdapterBlockedAuthorityKindsCountIsCanonical :
      authorityBoundaryCoreAdapterBlockedAuthorityKindsCount
      ≡
      AuthorityBoundary.canonicalBlockedAuthorityKindCount

    authorityBoundaryCoreAdapterBlockedAuthorityKindsFalse :
      AuthorityNA.AllAuthorityKindsFalse
        (AuthorityBoundary.receiptAuthorityBundle authorityBoundaryCoreAdapter)
        authorityBoundaryCoreAdapterBlockedAuthorityKinds

    authorityBoundaryCoreAdapterBoundaryPromoted :
      Bool

    authorityBoundaryCoreAdapterBoundaryPromotedIsFalse :
      authorityBoundaryCoreAdapterBoundaryPromoted ≡ false

    bridgeStatus :
      InterMediaBridgeStatus

    bridgeRows :
      List InterMediaBridgeRow

    bridgeRowsAreCanonical :
      bridgeRows ≡ canonicalInterMediaBridgeRows

    spatialAttentionReceipt :
      InterMediaBridgeRowReceipt spatialToAttentionBridgeRow

    movingBodyAttentionReceipt :
      InterMediaBridgeRowReceipt movingBodyToAttentionBridgeRow

    attentionRelationReceipt :
      InterMediaBridgeRowReceipt attentionToRelationBridgeRow

    truthAuthorityPromoted :
      Bool

    truthAuthorityPromotedIsFalse :
      truthAuthorityPromoted ≡ false

    supportAuthorityPromoted :
      Bool

    supportAuthorityPromotedIsFalse :
      supportAuthorityPromoted ≡ false

    admissibilityAuthorityPromoted :
      Bool

    admissibilityAuthorityPromotedIsFalse :
      admissibilityAuthorityPromoted ≡ false

    clinicalAuthorityPromoted :
      Bool

    clinicalAuthorityPromotedIsFalse :
      clinicalAuthorityPromoted ≡ false

    metaphysicalAuthorityPromoted :
      Bool

    metaphysicalAuthorityPromotedIsFalse :
      metaphysicalAuthorityPromoted ≡ false

    clayAuthorityPromoted :
      Bool

    clayAuthorityPromotedIsFalse :
      clayAuthorityPromoted ≡ false

    promotions :
      List InterMediaBridgePromotion

    promotionsEmpty :
      promotions ≡ []

    promotionImpossible :
      InterMediaBridgePromotion →
      ⊥

open InterMediaCarrierBridgeReceipt public

canonicalInterMediaCarrierBridgeReceipt :
  InterMediaCarrierBridgeReceipt
canonicalInterMediaCarrierBridgeReceipt =
  interMediaCarrierBridgeReceipt
    AuthorityNA.canonicalAuthorityNonPromotionBundle
    refl
    CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    refl
    BridgeReq.canonicalBridgeRequirementCoreReceipt
    refl
    EmptyPromotion.canonicalEmptyPromotionReceipt
    refl
    AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt
    refl
    (AuthorityBoundary.receiptCandidateReceipt
      AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt)
    refl
    (AuthorityBoundary.authorityBoundaryGenericReceipt
      AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt)
    refl
    AuthorityBoundary.canonicalBlockedAuthorityKinds
    refl
    AuthorityBoundary.canonicalBlockedAuthorityKindCount
    refl
    (AuthorityNA.proveAllAuthorityKindsFalse
      (AuthorityBoundary.receiptAuthorityBundle
        AuthorityBoundary.canonicalRuntimeAuthorityBoundaryReceipt)
      AuthorityBoundary.canonicalBlockedAuthorityKinds)
    false
    refl
    interMediaBridge_candidateOnly
    canonicalInterMediaBridgeRows
    refl
    spatialToAttentionBridgeRowReceipt
    movingBodyToAttentionBridgeRowReceipt
    attentionToRelationBridgeRowReceipt
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    []
    refl
    interMediaBridgePromotionImpossible

canonicalInterMediaTruthAuthorityFalse :
  truthAuthorityPromoted canonicalInterMediaCarrierBridgeReceipt ≡ false
canonicalInterMediaTruthAuthorityFalse =
  refl

canonicalInterMediaClinicalAuthorityFalse :
  clinicalAuthorityPromoted canonicalInterMediaCarrierBridgeReceipt ≡ false
canonicalInterMediaClinicalAuthorityFalse =
  refl

canonicalInterMediaAuthorityCoreTruthFalse :
  AuthorityNA.truthAuthorityFlag
    (authorityNonPromotionCoreAdapter canonicalInterMediaCarrierBridgeReceipt)
  ≡
  false
canonicalInterMediaAuthorityCoreTruthFalse =
  refl

canonicalInterMediaCandidateOnlyCoreCandidateTrue :
  CandidateOnly.candidateOnly
    CandidateOnly.canonicalBridgeCandidateOnlyRow
  ≡
  true
canonicalInterMediaCandidateOnlyCoreCandidateTrue =
  refl

canonicalInterMediaBridgeRequirementCoreAuthorityFalse :
  BridgeReq.receiptAuthorityPromotion
    (bridgeRequirementCoreAdapter canonicalInterMediaCarrierBridgeReceipt)
  ≡
  false
canonicalInterMediaBridgeRequirementCoreAuthorityFalse =
  refl

canonicalInterMediaEmptyPromotionCoreEmpty :
  EmptyPromotion.promotions
    (emptyPromotionCoreAdapter canonicalInterMediaCarrierBridgeReceipt)
  ≡
  []
canonicalInterMediaEmptyPromotionCoreEmpty =
  refl

canonicalInterMediaAuthorityBoundaryCandidateOnlyTrue :
  CandidateOnly.candidateOnly
    (AuthorityBoundary.receiptCandidateRow
      (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt))
  ≡
  true
canonicalInterMediaAuthorityBoundaryCandidateOnlyTrue =
  refl

canonicalInterMediaAuthorityBoundaryCandidateReceiptIsCanonical :
  authorityBoundaryCoreAdapterCandidateReceipt
    canonicalInterMediaCarrierBridgeReceipt
  ≡
  AuthorityBoundary.receiptCandidateReceipt
    (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt)
canonicalInterMediaAuthorityBoundaryCandidateReceiptIsCanonical =
  refl

canonicalInterMediaAuthorityBoundaryGenericReceiptIsCanonical :
  authorityBoundaryCoreAdapterGenericReceipt
    canonicalInterMediaCarrierBridgeReceipt
  ≡
  AuthorityBoundary.authorityBoundaryGenericReceipt
    (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt)
canonicalInterMediaAuthorityBoundaryGenericReceiptIsCanonical =
  refl

canonicalInterMediaAuthorityBoundaryBlockedKindsAreCanonical :
  authorityBoundaryCoreAdapterBlockedAuthorityKinds
    canonicalInterMediaCarrierBridgeReceipt
  ≡
  AuthorityBoundary.canonicalBlockedAuthorityKinds
canonicalInterMediaAuthorityBoundaryBlockedKindsAreCanonical =
  authorityBoundaryCoreAdapterBlockedAuthorityKindsAreCanonical
    canonicalInterMediaCarrierBridgeReceipt

canonicalInterMediaAuthorityBoundaryBlockedKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    (AuthorityBoundary.receiptAuthorityBundle
      (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt))
    (authorityBoundaryCoreAdapterBlockedAuthorityKinds
      canonicalInterMediaCarrierBridgeReceipt)
canonicalInterMediaAuthorityBoundaryBlockedKindsFalse =
  authorityBoundaryCoreAdapterBlockedAuthorityKindsFalse
    canonicalInterMediaCarrierBridgeReceipt

canonicalInterMediaAuthorityBoundaryBlockedKindsCountIsCanonical :
  authorityBoundaryCoreAdapterBlockedAuthorityKindsCount
    canonicalInterMediaCarrierBridgeReceipt
  ≡
  AuthorityBoundary.canonicalBlockedAuthorityKindCount
canonicalInterMediaAuthorityBoundaryBlockedKindsCountIsCanonical =
  refl

canonicalInterMediaAuthorityBoundaryPromotedFalse :
  AuthorityBoundary.receiptBoundaryPromoted
    (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt)
  ≡
  false
canonicalInterMediaAuthorityBoundaryPromotedFalse =
  refl

canonicalInterMediaAuthorityBoundaryClaimKindMatchesDomain :
  AuthorityBoundary.receiptDomain
    (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt)
  ≡
  AuthorityBoundary.authorityBoundaryClaimDomain
    (AuthorityBoundary.receiptClaimKind
      (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt))
canonicalInterMediaAuthorityBoundaryClaimKindMatchesDomain =
  AuthorityBoundary.receiptClaimDomainMatches
    (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt)

canonicalInterMediaAuthorityBoundaryClaimKindMatchesAuthorityKind :
  AuthorityBoundary.receiptClaimAuthorityKind
    (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt)
  ≡
  AuthorityBoundary.authorityBoundaryClaimAuthorityKind
    (AuthorityBoundary.receiptClaimKind
      (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt))
canonicalInterMediaAuthorityBoundaryClaimKindMatchesAuthorityKind =
  AuthorityBoundary.receiptClaimAuthorityKindMatches
    (authorityBoundaryCoreAdapter canonicalInterMediaCarrierBridgeReceipt)

canonicalSpatialToAttentionCandidateOnly :
  candidateOnly spatialToAttentionBridgeRow ≡ true
canonicalSpatialToAttentionCandidateOnly =
  refl

canonicalMovingBodyToAttentionTruthFalse :
  carriesTruthAuthority movingBodyToAttentionBridgeRow ≡ false
canonicalMovingBodyToAttentionTruthFalse =
  refl
