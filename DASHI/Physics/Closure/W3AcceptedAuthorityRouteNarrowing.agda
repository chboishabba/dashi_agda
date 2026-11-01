module DASHI.Physics.Closure.W3AcceptedAuthorityRouteNarrowing where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation as W8
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as AUTH
import DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation as W3

------------------------------------------------------------------------
-- W3o accepted-authority route narrowing.
--
-- This module does not construct accepted empirical authority.  It names the
-- exact positive route required to replace the current surrogate W3 target:
-- accepted authority token, evidence-backed empirical target, B4 empirical
-- promotion, and origin-promotion compatibility.  The exported current value
-- records that every route ingredient is still blocked by existing
-- non-promotion surfaces.

data W3AcceptedAuthorityRouteIngredient : Set where
  acceptedEvidenceAuthorityTokenIngredient :
    W3AcceptedAuthorityRouteIngredient
  evidenceBackedEmpiricalTargetIngredient :
    W3AcceptedAuthorityRouteIngredient
  b4EmpiricalPromotionIngredient :
    W3AcceptedAuthorityRouteIngredient
  originPromotionCompatibilityIngredient :
    W3AcceptedAuthorityRouteIngredient

data W3AcceptedAuthorityRouteBlocker : Set where
  authorityTokenConstructorless :
    W3AcceptedAuthorityRouteBlocker
  evidenceBackedTargetRequiresAuthorityToken :
    W3AcceptedAuthorityRouteBlocker
  externalReceiptRequiresAuthorityToken :
    W3AcceptedAuthorityRouteBlocker
  b4EmpiricalPromotionStillStandalone :
    W3AcceptedAuthorityRouteBlocker
  originPromotionStillEmpiricalBlocked :
    W3AcceptedAuthorityRouteBlocker
  originPromotionExternalCompatibilityMissing :
    W3AcceptedAuthorityRouteBlocker
  routeNarrowingOnlyNoPromotion :
    W3AcceptedAuthorityRouteBlocker

data W3AcceptedAuthorityRouteImpossible : Set where

record W3AcceptedAuthorityPositiveRoute : Setω where
  field
    authorityToken :
      AUTH.W3AcceptedEvidenceAuthorityToken

    evidenceBackedEmpiricalTarget :
      AUTH.W3EvidenceBackedEmpiricalTarget

    evidenceTargetCarriesAuthority :
      AUTH.W3EvidenceBackedEmpiricalTarget.evidenceAuthority
        evidenceBackedEmpiricalTarget
      ≡
      authorityToken

    b4EmpiricalPromotion :
      W3.B4EmpiricalPromotionObligation

    originReceiptPromotion :
      W3.OriginReceiptPromotionObligation

    acceptedAuthorityExternalReceipt :
      EXT.W3AcceptedAuthorityExternalReceipt

    externalReceiptCarriesAuthority :
      EXT.W3AcceptedAuthorityExternalReceipt.authorityToken
        acceptedAuthorityExternalReceipt
      ≡
      authorityToken

    originPromotionExternalReceipt :
      W8.OriginReceiptPromotionExternalReceipt

record W3AcceptedAuthorityRouteCurrentDiagnostic : Setω where
  field
    authorityGateStatus :
      AUTH.W3CurrentAcceptedEmpiricalAuthorityGateStatus

    acceptedAuthorityExternalStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    empiricalTargetPromotionReceipt :
      W3.W3EmpiricalTargetPromotionBridgeObligationReceipt

    originPromotionExternalStatus :
      W8.OriginReceiptPromotionExternalCurrentStatus

    routeIngredients :
      List W3AcceptedAuthorityRouteIngredient

    currentBlockers :
      List W3AcceptedAuthorityRouteBlocker

    acceptedAuthorityTokenUninhabited :
      AUTH.W3AcceptedEvidenceAuthorityToken →
      W3AcceptedAuthorityRouteImpossible

    evidenceBackedTargetBlockedByToken :
      AUTH.W3EvidenceBackedEmpiricalTarget →
      W3AcceptedAuthorityRouteImpossible

    externalReceiptBlockedByToken :
      EXT.W3AcceptedAuthorityExternalReceipt →
      W3AcceptedAuthorityRouteImpossible

    obligationsNeededToken :
      W3.W3EmpiricalTargetPromotionBoundaryToken

    currentNonPromotionToken :
      W3.W3EmpiricalTargetPromotionBoundaryToken

    routeBoundary :
      List String

    nonPromotionBoundary :
      List String

currentAcceptedAuthorityTokenUninhabited :
  AUTH.W3AcceptedEvidenceAuthorityToken →
  W3AcceptedAuthorityRouteImpossible
currentAcceptedAuthorityTokenUninhabited ()

currentEvidenceBackedTargetBlockedByToken :
  AUTH.W3EvidenceBackedEmpiricalTarget →
  W3AcceptedAuthorityRouteImpossible
currentEvidenceBackedTargetBlockedByToken target =
  currentAcceptedAuthorityTokenUninhabited
    (AUTH.W3EvidenceBackedEmpiricalTarget.evidenceAuthority target)

currentExternalReceiptBlockedByToken :
  EXT.W3AcceptedAuthorityExternalReceipt →
  W3AcceptedAuthorityRouteImpossible
currentExternalReceiptBlockedByToken receipt =
  currentAcceptedAuthorityTokenUninhabited
    (EXT.W3AcceptedAuthorityExternalReceipt.authorityToken receipt)

canonicalW3AcceptedAuthorityRouteCurrentDiagnostic :
  W3AcceptedAuthorityRouteCurrentDiagnostic
canonicalW3AcceptedAuthorityRouteCurrentDiagnostic =
  record
    { authorityGateStatus =
        AUTH.currentW3AcceptedEmpiricalAuthorityGateStatus
    ; acceptedAuthorityExternalStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; empiricalTargetPromotionReceipt =
        W3.canonicalW3EmpiricalTargetPromotionBridgeObligationReceipt
    ; originPromotionExternalStatus =
        W8.canonicalOriginReceiptPromotionExternalCurrentStatus
    ; routeIngredients =
        acceptedEvidenceAuthorityTokenIngredient
        ∷ evidenceBackedEmpiricalTargetIngredient
        ∷ b4EmpiricalPromotionIngredient
        ∷ originPromotionCompatibilityIngredient
        ∷ []
    ; currentBlockers =
        authorityTokenConstructorless
        ∷ evidenceBackedTargetRequiresAuthorityToken
        ∷ externalReceiptRequiresAuthorityToken
        ∷ b4EmpiricalPromotionStillStandalone
        ∷ originPromotionStillEmpiricalBlocked
        ∷ originPromotionExternalCompatibilityMissing
        ∷ routeNarrowingOnlyNoPromotion
        ∷ []
    ; acceptedAuthorityTokenUninhabited =
        currentAcceptedAuthorityTokenUninhabited
    ; evidenceBackedTargetBlockedByToken =
        currentEvidenceBackedTargetBlockedByToken
    ; externalReceiptBlockedByToken =
        currentExternalReceiptBlockedByToken
    ; obligationsNeededToken =
        W3.canonicalW3EmpiricalTargetPromotionObligationsNeededToken
    ; currentNonPromotionToken =
        W3.canonicalW3EmpiricalTargetPromotionCurrentNonPromotionToken
    ; routeBoundary =
        "W3 accepted route requires an accepted evidence authority token"
        ∷ "W3 accepted route requires an evidence-backed empirical target carrying that token"
        ∷ "W3 accepted route requires B4 empirical promotion, not standalone shell comparison"
        ∷ "W3 accepted route requires origin promotion compatibility with the external origin receipt surface"
        ∷ []
    ; nonPromotionBoundary =
        "This module narrows the W3 accepted-authority route only"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed"
        ∷ "No W3EvidenceBackedEmpiricalTarget is constructed"
        ∷ "No B4 empirical promotion or origin receipt promotion is constructed"
        ∷ "No obs(fixedPoint)=empirical theorem is inhabited"
        ∷ []
    }

canonicalW3AcceptedAuthorityRouteBlockers :
  List W3AcceptedAuthorityRouteBlocker
canonicalW3AcceptedAuthorityRouteBlockers =
  W3AcceptedAuthorityRouteCurrentDiagnostic.currentBlockers
    canonicalW3AcceptedAuthorityRouteCurrentDiagnostic
