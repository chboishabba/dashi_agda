module DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as AUTH
open import DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation as W3

------------------------------------------------------------------------
-- W3n accepted-authority external receipt obligation.
--
-- W3AcceptedEvidenceAuthorityToken is intentionally constructorless in
-- W3AcceptedEmpiricalAuthorityGate.  This module names the external upstream
-- receipt shape that could later inhabit the accepted-authority gate, while
-- the current value below records only blocked / obligations-needed status.

record W3AcceptedAuthorityExternalReceipt : Setω where
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

    bridgeObligations :
      W3.W3EmpiricalTargetPromotionBridgeObligations

    bridgeTargetMatchesEvidence :
      W3.W3EmpiricalTargetPromotionBridgeObligations.empiricalObservationTarget
        bridgeObligations
      ≡
      AUTH.W3EvidenceBackedEmpiricalTarget.empiricalObservationTarget
        evidenceBackedEmpiricalTarget

------------------------------------------------------------------------
-- Current non-promoting status.

data W3AcceptedAuthorityExternalReceiptStatus : Set where
  authorityTokenObligationNeeded :
    W3AcceptedAuthorityExternalReceiptStatus
  evidenceBackedEmpiricalTargetBlocked :
    W3AcceptedAuthorityExternalReceiptStatus
  b4EmpiricalPromotionBlocked :
    W3AcceptedAuthorityExternalReceiptStatus
  originReceiptPromotionBlocked :
    W3AcceptedAuthorityExternalReceiptStatus
  externalReceiptObligationOnly :
    W3AcceptedAuthorityExternalReceiptStatus

record W3AcceptedAuthorityExternalReceiptCurrentStatus : Setω where
  field
    authorityGateStatus :
      AUTH.W3CurrentAcceptedEmpiricalAuthorityGateStatus

    empiricalTargetPromotionObligationReceipt :
      W3.W3EmpiricalTargetPromotionBridgeObligationReceipt

    authorityStatuses :
      List AUTH.W3AuthorityGateStatus

    externalReceiptStatuses :
      List W3AcceptedAuthorityExternalReceiptStatus

    empiricalTargetObligationsNeeded :
      W3.W3EmpiricalTargetPromotionBoundaryToken

    empiricalTargetNonPromotion :
      W3.W3EmpiricalTargetPromotionBoundaryToken

    authorityBoundary :
      List String

    nonPromotionBoundary :
      List String

currentW3AcceptedAuthorityExternalReceiptStatus :
  W3AcceptedAuthorityExternalReceiptCurrentStatus
currentW3AcceptedAuthorityExternalReceiptStatus =
  record
    { authorityGateStatus =
        AUTH.currentW3AcceptedEmpiricalAuthorityGateStatus
    ; empiricalTargetPromotionObligationReceipt =
        W3.canonicalW3EmpiricalTargetPromotionBridgeObligationReceipt
    ; authorityStatuses =
        AUTH.canonicalCurrentW3AcceptedAuthorityStatuses
    ; externalReceiptStatuses =
        authorityTokenObligationNeeded
        ∷ evidenceBackedEmpiricalTargetBlocked
        ∷ b4EmpiricalPromotionBlocked
        ∷ originReceiptPromotionBlocked
        ∷ externalReceiptObligationOnly
        ∷ []
    ; empiricalTargetObligationsNeeded =
        W3.canonicalW3EmpiricalTargetPromotionObligationsNeededToken
    ; empiricalTargetNonPromotion =
        W3.canonicalW3EmpiricalTargetPromotionCurrentNonPromotionToken
    ; authorityBoundary =
        "External accepted evidence authority must supply W3AcceptedEvidenceAuthorityToken"
        ∷ "The current repo deliberately constructs no W3AcceptedEvidenceAuthorityToken"
        ∷ "The evidence-backed target, B4 empirical promotion, and origin receipt promotion must arrive together"
        ∷ []
    ; nonPromotionBoundary =
        "This module is an external receipt obligation only"
        ∷ "No accepted empirical authority gate is inhabited here"
        ∷ "No obs(fixedPoint)=empirical theorem is inhabited here"
        ∷ []
    }

canonicalW3AcceptedAuthorityExternalReceiptStatuses :
  List W3AcceptedAuthorityExternalReceiptStatus
canonicalW3AcceptedAuthorityExternalReceiptStatuses =
  W3AcceptedAuthorityExternalReceiptCurrentStatus.externalReceiptStatuses
    currentW3AcceptedAuthorityExternalReceiptStatus
