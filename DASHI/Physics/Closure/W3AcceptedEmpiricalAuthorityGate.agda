module DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.MinimalCredibleShiftOriginObservation as ORIGIN
open import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
open import DASHI.Physics.Closure.PhotonuclearEmpiricalEvidenceSummary as PEES
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import DASHI.Physics.Closure.Validation.RootSystemB4PromotionBridge as B4PB
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C
open import DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation as W3
open import DASHI.Physics.Closure.W3SurrogateEmpiricalTargetBoundary as W3S

------------------------------------------------------------------------
-- W3 accepted empirical authority gate.
--
-- The surrogate target may inhabit the local W3 chi2 target shape, but this
-- module makes replacement by accepted empirical evidence an explicit typed
-- gate.  No accepted authority value is constructible here from the current
-- photonuclear summaries alone: the authority token deliberately has no
-- constructor in this module, those summaries expose empirical-only
-- packaging/status tags, while B4 shell promotion and origin promotion remain
-- blocked at their own surfaces.

data W3AuthorityLane : Set where
  surrogateTargetLane :
    W3AuthorityLane
  acceptedEvidenceBackedTargetLane :
    W3AuthorityLane
  b4EmpiricalPromotionLane :
    W3AuthorityLane
  originPromotionLane :
    W3AuthorityLane

data W3AuthorityGateStatus : Set where
  surrogateAvailable :
    W3AuthorityGateStatus
  acceptedEvidenceBlocked :
    W3AuthorityGateStatus
  b4EmpiricalPromotionBlocked :
    W3AuthorityGateStatus
  originPromotionBlocked :
    W3AuthorityGateStatus
  acceptedAuthorityReady :
    W3AuthorityGateStatus

data W3AcceptedEvidenceAuthorityToken : Set where

record W3EvidenceBackedEmpiricalTarget : Setω where
  field
    photonuclearEvidenceSummary :
      PEES.PhotonuclearEvidenceSummary Nat

    photonuclearValidationSummary :
      PEVS.PhotonuclearEmpiricalValidationSummary Nat

    evidenceAuthority :
      W3AcceptedEvidenceAuthorityToken

    empiricalObservationTarget :
      W3.EmpiricalObservationTargetOverTransportedChi2Pool

    empiricalPromotionBridge :
      W3.Chi2LocalCandidateToEmpiricalAdequacyPromotion
        empiricalObservationTarget

record W3SurrogateReplacementConditions : Setω where
  field
    surrogateBoundary :
      W3S.W3SurrogateEmpiricalTargetBoundaryReceipt

    evidenceBackedTarget :
      W3EvidenceBackedEmpiricalTarget

    b4EmpiricalPromotion :
      W3.B4EmpiricalPromotionObligation

    originPromotion :
      W3.OriginReceiptPromotionObligation

record W3AcceptedEmpiricalAuthorityGate : Setω where
  field
    replacementConditions :
      W3SurrogateReplacementConditions

    acceptedAuthorityStatus :
      W3AuthorityGateStatus

    acceptedAuthorityStatusReady :
      acceptedAuthorityStatus
      ≡
      acceptedAuthorityReady

------------------------------------------------------------------------
-- Current blocker receipt.

data W3CurrentAcceptedAuthorityBlocker : Set where
  photonuclearEvidenceIsEmpiricalOnly :
    W3CurrentAcceptedAuthorityBlocker
  photonuclearValidationIsEmpiricalOnly :
    W3CurrentAcceptedAuthorityBlocker
  b4ShellReportStillStandaloneOnly :
    W3CurrentAcceptedAuthorityBlocker
  originObservationReceiptStillEmpiricalBlocked :
    W3CurrentAcceptedAuthorityBlocker

record W3CurrentAcceptedEmpiricalAuthorityGateStatus : Setω where
  field
    surrogateBoundary :
      W3S.W3SurrogateEmpiricalTargetBoundaryReceipt

    photonuclearEvidenceSummary :
      PEES.PhotonuclearEvidenceSummary Nat

    photonuclearEvidenceNonClaimBoundary :
      PEES.PhotonuclearEvidenceSummary.nonClaimBoundary
        photonuclearEvidenceSummary
      ≡
      PEES.empiricalOnly

    photonuclearValidationSummary :
      PEVS.PhotonuclearEmpiricalValidationSummary Nat

    photonuclearValidationNonClaimBoundary :
      PEVS.PhotonuclearEmpiricalValidationSummary.nonClaimBoundary
        photonuclearValidationSummary
      ≡
      PEVS.empiricalOnlyValidation

    b4ShellReport :
      B4C.B4ShellComparisonReport

    b4ShellReportStandaloneOnly :
      B4C.B4ShellComparisonReport.promotionStatus b4ShellReport
      ≡
      B4C.standaloneOnly

    b4ClosureBridgeReadyButNotEmpiricalShellPromotion :
      B4PB.B4PromotionBridge.promotionStatus B4PB.bridge
      ≡
      B4PB.admissiblePromotionReady

    originObservationReceipt :
      P0.OriginObservationReceipt

    originObservationReceiptBlocked :
      P0.OriginObservationReceipt.empiricalStatus originObservationReceipt
      ≡
      P0.empiricalBlocked

    lanes :
      List W3AuthorityLane

    statuses :
      List W3AuthorityGateStatus

    blockers :
      List W3CurrentAcceptedAuthorityBlocker

    authorityBoundary :
      List String

currentW3AcceptedEmpiricalAuthorityGateStatus :
  W3CurrentAcceptedEmpiricalAuthorityGateStatus
currentW3AcceptedEmpiricalAuthorityGateStatus =
  record
    { surrogateBoundary =
        W3S.w3SurrogateEmpiricalTargetBoundaryReceipt
    ; photonuclearEvidenceSummary =
        DDSI.photonuclearEvidenceSummaryNat
    ; photonuclearEvidenceNonClaimBoundary =
        refl
    ; photonuclearValidationSummary =
        DDSI.photonuclearValidationSummaryNat
    ; photonuclearValidationNonClaimBoundary =
        refl
    ; b4ShellReport =
        B4C.report
    ; b4ShellReportStandaloneOnly =
        refl
    ; b4ClosureBridgeReadyButNotEmpiricalShellPromotion =
        refl
    ; originObservationReceipt =
        ORIGIN.minimalCredibleShiftOriginObservationReceipt
    ; originObservationReceiptBlocked =
        refl
    ; lanes =
        surrogateTargetLane
        ∷ acceptedEvidenceBackedTargetLane
        ∷ b4EmpiricalPromotionLane
        ∷ originPromotionLane
        ∷ []
    ; statuses =
        surrogateAvailable
        ∷ acceptedEvidenceBlocked
        ∷ b4EmpiricalPromotionBlocked
        ∷ originPromotionBlocked
        ∷ []
    ; blockers =
        photonuclearEvidenceIsEmpiricalOnly
        ∷ photonuclearValidationIsEmpiricalOnly
        ∷ b4ShellReportStillStandaloneOnly
        ∷ originObservationReceiptStillEmpiricalBlocked
        ∷ []
    ; authorityBoundary =
        "The W3 surrogate target is available only as a syntactic chi2/shift-pressure target shape"
        ∷ "Accepted empirical replacement requires an evidence-backed W3 target carrying W3AcceptedEvidenceAuthorityToken"
        ∷ "The canonical photonuclear summaries currently expose empiricalOnly and empiricalOnlyValidation non-claim boundaries"
        ∷ "B4 shell comparison remains standaloneOnly, so B4 empirical promotion is blocked"
        ∷ "Origin observation remains empiricalBlocked, so origin promotion and P0.OriginReceipt remain blocked"
        ∷ []
    }

canonicalCurrentW3AcceptedAuthorityStatuses :
  List W3AuthorityGateStatus
canonicalCurrentW3AcceptedAuthorityStatuses =
  W3CurrentAcceptedEmpiricalAuthorityGateStatus.statuses
    currentW3AcceptedEmpiricalAuthorityGateStatus
