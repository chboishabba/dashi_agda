module DASHI.Interop.PNFResidualConsumerNextObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual
import Ontology.Hecke.PNFResidualBridge as Hecke

------------------------------------------------------------------------
-- W6n PNF residual consumer next obligation.
--
-- The existing interop bridge defines the PredicatePNF carrier and residual
-- computation, while the Hecke bridge exposes quotient fibres only as
-- candidate pools.  This module names the receipt-bearing consumer shape that
-- would be needed to wire ITIR/PNF residuals through that surface.  It does
-- not construct runtime receipts and does not assign wrapper, qualifier, role,
-- residual, or Hecke labels by inspection.

record PNFResidualConsumerReceipt : Setω where
  field
    consumerProfile :
      String

    runtimeReceiptId :
      String

    leftEmissionReceipt :
      Residual.PNFEmissionReceipt

    rightEmissionReceipt :
      Residual.PNFEmissionReceipt

    emittedLeftAtom :
      Residual.PredicatePNF

    emittedRightAtom :
      Residual.PredicatePNF

    leftAtomComesFromReceipt :
      emittedLeftAtom
      ≡
      Residual.PNFEmissionReceipt.emittedAtom leftEmissionReceipt

    rightAtomComesFromReceipt :
      emittedRightAtom
      ≡
      Residual.PNFEmissionReceipt.emittedAtom rightEmissionReceipt

    residualLevel :
      Residual.ResidualLevel

    residualComesFromReceiptComputation :
      residualLevel
      ≡
      Residual.receiptResidual leftEmissionReceipt rightEmissionReceipt

    heckeResidualBridgeSurface :
      Hecke.HeckePNFResidualBridgeSurface

    heckeBridgeBoundaryAcknowledged :
      List String

------------------------------------------------------------------------
-- Current blocked status.

data PNFResidualConsumerMissingReceiptField : Set where
  missingLeftEmissionReceipt :
    PNFResidualConsumerMissingReceiptField
  missingRightEmissionReceipt :
    PNFResidualConsumerMissingReceiptField
  missingReceiptBackedAtomProjection :
    PNFResidualConsumerMissingReceiptField
  missingReceiptBackedResidualComputation :
    PNFResidualConsumerMissingReceiptField
  missingRuntimeConsumerProfile :
    PNFResidualConsumerMissingReceiptField
  missingRuntimeReceiptId :
    PNFResidualConsumerMissingReceiptField
  missingHeckeCandidatePoolReceipt :
    PNFResidualConsumerMissingReceiptField

data PNFResidualConsumerNonInspectionBoundary : Set where
  noWrapperByInspection :
    PNFResidualConsumerNonInspectionBoundary
  noQualifierByInspection :
    PNFResidualConsumerNonInspectionBoundary
  noRoleBindingByInspection :
    PNFResidualConsumerNonInspectionBoundary
  noResidualLevelByInspection :
    PNFResidualConsumerNonInspectionBoundary
  noHeckeFibreLabelByInspection :
    PNFResidualConsumerNonInspectionBoundary

data PNFResidualConsumerCurrentStatus : Set where
  receiptConsumerObligationOnly :
    PNFResidualConsumerCurrentStatus
  runtimePNFReceiptsBlocked :
    PNFResidualConsumerCurrentStatus
  residualComputationReceiptBlocked :
    PNFResidualConsumerCurrentStatus
  heckeCandidatePoolReceiptBlocked :
    PNFResidualConsumerCurrentStatus
  nonPromotingDiagnostic :
    PNFResidualConsumerCurrentStatus

record PNFResidualConsumerMissingReceiptDiagnostic : Setω where
  field
    currentStatus :
      PNFResidualConsumerCurrentStatus

    missingReceiptFields :
      List PNFResidualConsumerMissingReceiptField

    nonInspectionBoundaries :
      List PNFResidualConsumerNonInspectionBoundary

    heckeBridgeNonClaimBoundary :
      List String

    requiredNextReceipt :
      String

    noPromotionBoundary :
      List String

canonicalPNFResidualConsumerMissingReceiptDiagnostic :
  PNFResidualConsumerMissingReceiptDiagnostic
canonicalPNFResidualConsumerMissingReceiptDiagnostic =
  record
    { currentStatus =
        nonPromotingDiagnostic
    ; missingReceiptFields =
        missingLeftEmissionReceipt
        ∷ missingRightEmissionReceipt
        ∷ missingReceiptBackedAtomProjection
        ∷ missingReceiptBackedResidualComputation
        ∷ missingRuntimeConsumerProfile
        ∷ missingRuntimeReceiptId
        ∷ missingHeckeCandidatePoolReceipt
        ∷ []
    ; nonInspectionBoundaries =
        noWrapperByInspection
        ∷ noQualifierByInspection
        ∷ noRoleBindingByInspection
        ∷ noResidualLevelByInspection
        ∷ noHeckeFibreLabelByInspection
        ∷ []
    ; heckeBridgeNonClaimBoundary =
        Hecke.HeckePNFResidualBridgeSurface.nonClaimBoundary
          Hecke.heckePNFResidualBridgeSurface
    ; requiredNextReceipt =
        "provide paired PNFEmissionReceipt values, receipt-backed residual computation, runtime consumer profile/id, and Hecke candidate-pool receipt"
    ; noPromotionBoundary =
        "This module names the W6 PNF residual consumer obligation only"
        ∷ "No PNFEmissionReceipt is constructed here"
        ∷ "No wrapper, qualifier, role, residual, or Hecke fibre label is assigned by inspection"
        ∷ "No runtime ITIR/SensibLaw consumer is imported or promoted here"
        ∷ []
    }

canonicalPNFResidualConsumerMissingFields :
  List PNFResidualConsumerMissingReceiptField
canonicalPNFResidualConsumerMissingFields =
  PNFResidualConsumerMissingReceiptDiagnostic.missingReceiptFields
    canonicalPNFResidualConsumerMissingReceiptDiagnostic
