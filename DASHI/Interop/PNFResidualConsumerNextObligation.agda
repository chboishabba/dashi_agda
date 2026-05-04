module DASHI.Interop.PNFResidualConsumerNextObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
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

    heckeCandidatePoolReceiptId :
      String

    heckeBridgeBoundaryAcknowledged :
      List String

pnfResidualConsumerReceiptFromRuntimeEvidence :
  (consumerProfile runtimeReceiptId : String) →
  (leftEmissionReceipt rightEmissionReceipt :
    Residual.PNFEmissionReceipt) →
  (heckeCandidatePoolReceiptId : String) →
  PNFResidualConsumerReceipt
pnfResidualConsumerReceiptFromRuntimeEvidence
  consumerProfile
  runtimeReceiptId
  leftEmissionReceipt
  rightEmissionReceipt
  heckeCandidatePoolReceiptId =
  record
    { consumerProfile =
        consumerProfile
    ; runtimeReceiptId =
        runtimeReceiptId
    ; leftEmissionReceipt =
        leftEmissionReceipt
    ; rightEmissionReceipt =
        rightEmissionReceipt
    ; emittedLeftAtom =
        Residual.PNFEmissionReceipt.emittedAtom leftEmissionReceipt
    ; emittedRightAtom =
        Residual.PNFEmissionReceipt.emittedAtom rightEmissionReceipt
    ; leftAtomComesFromReceipt =
        refl
    ; rightAtomComesFromReceipt =
        refl
    ; residualLevel =
        Residual.receiptResidual leftEmissionReceipt rightEmissionReceipt
    ; residualComesFromReceiptComputation =
        refl
    ; heckeResidualBridgeSurface =
        Hecke.heckePNFResidualBridgeSurface
    ; heckeCandidatePoolReceiptId =
        heckeCandidatePoolReceiptId
    ; heckeBridgeBoundaryAcknowledged =
        Hecke.HeckePNFResidualBridgeSurface.nonClaimBoundary
          Hecke.heckePNFResidualBridgeSurface
    }

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

data PNFResidualConsumerDerivedReceiptField : Set where
  emittedAtomsDeriveFromEmissionReceipts :
    PNFResidualConsumerDerivedReceiptField
  residualLevelDerivesFromReceiptResidual :
    PNFResidualConsumerDerivedReceiptField
  heckeBoundaryDerivesFromBridgeSurface :
    PNFResidualConsumerDerivedReceiptField

data PNFResidualConsumerRuntimeSuppliedField : Set where
  runtimeSuppliesConsumerProfile :
    PNFResidualConsumerRuntimeSuppliedField
  runtimeSuppliesReceiptId :
    PNFResidualConsumerRuntimeSuppliedField
  runtimeSuppliesLeftEmissionReceipt :
    PNFResidualConsumerRuntimeSuppliedField
  runtimeSuppliesRightEmissionReceipt :
    PNFResidualConsumerRuntimeSuppliedField
  runtimeSuppliesHeckeCandidatePoolReceiptId :
    PNFResidualConsumerRuntimeSuppliedField

data PNFResidualConsumerExistingRuntimeSource : Set where
  pnfEmissionReceiptConstructorExists :
    PNFResidualConsumerExistingRuntimeSource
  pnfResidualConsumerBuilderExists :
    PNFResidualConsumerExistingRuntimeSource
  heckeCandidatePoolSurfaceExists :
    PNFResidualConsumerExistingRuntimeSource

data PNFResidualConsumerMissingRuntimeSource : Set where
  missingConcreteConsumerProfileValue :
    PNFResidualConsumerMissingRuntimeSource
  missingConcreteRuntimeReceiptIdValue :
    PNFResidualConsumerMissingRuntimeSource
  missingConcreteLeftPNFEmissionReceiptValue :
    PNFResidualConsumerMissingRuntimeSource
  missingConcreteRightPNFEmissionReceiptValue :
    PNFResidualConsumerMissingRuntimeSource
  missingConcreteHeckeCandidatePoolReceiptIdValue :
    PNFResidualConsumerMissingRuntimeSource

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

    derivableAfterRuntimeReceipts :
      List PNFResidualConsumerDerivedReceiptField

    heckeBridgeNonClaimBoundary :
      List String

    requiredNextReceipt :
      String

    noPromotionBoundary :
      List String

record PNFResidualConsumerRuntimeIntakeRequest : Set where
  field
    runtimeSuppliedFields :
      List PNFResidualConsumerRuntimeSuppliedField

    derivedAfterIntake :
      List PNFResidualConsumerDerivedReceiptField

    consumerReceiptBuilder :
      String

    noRuntimeDataFabricatedHere :
      List String

record PNFResidualConsumerRuntimeReceiptSourceDiagnostic : Set where
  field
    existingRuntimeSources :
      List PNFResidualConsumerExistingRuntimeSource

    missingRuntimeSources :
      List PNFResidualConsumerMissingRuntimeSource

    constructibleAfterSources :
      List PNFResidualConsumerDerivedReceiptField

    sourceSearchBoundary :
      List String

canonicalPNFResidualConsumerRuntimeIntakeRequest :
  PNFResidualConsumerRuntimeIntakeRequest
canonicalPNFResidualConsumerRuntimeIntakeRequest =
  record
    { runtimeSuppliedFields =
        runtimeSuppliesConsumerProfile
        ∷ runtimeSuppliesReceiptId
        ∷ runtimeSuppliesLeftEmissionReceipt
        ∷ runtimeSuppliesRightEmissionReceipt
        ∷ runtimeSuppliesHeckeCandidatePoolReceiptId
        ∷ []
    ; derivedAfterIntake =
        emittedAtomsDeriveFromEmissionReceipts
        ∷ residualLevelDerivesFromReceiptResidual
        ∷ heckeBoundaryDerivesFromBridgeSurface
        ∷ []
    ; consumerReceiptBuilder =
        "pnfResidualConsumerReceiptFromRuntimeEvidence"
    ; noRuntimeDataFabricatedHere =
        "Runtime must supply the consumer profile and runtime receipt id"
        ∷ "Runtime must supply the left and right PNFEmissionReceipt values"
        ∷ "Runtime must supply the Hecke candidate-pool receipt id"
        ∷ "This request does not construct atoms, residuals, or Hecke labels"
        ∷ []
    }

canonicalPNFResidualConsumerRuntimeReceiptSourceDiagnostic :
  PNFResidualConsumerRuntimeReceiptSourceDiagnostic
canonicalPNFResidualConsumerRuntimeReceiptSourceDiagnostic =
  record
    { existingRuntimeSources =
        pnfEmissionReceiptConstructorExists
        ∷ pnfResidualConsumerBuilderExists
        ∷ heckeCandidatePoolSurfaceExists
        ∷ []
    ; missingRuntimeSources =
        missingConcreteConsumerProfileValue
        ∷ missingConcreteRuntimeReceiptIdValue
        ∷ missingConcreteLeftPNFEmissionReceiptValue
        ∷ missingConcreteRightPNFEmissionReceiptValue
        ∷ missingConcreteHeckeCandidatePoolReceiptIdValue
        ∷ []
    ; constructibleAfterSources =
        emittedAtomsDeriveFromEmissionReceipts
        ∷ residualLevelDerivesFromReceiptResidual
        ∷ heckeBoundaryDerivesFromBridgeSurface
        ∷ []
    ; sourceSearchBoundary =
        "DASHI.Interop.SensibLawResidualLattice exports the PNFEmissionReceipt constructor, not concrete runtime receipt values"
        ∷ "DASHI.Interop.PNFResidualConsumerNextObligation exports the consumer builder, not runtime inputs"
        ∷ "Ontology.Hecke.PNFResidualBridge exports the candidate-pool surface, not a runtime candidate-pool receipt id"
        ∷ "A concrete PNFResidualConsumerReceipt is constructible only after runtime supplies the five intake fields"
        ∷ []
    }

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
    ; derivableAfterRuntimeReceipts =
        emittedAtomsDeriveFromEmissionReceipts
        ∷ residualLevelDerivesFromReceiptResidual
        ∷ heckeBoundaryDerivesFromBridgeSurface
        ∷ []
    ; heckeBridgeNonClaimBoundary =
        Hecke.HeckePNFResidualBridgeSurface.nonClaimBoundary
          Hecke.heckePNFResidualBridgeSurface
    ; requiredNextReceipt =
        "provide runtime consumer profile/id, paired runtime PNFEmissionReceipt values, and a Hecke candidate-pool receipt id; atom projection and residual level then derive by refl from receiptResidual"
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

canonicalPNFResidualConsumerDerivableFields :
  List PNFResidualConsumerDerivedReceiptField
canonicalPNFResidualConsumerDerivableFields =
  PNFResidualConsumerMissingReceiptDiagnostic.derivableAfterRuntimeReceipts
    canonicalPNFResidualConsumerMissingReceiptDiagnostic

canonicalPNFResidualConsumerRuntimeSuppliedFields :
  List PNFResidualConsumerRuntimeSuppliedField
canonicalPNFResidualConsumerRuntimeSuppliedFields =
  PNFResidualConsumerRuntimeIntakeRequest.runtimeSuppliedFields
    canonicalPNFResidualConsumerRuntimeIntakeRequest

canonicalPNFResidualConsumerMissingRuntimeSources :
  List PNFResidualConsumerMissingRuntimeSource
canonicalPNFResidualConsumerMissingRuntimeSources =
  PNFResidualConsumerRuntimeReceiptSourceDiagnostic.missingRuntimeSources
    canonicalPNFResidualConsumerRuntimeReceiptSourceDiagnostic
