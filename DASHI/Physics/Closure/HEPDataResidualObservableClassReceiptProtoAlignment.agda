module DASHI.Physics.Closure.HEPDataResidualObservableClassReceiptProtoAlignment where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate as Gate
import DASHI.Physics.Closure.HEPDataResidualObservableClassExternalAlignment as External
import DASHI.Physics.Closure.HEPDataResidualObservableClassProtoReceipt as Proto
import DASHI.Physics.Closure.HEPDataResidualProviderPayloadIntake as Intake
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack

------------------------------------------------------------------------
-- HEPData residual observable-class receipt/proto alignment.
--
-- This is the W3 residual-closure output for the current lane.  It aligns the
-- local phistar_50_76 proto receipt with the provider-facing
-- residualObservableClassReceipt slot, but keeps the slot first-missing until a
-- real provider payload supplies the accepted receipt.  It constructs no
-- selected observable, non-collapse witness, comparison law, accepted authority
-- route, W3AcceptedAuthorityExternalReceipt, or promotion token.

data HEPDataResidualObservableClassReceiptProtoAlignmentStatus : Set where
  protoAlignedToFirstMissingResidualObservableClassReceipt :
    HEPDataResidualObservableClassReceiptProtoAlignmentStatus

data HEPDataResidualObservableClassReceiptProtoAlignmentField : Set where
  alignmentBindsProtoReceipt :
    HEPDataResidualObservableClassReceiptProtoAlignmentField
  alignmentBindsExternalVocabulary :
    HEPDataResidualObservableClassReceiptProtoAlignmentField
  alignmentBindsProviderReceiptSlot :
    HEPDataResidualObservableClassReceiptProtoAlignmentField
  alignmentBindsFirstMissingPolicy :
    HEPDataResidualObservableClassReceiptProtoAlignmentField
  alignmentBindsIntakeRejection :
    HEPDataResidualObservableClassReceiptProtoAlignmentField
  alignmentBindsAuthorityGateBlock :
    HEPDataResidualObservableClassReceiptProtoAlignmentField
  alignmentRecordsRemainingReceiptChain :
    HEPDataResidualObservableClassReceiptProtoAlignmentField

canonicalHEPDataResidualObservableClassReceiptProtoAlignmentFields :
  List HEPDataResidualObservableClassReceiptProtoAlignmentField
canonicalHEPDataResidualObservableClassReceiptProtoAlignmentFields =
  alignmentBindsProtoReceipt
  ∷ alignmentBindsExternalVocabulary
  ∷ alignmentBindsProviderReceiptSlot
  ∷ alignmentBindsFirstMissingPolicy
  ∷ alignmentBindsIntakeRejection
  ∷ alignmentBindsAuthorityGateBlock
  ∷ alignmentRecordsRemainingReceiptChain
  ∷ []

record HEPDataResidualObservableClassReceiptProtoAlignment : Setω where
  field
    status :
      HEPDataResidualObservableClassReceiptProtoAlignmentStatus

    protoReceipt :
      Proto.HEPDataResidualObservableClassProtoReceipt

    externalAlignment :
      External.HEPDataResidualObservableClassExternalAlignment

    alignmentFields :
      List HEPDataResidualObservableClassReceiptProtoAlignmentField

    alignmentFieldsAreCanonical :
      alignmentFields
      ≡
      canonicalHEPDataResidualObservableClassReceiptProtoAlignmentFields

    providerReceiptSlot :
      Pack.HEPDataResidualProviderRequiredReceipt

    providerReceiptSlotIsResidualObservableClass :
      providerReceiptSlot
      ≡
      Pack.residualObservableClassReceipt

    firstMissingReceipt :
      Pack.HEPDataResidualProviderFirstMissingReceipt

    firstMissingReceiptIsResidualObservableClass :
      firstMissingReceipt
      ≡
      Pack.firstMissingResidualObservableClass

    protoFirstMissingMatchesAlignment :
      firstMissingReceipt
      ≡
      Proto.HEPDataResidualObservableClassProtoReceipt.firstMissingReceipt
        protoReceipt

    externalFirstMissingMatchesAlignment :
      firstMissingReceipt
      ≡
      External.HEPDataResidualObservableClassExternalAlignment.providerFirstMissingReceipt
        externalAlignment

    intakeStatus :
      Intake.HEPDataResidualProviderPayloadIntakeStatus

    intakeStatusIsRejectedAtResidualObservableClass :
      intakeStatus
      ≡
      Intake.intakeRejectedAtFirstMissingReceipt
        Pack.firstMissingResidualObservableClass

    authorityGateStatus :
      Gate.HEPDataResidualBridgeAuthorityGateStatus

    authorityGateStatusIsBlocked :
      authorityGateStatus
      ≡
      Gate.blockedAwaitingResidualAuthorityReceiptChain

    protoCanBeReturnedAsFirstMissingDiagnostic :
      Bool

    protoIsAcceptedResidualObservableClassReceipt :
      Bool

    residualAuthorityConstructibleHere :
      Bool

    remainingProviderReceiptsAfterProto :
      List Pack.HEPDataResidualProviderRequiredReceipt

    residualClosureOutputBoundary :
      List String

    firstMissingDiagnostic :
      String

canonicalHEPDataResidualObservableClassReceiptProtoAlignment :
  HEPDataResidualObservableClassReceiptProtoAlignment
canonicalHEPDataResidualObservableClassReceiptProtoAlignment =
  record
    { status =
        protoAlignedToFirstMissingResidualObservableClassReceipt
    ; protoReceipt =
        Proto.canonicalHEPDataResidualObservableClassProtoReceipt
    ; externalAlignment =
        External.canonicalHEPDataResidualObservableClassExternalAlignment
    ; alignmentFields =
        canonicalHEPDataResidualObservableClassReceiptProtoAlignmentFields
    ; alignmentFieldsAreCanonical =
        refl
    ; providerReceiptSlot =
        Pack.residualObservableClassReceipt
    ; providerReceiptSlotIsResidualObservableClass =
        refl
    ; firstMissingReceipt =
        Pack.firstMissingResidualObservableClass
    ; firstMissingReceiptIsResidualObservableClass =
        refl
    ; protoFirstMissingMatchesAlignment =
        refl
    ; externalFirstMissingMatchesAlignment =
        refl
    ; intakeStatus =
        Intake.intakeRejectedAtFirstMissingReceipt
          Pack.firstMissingResidualObservableClass
    ; intakeStatusIsRejectedAtResidualObservableClass =
        refl
    ; authorityGateStatus =
        Gate.blockedAwaitingResidualAuthorityReceiptChain
    ; authorityGateStatusIsBlocked =
        refl
    ; protoCanBeReturnedAsFirstMissingDiagnostic =
        true
    ; protoIsAcceptedResidualObservableClassReceipt =
        false
    ; residualAuthorityConstructibleHere =
        false
    ; remainingProviderReceiptsAfterProto =
        Pack.canonicalHEPDataResidualProviderRequiredReceipts
    ; residualClosureOutputBoundary =
        "The proto receipt is aligned to the provider residualObservableClassReceipt slot"
        ∷ "The aligned proto is admissible only as a first-missing typed diagnostic"
        ∷ "The provider receipt remains missing until a real external payload accepts the residual observable class"
        ∷ "nonCollapseWitnessReceipt remains a later required receipt and is not constructed here"
        ∷ "acceptedAuthorityRouteReceipt and W3AcceptedAuthorityExternalReceipt remain external and unconstructed"
        ∷ "No W3, W4, W5, or W8 promotion follows from this alignment"
        ∷ []
    ; firstMissingDiagnostic =
        "first missing W3 residual receipt: residualObservableClassReceipt; local proto aligns to the requested slot but is not an accepted provider receipt"
    }
