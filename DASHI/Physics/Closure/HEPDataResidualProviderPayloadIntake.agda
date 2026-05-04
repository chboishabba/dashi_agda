module DASHI.Physics.Closure.HEPDataResidualProviderPayloadIntake where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack

------------------------------------------------------------------------
-- HEPData residual provider payload intake.
--
-- This module is a diagnostic intake/filter surface only.  It names the
-- residual provider payload fields, intake statuses, and first-missing
-- outcomes that must be reported before any residual bridge promotion can be
-- considered.  It reuses HEPDataResidualProviderReceiptRequestPack as the
-- receipt-chain source of truth and constructs no selected observable,
-- empirical receipt, authority token, local candidate promotion, or raw
-- saturated value.

data HEPDataResidualProviderPayloadField : Set where
  payloadResidualObservableKind :
    HEPDataResidualProviderPayloadField
  payloadExactSelectedResidualObservable :
    HEPDataResidualProviderPayloadField
  payloadChecksumBoundSelection :
    HEPDataResidualProviderPayloadField
  payloadBaselineOrInvarianceModel :
    HEPDataResidualProviderPayloadField
  payloadResidualDefinition :
    HEPDataResidualProviderPayloadField
  payloadNonCollapseWitnessReceipt :
    HEPDataResidualProviderPayloadField
  payloadCalibrationCovarianceReceipt :
    HEPDataResidualProviderPayloadField
  payloadTheoremSideProjectionReceipt :
    HEPDataResidualProviderPayloadField
  payloadDefectProjectionReceipt :
    HEPDataResidualProviderPayloadField
  payloadResidualComparisonLawReceipt :
    HEPDataResidualProviderPayloadField
  payloadAcceptedAuthorityRouteReceipt :
    HEPDataResidualProviderPayloadField

canonicalHEPDataResidualProviderPayloadFields :
  List HEPDataResidualProviderPayloadField
canonicalHEPDataResidualProviderPayloadFields =
  payloadResidualObservableKind
  ∷ payloadExactSelectedResidualObservable
  ∷ payloadChecksumBoundSelection
  ∷ payloadBaselineOrInvarianceModel
  ∷ payloadResidualDefinition
  ∷ payloadNonCollapseWitnessReceipt
  ∷ payloadCalibrationCovarianceReceipt
  ∷ payloadTheoremSideProjectionReceipt
  ∷ payloadDefectProjectionReceipt
  ∷ payloadResidualComparisonLawReceipt
  ∷ payloadAcceptedAuthorityRouteReceipt
  ∷ []

data HEPDataResidualProviderPayloadIntakeStatus : Set where
  intakeAwaitingProviderPayload :
    HEPDataResidualProviderPayloadIntakeStatus
  intakeRejectedAtFirstMissingReceipt :
    Pack.HEPDataResidualProviderFirstMissingReceipt →
    HEPDataResidualProviderPayloadIntakeStatus
  intakePassedResidualSpecificReceiptChain :
    HEPDataResidualProviderPayloadIntakeStatus

data HEPDataResidualProviderPayloadFirstMissingOutcome : Set where
  reportFirstMissingResidualReceipt :
    Pack.HEPDataResidualProviderFirstMissingReceipt →
    HEPDataResidualProviderPayloadFirstMissingOutcome
  reportResidualChainPresentButNonPromoting :
    HEPDataResidualProviderPayloadFirstMissingOutcome

canonicalHEPDataResidualProviderPayloadFirstMissingOutcomes :
  List HEPDataResidualProviderPayloadFirstMissingOutcome
canonicalHEPDataResidualProviderPayloadFirstMissingOutcomes =
  reportFirstMissingResidualReceipt Pack.firstMissingResidualObservableClass
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingExactSelectedResidualObservable
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingChecksumBoundSelection
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingBaselineOrInvarianceModel
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingResidualDefinition
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingNonCollapseWitness
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingCalibrationCovariance
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingTheoremSideProjection
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingDefectProjection
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingResidualComparisonLaw
  ∷ reportFirstMissingResidualReceipt Pack.firstMissingAcceptedAuthorityRoute
  ∷ reportResidualChainPresentButNonPromoting
  ∷ []

record HEPDataResidualProviderPayloadIntakeFilter : Setω where
  field
    receiptRequestPack :
      Pack.HEPDataResidualProviderReceiptRequestPack

    currentReceiptPackStatus :
      Pack.HEPDataResidualProviderReceiptRequestPackStatus

    currentIntakeStatus :
      HEPDataResidualProviderPayloadIntakeStatus

    requiredPayloadFields :
      List HEPDataResidualProviderPayloadField

    requiredPayloadFieldsAreCanonical :
      requiredPayloadFields
      ≡
      canonicalHEPDataResidualProviderPayloadFields

    residualRequiredReceipts :
      List Pack.HEPDataResidualProviderRequiredReceipt

    residualRequiredReceiptsAreCanonical :
      residualRequiredReceipts
      ≡
      Pack.canonicalHEPDataResidualProviderRequiredReceipts

    firstMissingPolicy :
      List Pack.HEPDataResidualProviderFirstMissingReceipt

    firstMissingPolicyIsCanonical :
      firstMissingPolicy
      ≡
      Pack.canonicalHEPDataResidualProviderFirstMissingPolicy

    firstMissingOutcomes :
      List HEPDataResidualProviderPayloadFirstMissingOutcome

    intakeFilterRule :
      String

    providerPayloadFieldNames :
      List String

    providerPayloadFieldNamesMatchPack :
      providerPayloadFieldNames
      ≡
      Pack.HEPDataResidualProviderPayloadRequest.exactRequiredPayloadFields
        Pack.canonicalHEPDataResidualProviderPayloadRequest

    firstMissingReportingRule :
      String

    promotionGateRule :
      String

    governanceBoundary :
      List String

    diagramNodeText :
      String

    diagramEdgeText :
      String

canonicalHEPDataResidualProviderPayloadIntakeFilter :
  HEPDataResidualProviderPayloadIntakeFilter
canonicalHEPDataResidualProviderPayloadIntakeFilter =
  record
    { receiptRequestPack =
        Pack.canonicalHEPDataResidualProviderReceiptRequestPack
    ; currentReceiptPackStatus =
        Pack.blockedAwaitingResidualProviderReceiptChain
    ; currentIntakeStatus =
        intakeAwaitingProviderPayload
    ; requiredPayloadFields =
        canonicalHEPDataResidualProviderPayloadFields
    ; requiredPayloadFieldsAreCanonical =
        refl
    ; residualRequiredReceipts =
        Pack.canonicalHEPDataResidualProviderRequiredReceipts
    ; residualRequiredReceiptsAreCanonical =
        refl
    ; firstMissingPolicy =
        Pack.canonicalHEPDataResidualProviderFirstMissingPolicy
    ; firstMissingPolicyIsCanonical =
        refl
    ; firstMissingOutcomes =
        canonicalHEPDataResidualProviderPayloadFirstMissingOutcomes
    ; intakeFilterRule =
        "A provider payload may pass residual intake only after every residual-specific required receipt in Pack.canonicalHEPDataResidualProviderRequiredReceipts is present and mutually bound"
    ; providerPayloadFieldNames =
        Pack.HEPDataResidualProviderPayloadRequest.exactRequiredPayloadFields
          Pack.canonicalHEPDataResidualProviderPayloadRequest
    ; providerPayloadFieldNamesMatchPack =
        refl
    ; firstMissingReportingRule =
        "If any residual receipt is unavailable, intake reports exactly the earliest missing receipt according to Pack.canonicalHEPDataResidualProviderFirstMissingPolicy"
    ; promotionGateRule =
        "Passing residual payload intake is necessary but not sufficient for W3/W4/W5/W8 promotion; later external promotion receipts remain independent gates"
    ; governanceBoundary =
        "No fake HEPData data is accepted by this intake surface"
        ∷ "No authority token is constructed by this intake surface"
        ∷ "No local residual source candidate is promoted by this intake surface"
        ∷ "No raw saturated values are admitted as provider payload receipts"
        ∷ "No selected observable or empirical receipt is constructed here"
        ∷ []
    ; diagramNodeText =
        "rectangle \"HEP-R8\\nresidual provider payload intake\\npayload field filter\\nfirst-missing outcome diagnostics\\nnon-promoting\" as HEPDATA_HEPR8 #dcfce7"
    ; diagramEdgeText =
        "HEPDATA_HEPR4 --> HEPDATA_HEPR8 : receipt request pack supplies canonical residual chain + first-missing policy\nHEPDATA_HEPR8 --> Plateau : blocked unless payload passes residualObservableClass through acceptedAuthorityRoute receipts\nHEPDATA_HEPR8 --> W3 : no accepted-authority promotion from intake alone\nHEPDATA_HEPR8 --> W4 : no calibration promotion from intake alone\nHEPDATA_HEPR8 --> W5 : no physical closure promotion from intake alone\nHEPDATA_HEPR8 --> W8 : no origin receipt promotion from intake alone"
    }
