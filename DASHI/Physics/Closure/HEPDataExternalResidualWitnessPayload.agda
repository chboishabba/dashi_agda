module DASHI.Physics.Closure.HEPDataExternalResidualWitnessPayload where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataNonCollapseObservableObligation as NonCollapse
import DASHI.Physics.Closure.HEPDataObservableSchema as HEP
import DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate as Gate
import DASHI.Physics.Closure.HEPDataResidualProviderPayloadIntake as Intake
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack

------------------------------------------------------------------------
-- HEPData external residual witness payload.
--
-- This module names the minimal typed provider payload surface for the
-- residual nonCollapseWitnessReceipt.  It does not construct a HEPData datum:
-- the selected observable is an input index, and the external receipt remains
-- the constructorless authority field from HEPDataNonCollapseObservableObligation.

data HEPDataExternalResidualWitnessPayloadStatus : Set where
  blockedAwaitingConcreteProviderWitnessPayload :
    HEPDataExternalResidualWitnessPayloadStatus

data HEPDataExternalResidualWitnessPayloadField : Set where
  payloadExternallySelectedObservable :
    HEPDataExternalResidualWitnessPayloadField
  payloadExternalNonCollapseWitnessReceipt :
    HEPDataExternalResidualWitnessPayloadField
  payloadObservationOrBinDomain :
    HEPDataExternalResidualWitnessPayloadField
  payloadResidualProfileDomain :
    HEPDataExternalResidualWitnessPayloadField
  payloadDefectDiscriminatorDomain :
    HEPDataExternalResidualWitnessPayloadField
  payloadObservationOrBinPair :
    HEPDataExternalResidualWitnessPayloadField
  payloadObservationOrBinDistinctness :
    HEPDataExternalResidualWitnessPayloadField
  payloadResidualProfileMap :
    HEPDataExternalResidualWitnessPayloadField
  payloadResidualProfileDistinction :
    HEPDataExternalResidualWitnessPayloadField
  payloadNotConstantProofTarget :
    HEPDataExternalResidualWitnessPayloadField
  payloadDefectDiscriminatorMap :
    HEPDataExternalResidualWitnessPayloadField
  payloadDefectDiscriminatorDistinction :
    HEPDataExternalResidualWitnessPayloadField
  payloadDefectDiscriminatorPreservation :
    HEPDataExternalResidualWitnessPayloadField
  payloadCovarianceAdequacyLabel :
    HEPDataExternalResidualWitnessPayloadField
  payloadComparisonLawSchemaMatch :
    HEPDataExternalResidualWitnessPayloadField
  payloadAuthorityDependencies :
    HEPDataExternalResidualWitnessPayloadField

canonicalHEPDataExternalResidualWitnessPayloadFields :
  List HEPDataExternalResidualWitnessPayloadField
canonicalHEPDataExternalResidualWitnessPayloadFields =
  payloadExternallySelectedObservable
  ∷ payloadExternalNonCollapseWitnessReceipt
  ∷ payloadObservationOrBinDomain
  ∷ payloadResidualProfileDomain
  ∷ payloadDefectDiscriminatorDomain
  ∷ payloadObservationOrBinPair
  ∷ payloadObservationOrBinDistinctness
  ∷ payloadResidualProfileMap
  ∷ payloadResidualProfileDistinction
  ∷ payloadNotConstantProofTarget
  ∷ payloadDefectDiscriminatorMap
  ∷ payloadDefectDiscriminatorDistinction
  ∷ payloadDefectDiscriminatorPreservation
  ∷ payloadCovarianceAdequacyLabel
  ∷ payloadComparisonLawSchemaMatch
  ∷ payloadAuthorityDependencies
  ∷ []

record HEPDataExternalResidualWitnessPayload
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    externalNonCollapseWitnessReceipt :
      NonCollapse.HEPDataExternalNonCollapseWitnessReceipt

    nonCollapseWitness :
      NonCollapse.HEPDataNonCollapseWitness observable

    boundProviderReceipt :
      Pack.HEPDataResidualProviderRequiredReceipt

    boundProviderReceiptIsNonCollapse :
      boundProviderReceipt
      ≡
      Pack.nonCollapseWitnessReceipt

    boundIntakePayloadField :
      Intake.HEPDataResidualProviderPayloadField

    boundIntakePayloadFieldIsNonCollapse :
      boundIntakePayloadField
      ≡
      Intake.payloadNonCollapseWitnessReceipt

    boundGatePayloadField :
      Gate.HEPDataResidualBridgeGateRequiredPayloadField

    boundGatePayloadFieldIsNonCollapse :
      boundGatePayloadField
      ≡
      Gate.gateRequiresNonCollapseWitness

externalResidualWitnessPayloadToReceiptTarget :
  {observable : HEP.HEPDataObservable} →
  HEPDataExternalResidualWitnessPayload observable →
  NonCollapse.HEPDataNonCollapseWitnessReceiptTarget observable
externalResidualWitnessPayloadToReceiptTarget payload =
  record
    { externalNonCollapseWitnessReceipt =
        HEPDataExternalResidualWitnessPayload.externalNonCollapseWitnessReceipt
          payload
    ; nonCollapseWitness =
        HEPDataExternalResidualWitnessPayload.nonCollapseWitness payload
    }

externalResidualWitnessPayloadImpossibleHere :
  {observable : HEP.HEPDataObservable} →
  HEPDataExternalResidualWitnessPayload observable →
  ⊥
externalResidualWitnessPayloadImpossibleHere payload =
  NonCollapse.externalNonCollapseWitnessReceiptImpossibleHere
    (HEPDataExternalResidualWitnessPayload.externalNonCollapseWitnessReceipt
      payload)

record HEPDataExternalResidualWitnessPayloadDiagnostic : Setω where
  field
    receiptRequestPack :
      Pack.HEPDataResidualProviderReceiptRequestPack

    payloadIntakeFilter :
      Intake.HEPDataResidualProviderPayloadIntakeFilter

    authorityGate :
      Gate.HEPDataResidualBridgeAuthorityGate

    status :
      HEPDataExternalResidualWitnessPayloadStatus

    currentRepoHasConcretePayload :
      Bool

    requiredPayloadFields :
      List HEPDataExternalResidualWitnessPayloadField

    requiredPayloadFieldsAreCanonical :
      requiredPayloadFields
      ≡
      canonicalHEPDataExternalResidualWitnessPayloadFields

    providerReceiptName :
      Pack.HEPDataResidualProviderRequiredReceipt

    providerReceiptNameIsNonCollapse :
      providerReceiptName
      ≡
      Pack.nonCollapseWitnessReceipt

    intakePayloadField :
      Intake.HEPDataResidualProviderPayloadField

    intakePayloadFieldIsNonCollapse :
      intakePayloadField
      ≡
      Intake.payloadNonCollapseWitnessReceipt

    gatePayloadField :
      Gate.HEPDataResidualBridgeGateRequiredPayloadField

    gatePayloadFieldIsNonCollapse :
      gatePayloadField
      ≡
      Gate.gateRequiresNonCollapseWitness

    impossiblePayloadHere :
      {observable : HEP.HEPDataObservable} →
      HEPDataExternalResidualWitnessPayload observable →
      ⊥

    nonFabricationBoundary :
      List String

    remainingExternalFields :
      List String

    validationTarget :
      String

canonicalHEPDataExternalResidualWitnessPayloadDiagnostic :
  HEPDataExternalResidualWitnessPayloadDiagnostic
canonicalHEPDataExternalResidualWitnessPayloadDiagnostic =
  record
    { receiptRequestPack =
        Pack.canonicalHEPDataResidualProviderReceiptRequestPack
    ; payloadIntakeFilter =
        Intake.canonicalHEPDataResidualProviderPayloadIntakeFilter
    ; authorityGate =
        Gate.canonicalHEPDataResidualBridgeAuthorityGate
    ; status =
        blockedAwaitingConcreteProviderWitnessPayload
    ; currentRepoHasConcretePayload =
        false
    ; requiredPayloadFields =
        canonicalHEPDataExternalResidualWitnessPayloadFields
    ; requiredPayloadFieldsAreCanonical =
        refl
    ; providerReceiptName =
        Pack.nonCollapseWitnessReceipt
    ; providerReceiptNameIsNonCollapse =
        refl
    ; intakePayloadField =
        Intake.payloadNonCollapseWitnessReceipt
    ; intakePayloadFieldIsNonCollapse =
        refl
    ; gatePayloadField =
        Gate.gateRequiresNonCollapseWitness
    ; gatePayloadFieldIsNonCollapse =
        refl
    ; impossiblePayloadHere =
        externalResidualWitnessPayloadImpossibleHere
    ; nonFabricationBoundary =
        "The selected HEPData observable is an index supplied to the payload type, not constructed here"
        ∷ "The external non-collapse witness receipt is constructorless in the current repo"
        ∷ "The payload can be converted to HEPDataNonCollapseWitnessReceiptTarget only after the external receipt and selected observable already exist"
        ∷ "This diagnostic does not alter HEPDataResidualProviderReceiptRequestPack, PayloadIntake, or AuthorityGate promotion boundaries"
        ∷ []
    ; remainingExternalFields =
        "externally selected checksum-bound HEPData residual observable"
        ∷ "provider-supplied HEPDataExternalNonCollapseWitnessReceipt"
        ∷ "two selected observations or bins from that observable"
        ∷ "proof that the observations or bins are distinct"
        ∷ "residual profile domain and residual profile map"
        ∷ "proof that the selected residual profiles are distinct"
        ∷ "not-constant proof target for the residual profile"
        ∷ "defect discriminator domain and discriminator map"
        ∷ "proof that the selected defect discriminators are distinct"
        ∷ "proof that discriminator distinction is preserved by residual profiles"
        ∷ "uncertainty/covariance adequacy label and justification"
        ∷ "comparison-law label matching the observable schema target"
        ∷ "provider, accepted authority, comparison-law, and covariance receipt dependencies"
        ∷ []
    ; validationTarget =
        "agda DASHI/Physics/Closure/HEPDataExternalResidualWitnessPayload.agda"
    }
