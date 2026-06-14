module DASHI.Promotion.Cs133NumericAuthorityPayloadRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload

------------------------------------------------------------------------
-- Cs-133 SI defining-constant payload request.
--
-- This module is request-shaped only.  It names the exact SI row and the
-- raw textual value requested from that row, but it does not load an
-- authority artifact, accept a token, parse a numeric carrier, or promote a
-- numeric value.

data Cs133PayloadFieldKey : Set where
  authorityArtifactKey : Cs133PayloadFieldKey
  authorityArtifactSha256Key : Cs133PayloadFieldKey
  authorityAccessDateEvidenceKey : Cs133PayloadFieldKey
  rawNumericValueTextKey : Cs133PayloadFieldKey
  rawUncertaintyTextKey : Cs133PayloadFieldKey
  parsedNumericCarrierPayloadKey : Cs133PayloadFieldKey
  covarianceMatrixOrIndependenceReceiptKey : Cs133PayloadFieldKey
  consumerValueIngestionReceiptKey : Cs133PayloadFieldKey

record Cs133PayloadFields : Set₁ where
  field
    authorityArtifact :
      Payload.PayloadSchemaField
    authorityArtifactSha256 :
      Payload.PayloadSchemaField
    authorityAccessDateEvidence :
      Payload.PayloadSchemaField
    rawNumericValueText :
      String
    rawUncertaintyText :
      String
    parsedNumericCarrierPayload :
      Payload.PayloadSchemaField
    covarianceMatrixOrIndependenceReceipt :
      Payload.PayloadSchemaField
    consumerValueIngestionReceipt :
      Payload.PayloadSchemaField

open Cs133PayloadFields public

canonicalCs133PayloadFields : Cs133PayloadFields
canonicalCs133PayloadFields = record
  { authorityArtifact =
      Payload.missingAuthorityArtifactField
  ; authorityArtifactSha256 =
      Payload.missingArtifactDigestField
  ; authorityAccessDateEvidence =
      Payload.missingAccessEvidenceField
  ; rawNumericValueText =
      "9 192 631 770"
  ; rawUncertaintyText =
      "0"
  ; parsedNumericCarrierPayload =
      Payload.missingParsedCarrierField
  ; covarianceMatrixOrIndependenceReceipt =
      Payload.missingCovarianceField
  ; consumerValueIngestionReceipt =
      Payload.missingConsumerIngestionReceiptField
  }

canonicalCs133FieldKeys : List Cs133PayloadFieldKey
canonicalCs133FieldKeys =
  authorityArtifactKey
  ∷ authorityArtifactSha256Key
  ∷ authorityAccessDateEvidenceKey
  ∷ rawNumericValueTextKey
  ∷ rawUncertaintyTextKey
  ∷ parsedNumericCarrierPayloadKey
  ∷ covarianceMatrixOrIndependenceReceiptKey
  ∷ consumerValueIngestionReceiptKey
  ∷ []

canonicalCs133AuthorityFamily : String
canonicalCs133AuthorityFamily =
  "BIPM SI defining constants"

canonicalCs133SourceUri : String
canonicalCs133SourceUri =
  "https://www.bipm.org/en/measurement-units/si-defining-constants"

canonicalCs133RegistryRow : Registry.KnownConstantSlot
canonicalCs133RegistryRow =
  Registry.mkConstant
    "caesium-133 hyperfine transition frequency"
    "Delta nu Cs"
    "9192631770"
    "Hz"
    Registry.exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "time/frequency"
    ∷ "measurement"
    ∷ "runtime clock provenance"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "unit definition only; no dynamics theorem"
    ∷ []
    )

record Cs133NumericAuthorityPayloadRequest : Set₁ where
  field
    requestLabel :
      String
    sourceRegistry :
      Registry.ConstantsRegistry
    sourceRegistryRow :
      Registry.KnownConstantSlot
    sourcePayloadValidator :
      Payload.NumericAuthorityPayloadValidatorReceipt
    payloadFields :
      Cs133PayloadFields
    payloadFieldKeys :
      List Cs133PayloadFieldKey
    payloadFieldKeyCount :
      Nat
    payloadFieldKeyCountIs8 :
      payloadFieldKeyCount ≡ 8
    symbol :
      String
    authorityFamily :
      String
    unitConvention :
      String
    sourceUri :
      String
    exactZeroUncertaintyText :
      String
    atomicClockSISecondBridgeCrossReference :
      String
    authorityArtifactPresent :
      Bool
    authorityArtifactPresentIsFalse :
      authorityArtifactPresent ≡ false
    authorityArtifactSha256Present :
      Bool
    authorityArtifactSha256PresentIsFalse :
      authorityArtifactSha256Present ≡ false
    authorityAccessDateEvidencePresent :
      Bool
    authorityAccessDateEvidencePresentIsFalse :
      authorityAccessDateEvidencePresent ≡ false
    parsedNumericCarrierPayloadPresent :
      Bool
    parsedNumericCarrierPayloadPresentIsFalse :
      parsedNumericCarrierPayloadPresent ≡ false
    covarianceMatrixOrIndependenceReceiptPresent :
      Bool
    covarianceMatrixOrIndependenceReceiptPresentIsFalse :
      covarianceMatrixOrIndependenceReceiptPresent ≡ false
    consumerIngestionReceiptPresent :
      Bool
    consumerIngestionReceiptPresentIsFalse :
      consumerIngestionReceiptPresent ≡ false
    acceptedAuthorityTokenPresent :
      Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValuePromoted :
      Bool
    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false
    externalArtifactLoaded :
      Bool
    externalArtifactLoadedIsFalse :
      externalArtifactLoaded ≡ false
    externalArtifactAccepted :
      Bool
    externalArtifactAcceptedIsFalse :
      externalArtifactAccepted ≡ false
    inheritsValidatorFailClosedTokenGuard :
      acceptedAuthorityTokenPresent
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresent
        sourcePayloadValidator
    inheritsValidatorFailClosedPromotionGuard :
      numericValuePromoted
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.numericValuePromoted
        sourcePayloadValidator

open Cs133NumericAuthorityPayloadRequest public

canonicalCs133NumericAuthorityPayloadRequest :
  Cs133NumericAuthorityPayloadRequest
canonicalCs133NumericAuthorityPayloadRequest = record
  { requestLabel =
      "Cs-133 exact SI defining-constant numeric authority payload request"
  ; sourceRegistry =
      Registry.repoWideConstantsRegistry
  ; sourceRegistryRow =
      canonicalCs133RegistryRow
  ; sourcePayloadValidator =
      Payload.canonicalNumericAuthorityPayloadValidatorReceipt
  ; payloadFields =
      canonicalCs133PayloadFields
  ; payloadFieldKeys =
      canonicalCs133FieldKeys
  ; payloadFieldKeyCount =
      Payload.listCount canonicalCs133FieldKeys
  ; payloadFieldKeyCountIs8 =
      refl
  ; symbol =
      "Delta nu Cs"
  ; authorityFamily =
      canonicalCs133AuthorityFamily
  ; unitConvention =
      "Hz"
  ; sourceUri =
      canonicalCs133SourceUri
  ; exactZeroUncertaintyText =
      Cs133PayloadFields.rawUncertaintyText canonicalCs133PayloadFields
  ; atomicClockSISecondBridgeCrossReference =
      "DASHI.Promotion.AtomicClockSISecondBridge"
  ; authorityArtifactPresent =
      false
  ; authorityArtifactPresentIsFalse =
      refl
  ; authorityArtifactSha256Present =
      false
  ; authorityArtifactSha256PresentIsFalse =
      refl
  ; authorityAccessDateEvidencePresent =
      false
  ; authorityAccessDateEvidencePresentIsFalse =
      refl
  ; parsedNumericCarrierPayloadPresent =
      false
  ; parsedNumericCarrierPayloadPresentIsFalse =
      refl
  ; covarianceMatrixOrIndependenceReceiptPresent =
      false
  ; covarianceMatrixOrIndependenceReceiptPresentIsFalse =
      refl
  ; consumerIngestionReceiptPresent =
      false
  ; consumerIngestionReceiptPresentIsFalse =
      refl
  ; acceptedAuthorityTokenPresent =
      false
  ; acceptedAuthorityTokenPresentIsFalse =
      refl
  ; numericValuePromoted =
      false
  ; numericValuePromotedIsFalse =
      refl
  ; externalArtifactLoaded =
      false
  ; externalArtifactLoadedIsFalse =
      refl
  ; externalArtifactAccepted =
      false
  ; externalArtifactAcceptedIsFalse =
      refl
  ; inheritsValidatorFailClosedTokenGuard =
      refl
  ; inheritsValidatorFailClosedPromotionGuard =
      refl
  }

canonicalCs133RawNumericValueTextIsSpacedSIValue :
  Cs133PayloadFields.rawNumericValueText canonicalCs133PayloadFields
  ≡ "9 192 631 770"
canonicalCs133RawNumericValueTextIsSpacedSIValue = refl

canonicalCs133RawUncertaintyTextIsExactZero :
  Cs133PayloadFields.rawUncertaintyText canonicalCs133PayloadFields
  ≡ "0"
canonicalCs133RawUncertaintyTextIsExactZero = refl

canonicalCs133RegistryRowSymbolMatchesRequest :
  Registry.KnownConstantSlot.symbol
    (Cs133NumericAuthorityPayloadRequest.sourceRegistryRow
      canonicalCs133NumericAuthorityPayloadRequest)
  ≡
  Cs133NumericAuthorityPayloadRequest.symbol
    canonicalCs133NumericAuthorityPayloadRequest
canonicalCs133RegistryRowSymbolMatchesRequest = refl

canonicalCs133RegistryRowValueIsUnspacedExactInteger :
  Registry.KnownConstantSlot.value canonicalCs133RegistryRow
  ≡ "9192631770"
canonicalCs133RegistryRowValueIsUnspacedExactInteger = refl

canonicalCs133RegistryRowUnitMatchesRequest :
  Registry.KnownConstantSlot.unit canonicalCs133RegistryRow
  ≡
  Cs133NumericAuthorityPayloadRequest.unitConvention
    canonicalCs133NumericAuthorityPayloadRequest
canonicalCs133RegistryRowUnitMatchesRequest = refl

canonicalCs133RegistryRowIsSIDefiningConstant :
  Registry.KnownConstantSlot.authorityClass canonicalCs133RegistryRow
  ≡ Registry.exactSIDefiningConstant
canonicalCs133RegistryRowIsSIDefiningConstant = refl

canonicalCs133PayloadFieldKeyCountIs8 :
  Cs133NumericAuthorityPayloadRequest.payloadFieldKeyCount
    canonicalCs133NumericAuthorityPayloadRequest
  ≡ 8
canonicalCs133PayloadFieldKeyCountIs8 = refl

canonicalCs133AuthorityArtifactPresentIsFalse :
  Cs133NumericAuthorityPayloadRequest.authorityArtifactPresent
    canonicalCs133NumericAuthorityPayloadRequest
  ≡ false
canonicalCs133AuthorityArtifactPresentIsFalse = refl

canonicalCs133AuthorityArtifactSha256PresentIsFalse :
  Cs133NumericAuthorityPayloadRequest.authorityArtifactSha256Present
    canonicalCs133NumericAuthorityPayloadRequest
  ≡ false
canonicalCs133AuthorityArtifactSha256PresentIsFalse = refl

canonicalCs133ConsumerIngestionReceiptPresentIsFalse :
  Cs133NumericAuthorityPayloadRequest.consumerIngestionReceiptPresent
    canonicalCs133NumericAuthorityPayloadRequest
  ≡ false
canonicalCs133ConsumerIngestionReceiptPresentIsFalse = refl

canonicalCs133AcceptedAuthorityTokenPresentIsFalse :
  Cs133NumericAuthorityPayloadRequest.acceptedAuthorityTokenPresent
    canonicalCs133NumericAuthorityPayloadRequest
  ≡ false
canonicalCs133AcceptedAuthorityTokenPresentIsFalse = refl

canonicalCs133NumericValuePromotedIsFalse :
  Cs133NumericAuthorityPayloadRequest.numericValuePromoted
    canonicalCs133NumericAuthorityPayloadRequest
  ≡ false
canonicalCs133NumericValuePromotedIsFalse = refl

canonicalCs133ExternalArtifactLoadedIsFalse :
  Cs133NumericAuthorityPayloadRequest.externalArtifactLoaded
    canonicalCs133NumericAuthorityPayloadRequest
  ≡ false
canonicalCs133ExternalArtifactLoadedIsFalse = refl

canonicalCs133ExternalArtifactAcceptedIsFalse :
  Cs133NumericAuthorityPayloadRequest.externalArtifactAccepted
    canonicalCs133NumericAuthorityPayloadRequest
  ≡ false
canonicalCs133ExternalArtifactAcceptedIsFalse = refl

canonicalCs133ValidatorTokenGuardCrossCheck :
  Cs133NumericAuthorityPayloadRequest.acceptedAuthorityTokenPresent
    canonicalCs133NumericAuthorityPayloadRequest
  ≡
  Payload.NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresent
    Payload.canonicalNumericAuthorityPayloadValidatorReceipt
canonicalCs133ValidatorTokenGuardCrossCheck = refl

canonicalCs133ValidatorPromotionGuardCrossCheck :
  Cs133NumericAuthorityPayloadRequest.numericValuePromoted
    canonicalCs133NumericAuthorityPayloadRequest
  ≡
  Payload.NumericAuthorityPayloadValidatorReceipt.numericValuePromoted
    Payload.canonicalNumericAuthorityPayloadValidatorReceipt
canonicalCs133ValidatorPromotionGuardCrossCheck = refl
