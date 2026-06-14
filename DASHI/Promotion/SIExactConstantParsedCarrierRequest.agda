module DASHI.Promotion.SIExactConstantParsedCarrierRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.Cs133NumericAuthorityPayloadRequest as Cs133
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload
import DASHI.Promotion.PlanckHbarSIPayloadRequest as Planck
import DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest as SIArtifact

------------------------------------------------------------------------
-- Parsed carrier request surface for exact SI defining constants.
--
-- This module supplies typed, finite carrier shapes for the exact textual
-- rows Delta nu Cs, c, and h.  It intentionally does not claim that an
-- external artifact was downloaded, accepted, or promoted.  The carriers
-- are structural: integers are Nat/text pairs, and h is decimal/scientific
-- notation represented by sign, digits, decimal scale, and exponent.

data DecimalDigit : Set where
  d0 : DecimalDigit
  d1 : DecimalDigit
  d2 : DecimalDigit
  d3 : DecimalDigit
  d4 : DecimalDigit
  d5 : DecimalDigit
  d6 : DecimalDigit
  d7 : DecimalDigit
  d8 : DecimalDigit
  d9 : DecimalDigit

data IntegerSign : Set where
  positiveSign : IntegerSign
  negativeSign : IntegerSign

record ExactIntegerTextCarrier : Set where
  field
    sign :
      IntegerSign
    absoluteValue :
      Nat
    canonicalText :
      String
    rawAuthorityText :
      String
    digitCount :
      Nat
    rawTextMatchesRequest :
      rawAuthorityText ≡ canonicalText
    uncertaintyText :
      String
    uncertaintyTextIsZero :
      uncertaintyText ≡ "0"
    exactBySIDefinition :
      Bool
    exactBySIDefinitionIsTrue :
      exactBySIDefinition ≡ true

open ExactIntegerTextCarrier public

record ExactScientificDecimalCarrier : Set where
  field
    sign :
      IntegerSign
    significandDigits :
      List DecimalDigit
    significandDigitCount :
      Nat
    decimalPlaces :
      Nat
    exponentSign :
      IntegerSign
    exponentMagnitude :
      Nat
    rawAuthorityText :
      String
    compactRegistryText :
      String
    unitText :
      String
    uncertaintyText :
      String
    uncertaintyTextIsZero :
      uncertaintyText ≡ "0"
    usesFloatCarrier :
      Bool
    usesFloatCarrierIsFalse :
      usesFloatCarrier ≡ false
    exactBySIDefinition :
      Bool
    exactBySIDefinitionIsTrue :
      exactBySIDefinition ≡ true

open ExactScientificDecimalCarrier public

data SIExactParsedCarrierKind : Set where
  naturalIntegerTextCarrier : SIExactParsedCarrierKind
  exactMetrePerSecondIntegerCarrier : SIExactParsedCarrierKind
  exactScientificDecimalTextCarrier : SIExactParsedCarrierKind

data SIExactParsedCarrierFieldKey : Set where
  sourceManifestRefKey : SIExactParsedCarrierFieldKey
  sourceRegistryRowRefKey : SIExactParsedCarrierFieldKey
  rawTextKey : SIExactParsedCarrierFieldKey
  compactRegistryTextKey : SIExactParsedCarrierFieldKey
  unitTextKey : SIExactParsedCarrierFieldKey
  parsedCarrierShapeKey : SIExactParsedCarrierFieldKey
  rawTextMatchWitnessKey : SIExactParsedCarrierFieldKey
  zeroUncertaintyWitnessKey : SIExactParsedCarrierFieldKey
  exactnessWitnessKey : SIExactParsedCarrierFieldKey
  failClosedPromotionGuardKey : SIExactParsedCarrierFieldKey

canonicalSIExactParsedCarrierFieldKeys :
  List SIExactParsedCarrierFieldKey
canonicalSIExactParsedCarrierFieldKeys =
  sourceManifestRefKey
  ∷ sourceRegistryRowRefKey
  ∷ rawTextKey
  ∷ compactRegistryTextKey
  ∷ unitTextKey
  ∷ parsedCarrierShapeKey
  ∷ rawTextMatchWitnessKey
  ∷ zeroUncertaintyWitnessKey
  ∷ exactnessWitnessKey
  ∷ failClosedPromotionGuardKey
  ∷ []

canonicalDeltaNuCsNaturalCarrier : ExactIntegerTextCarrier
canonicalDeltaNuCsNaturalCarrier =
  record
    { sign =
        positiveSign
    ; absoluteValue =
        9192631770
    ; canonicalText =
        "9 192 631 770"
    ; rawAuthorityText =
        SIArtifact.rawValueText
          SIArtifact.canonicalDeltaNuCsAuthorityArtifactRowRequest
    ; digitCount =
        10
    ; rawTextMatchesRequest =
        refl
    ; uncertaintyText =
        SIArtifact.exactZeroUncertaintyText
    ; uncertaintyTextIsZero =
        refl
    ; exactBySIDefinition =
        true
    ; exactBySIDefinitionIsTrue =
        refl
    }

canonicalCMetrePerSecondIntegerCarrier : ExactIntegerTextCarrier
canonicalCMetrePerSecondIntegerCarrier =
  record
    { sign =
        positiveSign
    ; absoluteValue =
        299792458
    ; canonicalText =
        "299 792 458"
    ; rawAuthorityText =
        SIArtifact.rawValueText
          SIArtifact.canonicalCAuthorityArtifactRowRequest
    ; digitCount =
        9
    ; rawTextMatchesRequest =
        refl
    ; uncertaintyText =
        SIArtifact.exactZeroUncertaintyText
    ; uncertaintyTextIsZero =
        refl
    ; exactBySIDefinition =
        true
    ; exactBySIDefinitionIsTrue =
        refl
    }

canonicalHScientificDecimalCarrier : ExactScientificDecimalCarrier
canonicalHScientificDecimalCarrier =
  record
    { sign =
        positiveSign
    ; significandDigits =
        d6 ∷ d6 ∷ d2 ∷ d6 ∷ d0 ∷ d7 ∷ d0 ∷ d1 ∷ d5 ∷ []
    ; significandDigitCount =
        9
    ; decimalPlaces =
        8
    ; exponentSign =
        negativeSign
    ; exponentMagnitude =
        34
    ; rawAuthorityText =
        SIArtifact.rawValueText
          SIArtifact.canonicalHAuthorityArtifactRowRequest
    ; compactRegistryText =
        Registry.KnownConstantSlot.value SIArtifact.canonicalHRegistryRow
    ; unitText =
        Registry.KnownConstantSlot.unit SIArtifact.canonicalHRegistryRow
    ; uncertaintyText =
        SIArtifact.exactZeroUncertaintyText
    ; uncertaintyTextIsZero =
        refl
    ; usesFloatCarrier =
        false
    ; usesFloatCarrierIsFalse =
        refl
    ; exactBySIDefinition =
        true
    ; exactBySIDefinitionIsTrue =
        refl
    }

record SIExactParsedCarrierRowRequest : Set₁ where
  field
    rowLabel :
      String
    carrierKind :
      SIExactParsedCarrierKind
    sourceRegistryRow :
      Registry.KnownConstantSlot
    sourceArtifactRow :
      SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest
    sourceManifest :
      SIArtifact.SIDefiningConstantsAuthorityArtifactRequestManifest
    sourceManifestRef :
      String
    sourceRegistryRowRef :
      String
    rawAuthorityText :
      String
    registryCompactText :
      String
    unitText :
      String
    uncertaintyText :
      String
    uncertaintyTextIsZero :
      uncertaintyText ≡ "0"
    rawTextMatchesArtifactRequest :
      rawAuthorityText ≡ SIArtifact.rawValueText sourceArtifactRow
    registryTextMatchesSourceRow :
      registryCompactText ≡ Registry.KnownConstantSlot.value sourceRegistryRow
    unitTextMatchesSourceRow :
      unitText ≡ Registry.KnownConstantSlot.unit sourceRegistryRow
    fieldKeys :
      List SIExactParsedCarrierFieldKey
    fieldKeyCount :
      Nat
    fieldKeyCountIs10 :
      fieldKeyCount ≡ 10
    parsedCarrierStructurallySupplied :
      Bool
    parsedCarrierStructurallySuppliedIsTrue :
      parsedCarrierStructurallySupplied ≡ true
    authorityArtifactPresent :
      Bool
    authorityArtifactPresentIsFalse :
      authorityArtifactPresent ≡ false
    acceptedAuthorityTokenPresent :
      Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    consumerIngestionReceiptPresent :
      Bool
    consumerIngestionReceiptPresentIsFalse :
      consumerIngestionReceiptPresent ≡ false
    numericValuePromoted :
      Bool
    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false
    externalArtifactAccepted :
      Bool
    externalArtifactAcceptedIsFalse :
      externalArtifactAccepted ≡ false
    failClosedTokenGuard :
      acceptedAuthorityTokenPresent
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresent
        SIArtifact.payloadValidator sourceManifest
    failClosedPromotionGuard :
      numericValuePromoted
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.numericValuePromoted
        SIArtifact.payloadValidator sourceManifest

open SIExactParsedCarrierRowRequest public

mkSIExactParsedCarrierRowRequest :
  String →
  SIExactParsedCarrierKind →
  Registry.KnownConstantSlot →
  SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest →
  String →
  String →
  String →
  SIExactParsedCarrierRowRequest
mkSIExactParsedCarrierRowRequest label kind row artifactRow rowRef rawText compactText =
  record
    { rowLabel =
        label
    ; carrierKind =
        kind
    ; sourceRegistryRow =
        row
    ; sourceArtifactRow =
        artifactRow
    ; sourceManifest =
        SIArtifact.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; sourceManifestRef =
        "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest"
    ; sourceRegistryRowRef =
        rowRef
    ; rawAuthorityText =
        rawText
    ; registryCompactText =
        compactText
    ; unitText =
        Registry.KnownConstantSlot.unit row
    ; uncertaintyText =
        SIArtifact.exactZeroUncertaintyText
    ; uncertaintyTextIsZero =
        refl
    ; rawTextMatchesArtifactRequest =
        refl
    ; registryTextMatchesSourceRow =
        refl
    ; unitTextMatchesSourceRow =
        refl
    ; fieldKeys =
        canonicalSIExactParsedCarrierFieldKeys
    ; fieldKeyCount =
        Payload.listCount canonicalSIExactParsedCarrierFieldKeys
    ; fieldKeyCountIs10 =
        refl
    ; parsedCarrierStructurallySupplied =
        true
    ; parsedCarrierStructurallySuppliedIsTrue =
        refl
    ; authorityArtifactPresent =
        false
    ; authorityArtifactPresentIsFalse =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; consumerIngestionReceiptPresent =
        false
    ; consumerIngestionReceiptPresentIsFalse =
        refl
    ; numericValuePromoted =
        false
    ; numericValuePromotedIsFalse =
        refl
    ; externalArtifactAccepted =
        false
    ; externalArtifactAcceptedIsFalse =
        refl
    ; failClosedTokenGuard =
        refl
    ; failClosedPromotionGuard =
        refl
    }

canonicalDeltaNuCsParsedCarrierRowRequest :
  SIExactParsedCarrierRowRequest
canonicalDeltaNuCsParsedCarrierRowRequest =
  mkSIExactParsedCarrierRowRequest
    "Delta nu Cs parsed natural/integer-text carrier request"
    naturalIntegerTextCarrier
    SIArtifact.canonicalDeltaNuCsRegistryRow
    SIArtifact.canonicalDeltaNuCsAuthorityArtifactRowRequest
    SIArtifact.canonicalDeltaNuCsRegistrySourceRef
    (ExactIntegerTextCarrier.rawAuthorityText canonicalDeltaNuCsNaturalCarrier)
    (Registry.KnownConstantSlot.value SIArtifact.canonicalDeltaNuCsRegistryRow)

canonicalCParsedCarrierRowRequest :
  SIExactParsedCarrierRowRequest
canonicalCParsedCarrierRowRequest =
  mkSIExactParsedCarrierRowRequest
    "c exact integer metre-per-second parsed carrier request"
    exactMetrePerSecondIntegerCarrier
    SIArtifact.canonicalCRegistryRow
    SIArtifact.canonicalCAuthorityArtifactRowRequest
    SIArtifact.canonicalCRegistrySourceRef
    (ExactIntegerTextCarrier.rawAuthorityText
      canonicalCMetrePerSecondIntegerCarrier)
    (Registry.KnownConstantSlot.value SIArtifact.canonicalCRegistryRow)

canonicalHParsedCarrierRowRequest :
  SIExactParsedCarrierRowRequest
canonicalHParsedCarrierRowRequest =
  mkSIExactParsedCarrierRowRequest
    "h exact structural decimal/scientific parsed carrier request"
    exactScientificDecimalTextCarrier
    SIArtifact.canonicalHRegistryRow
    SIArtifact.canonicalHAuthorityArtifactRowRequest
    SIArtifact.canonicalHRegistrySourceRef
    (ExactScientificDecimalCarrier.rawAuthorityText
      canonicalHScientificDecimalCarrier)
    (ExactScientificDecimalCarrier.compactRegistryText
      canonicalHScientificDecimalCarrier)

record SIExactConstantParsedCarrierRequestManifest : Set₁ where
  field
    manifestLabel :
      String
    sourceArtifactManifest :
      SIArtifact.SIDefiningConstantsAuthorityArtifactRequestManifest
    cs133PayloadRequest :
      Cs133.Cs133NumericAuthorityPayloadRequest
    planckPayloadRequest :
      Planck.PlanckHbarSIPayloadRequest
    parsedCarrierRows :
      List SIExactParsedCarrierRowRequest
    parsedCarrierRowCount :
      Nat
    parsedCarrierRowCountIs3 :
      parsedCarrierRowCount ≡ 3
    fieldKeys :
      List SIExactParsedCarrierFieldKey
    fieldKeyCount :
      Nat
    fieldKeyCountIs10 :
      fieldKeyCount ≡ 10
    deltaNuCsCarrier :
      ExactIntegerTextCarrier
    cCarrier :
      ExactIntegerTextCarrier
    hCarrier :
      ExactScientificDecimalCarrier
    exactnessPolicyText :
      String
    rawTextMatchPolicyText :
      String
    failClosedPolicyText :
      String
    authorityArtifactPresent :
      Bool
    authorityArtifactPresentIsFalse :
      authorityArtifactPresent ≡ false
    acceptedAuthorityTokenPresent :
      Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    consumerIngestionReceiptPresent :
      Bool
    consumerIngestionReceiptPresentIsFalse :
      consumerIngestionReceiptPresent ≡ false
    anyNumericValuePromoted :
      Bool
    anyNumericValuePromotedIsFalse :
      anyNumericValuePromoted ≡ false
    externalArtifactAccepted :
      Bool
    externalArtifactAcceptedIsFalse :
      externalArtifactAccepted ≡ false
    failClosedTokenGuard :
      acceptedAuthorityTokenPresent
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresent
        (SIArtifact.payloadValidator sourceArtifactManifest)
    failClosedPromotionGuard :
      anyNumericValuePromoted
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.numericValuePromoted
        (SIArtifact.payloadValidator sourceArtifactManifest)

open SIExactConstantParsedCarrierRequestManifest public

canonicalSIExactConstantParsedCarrierRequestManifest :
  SIExactConstantParsedCarrierRequestManifest
canonicalSIExactConstantParsedCarrierRequestManifest =
  record
    { manifestLabel =
        "Exact SI defining constants parsed-carrier request manifest"
    ; sourceArtifactManifest =
        SIArtifact.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; cs133PayloadRequest =
        Cs133.canonicalCs133NumericAuthorityPayloadRequest
    ; planckPayloadRequest =
        Planck.canonicalPlanckHbarSIPayloadRequest
    ; parsedCarrierRows =
        canonicalDeltaNuCsParsedCarrierRowRequest
        ∷ canonicalCParsedCarrierRowRequest
        ∷ canonicalHParsedCarrierRowRequest
        ∷ []
    ; parsedCarrierRowCount =
        Payload.listCount
          ( canonicalDeltaNuCsParsedCarrierRowRequest
          ∷ canonicalCParsedCarrierRowRequest
          ∷ canonicalHParsedCarrierRowRequest
          ∷ []
          )
    ; parsedCarrierRowCountIs3 =
        refl
    ; fieldKeys =
        canonicalSIExactParsedCarrierFieldKeys
    ; fieldKeyCount =
        Payload.listCount canonicalSIExactParsedCarrierFieldKeys
    ; fieldKeyCountIs10 =
        refl
    ; deltaNuCsCarrier =
        canonicalDeltaNuCsNaturalCarrier
    ; cCarrier =
        canonicalCMetrePerSecondIntegerCarrier
    ; hCarrier =
        canonicalHScientificDecimalCarrier
    ; exactnessPolicyText =
        "all three rows are exact SI defining constants with uncertainty text 0"
    ; rawTextMatchPolicyText =
        "parsed carriers remain tied to raw authority text from the SI artifact request rows"
    ; failClosedPolicyText =
        "structural carrier availability does not imply authority-token acceptance, artifact acceptance, consumer ingestion, or numeric promotion"
    ; authorityArtifactPresent =
        false
    ; authorityArtifactPresentIsFalse =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; consumerIngestionReceiptPresent =
        false
    ; consumerIngestionReceiptPresentIsFalse =
        refl
    ; anyNumericValuePromoted =
        false
    ; anyNumericValuePromotedIsFalse =
        refl
    ; externalArtifactAccepted =
        false
    ; externalArtifactAcceptedIsFalse =
        refl
    ; failClosedTokenGuard =
        refl
    ; failClosedPromotionGuard =
        refl
    }

canonicalDeltaNuCsCarrierRawTextMatchesArtifactRow :
  ExactIntegerTextCarrier.rawAuthorityText canonicalDeltaNuCsNaturalCarrier
  ≡
  SIArtifact.rawValueText
    SIArtifact.canonicalDeltaNuCsAuthorityArtifactRowRequest
canonicalDeltaNuCsCarrierRawTextMatchesArtifactRow = refl

canonicalCCarrierRawTextMatchesArtifactRow :
  ExactIntegerTextCarrier.rawAuthorityText
    canonicalCMetrePerSecondIntegerCarrier
  ≡
  SIArtifact.rawValueText SIArtifact.canonicalCAuthorityArtifactRowRequest
canonicalCCarrierRawTextMatchesArtifactRow = refl

canonicalHCarrierRawTextMatchesArtifactRow :
  ExactScientificDecimalCarrier.rawAuthorityText
    canonicalHScientificDecimalCarrier
  ≡
  SIArtifact.rawValueText SIArtifact.canonicalHAuthorityArtifactRowRequest
canonicalHCarrierRawTextMatchesArtifactRow = refl

canonicalDeltaNuCsCarrierMatchesCs133PayloadRequest :
  ExactIntegerTextCarrier.rawAuthorityText canonicalDeltaNuCsNaturalCarrier
  ≡
  Cs133.Cs133PayloadFields.rawNumericValueText
    Cs133.canonicalCs133PayloadFields
canonicalDeltaNuCsCarrierMatchesCs133PayloadRequest = refl

canonicalHCarrierMatchesPlanckPayloadRequest :
  ExactScientificDecimalCarrier.compactRegistryText
    canonicalHScientificDecimalCarrier
  ≡
  Planck.PlanckHbarPayloadFields.planckRawNumericValueText
    Planck.canonicalPlanckHbarPayloadFields
canonicalHCarrierMatchesPlanckPayloadRequest = refl

canonicalDeltaNuCsCarrierRegistryValueIsUnspacedInteger :
  Registry.KnownConstantSlot.value SIArtifact.canonicalDeltaNuCsRegistryRow
  ≡ "9192631770"
canonicalDeltaNuCsCarrierRegistryValueIsUnspacedInteger = refl

canonicalCCarrierRegistryValueIsExactMetresPerSecondInteger :
  Registry.KnownConstantSlot.value SIArtifact.canonicalCRegistryRow
  ≡ "299792458"
canonicalCCarrierRegistryValueIsExactMetresPerSecondInteger = refl

canonicalHCarrierRegistryValueIsExactScientificDecimal :
  Registry.KnownConstantSlot.value SIArtifact.canonicalHRegistryRow
  ≡ "6.62607015e-34"
canonicalHCarrierRegistryValueIsExactScientificDecimal = refl

canonicalHCarrierDoesNotUseFloat :
  ExactScientificDecimalCarrier.usesFloatCarrier
    canonicalHScientificDecimalCarrier
  ≡ false
canonicalHCarrierDoesNotUseFloat = refl

canonicalParsedCarrierManifestKeepsPromotionFalse :
  anyNumericValuePromoted
    canonicalSIExactConstantParsedCarrierRequestManifest
  ≡ false
canonicalParsedCarrierManifestKeepsPromotionFalse = refl

canonicalParsedCarrierManifestTokenGuardCrossCheck :
  acceptedAuthorityTokenPresent
    canonicalSIExactConstantParsedCarrierRequestManifest
  ≡
  Payload.NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresent
    Payload.canonicalNumericAuthorityPayloadValidatorReceipt
canonicalParsedCarrierManifestTokenGuardCrossCheck = refl

canonicalParsedCarrierManifestPromotionGuardCrossCheck :
  anyNumericValuePromoted
    canonicalSIExactConstantParsedCarrierRequestManifest
  ≡
  Payload.NumericAuthorityPayloadValidatorReceipt.numericValuePromoted
    Payload.canonicalNumericAuthorityPayloadValidatorReceipt
canonicalParsedCarrierManifestPromotionGuardCrossCheck = refl
