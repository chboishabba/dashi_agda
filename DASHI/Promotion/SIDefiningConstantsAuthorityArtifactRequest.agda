module DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload

------------------------------------------------------------------------
-- BIPM SI defining-constant authority-artifact request.
--
-- This module is request-shaped only.  It names the BIPM canonical rows
-- needed by this lane and the artifact fields an importer must later
-- provide.  It does not download an artifact, invent a checksum, parse a
-- numeric carrier, or promote any row into consumer use.
-- It does not construct Candidate256PhysicalCalibrationExternalReceipt;
-- the Candidate256/W4 receipt remains a separate external authority wall.

data SIDefiningConstant : Set where
  deltaNuCs :
    SIDefiningConstant

  speedOfLightC :
    SIDefiningConstant

  planckConstantH :
    SIDefiningConstant

data SIArtifactFieldKey : Set where
  artifactIdentityKey :
    SIArtifactFieldKey

  artifactSha256Key :
    SIArtifactFieldKey

  artifactAccessDateKey :
    SIArtifactFieldKey

  rawNumericTextKey :
    SIArtifactFieldKey

  rawUncertaintyTextKey :
    SIArtifactFieldKey

  parsedCarrierKey :
    SIArtifactFieldKey

  covarianceOrIndependenceKey :
    SIArtifactFieldKey

  consumerIngestionReceiptKey :
    SIArtifactFieldKey

record SIArtifactRequestFields : Set₁ where
  field
    artifactIdentity :
      Payload.PayloadSchemaField

    artifactSha256 :
      Payload.PayloadSchemaField

    artifactAccessDate :
      Payload.PayloadSchemaField

    rawNumericText :
      String

    rawUncertaintyText :
      String

    parsedCarrier :
      Payload.PayloadSchemaField

    covarianceOrIndependence :
      Payload.PayloadSchemaField

    consumerIngestionReceipt :
      Payload.PayloadSchemaField

open SIArtifactRequestFields public

canonicalSIArtifactFieldKeys : List SIArtifactFieldKey
canonicalSIArtifactFieldKeys =
  artifactIdentityKey
  ∷ artifactSha256Key
  ∷ artifactAccessDateKey
  ∷ rawNumericTextKey
  ∷ rawUncertaintyTextKey
  ∷ parsedCarrierKey
  ∷ covarianceOrIndependenceKey
  ∷ consumerIngestionReceiptKey
  ∷ []

canonicalBIPMAuthorityFamily : String
canonicalBIPMAuthorityFamily =
  "BIPM SI defining constants"

canonicalBIPMSourceUri : String
canonicalBIPMSourceUri =
  "https://www.bipm.org/en/measurement-units/si-defining-constants"

canonicalBIPMVersion : String
canonicalBIPMVersion =
  "SI Brochure 9th edition defining constants table"

canonicalDeltaNuCsRegistrySourceRef : String
canonicalDeltaNuCsRegistrySourceRef =
  "DASHI.Constants.Registry.canonicalSIDefiningConstants.Delta nu Cs"

canonicalCRegistrySourceRef : String
canonicalCRegistrySourceRef =
  "DASHI.Constants.Registry.canonicalSIDefiningConstants.c"

canonicalHRegistrySourceRef : String
canonicalHRegistrySourceRef =
  "DASHI.Constants.Registry.canonicalSIDefiningConstants.h"

exactZeroUncertaintyText : String
exactZeroUncertaintyText =
  "0"

canonicalDeltaNuCsRawValueText : String
canonicalDeltaNuCsRawValueText =
  "9 192 631 770"

canonicalCRawValueText : String
canonicalCRawValueText =
  "299 792 458"

canonicalHRawValueText : String
canonicalHRawValueText =
  "6.626 070 15 e-34"

siArtifactRequestFieldsFor :
  String →
  SIArtifactRequestFields
siArtifactRequestFieldsFor rawText =
  record
    { artifactIdentity =
        Payload.missingAuthorityArtifactField
    ; artifactSha256 =
        Payload.missingArtifactDigestField
    ; artifactAccessDate =
        Payload.missingAccessEvidenceField
    ; rawNumericText =
        rawText
    ; rawUncertaintyText =
        exactZeroUncertaintyText
    ; parsedCarrier =
        Payload.missingParsedCarrierField
    ; covarianceOrIndependence =
        Payload.missingCovarianceField
    ; consumerIngestionReceipt =
        Payload.missingConsumerIngestionReceiptField
    }

canonicalDeltaNuCsArtifactFields : SIArtifactRequestFields
canonicalDeltaNuCsArtifactFields =
  siArtifactRequestFieldsFor canonicalDeltaNuCsRawValueText

canonicalCArtifactFields : SIArtifactRequestFields
canonicalCArtifactFields =
  siArtifactRequestFieldsFor canonicalCRawValueText

canonicalHArtifactFields : SIArtifactRequestFields
canonicalHArtifactFields =
  siArtifactRequestFieldsFor canonicalHRawValueText

canonicalDeltaNuCsRegistryRow : Registry.KnownConstantSlot
canonicalDeltaNuCsRegistryRow =
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
    ∷ "authority artifact still required before consumer ingestion"
    ∷ []
    )

canonicalCRegistryRow : Registry.KnownConstantSlot
canonicalCRegistryRow =
  Registry.mkConstant
    "speed of light in vacuum"
    "c"
    "299792458"
    "m s^-1"
    Registry.exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "Maxwell"
    ∷ "relativity"
    ∷ "GR"
    ∷ "QFT"
    ∷ "empirical calibration"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "authority artifact still required before consumer ingestion"
    ∷ []
    )

canonicalHRegistryRow : Registry.KnownConstantSlot
canonicalHRegistryRow =
  Registry.mkConstant
    "Planck constant"
    "h"
    "6.62607015e-34"
    "J s"
    Registry.exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "Schrodinger"
    ∷ "QFT"
    ∷ "quantum measurement"
    ∷ "chemistry spectra"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "authority artifact still required before consumer ingestion"
    ∷ []
    )

record SIDefiningConstantAuthorityArtifactRowRequest : Set₁ where
  field
    constant :
      SIDefiningConstant

    sourceRegistryRow :
      Registry.KnownConstantSlot

    sourceUri :
      String

    sourceVersion :
      String

    authorityFamily :
      String

    rawValueText :
      String

    unitText :
      String

    exactnessText :
      String

    artifactFields :
      SIArtifactRequestFields

    fieldKeys :
      List SIArtifactFieldKey

    fieldKeyCount :
      Nat

    fieldKeyCountIs8 :
      fieldKeyCount ≡ 8

    artifactLoaded :
      Bool

    artifactLoadedIsFalse :
      artifactLoaded ≡ false

    rowPromoted :
      Bool

    rowPromotedIsFalse :
      rowPromoted ≡ false

    acceptedAuthorityTokenPresent :
      Bool

    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false

    artifactAccepted :
      Bool

    artifactAcceptedIsFalse :
      artifactAccepted ≡ false

open SIDefiningConstantAuthorityArtifactRowRequest public

mkSIArtifactRowRequest :
  SIDefiningConstant →
  Registry.KnownConstantSlot →
  String →
  String →
  SIArtifactRequestFields →
  SIDefiningConstantAuthorityArtifactRowRequest
mkSIArtifactRowRequest constant row raw unit fields =
  record
    { constant =
        constant
    ; sourceRegistryRow =
        row
    ; sourceUri =
        canonicalBIPMSourceUri
    ; sourceVersion =
        canonicalBIPMVersion
    ; authorityFamily =
        canonicalBIPMAuthorityFamily
    ; rawValueText =
        raw
    ; unitText =
        unit
    ; exactnessText =
        "exact by SI definition; uncertainty text requested as 0"
    ; artifactFields =
        fields
    ; fieldKeys =
        canonicalSIArtifactFieldKeys
    ; fieldKeyCount =
        Payload.listCount canonicalSIArtifactFieldKeys
    ; fieldKeyCountIs8 =
        refl
    ; artifactLoaded =
        false
    ; artifactLoadedIsFalse =
        refl
    ; rowPromoted =
        false
    ; rowPromotedIsFalse =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; artifactAccepted =
        false
    ; artifactAcceptedIsFalse =
        refl
    }

canonicalDeltaNuCsAuthorityArtifactRowRequest :
  SIDefiningConstantAuthorityArtifactRowRequest
canonicalDeltaNuCsAuthorityArtifactRowRequest =
  mkSIArtifactRowRequest
    deltaNuCs
    canonicalDeltaNuCsRegistryRow
    canonicalDeltaNuCsRawValueText
    "Hz"
    canonicalDeltaNuCsArtifactFields

canonicalCAuthorityArtifactRowRequest :
  SIDefiningConstantAuthorityArtifactRowRequest
canonicalCAuthorityArtifactRowRequest =
  mkSIArtifactRowRequest
    speedOfLightC
    canonicalCRegistryRow
    canonicalCRawValueText
    "m s^-1"
    canonicalCArtifactFields

canonicalHAuthorityArtifactRowRequest :
  SIDefiningConstantAuthorityArtifactRowRequest
canonicalHAuthorityArtifactRowRequest =
  mkSIArtifactRowRequest
    planckConstantH
    canonicalHRegistryRow
    canonicalHRawValueText
    "J s"
    canonicalHArtifactFields

record SIDefiningConstantsAuthorityArtifactRequestManifest : Set₁ where
  field
    manifestLabel :
      String

    sourceRegistry :
      Registry.ConstantsRegistry

    payloadValidator :
      Payload.NumericAuthorityPayloadValidatorReceipt

    requestedConstants :
      List SIDefiningConstant

    requestedRows :
      List SIDefiningConstantAuthorityArtifactRowRequest

    requestedRowCount :
      Nat

    requestedRowCountIs3 :
      requestedRowCount ≡ 3

    requiredArtifactFields :
      List SIArtifactFieldKey

    requiredArtifactFieldCount :
      Nat

    requiredArtifactFieldCountIs8 :
      requiredArtifactFieldCount ≡ 8

    artifactLoaded :
      Bool

    artifactLoadedIsFalse :
      artifactLoaded ≡ false

    anyRowPromoted :
      Bool

    anyRowPromotedIsFalse :
      anyRowPromoted ≡ false

    inheritsValidatorFailClosedTokenGuard :
      anyRowPromoted
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.numericValuePromoted
        payloadValidator

open SIDefiningConstantsAuthorityArtifactRequestManifest public

canonicalSIDefiningConstantsAuthorityArtifactRequestManifest :
  SIDefiningConstantsAuthorityArtifactRequestManifest
canonicalSIDefiningConstantsAuthorityArtifactRequestManifest =
  record
    { manifestLabel =
        "BIPM exact SI defining constants authority artifact request"
    ; sourceRegistry =
        Registry.repoWideConstantsRegistry
    ; payloadValidator =
        Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; requestedConstants =
        deltaNuCs
        ∷ speedOfLightC
        ∷ planckConstantH
        ∷ []
    ; requestedRows =
        canonicalDeltaNuCsAuthorityArtifactRowRequest
        ∷ canonicalCAuthorityArtifactRowRequest
        ∷ canonicalHAuthorityArtifactRowRequest
        ∷ []
    ; requestedRowCount =
        Payload.listCount
          ( canonicalDeltaNuCsAuthorityArtifactRowRequest
          ∷ canonicalCAuthorityArtifactRowRequest
          ∷ canonicalHAuthorityArtifactRowRequest
          ∷ []
          )
    ; requestedRowCountIs3 =
        refl
    ; requiredArtifactFields =
        canonicalSIArtifactFieldKeys
    ; requiredArtifactFieldCount =
        Payload.listCount canonicalSIArtifactFieldKeys
    ; requiredArtifactFieldCountIs8 =
        refl
    ; artifactLoaded =
        false
    ; artifactLoadedIsFalse =
        refl
    ; anyRowPromoted =
        false
    ; anyRowPromotedIsFalse =
        refl
    ; inheritsValidatorFailClosedTokenGuard =
        refl
    }

canonicalDeltaNuCsRowSymbolIsCanonical :
  Registry.KnownConstantSlot.symbol canonicalDeltaNuCsRegistryRow
  ≡ "Delta nu Cs"
canonicalDeltaNuCsRowSymbolIsCanonical = refl

canonicalDeltaNuCsRowValueIsCanonical :
  Registry.KnownConstantSlot.value canonicalDeltaNuCsRegistryRow
  ≡ "9192631770"
canonicalDeltaNuCsRowValueIsCanonical = refl

canonicalDeltaNuCsRowUnitIsCanonical :
  Registry.KnownConstantSlot.unit canonicalDeltaNuCsRegistryRow
  ≡ "Hz"
canonicalDeltaNuCsRowUnitIsCanonical = refl

canonicalDeltaNuCsRowIsExactSIDefining :
  Registry.KnownConstantSlot.authorityClass canonicalDeltaNuCsRegistryRow
  ≡ Registry.exactSIDefiningConstant
canonicalDeltaNuCsRowIsExactSIDefining = refl

canonicalCRowSymbolIsCanonical :
  Registry.KnownConstantSlot.symbol canonicalCRegistryRow
  ≡ "c"
canonicalCRowSymbolIsCanonical = refl

canonicalCRowValueIsCanonical :
  Registry.KnownConstantSlot.value canonicalCRegistryRow
  ≡ "299792458"
canonicalCRowValueIsCanonical = refl

canonicalCRowUnitIsCanonical :
  Registry.KnownConstantSlot.unit canonicalCRegistryRow
  ≡ "m s^-1"
canonicalCRowUnitIsCanonical = refl

canonicalCRowIsExactSIDefining :
  Registry.KnownConstantSlot.authorityClass canonicalCRegistryRow
  ≡ Registry.exactSIDefiningConstant
canonicalCRowIsExactSIDefining = refl

canonicalHRowSymbolIsCanonical :
  Registry.KnownConstantSlot.symbol canonicalHRegistryRow
  ≡ "h"
canonicalHRowSymbolIsCanonical = refl

canonicalHRowValueIsCanonical :
  Registry.KnownConstantSlot.value canonicalHRegistryRow
  ≡ "6.62607015e-34"
canonicalHRowValueIsCanonical = refl

canonicalHRowUnitIsCanonical :
  Registry.KnownConstantSlot.unit canonicalHRegistryRow
  ≡ "J s"
canonicalHRowUnitIsCanonical = refl

canonicalHRowIsExactSIDefining :
  Registry.KnownConstantSlot.authorityClass canonicalHRegistryRow
  ≡ Registry.exactSIDefiningConstant
canonicalHRowIsExactSIDefining = refl

canonicalDeltaNuCsRawTextMatchesField :
  rawValueText canonicalDeltaNuCsAuthorityArtifactRowRequest
  ≡
  rawNumericText
    (artifactFields canonicalDeltaNuCsAuthorityArtifactRowRequest)
canonicalDeltaNuCsRawTextMatchesField = refl

canonicalCRawTextMatchesField :
  rawValueText canonicalCAuthorityArtifactRowRequest
  ≡
  rawNumericText
    (artifactFields canonicalCAuthorityArtifactRowRequest)
canonicalCRawTextMatchesField = refl

canonicalHRawTextMatchesField :
  rawValueText canonicalHAuthorityArtifactRowRequest
  ≡
  rawNumericText
    (artifactFields canonicalHAuthorityArtifactRowRequest)
canonicalHRawTextMatchesField = refl

canonicalDeltaNuCsArtifactLoadedIsFalse :
  artifactLoaded canonicalDeltaNuCsAuthorityArtifactRowRequest
  ≡ false
canonicalDeltaNuCsArtifactLoadedIsFalse = refl

canonicalCArtifactLoadedIsFalse :
  artifactLoaded canonicalCAuthorityArtifactRowRequest
  ≡ false
canonicalCArtifactLoadedIsFalse = refl

canonicalHArtifactLoadedIsFalse :
  artifactLoaded canonicalHAuthorityArtifactRowRequest
  ≡ false
canonicalHArtifactLoadedIsFalse = refl

canonicalDeltaNuCsRowPromotedIsFalse :
  rowPromoted canonicalDeltaNuCsAuthorityArtifactRowRequest
  ≡ false
canonicalDeltaNuCsRowPromotedIsFalse = refl

canonicalCRowPromotedIsFalse :
  rowPromoted canonicalCAuthorityArtifactRowRequest
  ≡ false
canonicalCRowPromotedIsFalse = refl

canonicalHRowPromotedIsFalse :
  rowPromoted canonicalHAuthorityArtifactRowRequest
  ≡ false
canonicalHRowPromotedIsFalse = refl

canonicalSIManifestRowCountIs3 :
  requestedRowCount
    canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
  ≡ 3
canonicalSIManifestRowCountIs3 = refl

canonicalSIManifestRequiredArtifactFieldCountIs8 :
  requiredArtifactFieldCount
    canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
  ≡ 8
canonicalSIManifestRequiredArtifactFieldCountIs8 = refl

canonicalSIManifestArtifactLoadedIsFalse :
  artifactLoaded canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
  ≡ false
canonicalSIManifestArtifactLoadedIsFalse = refl

canonicalSIManifestAnyRowPromotedIsFalse :
  anyRowPromoted canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
  ≡ false
canonicalSIManifestAnyRowPromotedIsFalse = refl
