module DASHI.Promotion.NumericAuthorityPayloadValidator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAndAuthorityObligations as Numeric
import DASHI.Promotion.NumericAuthorityTokenIntake as Intake
import DASHI.Promotion.NumericMeasuredAuthorityBinding as Binding
import DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization as Norm

------------------------------------------------------------------------
-- Numeric authority payload validator.
--
-- Binding names the measured slots.  Intake records requested tokens.
-- Normalization expands those requests into the broader measured-token
-- population.  This module adds the payload validator surface that an
-- importer must satisfy before any measured numeric value can be read.
--
-- It deliberately carries field names, families, counts, and guards only:
-- no measured numeric values, no parsed numerals, and no promotion.

data PayloadSourceFamily : Set where
  codataPayloadFamily : PayloadSourceFamily
  pdgPayloadFamily : PayloadSourceFamily
  codataPDGPayloadFamily : PayloadSourceFamily

data PayloadFieldStatus : Set where
  schemaMetadataKnown : PayloadFieldStatus
  authorityPayloadMissing : PayloadFieldStatus

data PayloadValidationState : Set where
  payloadMissing : PayloadValidationState
  payloadMalformed : PayloadValidationState
  payloadMetadataOnly : PayloadValidationState
  payloadAcceptedAndValueLoaded : PayloadValidationState

record PayloadSchemaField : Set where
  field
    payloadFieldName : String
    payloadFieldStatus : PayloadFieldStatus
    payloadFieldPurpose : String
    payloadFieldOwnerSurface : String
    containsMeasuredNumericValue : Bool
    containsMeasuredNumericValueIsFalse :
      containsMeasuredNumericValue ≡ false

open PayloadSchemaField public

mkSchemaKnownField : String → String → String → PayloadSchemaField
mkSchemaKnownField name purpose owner =
  record
    { payloadFieldName = name
    ; payloadFieldStatus = schemaMetadataKnown
    ; payloadFieldPurpose = purpose
    ; payloadFieldOwnerSurface = owner
    ; containsMeasuredNumericValue = false
    ; containsMeasuredNumericValueIsFalse = refl
    }

mkAuthorityMissingField : String → String → String → PayloadSchemaField
mkAuthorityMissingField name purpose owner =
  record
    { payloadFieldName = name
    ; payloadFieldStatus = authorityPayloadMissing
    ; payloadFieldPurpose = purpose
    ; payloadFieldOwnerSurface = owner
    ; containsMeasuredNumericValue = false
    ; containsMeasuredNumericValueIsFalse = refl
    }

schemaSymbolField : PayloadSchemaField
schemaSymbolField =
  mkSchemaKnownField
    "symbol"
    "registry-facing symbolic identifier"
    "NumericMeasuredAuthorityBinding.MeasuredConstantSlot.symbol"

schemaRegistrySlotField : PayloadSchemaField
schemaRegistrySlotField =
  mkSchemaKnownField
    "registrySlotName"
    "canonical Constants.Registry slot path"
    "NumericMeasuredAuthorityBinding.MeasuredConstantSlot.registrySlotName"

schemaAuthorityFamilyField : PayloadSchemaField
schemaAuthorityFamilyField =
  mkSchemaKnownField
    "authorityFamily"
    "CODATA, PDG, or cross-authority payload family"
    "NumericMeasuredAuthorityTokenNormalization.normalizedProvider"

schemaAuthorityVersionField : PayloadSchemaField
schemaAuthorityVersionField =
  mkSchemaKnownField
    "authorityVersion"
    "authority version label required before ingestion"
    "NumericMeasuredAuthorityBinding.AuthorityVersion"

schemaSourceUriField : PayloadSchemaField
schemaSourceUriField =
  mkSchemaKnownField
    "sourceUri"
    "authority source URI policy"
    "NumericMeasuredAuthorityBinding.SourceUri"

schemaChecksumPolicyField : PayloadSchemaField
schemaChecksumPolicyField =
  mkSchemaKnownField
    "sourceChecksumPolicy"
    "hash algorithm and coverage policy"
    "NumericMeasuredAuthorityBinding.SourceChecksum"

schemaAccessDatePolicyField : PayloadSchemaField
schemaAccessDatePolicyField =
  mkSchemaKnownField
    "sourceAccessDatePolicy"
    "date field policy for the authority artifact"
    "NumericMeasuredAuthorityBinding.SourceAccessDate"

schemaUncertaintyConventionField : PayloadSchemaField
schemaUncertaintyConventionField =
  mkSchemaKnownField
    "uncertaintyConvention"
    "uncertainty convention and covariance policy"
    "NumericMeasuredAuthorityBinding.ValueUncertainty"

schemaRoundingPolicyField : PayloadSchemaField
schemaRoundingPolicyField =
  mkSchemaKnownField
    "roundingPolicy"
    "authority significant-digit preservation policy"
    "NumericMeasuredAuthorityBinding.RoundingPolicy"

schemaUnitConventionField : PayloadSchemaField
schemaUnitConventionField =
  mkSchemaKnownField
    "unitConvention"
    "unit system and conversion boundary"
    "NumericMeasuredAuthorityBinding.UnitConvention"

schemaValidityRegimeField : PayloadSchemaField
schemaValidityRegimeField =
  mkSchemaKnownField
    "validityRegime"
    "consumer validity boundary for the value"
    "NumericMeasuredAuthorityBinding.ValidityRegime"

schemaIngestionReceiptField : PayloadSchemaField
schemaIngestionReceiptField =
  mkSchemaKnownField
    "valueIngestionReceiptName"
    "receipt name required before any numeric use"
    "NumericAuthorityTokenIntake.NumericAuthorityTokenRequest"

missingAuthorityArtifactField : PayloadSchemaField
missingAuthorityArtifactField =
  mkAuthorityMissingField
    "authorityArtifact"
    "downloaded authority artifact selected by the importer"
    "external CODATA/PDG artifact"

missingArtifactDigestField : PayloadSchemaField
missingArtifactDigestField =
  mkAuthorityMissingField
    "authorityArtifactSha256"
    "actual SHA-256 digest for the downloaded authority artifact"
    "external CODATA/PDG artifact"

missingAccessEvidenceField : PayloadSchemaField
missingAccessEvidenceField =
  mkAuthorityMissingField
    "authorityAccessDateEvidence"
    "actual access-date evidence tied to the authority artifact"
    "external CODATA/PDG artifact"

missingRawValueTextField : PayloadSchemaField
missingRawValueTextField =
  mkAuthorityMissingField
    "rawNumericValueText"
    "unparsed authority value text; absent in this module"
    "external CODATA/PDG artifact"

missingRawUncertaintyTextField : PayloadSchemaField
missingRawUncertaintyTextField =
  mkAuthorityMissingField
    "rawUncertaintyText"
    "unparsed authority uncertainty text; absent in this module"
    "external CODATA/PDG artifact"

missingParsedCarrierField : PayloadSchemaField
missingParsedCarrierField =
  mkAuthorityMissingField
    "parsedNumericCarrierPayload"
    "finite numeric carrier payload produced by a parser"
    "future value-ingestion receipt"

missingCovarianceField : PayloadSchemaField
missingCovarianceField =
  mkAuthorityMissingField
    "covarianceMatrixOrIndependenceReceipt"
    "covariance payload or explicit independence receipt"
    "future value-ingestion receipt"

missingConsumerIngestionReceiptField : PayloadSchemaField
missingConsumerIngestionReceiptField =
  mkAuthorityMissingField
    "consumerValueIngestionReceipt"
    "consumer-specific receipt proving the value was loaded under policy"
    "future value-ingestion receipt"

missingDimensionVectorCarrierField : PayloadSchemaField
missingDimensionVectorCarrierField =
  mkAuthorityMissingField
    "dimensionVectorCarrier"
    "typed SI-base-dimension exponent vector for the authority row"
    "future authority-payload shape validator"

missingDimensionVectorWitnessField : PayloadSchemaField
missingDimensionVectorWitnessField =
  mkAuthorityMissingField
    "dimensionVectorMatchesUnitConvention"
    "proof that the external dimension vector matches the normalized unit convention"
    "future authority-payload shape validator"

missingUnitFactorizationReceiptField : PayloadSchemaField
missingUnitFactorizationReceiptField =
  mkAuthorityMissingField
    "unitFactorizationReceipt"
    "proof that parsed value, unit, and conversion policy factor through the authority unit convention"
    "future authority-payload shape validator"

canonicalSchemaKnownFields : List PayloadSchemaField
canonicalSchemaKnownFields =
  schemaSymbolField
  ∷ schemaRegistrySlotField
  ∷ schemaAuthorityFamilyField
  ∷ schemaAuthorityVersionField
  ∷ schemaSourceUriField
  ∷ schemaChecksumPolicyField
  ∷ schemaAccessDatePolicyField
  ∷ schemaUncertaintyConventionField
  ∷ schemaRoundingPolicyField
  ∷ schemaUnitConventionField
  ∷ schemaValidityRegimeField
  ∷ schemaIngestionReceiptField
  ∷ []

canonicalMissingAuthorityPayloadFields : List PayloadSchemaField
canonicalMissingAuthorityPayloadFields =
  missingAuthorityArtifactField
  ∷ missingArtifactDigestField
  ∷ missingAccessEvidenceField
  ∷ missingRawValueTextField
  ∷ missingRawUncertaintyTextField
  ∷ missingParsedCarrierField
  ∷ missingCovarianceField
  ∷ missingConsumerIngestionReceiptField
  ∷ []

canonicalExternalShapePayloadFields : List PayloadSchemaField
canonicalExternalShapePayloadFields =
  missingDimensionVectorCarrierField
  ∷ missingDimensionVectorWitnessField
  ∷ missingUnitFactorizationReceiptField
  ∷ []

canonicalPayloadSchemaFields : List PayloadSchemaField
canonicalPayloadSchemaFields =
  schemaSymbolField
  ∷ schemaRegistrySlotField
  ∷ schemaAuthorityFamilyField
  ∷ schemaAuthorityVersionField
  ∷ schemaSourceUriField
  ∷ schemaChecksumPolicyField
  ∷ schemaAccessDatePolicyField
  ∷ schemaUncertaintyConventionField
  ∷ schemaRoundingPolicyField
  ∷ schemaUnitConventionField
  ∷ schemaValidityRegimeField
  ∷ schemaIngestionReceiptField
  ∷ missingAuthorityArtifactField
  ∷ missingArtifactDigestField
  ∷ missingAccessEvidenceField
  ∷ missingRawValueTextField
  ∷ missingRawUncertaintyTextField
  ∷ missingParsedCarrierField
  ∷ missingCovarianceField
  ∷ missingConsumerIngestionReceiptField
  ∷ []

record PayloadFamilyCoverage : Set₁ where
  field
    familyLabel : String
    payloadSourceFamily : PayloadSourceFamily
    normalizedTokenRows : List Norm.NormalizedMeasuredAuthorityToken
    boundMeasuredSlots : List Binding.MeasuredConstantSlot
    intakeRequests : List Intake.NumericAuthorityTokenRequest
    normalizedTokenRowCount : Nat
    boundMeasuredSlotCount : Nat
    intakeRequestCount : Nat
    hasExplicitFamilyBoundary : Bool
    hasExplicitFamilyBoundaryIsTrue :
      hasExplicitFamilyBoundary ≡ true
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValueLoaded : Bool
    numericValueLoadedIsFalse : numericValueLoaded ≡ false

open PayloadFamilyCoverage public

record SIBaseDimensionVector : Set where
  field
    lengthPositiveExponent : Nat
    lengthNegativeExponent : Nat
    massPositiveExponent : Nat
    massNegativeExponent : Nat
    timePositiveExponent : Nat
    timeNegativeExponent : Nat
    electricCurrentPositiveExponent : Nat
    electricCurrentNegativeExponent : Nat
    thermodynamicTemperaturePositiveExponent : Nat
    thermodynamicTemperatureNegativeExponent : Nat
    amountOfSubstancePositiveExponent : Nat
    amountOfSubstanceNegativeExponent : Nat
    luminousIntensityPositiveExponent : Nat
    luminousIntensityNegativeExponent : Nat

open SIBaseDimensionVector public

dimensionlessSIBaseDimensionVector : SIBaseDimensionVector
dimensionlessSIBaseDimensionVector = record
  { lengthPositiveExponent = zero
  ; lengthNegativeExponent = zero
  ; massPositiveExponent = zero
  ; massNegativeExponent = zero
  ; timePositiveExponent = zero
  ; timeNegativeExponent = zero
  ; electricCurrentPositiveExponent = zero
  ; electricCurrentNegativeExponent = zero
  ; thermodynamicTemperaturePositiveExponent = zero
  ; thermodynamicTemperatureNegativeExponent = zero
  ; amountOfSubstancePositiveExponent = zero
  ; amountOfSubstanceNegativeExponent = zero
  ; luminousIntensityPositiveExponent = zero
  ; luminousIntensityNegativeExponent = zero
  }

kgDimensionVector : SIBaseDimensionVector
kgDimensionVector = record
  { lengthPositiveExponent = zero
  ; lengthNegativeExponent = zero
  ; massPositiveExponent = suc zero
  ; massNegativeExponent = zero
  ; timePositiveExponent = zero
  ; timeNegativeExponent = zero
  ; electricCurrentPositiveExponent = zero
  ; electricCurrentNegativeExponent = zero
  ; thermodynamicTemperaturePositiveExponent = zero
  ; thermodynamicTemperatureNegativeExponent = zero
  ; amountOfSubstancePositiveExponent = zero
  ; amountOfSubstanceNegativeExponent = zero
  ; luminousIntensityPositiveExponent = zero
  ; luminousIntensityNegativeExponent = zero
  }

newtonianGDimensionVector : SIBaseDimensionVector
newtonianGDimensionVector = record
  { lengthPositiveExponent = suc (suc (suc zero))
  ; lengthNegativeExponent = zero
  ; massPositiveExponent = zero
  ; massNegativeExponent = suc zero
  ; timePositiveExponent = zero
  ; timeNegativeExponent = suc (suc zero)
  ; electricCurrentPositiveExponent = zero
  ; electricCurrentNegativeExponent = zero
  ; thermodynamicTemperaturePositiveExponent = zero
  ; thermodynamicTemperatureNegativeExponent = zero
  ; amountOfSubstancePositiveExponent = zero
  ; amountOfSubstanceNegativeExponent = zero
  ; luminousIntensityPositiveExponent = zero
  ; luminousIntensityNegativeExponent = zero
  }

record ExternalPayloadShapeRequirement : Set₁ where
  field
    shapeRequirementLabel : String
    normalizedToken : Norm.NormalizedMeasuredAuthorityToken
    requestedDimensionVector : SIBaseDimensionVector
    externalShapePayloadFields : List PayloadSchemaField
    externalShapePayloadFieldCount : Nat
    externalShapePayloadFieldCountIs3 :
      externalShapePayloadFieldCount ≡ 3
    dimensionVectorCarrierPresent : Bool
    dimensionVectorCarrierPresentIsFalse :
      dimensionVectorCarrierPresent ≡ false
    dimensionVectorWitnessPresent : Bool
    dimensionVectorWitnessPresentIsFalse :
      dimensionVectorWitnessPresent ≡ false
    unitFactorizationReceiptPresent : Bool
    unitFactorizationReceiptPresentIsFalse :
      unitFactorizationReceiptPresent ≡ false
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValueLoaded : Bool
    numericValueLoadedIsFalse :
      numericValueLoaded ≡ false

open ExternalPayloadShapeRequirement public

mkExternalPayloadShapeRequirement :
  String →
  Norm.NormalizedMeasuredAuthorityToken →
  SIBaseDimensionVector →
  ExternalPayloadShapeRequirement
mkExternalPayloadShapeRequirement label token vector = record
  { shapeRequirementLabel = label
  ; normalizedToken = token
  ; requestedDimensionVector = vector
  ; externalShapePayloadFields = canonicalExternalShapePayloadFields
  ; externalShapePayloadFieldCount = suc (suc (suc zero))
  ; externalShapePayloadFieldCountIs3 = refl
  ; dimensionVectorCarrierPresent = false
  ; dimensionVectorCarrierPresentIsFalse = refl
  ; dimensionVectorWitnessPresent = false
  ; dimensionVectorWitnessPresentIsFalse = refl
  ; unitFactorizationReceiptPresent = false
  ; unitFactorizationReceiptPresentIsFalse = refl
  ; acceptedAuthorityTokenPresent = false
  ; acceptedAuthorityTokenPresentIsFalse = refl
  ; numericValueLoaded = false
  ; numericValueLoadedIsFalse = refl
  }

canonicalExternalPayloadShapeRequirements :
  List ExternalPayloadShapeRequirement
canonicalExternalPayloadShapeRequirements =
  mkExternalPayloadShapeRequirement
    "external shape requirement for CODATA G"
    Norm.gNormalizedToken
    newtonianGDimensionVector
  ∷ mkExternalPayloadShapeRequirement
    "external shape requirement for CODATA alpha"
    Norm.alphaNormalizedToken
    dimensionlessSIBaseDimensionVector
  ∷ mkExternalPayloadShapeRequirement
    "external shape requirement for CODATA electron mass"
    Norm.electronMassNormalizedToken
    kgDimensionVector
  ∷ mkExternalPayloadShapeRequirement
    "external shape requirement for PDG strong coupling"
    Norm.alphaSNormalizedToken
    dimensionlessSIBaseDimensionVector
  ∷ []

codataPayloadFamilyCoverage : PayloadFamilyCoverage
codataPayloadFamilyCoverage = record
  { familyLabel = "CODATA measured numeric payload family"
  ; payloadSourceFamily = codataPayloadFamily
  ; normalizedTokenRows = Norm.canonicalNormalizedCODATATokens
  ; boundMeasuredSlots = Binding.canonicalCODATABoundMeasuredSlots
  ; intakeRequests = Intake.canonicalCODATATokenRequests
  ; normalizedTokenRowCount =
      Norm.listCount Norm.canonicalNormalizedCODATATokens
  ; boundMeasuredSlotCount =
      Binding.listCount Binding.canonicalCODATABoundMeasuredSlots
  ; intakeRequestCount =
      Intake.listCount Intake.canonicalCODATATokenRequests
  ; hasExplicitFamilyBoundary = true
  ; hasExplicitFamilyBoundaryIsTrue = refl
  ; acceptedAuthorityTokenPresent = false
  ; acceptedAuthorityTokenPresentIsFalse = refl
  ; numericValueLoaded = false
  ; numericValueLoadedIsFalse = refl
  }

pdgPayloadFamilyCoverage : PayloadFamilyCoverage
pdgPayloadFamilyCoverage = record
  { familyLabel = "PDG measured numeric payload family"
  ; payloadSourceFamily = pdgPayloadFamily
  ; normalizedTokenRows = Norm.canonicalNormalizedPDGTokens
  ; boundMeasuredSlots = Binding.canonicalPDGBoundMeasuredSlots
  ; intakeRequests = Intake.canonicalPDGTokenRequests
  ; normalizedTokenRowCount =
      Norm.listCount Norm.canonicalNormalizedPDGTokens
  ; boundMeasuredSlotCount =
      Binding.listCount Binding.canonicalPDGBoundMeasuredSlots
  ; intakeRequestCount =
      Intake.listCount Intake.canonicalPDGTokenRequests
  ; hasExplicitFamilyBoundary = true
  ; hasExplicitFamilyBoundaryIsTrue = refl
  ; acceptedAuthorityTokenPresent = false
  ; acceptedAuthorityTokenPresentIsFalse = refl
  ; numericValueLoaded = false
  ; numericValueLoadedIsFalse = refl
  }

codataPDGPayloadFamilyCoverage : PayloadFamilyCoverage
codataPDGPayloadFamilyCoverage = record
  { familyLabel = "CODATA/PDG cross-authority payload family"
  ; payloadSourceFamily = codataPDGPayloadFamily
  ; normalizedTokenRows = Norm.canonicalNormalizedCODATAPDGTokens
  ; boundMeasuredSlots = []
  ; intakeRequests = []
  ; normalizedTokenRowCount =
      Norm.listCount Norm.canonicalNormalizedCODATAPDGTokens
  ; boundMeasuredSlotCount = zero
  ; intakeRequestCount = zero
  ; hasExplicitFamilyBoundary = true
  ; hasExplicitFamilyBoundaryIsTrue = refl
  ; acceptedAuthorityTokenPresent = false
  ; acceptedAuthorityTokenPresentIsFalse = refl
  ; numericValueLoaded = false
  ; numericValueLoadedIsFalse = refl
  }

canonicalPayloadFamilyCoverageRows : List PayloadFamilyCoverage
canonicalPayloadFamilyCoverageRows =
  codataPayloadFamilyCoverage
  ∷ pdgPayloadFamilyCoverage
  ∷ codataPDGPayloadFamilyCoverage
  ∷ []

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

record PayloadEnvelope : Set₁ where
  field
    payloadEnvelopeLabel : String
    payloadSourceFamily : PayloadSourceFamily
    normalizedToken : Norm.NormalizedMeasuredAuthorityToken
    validationState : PayloadValidationState
    schemaKnownFields : List PayloadSchemaField
    missingAuthorityPayloadFields : List PayloadSchemaField
    schemaFieldCount : Nat
    schemaFieldCountIs12 : schemaFieldCount ≡ 12
    missingAuthorityPayloadFieldCount : Nat
    missingAuthorityPayloadFieldCountIs8 :
      missingAuthorityPayloadFieldCount ≡ 8
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValueLoaded : Bool
    numericValueLoadedIsFalse : numericValueLoaded ≡ false
    numericValuePromoted : Bool
    numericValuePromotedIsFalse : numericValuePromoted ≡ false
    noMeasuredNumericValueInEnvelope : Bool
    noMeasuredNumericValueInEnvelopeIsTrue :
      noMeasuredNumericValueInEnvelope ≡ true

open PayloadEnvelope public

mkMissingPayloadEnvelope :
  String →
  PayloadSourceFamily →
  Norm.NormalizedMeasuredAuthorityToken →
  PayloadEnvelope
mkMissingPayloadEnvelope label family token = record
  { payloadEnvelopeLabel = label
  ; payloadSourceFamily = family
  ; normalizedToken = token
  ; validationState = payloadMissing
  ; schemaKnownFields = canonicalSchemaKnownFields
  ; missingAuthorityPayloadFields =
      canonicalMissingAuthorityPayloadFields
  ; schemaFieldCount = listCount canonicalSchemaKnownFields
  ; schemaFieldCountIs12 = refl
  ; missingAuthorityPayloadFieldCount =
      listCount canonicalMissingAuthorityPayloadFields
  ; missingAuthorityPayloadFieldCountIs8 = refl
  ; acceptedAuthorityTokenPresent = false
  ; acceptedAuthorityTokenPresentIsFalse = refl
  ; numericValueLoaded = false
  ; numericValueLoadedIsFalse = refl
  ; numericValuePromoted = false
  ; numericValuePromotedIsFalse = refl
  ; noMeasuredNumericValueInEnvelope = true
  ; noMeasuredNumericValueInEnvelopeIsTrue = refl
  }

canonicalCODATAPayloadEnvelopes : List PayloadEnvelope
canonicalCODATAPayloadEnvelopes =
  mkMissingPayloadEnvelope "CODATA payload envelope for G" codataPayloadFamily Norm.gNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for alpha" codataPayloadFamily Norm.alphaNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for m_e" codataPayloadFamily Norm.electronMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for m_p" codataPayloadFamily Norm.protonMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for m_n" codataPayloadFamily Norm.neutronMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for m_p c^2" codataPayloadFamily Norm.protonMassEnergyNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for epsilon_0" codataPayloadFamily Norm.epsilonZeroNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for mu_0" codataPayloadFamily Norm.muZeroNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for Z_0" codataPayloadFamily Norm.zZeroNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for R_infinity" codataPayloadFamily Norm.rydbergNormalizedToken
  ∷ []

canonicalPDGPayloadEnvelopes : List PayloadEnvelope
canonicalPDGPayloadEnvelopes =
  mkMissingPayloadEnvelope "PDG payload envelope for m_H" pdgPayloadFamily Norm.higgsMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for m_W and m_Z" pdgPayloadFamily Norm.wzMassesNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for quark masses" pdgPayloadFamily Norm.quarkMassesNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for CKM and PMNS" pdgPayloadFamily Norm.ckmPmnsNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for alpha_s" pdgPayloadFamily Norm.alphaSNormalizedToken
  ∷ []

canonicalCODATAPDGPayloadEnvelopes : List PayloadEnvelope
canonicalCODATAPDGPayloadEnvelopes =
  mkMissingPayloadEnvelope "CODATA/PDG payload envelope for m_mu" codataPDGPayloadFamily Norm.muonMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA/PDG payload envelope for m_tau" codataPDGPayloadFamily Norm.tauMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA/PDG payload envelope for G_F" codataPDGPayloadFamily Norm.fermiCouplingNormalizedToken
  ∷ []

canonicalPayloadEnvelopes : List PayloadEnvelope
canonicalPayloadEnvelopes =
  mkMissingPayloadEnvelope "CODATA payload envelope for G" codataPayloadFamily Norm.gNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for alpha" codataPayloadFamily Norm.alphaNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for m_e" codataPayloadFamily Norm.electronMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for m_p" codataPayloadFamily Norm.protonMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for m_n" codataPayloadFamily Norm.neutronMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA/PDG payload envelope for m_mu" codataPDGPayloadFamily Norm.muonMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA/PDG payload envelope for m_tau" codataPDGPayloadFamily Norm.tauMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for m_p c^2" codataPayloadFamily Norm.protonMassEnergyNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for epsilon_0" codataPayloadFamily Norm.epsilonZeroNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for mu_0" codataPayloadFamily Norm.muZeroNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for Z_0" codataPayloadFamily Norm.zZeroNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA payload envelope for R_infinity" codataPayloadFamily Norm.rydbergNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for m_H" pdgPayloadFamily Norm.higgsMassNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for m_W and m_Z" pdgPayloadFamily Norm.wzMassesNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for quark masses" pdgPayloadFamily Norm.quarkMassesNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for CKM and PMNS" pdgPayloadFamily Norm.ckmPmnsNormalizedToken
  ∷ mkMissingPayloadEnvelope "PDG payload envelope for alpha_s" pdgPayloadFamily Norm.alphaSNormalizedToken
  ∷ mkMissingPayloadEnvelope "CODATA/PDG payload envelope for G_F" codataPDGPayloadFamily Norm.fermiCouplingNormalizedToken
  ∷ []

canonicalPayloadValidationStates : List PayloadValidationState
canonicalPayloadValidationStates =
  payloadMissing
  ∷ payloadMalformed
  ∷ payloadMetadataOnly
  ∷ payloadAcceptedAndValueLoaded
  ∷ []

canonicalAcceptedPayloadEnvelopes : List PayloadEnvelope
canonicalAcceptedPayloadEnvelopes = []

canonicalLoadedPayloadEnvelopes : List PayloadEnvelope
canonicalLoadedPayloadEnvelopes = []

record NumericAuthorityPayloadValidatorReceipt : Set₁ where
  field
    receiptLabel : String
    sourceRegistry : Registry.ConstantsRegistry
    sourceBindingReceipt :
      Binding.NumericMeasuredAuthorityBindingReceipt
    sourceIntakeReceipt :
      Intake.NumericAuthorityTokenIntakeReceipt
    sourceNormalizedReceipt :
      Norm.NormalizedMeasuredAuthorityTokenReceipt
    sourceObligationIndex :
      Numeric.NumericAndAuthorityObligationIndex
    schemaFields : List PayloadSchemaField
    schemaKnownFields : List PayloadSchemaField
    missingAuthorityPayloadFields : List PayloadSchemaField
    externalShapePayloadFields : List PayloadSchemaField
    payloadFamilyCoverageRows : List PayloadFamilyCoverage
    externalPayloadShapeRequirements :
      List ExternalPayloadShapeRequirement
    validationStates : List PayloadValidationState
    payloadEnvelopes : List PayloadEnvelope
    codataPayloadEnvelopes : List PayloadEnvelope
    pdgPayloadEnvelopes : List PayloadEnvelope
    codataPDGPayloadEnvelopes : List PayloadEnvelope
    acceptedPayloadEnvelopes : List PayloadEnvelope
    loadedPayloadEnvelopes : List PayloadEnvelope
    schemaFieldCount : Nat
    schemaFieldCountIs20 : schemaFieldCount ≡ 20
    schemaKnownFieldCount : Nat
    schemaKnownFieldCountIs12 : schemaKnownFieldCount ≡ 12
    missingAuthorityPayloadFieldCount : Nat
    missingAuthorityPayloadFieldCountIs8 :
      missingAuthorityPayloadFieldCount ≡ 8
    externalShapePayloadFieldCount : Nat
    externalShapePayloadFieldCountIs3 :
      externalShapePayloadFieldCount ≡ 3
    payloadFamilyCoverageCount : Nat
    payloadFamilyCoverageCountIs3 : payloadFamilyCoverageCount ≡ 3
    externalPayloadShapeRequirementCount : Nat
    externalPayloadShapeRequirementCountIs4 :
      externalPayloadShapeRequirementCount ≡ 4
    validationStateCount : Nat
    validationStateCountIs4 : validationStateCount ≡ 4
    payloadEnvelopeCount : Nat
    payloadEnvelopeCountIs18 : payloadEnvelopeCount ≡ 18
    codataPayloadEnvelopeCount : Nat
    codataPayloadEnvelopeCountIs10 :
      codataPayloadEnvelopeCount ≡ 10
    pdgPayloadEnvelopeCount : Nat
    pdgPayloadEnvelopeCountIs5 : pdgPayloadEnvelopeCount ≡ 5
    codataPDGPayloadEnvelopeCount : Nat
    codataPDGPayloadEnvelopeCountIs3 :
      codataPDGPayloadEnvelopeCount ≡ 3
    acceptedPayloadEnvelopeCount : Nat
    acceptedPayloadEnvelopeCountIs0 :
      acceptedPayloadEnvelopeCount ≡ 0
    loadedPayloadEnvelopeCount : Nat
    loadedPayloadEnvelopeCountIs0 :
      loadedPayloadEnvelopeCount ≡ 0
    normalizedTokenCountCrossCheck : Nat
    normalizedTokenCountCrossCheckIs18 :
      normalizedTokenCountCrossCheck ≡ 18
    bindingSlotCountCrossCheck : Nat
    bindingSlotCountCrossCheckIs9 :
      bindingSlotCountCrossCheck ≡ 9
    intakeRequestCountCrossCheck : Nat
    intakeRequestCountCrossCheckIs9 :
      intakeRequestCountCrossCheck ≡ 9
    allPayloadsMissingAuthorityArtifact : Bool
    allPayloadsMissingAuthorityArtifactIsTrue :
      allPayloadsMissingAuthorityArtifact ≡ true
    allExternalShapeRequirementsMissingPayload : Bool
    allExternalShapeRequirementsMissingPayloadIsTrue :
      allExternalShapeRequirementsMissingPayload ≡ true
    noPayloadCarriesMeasuredNumericValue : Bool
    noPayloadCarriesMeasuredNumericValueIsTrue :
      noPayloadCarriesMeasuredNumericValue ≡ true
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValueLoaded : Bool
    numericValueLoadedIsFalse :
      numericValueLoaded ≡ false
    numericValuePromoted : Bool
    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false
    normalizedNumericValuePromoted : Bool
    normalizedNumericValuePromotedIsFalse :
      normalizedNumericValuePromoted ≡ false
    intakeNumericValuePromoted : Bool
    intakeNumericValuePromotedIsFalse :
      intakeNumericValuePromoted ≡ false
    bindingNumericValuePromoted : Bool
    bindingNumericValuePromotedIsFalse :
      bindingNumericValuePromoted ≡ false
    obligationNumericValuePromoted : Bool
    obligationNumericValuePromotedIsFalse :
      obligationNumericValuePromoted ≡ false
    falseNumericPromotionGuard : Bool
    falseNumericPromotionGuardIsTrue :
      falseNumericPromotionGuard ≡ true

open NumericAuthorityPayloadValidatorReceipt public

canonicalNumericAuthorityPayloadValidatorReceipt :
  NumericAuthorityPayloadValidatorReceipt
canonicalNumericAuthorityPayloadValidatorReceipt = record
  { receiptLabel =
      "numeric authority payload validator surface; no measured values loaded"
  ; sourceRegistry = Registry.repoWideConstantsRegistry
  ; sourceBindingReceipt =
      Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; sourceIntakeReceipt =
      Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; sourceNormalizedReceipt =
      Norm.canonicalNormalizedMeasuredAuthorityTokenReceipt
  ; sourceObligationIndex =
      Numeric.canonicalNumericAndAuthorityObligationIndex
  ; schemaFields = canonicalPayloadSchemaFields
  ; schemaKnownFields = canonicalSchemaKnownFields
  ; missingAuthorityPayloadFields =
      canonicalMissingAuthorityPayloadFields
  ; externalShapePayloadFields =
      canonicalExternalShapePayloadFields
  ; payloadFamilyCoverageRows =
      canonicalPayloadFamilyCoverageRows
  ; externalPayloadShapeRequirements =
      canonicalExternalPayloadShapeRequirements
  ; validationStates = canonicalPayloadValidationStates
  ; payloadEnvelopes = canonicalPayloadEnvelopes
  ; codataPayloadEnvelopes = canonicalCODATAPayloadEnvelopes
  ; pdgPayloadEnvelopes = canonicalPDGPayloadEnvelopes
  ; codataPDGPayloadEnvelopes =
      canonicalCODATAPDGPayloadEnvelopes
  ; acceptedPayloadEnvelopes = canonicalAcceptedPayloadEnvelopes
  ; loadedPayloadEnvelopes = canonicalLoadedPayloadEnvelopes
  ; schemaFieldCount = listCount canonicalPayloadSchemaFields
  ; schemaFieldCountIs20 = refl
  ; schemaKnownFieldCount = listCount canonicalSchemaKnownFields
  ; schemaKnownFieldCountIs12 = refl
  ; missingAuthorityPayloadFieldCount =
      listCount canonicalMissingAuthorityPayloadFields
  ; missingAuthorityPayloadFieldCountIs8 = refl
  ; externalShapePayloadFieldCount =
      listCount canonicalExternalShapePayloadFields
  ; externalShapePayloadFieldCountIs3 = refl
  ; payloadFamilyCoverageCount =
      listCount canonicalPayloadFamilyCoverageRows
  ; payloadFamilyCoverageCountIs3 = refl
  ; externalPayloadShapeRequirementCount =
      listCount canonicalExternalPayloadShapeRequirements
  ; externalPayloadShapeRequirementCountIs4 = refl
  ; validationStateCount =
      listCount canonicalPayloadValidationStates
  ; validationStateCountIs4 = refl
  ; payloadEnvelopeCount = listCount canonicalPayloadEnvelopes
  ; payloadEnvelopeCountIs18 = refl
  ; codataPayloadEnvelopeCount =
      listCount canonicalCODATAPayloadEnvelopes
  ; codataPayloadEnvelopeCountIs10 = refl
  ; pdgPayloadEnvelopeCount =
      listCount canonicalPDGPayloadEnvelopes
  ; pdgPayloadEnvelopeCountIs5 = refl
  ; codataPDGPayloadEnvelopeCount =
      listCount canonicalCODATAPDGPayloadEnvelopes
  ; codataPDGPayloadEnvelopeCountIs3 = refl
  ; acceptedPayloadEnvelopeCount =
      listCount canonicalAcceptedPayloadEnvelopes
  ; acceptedPayloadEnvelopeCountIs0 = refl
  ; loadedPayloadEnvelopeCount =
      listCount canonicalLoadedPayloadEnvelopes
  ; loadedPayloadEnvelopeCountIs0 = refl
  ; normalizedTokenCountCrossCheck =
      Norm.NormalizedMeasuredAuthorityTokenReceipt.normalizedTokenCount
        Norm.canonicalNormalizedMeasuredAuthorityTokenReceipt
  ; normalizedTokenCountCrossCheckIs18 =
      Norm.NormalizedMeasuredAuthorityTokenReceipt.normalizedTokenCountIs18
        Norm.canonicalNormalizedMeasuredAuthorityTokenReceipt
  ; bindingSlotCountCrossCheck =
      Binding.NumericMeasuredAuthorityBindingReceipt.measuredSlotCount
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; bindingSlotCountCrossCheckIs9 =
      Binding.NumericMeasuredAuthorityBindingReceipt.measuredSlotCountIs9
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; intakeRequestCountCrossCheck =
      Intake.NumericAuthorityTokenIntakeReceipt.requestedTokenCount
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; intakeRequestCountCrossCheckIs9 =
      Intake.NumericAuthorityTokenIntakeReceipt.requestedTokenCountIs9
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; allPayloadsMissingAuthorityArtifact = true
  ; allPayloadsMissingAuthorityArtifactIsTrue = refl
  ; allExternalShapeRequirementsMissingPayload = true
  ; allExternalShapeRequirementsMissingPayloadIsTrue = refl
  ; noPayloadCarriesMeasuredNumericValue = true
  ; noPayloadCarriesMeasuredNumericValueIsTrue = refl
  ; acceptedAuthorityTokenPresent = false
  ; acceptedAuthorityTokenPresentIsFalse = refl
  ; numericValueLoaded = false
  ; numericValueLoadedIsFalse = refl
  ; numericValuePromoted = false
  ; numericValuePromotedIsFalse = refl
  ; normalizedNumericValuePromoted =
      Norm.NormalizedMeasuredAuthorityTokenReceipt.normalizedNumericValuePromoted
        Norm.canonicalNormalizedMeasuredAuthorityTokenReceipt
  ; normalizedNumericValuePromotedIsFalse =
      Norm.NormalizedMeasuredAuthorityTokenReceipt.normalizedNumericValuePromotedIsFalse
        Norm.canonicalNormalizedMeasuredAuthorityTokenReceipt
  ; intakeNumericValuePromoted =
      Intake.NumericAuthorityTokenIntakeReceipt.numericValuePromoted
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; intakeNumericValuePromotedIsFalse =
      Intake.NumericAuthorityTokenIntakeReceipt.numericValuePromotedIsFalse
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; bindingNumericValuePromoted =
      Binding.NumericMeasuredAuthorityBindingReceipt.numericValuePromoted
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; bindingNumericValuePromotedIsFalse =
      Binding.NumericMeasuredAuthorityBindingReceipt.numericValuePromotedIsFalse
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; obligationNumericValuePromoted =
      Numeric.NumericAndAuthorityObligationIndex.numericValuePromoted
        Numeric.canonicalNumericAndAuthorityObligationIndex
  ; obligationNumericValuePromotedIsFalse =
      Numeric.NumericAndAuthorityObligationIndex.numericValuePromotedIsFalse
        Numeric.canonicalNumericAndAuthorityObligationIndex
  ; falseNumericPromotionGuard = true
  ; falseNumericPromotionGuardIsTrue = refl
  }

canonicalPayloadSchemaFieldCountIs20 :
  NumericAuthorityPayloadValidatorReceipt.schemaFieldCount
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 20
canonicalPayloadSchemaFieldCountIs20 = refl

canonicalPayloadSchemaKnownFieldCountIs12 :
  NumericAuthorityPayloadValidatorReceipt.schemaKnownFieldCount
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 12
canonicalPayloadSchemaKnownFieldCountIs12 = refl

canonicalPayloadMissingAuthorityFieldCountIs8 :
  NumericAuthorityPayloadValidatorReceipt.missingAuthorityPayloadFieldCount
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 8
canonicalPayloadMissingAuthorityFieldCountIs8 = refl

canonicalPayloadFamilyCoverageCountIs3 :
  NumericAuthorityPayloadValidatorReceipt.payloadFamilyCoverageCount
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 3
canonicalPayloadFamilyCoverageCountIs3 = refl

canonicalPayloadEnvelopeCountIs18 :
  NumericAuthorityPayloadValidatorReceipt.payloadEnvelopeCount
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 18
canonicalPayloadEnvelopeCountIs18 = refl

canonicalPayloadAcceptedEnvelopeCountIs0 :
  NumericAuthorityPayloadValidatorReceipt.acceptedPayloadEnvelopeCount
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 0
canonicalPayloadAcceptedEnvelopeCountIs0 = refl

canonicalPayloadLoadedEnvelopeCountIs0 :
  NumericAuthorityPayloadValidatorReceipt.loadedPayloadEnvelopeCount
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 0
canonicalPayloadLoadedEnvelopeCountIs0 = refl

canonicalPayloadNormalizedTokenCrossCheckIs18 :
  NumericAuthorityPayloadValidatorReceipt.normalizedTokenCountCrossCheck
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 18
canonicalPayloadNormalizedTokenCrossCheckIs18 = refl

canonicalPayloadBindingSlotCrossCheckIs9 :
  NumericAuthorityPayloadValidatorReceipt.bindingSlotCountCrossCheck
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 9
canonicalPayloadBindingSlotCrossCheckIs9 = refl

canonicalPayloadIntakeRequestCrossCheckIs9 :
  NumericAuthorityPayloadValidatorReceipt.intakeRequestCountCrossCheck
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ 9
canonicalPayloadIntakeRequestCrossCheckIs9 = refl

canonicalPayloadAcceptedAuthorityTokenPresentIsFalse :
  NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresent
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ false
canonicalPayloadAcceptedAuthorityTokenPresentIsFalse = refl

canonicalPayloadNumericValueLoadedIsFalse :
  NumericAuthorityPayloadValidatorReceipt.numericValueLoaded
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ false
canonicalPayloadNumericValueLoadedIsFalse = refl

canonicalPayloadNumericValuePromotedIsFalse :
  NumericAuthorityPayloadValidatorReceipt.numericValuePromoted
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ false
canonicalPayloadNumericValuePromotedIsFalse = refl

canonicalPayloadFalseNumericPromotionGuard :
  NumericAuthorityPayloadValidatorReceipt.falseNumericPromotionGuard
    canonicalNumericAuthorityPayloadValidatorReceipt
  ≡ true
canonicalPayloadFalseNumericPromotionGuard = refl
