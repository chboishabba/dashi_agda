module DASHI.Physics.Closure.HEPDataObservableSchema where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- HEPData observable schema surface.
--
-- This module defines the typed shape a future HEPDataObservable must carry
-- before it can feed any W3 accepted-authority or W8 origin-promotion route.
-- It is intentionally non-promoting: there is no authority token, no external
-- receipt, no real dataset receipt, and no empirical adequacy value here.

record HEPDataRecordSemantics : Set where
  field
    recordId :
      String

    recordVersion :
      String

    submissionId :
      String

    recordDoi :
      String

    sourceLandingPage :
      String

record HEPDataTableSemantics : Set where
  field
    tableName :
      String

    tablePath :
      String

    tableVersion :
      String

    rowSelection :
      String

    observableColumn :
      String

    uncertaintyColumns :
      List String

record HEPDataCitationSemantics : Set where
  field
    collaboration :
      String

    publicationDoi :
      String

    arxivId :
      String

    inspireRecord :
      String

    citationText :
      String

record HEPDataUnitSemantics : Set where
  field
    observableQuantity :
      String

    unitLabel :
      String

    dimensionLabel :
      String

    scaleConvention :
      String

    conversionToInternalCarrier :
      String

record HEPDataBinningSemantics : Set where
  field
    binAxis :
      String

    lowEdgeColumn :
      String

    highEdgeColumn :
      String

    centerColumn :
      String

    binInclusionConvention :
      String

record HEPDataCovarianceSemantics : Set where
  field
    covarianceSource :
      String

    covarianceKind :
      String

    matrixShape :
      String

    correlationNormalization :
      String

    statisticalSystematicSplit :
      String

record HEPDataLocalChecksumOrHash : Set where
  field
    localArtifactPath :
      String

    digestAlgorithm :
      String

    digestValue :
      String

    digestInputCanonicalization :
      String

    verificationCommand :
      String

record HEPDataProvenanceSemantics : Set where
  field
    retrievalUri :
      String

    retrievalTimestamp :
      String

    adapterName :
      String

    adapterVersion :
      String

    transformLog :
      List String

    licenseOrUseTerms :
      String

record HEPDataObservableSchemaSurface : Set where
  field
    recordSemantics :
      HEPDataRecordSemantics

    tableSemantics :
      HEPDataTableSemantics

    citationSemantics :
      HEPDataCitationSemantics

    unitSemantics :
      HEPDataUnitSemantics

    binningSemantics :
      HEPDataBinningSemantics

    covarianceSemantics :
      HEPDataCovarianceSemantics

    localChecksumOrHash :
      HEPDataLocalChecksumOrHash

    provenanceSemantics :
      HEPDataProvenanceSemantics

    dashiObservableTarget :
      String

    comparisonLawTarget :
      String

record HEPDataObservable : Setω where
  field
    schema :
      HEPDataObservableSchemaSurface

    projectionContractName :
      String

    goldenConformanceTestNames :
      List String

------------------------------------------------------------------------
-- Required-field diagnostic.

data HEPDataObservableRequiredField : Set where
  requiredRecordSemantics :
    HEPDataObservableRequiredField
  requiredTableSemantics :
    HEPDataObservableRequiredField
  requiredCitationSemantics :
    HEPDataObservableRequiredField
  requiredUnitSemantics :
    HEPDataObservableRequiredField
  requiredBinningSemantics :
    HEPDataObservableRequiredField
  requiredCovarianceSemantics :
    HEPDataObservableRequiredField
  requiredLocalChecksumOrHash :
    HEPDataObservableRequiredField
  requiredProvenanceSemantics :
    HEPDataObservableRequiredField
  requiredDashiObservableTarget :
    HEPDataObservableRequiredField
  requiredComparisonLawTarget :
    HEPDataObservableRequiredField
  requiredProjectionContract :
    HEPDataObservableRequiredField
  requiredGoldenConformanceTests :
    HEPDataObservableRequiredField

canonicalHEPDataObservableRequiredFields :
  List HEPDataObservableRequiredField
canonicalHEPDataObservableRequiredFields =
  requiredRecordSemantics
  ∷ requiredTableSemantics
  ∷ requiredCitationSemantics
  ∷ requiredUnitSemantics
  ∷ requiredBinningSemantics
  ∷ requiredCovarianceSemantics
  ∷ requiredLocalChecksumOrHash
  ∷ requiredProvenanceSemantics
  ∷ requiredDashiObservableTarget
  ∷ requiredComparisonLawTarget
  ∷ requiredProjectionContract
  ∷ requiredGoldenConformanceTests
  ∷ []

data HEPDataObservableSchemaCurrentStatus : Set where
  schemaSurfaceDefinedButObservableUnpromoted :
    HEPDataObservableSchemaCurrentStatus

data HEPDataObservablePromotionGate : Set where
  w3AcceptedAuthorityExternalReceiptRequired :
    HEPDataObservablePromotionGate
  w8OriginReceiptPromotionExternalReceiptRequired :
    HEPDataObservablePromotionGate
  hepDataToITIRAuthorityAdapterRequired :
    HEPDataObservablePromotionGate
  acceptedDatasetAuthorityRequired :
    HEPDataObservablePromotionGate

canonicalHEPDataObservablePromotionGates :
  List HEPDataObservablePromotionGate
canonicalHEPDataObservablePromotionGates =
  w3AcceptedAuthorityExternalReceiptRequired
  ∷ w8OriginReceiptPromotionExternalReceiptRequired
  ∷ hepDataToITIRAuthorityAdapterRequired
  ∷ acceptedDatasetAuthorityRequired
  ∷ []

record HEPDataObservableSchemaRequestDiagnostic : Setω where
  field
    currentStatus :
      HEPDataObservableSchemaCurrentStatus

    futureObservableName :
      String

    futureSchemaName :
      String

    requiredFields :
      List HEPDataObservableRequiredField

    requiredFieldsAreCanonical :
      requiredFields ≡ canonicalHEPDataObservableRequiredFields

    promotionGates :
      List HEPDataObservablePromotionGate

    promotionGatesAreCanonical :
      promotionGates ≡ canonicalHEPDataObservablePromotionGates

    exactRequiredFieldNames :
      List String

    exactExternalReceiptNames :
      List String

    providerInstructions :
      List String

    diagnosticBoundary :
      List String

    strictBlockerImpact :
      List String

canonicalHEPDataObservableSchemaRequestDiagnostic :
  HEPDataObservableSchemaRequestDiagnostic
canonicalHEPDataObservableSchemaRequestDiagnostic =
  record
    { currentStatus =
        schemaSurfaceDefinedButObservableUnpromoted
    ; futureObservableName =
        "DASHI.Physics.Closure.HEPDataObservableSchema.HEPDataObservable"
    ; futureSchemaName =
        "DASHI.Physics.Closure.HEPDataObservableSchema.HEPDataObservableSchemaSurface"
    ; requiredFields =
        canonicalHEPDataObservableRequiredFields
    ; requiredFieldsAreCanonical =
        refl
    ; promotionGates =
        canonicalHEPDataObservablePromotionGates
    ; promotionGatesAreCanonical =
        refl
    ; exactRequiredFieldNames =
        "recordSemantics : HEPDataRecordSemantics"
        ∷ "tableSemantics : HEPDataTableSemantics"
        ∷ "citationSemantics : HEPDataCitationSemantics"
        ∷ "unitSemantics : HEPDataUnitSemantics"
        ∷ "binningSemantics : HEPDataBinningSemantics"
        ∷ "covarianceSemantics : HEPDataCovarianceSemantics"
        ∷ "localChecksumOrHash : HEPDataLocalChecksumOrHash"
        ∷ "provenanceSemantics : HEPDataProvenanceSemantics"
        ∷ "dashiObservableTarget : String"
        ∷ "comparisonLawTarget : String"
        ∷ "projectionContractName : String"
        ∷ "goldenConformanceTestNames : List String"
        ∷ []
    ; exactExternalReceiptNames =
        "DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation.W3AcceptedAuthorityExternalReceipt"
        ∷ "DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation.OriginReceiptPromotionExternalReceipt"
        ∷ "accepted HEPData-to-ITIR authority adapter receipt"
        ∷ "accepted dataset authority token supplied outside this module"
        ∷ []
    ; providerInstructions =
        "Supply a concrete HEPDataObservable only after the record, table, citation, units, binning, covariance, checksum/hash, provenance, projection, comparison-law, and conformance-test fields are all populated"
        ∷ "The checksum/hash must identify the local canonical artifact that the projection and tests consume"
        ∷ "The provenance fields must identify retrieval URI, retrieval time, adapter identity, transform log, and license/use terms"
        ∷ "Promotion to W3 still requires the accepted-authority external receipt named above"
        ∷ "Promotion to W8 still requires the origin-promotion external receipt named above"
        ∷ []
    ; diagnosticBoundary =
        "This module is a schema/request surface for a future HEPDataObservable"
        ∷ "It does not construct a HEPDataObservable value from current data"
        ∷ "It does not construct an accepted dataset authority token"
        ∷ "It does not construct W3AcceptedAuthorityExternalReceipt"
        ∷ "It does not construct OriginReceiptPromotionExternalReceipt"
        ∷ "It does not promote empirical adequacy, origin promotion, or closure"
        ∷ []
    ; strictBlockerImpact =
        "HEPData source candidates remain non-promoting until this schema is populated and checked"
        ∷ "W3 remains blocked until the schema-backed observable also carries accepted empirical authority"
        ∷ "W8 remains blocked until origin-promotion evidence is externally supplied"
        ∷ "The next admissible worker lane is a concrete projection/adapter/checksum provider or a typed rejection at that contract"
        ∷ []
    }

canonicalHEPDataObservableSchemaCurrentStatus :
  HEPDataObservableSchemaCurrentStatus
canonicalHEPDataObservableSchemaCurrentStatus =
  schemaSurfaceDefinedButObservableUnpromoted
