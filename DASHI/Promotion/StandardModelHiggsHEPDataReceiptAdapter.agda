module DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Standard Model Higgs/HEPData receipt adapter.
--
-- This module is the typed consumer for
-- scripts/sm_higgs_hepdata_receipt_adapter.py.  The script emits
-- checksum-bound JSON receipts from the sibling dashiQ Higgs/HEPData
-- surfaces:
--
--   * observed ATLAS H -> gamma gamma full-covariance MDL shape analysis;
--   * pseudo-data detectability calibration using the same covariance source;
--   * an adapter summary with explicit false promotion gates.
--
-- The adapter is intentionally non-promoting.  It improves the empirical SM
-- observable surface by making the existing dashiQ work consumable, while
-- preserving the missing SM-relative baseline, authority-token, holdout, and
-- comparison-law blockers.

listCount : {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Source and artifact taxonomy.

data HiggsHEPDataSourceKind : Set where
  observedShapeScript :
    HiggsHEPDataSourceKind

  pseudoDetectabilityScript :
    HiggsHEPDataSourceKind

  hepDataQueryHelper :
    HiggsHEPDataSourceKind

  hepDataRecordResolver :
    HiggsHEPDataSourceKind

data HiggsHEPDataArtifactKind : Set where
  observedShapeReceiptJSON :
    HiggsHEPDataArtifactKind

  pseudoDetectabilityReceiptJSON :
    HiggsHEPDataArtifactKind

  adapterSummaryJSON :
    HiggsHEPDataArtifactKind

  adapterMarkdownSummary :
    HiggsHEPDataArtifactKind

data HiggsHEPDataGate : Set where
  sourceChecksumGate :
    HiggsHEPDataGate

  covarianceSurfaceGate :
    HiggsHEPDataGate

  pseudoDetectabilityGate :
    HiggsHEPDataGate

  smRelativeBaselineGate :
    HiggsHEPDataGate

  authorityTokenGate :
    HiggsHEPDataGate

  holdoutProtocolGate :
    HiggsHEPDataGate

  comparisonLawGate :
    HiggsHEPDataGate

  empiricalPromotionGate :
    HiggsHEPDataGate

sourceKindLabel :
  HiggsHEPDataSourceKind →
  String
sourceKindLabel observedShapeScript =
  "observed full-covariance MDL shape script"
sourceKindLabel pseudoDetectabilityScript =
  "pseudo-data detectability script"
sourceKindLabel hepDataQueryHelper =
  "HEPData query helper"
sourceKindLabel hepDataRecordResolver =
  "HEPData record resolver"

artifactKindLabel :
  HiggsHEPDataArtifactKind →
  String
artifactKindLabel observedShapeReceiptJSON =
  "observed shape receipt JSON"
artifactKindLabel pseudoDetectabilityReceiptJSON =
  "pseudo detectability receipt JSON"
artifactKindLabel adapterSummaryJSON =
  "adapter summary JSON"
artifactKindLabel adapterMarkdownSummary =
  "adapter markdown summary"

------------------------------------------------------------------------
-- Rows.

record HiggsHEPDataSourceRow : Set where
  field
    sourceKind :
      HiggsHEPDataSourceKind

    sourceKindText :
      String

    sourceKindTextIsCanonical :
      sourceKindText ≡ sourceKindLabel sourceKind

    sourcePath :
      String

    role :
      String

    checksumRequired :
      Bool

    checksumRequiredIsTrue :
      checksumRequired ≡ true

    theoremAuthority :
      Bool

    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

open HiggsHEPDataSourceRow public

mkSourceRow :
  HiggsHEPDataSourceKind →
  String →
  String →
  HiggsHEPDataSourceRow
mkSourceRow kind path rowRole =
  record
    { sourceKind = kind
    ; sourceKindText = sourceKindLabel kind
    ; sourceKindTextIsCanonical = refl
    ; sourcePath = path
    ; role = rowRole
    ; checksumRequired = true
    ; checksumRequiredIsTrue = refl
    ; theoremAuthority = false
    ; theoremAuthorityIsFalse = refl
    }

record HiggsHEPDataArtifactRow : Set where
  field
    artifactKind :
      HiggsHEPDataArtifactKind

    artifactKindText :
      String

    artifactKindTextIsCanonical :
      artifactKindText ≡ artifactKindLabel artifactKind

    artifactPath :
      String

    producedBy :
      String

    receiptSchema :
      String

    consumerSurface :
      String

    promotesEmpiricalValidation :
      Bool

    promotesEmpiricalValidationIsFalse :
      promotesEmpiricalValidation ≡ false

open HiggsHEPDataArtifactRow public

mkArtifactRow :
  HiggsHEPDataArtifactKind →
  String →
  String →
  HiggsHEPDataArtifactRow
mkArtifactRow kind path consumer =
  record
    { artifactKind = kind
    ; artifactKindText = artifactKindLabel kind
    ; artifactKindTextIsCanonical = refl
    ; artifactPath = path
    ; producedBy = "scripts/sm_higgs_hepdata_receipt_adapter.py"
    ; receiptSchema = "dashi-sm-higgs-hepdata-receipt-v1"
    ; consumerSurface = consumer
    ; promotesEmpiricalValidation = false
    ; promotesEmpiricalValidationIsFalse = refl
    }

record HiggsHEPDataGateStatus : Set where
  field
    gate :
      HiggsHEPDataGate

    gateLabel :
      String

    satisfiedByAdapter :
      Bool

    remainingObligation :
      String

    promotionGuardStillFalse :
      Bool

    promotionGuardStillFalseIsTrue :
      promotionGuardStillFalse ≡ true

open HiggsHEPDataGateStatus public

mkGateStatus :
  HiggsHEPDataGate →
  String →
  Bool →
  String →
  HiggsHEPDataGateStatus
mkGateStatus gate label satisfied obligation =
  record
    { gate = gate
    ; gateLabel = label
    ; satisfiedByAdapter = satisfied
    ; remainingObligation = obligation
    ; promotionGuardStillFalse = true
    ; promotionGuardStillFalseIsTrue = refl
    }

canonicalHiggsHEPDataSourceRows :
  List HiggsHEPDataSourceRow
canonicalHiggsHEPDataSourceRows =
  mkSourceRow
    observedShapeScript
    "/home/c/Documents/code/dashiQ/13tev.py"
    "ATLAS H to gamma gamma 13 TeV full-covariance MDL shape-complexity source"
  ∷ mkSourceRow
    pseudoDetectabilityScript
    "/home/c/Documents/code/dashiQ/pseudo_data_harness.py"
    "covariance-aware pseudo-data detectability source"
  ∷ mkSourceRow
    hepDataQueryHelper
    "/home/c/Documents/code/dashiQ/reusable_query.py"
    "provider-table discovery and reusable HEPData query helper"
  ∷ mkSourceRow
    hepDataRecordResolver
    "/home/c/Documents/code/dashiQ/resolve_hepdata_record.py"
    "record resolver for public HEPData Higgs/differential surfaces"
  ∷ []

canonicalHiggsHEPDataArtifactRows :
  List HiggsHEPDataArtifactRow
canonicalHiggsHEPDataArtifactRows =
  mkArtifactRow
    observedShapeReceiptJSON
    "outputs/sm_higgs_hepdata_receipts/sm_higgs_observed_shape_receipt.json"
    "DASHI.Promotion.StandardModelObservableAuthorityBridge"
  ∷ mkArtifactRow
    pseudoDetectabilityReceiptJSON
    "outputs/sm_higgs_hepdata_receipts/sm_higgs_pseudo_detectability_receipt.json"
    "DASHI.Promotion.StandardModelObservableAuthorityBridge"
  ∷ mkArtifactRow
    adapterSummaryJSON
    "outputs/sm_higgs_hepdata_receipts/sm_higgs_adapter_summary.json"
    "DASHI.Promotion.StandardModelObservableAuthorityBridge"
  ∷ mkArtifactRow
    adapterMarkdownSummary
    "outputs/sm_higgs_hepdata_receipts/sm_higgs_hepdata_receipt_adapter.md"
    "Docs/UnifiedRoutesLanePlan.md"
  ∷ []

canonicalHiggsHEPDataGateStatuses :
  List HiggsHEPDataGateStatus
canonicalHiggsHEPDataGateStatuses =
  mkGateStatus
    sourceChecksumGate
    "source checksums"
    true
    "adapter emits SHA-256 for the four dashiQ source files"
  ∷ mkGateStatus
    covarianceSurfaceGate
    "full covariance surface"
    true
    "13tev.py and pseudo_data_harness.py consume published correlation tables"
  ∷ mkGateStatus
    pseudoDetectabilityGate
    "pseudo detectability"
    true
    "pseudo-data injection and projection modes are exposed in the receipt"
  ∷ mkGateStatus
    smRelativeBaselineGate
    "SM-relative baseline"
    false
    "need a theory baseline table or event-generator replay digest"
  ∷ mkGateStatus
    authorityTokenGate
    "accepted authority token"
    false
    "need provider/version/checksum acceptance under repo authority policy"
  ∷ mkGateStatus
    holdoutProtocolGate
    "holdout protocol"
    false
    "need frozen-prediction or holdout protocol before empirical promotion"
  ∷ mkGateStatus
    comparisonLawGate
    "comparison law"
    false
    "need a covariance-aware prediction-versus-measurement law"
  ∷ mkGateStatus
    empiricalPromotionGate
    "empirical promotion"
    false
    "blocked by SM baseline, authority, holdout, and comparison-law gaps"
  ∷ []

sourceRowCount :
  Nat
sourceRowCount =
  listCount canonicalHiggsHEPDataSourceRows

artifactRowCount :
  Nat
artifactRowCount =
  listCount canonicalHiggsHEPDataArtifactRows

gateStatusCount :
  Nat
gateStatusCount =
  listCount canonicalHiggsHEPDataGateStatuses

sourceRowCountIsFour :
  sourceRowCount ≡ 4
sourceRowCountIsFour = refl

artifactRowCountIsFour :
  artifactRowCount ≡ 4
artifactRowCountIsFour = refl

gateStatusCountIsEight :
  gateStatusCount ≡ 8
gateStatusCountIsEight = refl

------------------------------------------------------------------------
-- Canonical adapter receipt.

record StandardModelHiggsHEPDataReceiptAdapter : Setω where
  field
    receiptLabel :
      String

    emitterScript :
      String

    validationCommand :
      String

    sourceRows :
      List HiggsHEPDataSourceRow

    sourceCount :
      Nat

    sourceCountMatches :
      sourceCount ≡ listCount sourceRows

    artifactRows :
      List HiggsHEPDataArtifactRow

    artifactCount :
      Nat

    artifactCountMatches :
      artifactCount ≡ listCount artifactRows

    gateStatuses :
      List HiggsHEPDataGateStatus

    gateCount :
      Nat

    gateCountMatches :
      gateCount ≡ listCount gateStatuses

    observedShapeSurfacePresent :
      Bool

    observedShapeSurfacePresentIsTrue :
      observedShapeSurfacePresent ≡ true

    pseudoDetectabilitySurfacePresent :
      Bool

    pseudoDetectabilitySurfacePresentIsTrue :
      pseudoDetectabilitySurfacePresent ≡ true

    smRelativeBaselinePresent :
      Bool

    smRelativeBaselinePresentIsFalse :
      smRelativeBaselinePresent ≡ false

    acceptedAuthorityTokenPresent :
      Bool

    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false

    empiricalValidationPromoted :
      Bool

    empiricalValidationPromotedIsFalse :
      empiricalValidationPromoted ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

open StandardModelHiggsHEPDataReceiptAdapter public

canonicalStandardModelHiggsHEPDataReceiptAdapter :
  StandardModelHiggsHEPDataReceiptAdapter
canonicalStandardModelHiggsHEPDataReceiptAdapter =
  record
    { receiptLabel =
        "canonical Standard Model Higgs HEPData receipt adapter"
    ; emitterScript =
        "scripts/sm_higgs_hepdata_receipt_adapter.py"
    ; validationCommand =
        "python scripts/sm_higgs_hepdata_receipt_adapter.py --generated-at 2026-06-07T00:00:00+00:00"
    ; sourceRows =
        canonicalHiggsHEPDataSourceRows
    ; sourceCount =
        sourceRowCount
    ; sourceCountMatches =
        refl
    ; artifactRows =
        canonicalHiggsHEPDataArtifactRows
    ; artifactCount =
        artifactRowCount
    ; artifactCountMatches =
        refl
    ; gateStatuses =
        canonicalHiggsHEPDataGateStatuses
    ; gateCount =
        gateStatusCount
    ; gateCountMatches =
        refl
    ; observedShapeSurfacePresent =
        true
    ; observedShapeSurfacePresentIsTrue =
        refl
    ; pseudoDetectabilitySurfacePresent =
        true
    ; pseudoDetectabilitySurfacePresentIsTrue =
        refl
    ; smRelativeBaselinePresent =
        false
    ; smRelativeBaselinePresentIsFalse =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; empiricalValidationPromoted =
        false
    ; empiricalValidationPromotedIsFalse =
        refl
    ; standardModelPromoted =
        false
    ; standardModelPromotedIsFalse =
        refl
    }

canonicalHiggsHEPDataAdapterSourceCountIsFour :
  StandardModelHiggsHEPDataReceiptAdapter.sourceCount
    canonicalStandardModelHiggsHEPDataReceiptAdapter
  ≡ 4
canonicalHiggsHEPDataAdapterSourceCountIsFour = refl

canonicalHiggsHEPDataAdapterArtifactCountIsFour :
  StandardModelHiggsHEPDataReceiptAdapter.artifactCount
    canonicalStandardModelHiggsHEPDataReceiptAdapter
  ≡ 4
canonicalHiggsHEPDataAdapterArtifactCountIsFour = refl

canonicalHiggsHEPDataAdapterGateCountIsEight :
  StandardModelHiggsHEPDataReceiptAdapter.gateCount
    canonicalStandardModelHiggsHEPDataReceiptAdapter
  ≡ 8
canonicalHiggsHEPDataAdapterGateCountIsEight = refl
