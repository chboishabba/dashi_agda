module DASHI.Promotion.StandardModelHiggsCovariantComparisonLaw where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter as HEPData

------------------------------------------------------------------------
-- Standard Model Higgs covariant comparison law.
--
-- This is the typed consumer surface for the intended
-- scripts/sm_higgs_covariant_comparison_law.py adapter.  It consumes the
-- checked Higgs/HEPData receipt adapter and records the four rows needed for
-- a covariance-aware H -> gamma gamma comparison against an SM-relative
-- baseline:
--
--   * baseline replay digest;
--   * HEPData binning compatibility;
--   * positive-definite covariance and chi-square law;
--   * observed receipt consumption.
--
-- It is deliberately fail-closed.  The row surface can be checked before an
-- accepted provider authority token, holdout split, empirical validation
-- verdict, or Standard Model promotion exists.

listCount : {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Taxonomy.

data HiggsComparisonRowKind : Set where
  baselineReplayDigestRow :
    HiggsComparisonRowKind

  hepDataBinningCompatibilityRow :
    HiggsComparisonRowKind

  covarianceChiSquareLawRow :
    HiggsComparisonRowKind

  observedReceiptConsumptionRow :
    HiggsComparisonRowKind

data HiggsComparisonArtifactKind : Set where
  comparisonLawScript :
    HiggsComparisonArtifactKind

  comparisonSummaryJSON :
    HiggsComparisonArtifactKind

  comparisonRowsJSON :
    HiggsComparisonArtifactKind

  comparisonMarkdownSummary :
    HiggsComparisonArtifactKind

data HiggsComparisonGate : Set where
  upstreamHEPDataAdapterGate :
    HiggsComparisonGate

  baselineReplayDigestGate :
    HiggsComparisonGate

  binningCompatibilityGate :
    HiggsComparisonGate

  covariancePositiveDefiniteGate :
    HiggsComparisonGate

  chiSquareLawWellTypedGate :
    HiggsComparisonGate

  authorityTokenGate :
    HiggsComparisonGate

  holdoutProtocolGate :
    HiggsComparisonGate

  empiricalAndSMPromotionGate :
    HiggsComparisonGate

comparisonRowKindLabel :
  HiggsComparisonRowKind →
  String
comparisonRowKindLabel baselineReplayDigestRow =
  "SM-relative baseline replay digest"
comparisonRowKindLabel hepDataBinningCompatibilityRow =
  "HEPData binning compatibility"
comparisonRowKindLabel covarianceChiSquareLawRow =
  "covariance positive-definite chi-square law"
comparisonRowKindLabel observedReceiptConsumptionRow =
  "observed Higgs HEPData receipt consumption"

artifactKindLabel :
  HiggsComparisonArtifactKind →
  String
artifactKindLabel comparisonLawScript =
  "covariant comparison law script"
artifactKindLabel comparisonSummaryJSON =
  "covariant comparison summary JSON"
artifactKindLabel comparisonRowsJSON =
  "covariant comparison rows JSON"
artifactKindLabel comparisonMarkdownSummary =
  "covariant comparison markdown summary"

gateLabel :
  HiggsComparisonGate →
  String
gateLabel upstreamHEPDataAdapterGate =
  "upstream Higgs HEPData adapter"
gateLabel baselineReplayDigestGate =
  "baseline replay digest"
gateLabel binningCompatibilityGate =
  "binning compatibility"
gateLabel covariancePositiveDefiniteGate =
  "covariance positive definite"
gateLabel chiSquareLawWellTypedGate =
  "chi-square law well typed"
gateLabel authorityTokenGate =
  "accepted authority token"
gateLabel holdoutProtocolGate =
  "holdout protocol"
gateLabel empiricalAndSMPromotionGate =
  "empirical and Standard Model promotion"

------------------------------------------------------------------------
-- Rows.

record HiggsComparisonRow : Set where
  field
    rowKind :
      HiggsComparisonRowKind

    rowKindText :
      String

    rowKindTextIsCanonical :
      rowKindText ≡ comparisonRowKindLabel rowKind

    observableName :
      String

    inputArtifact :
      String

    outputArtifact :
      String

    requiredEvidence :
      List String

    consumedUpstreamSurface :
      String

    comparisonLawComponentPresent :
      Bool

    comparisonLawComponentPresentIsTrue :
      comparisonLawComponentPresent ≡ true

    promotesEmpiricalValidation :
      Bool

    promotesEmpiricalValidationIsFalse :
      promotesEmpiricalValidation ≡ false

open HiggsComparisonRow public

mkComparisonRow :
  HiggsComparisonRowKind →
  String →
  String →
  String →
  List String →
  HiggsComparisonRow
mkComparisonRow kind observable input output evidence =
  record
    { rowKind =
        kind
    ; rowKindText =
        comparisonRowKindLabel kind
    ; rowKindTextIsCanonical =
        refl
    ; observableName =
        observable
    ; inputArtifact =
        input
    ; outputArtifact =
        output
    ; requiredEvidence =
        evidence
    ; consumedUpstreamSurface =
        "DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter"
    ; comparisonLawComponentPresent =
        true
    ; comparisonLawComponentPresentIsTrue =
        refl
    ; promotesEmpiricalValidation =
        false
    ; promotesEmpiricalValidationIsFalse =
        refl
    }

record HiggsComparisonArtifactRow : Set where
  field
    artifactKind :
      HiggsComparisonArtifactKind

    artifactKindText :
      String

    artifactKindTextIsCanonical :
      artifactKindText ≡ artifactKindLabel artifactKind

    artifactPath :
      String

    producer :
      String

    schemaOrRole :
      String

    checksumRequired :
      Bool

    checksumRequiredIsTrue :
      checksumRequired ≡ true

    promotesStandardModel :
      Bool

    promotesStandardModelIsFalse :
      promotesStandardModel ≡ false

open HiggsComparisonArtifactRow public

mkArtifactRow :
  HiggsComparisonArtifactKind →
  String →
  String →
  HiggsComparisonArtifactRow
mkArtifactRow kind path role =
  record
    { artifactKind =
        kind
    ; artifactKindText =
        artifactKindLabel kind
    ; artifactKindTextIsCanonical =
        refl
    ; artifactPath =
        path
    ; producer =
        "scripts/sm_higgs_covariant_comparison_law.py"
    ; schemaOrRole =
        role
    ; checksumRequired =
        true
    ; checksumRequiredIsTrue =
        refl
    ; promotesStandardModel =
        false
    ; promotesStandardModelIsFalse =
        refl
    }

record HiggsComparisonGateStatus : Set where
  field
    gate :
      HiggsComparisonGate

    gateText :
      String

    gateTextIsCanonical :
      gateText ≡ gateLabel gate

    satisfiedByComparisonSurface :
      Bool

    remainingObligation :
      String

    promotionGuardStillFalse :
      Bool

    promotionGuardStillFalseIsTrue :
      promotionGuardStillFalse ≡ true

open HiggsComparisonGateStatus public

mkGateStatus :
  HiggsComparisonGate →
  Bool →
  String →
  HiggsComparisonGateStatus
mkGateStatus gate satisfied obligation =
  record
    { gate =
        gate
    ; gateText =
        gateLabel gate
    ; gateTextIsCanonical =
        refl
    ; satisfiedByComparisonSurface =
        satisfied
    ; remainingObligation =
        obligation
    ; promotionGuardStillFalse =
        true
    ; promotionGuardStillFalseIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Canonical rows.

canonicalHiggsComparisonRows :
  List HiggsComparisonRow
canonicalHiggsComparisonRows =
  mkComparisonRow
    baselineReplayDigestRow
    "H -> gamma gamma SM baseline"
    "SM-relative theory baseline table or generator replay digest"
    "outputs/sm_higgs_covariant_comparison/sm_higgs_baseline_replay_digest.json"
    ( "baseline source identifier"
    ∷ "baseline source checksum"
    ∷ "generator, order, PDF, scale, and fiducial convention"
    ∷ []
    )
  ∷ mkComparisonRow
    hepDataBinningCompatibilityRow
    "pT_yy, yAbs_yy, N_j_30"
    "outputs/sm_higgs_hepdata_receipts/sm_higgs_observed_shape_receipt.json"
    "outputs/sm_higgs_covariant_comparison/sm_higgs_binning_compatibility.json"
    ( "observable names match the HEPData receipt"
    ∷ "bin edge count and order match the baseline"
    ∷ "unit and fiducial-region convention are recorded"
    ∷ []
    )
  ∷ mkComparisonRow
    covarianceChiSquareLawRow
    "ATLAS H -> gamma gamma full covariance"
    "outputs/sm_higgs_hepdata_receipts/sm_higgs_observed_shape_receipt.json"
    "outputs/sm_higgs_covariant_comparison/sm_higgs_covariant_comparison_rows.json"
    ( "covariance matrix is square and symmetric"
    ∷ "positive-definite check or fail-closed singular verdict"
    ∷ "chi-square residual (d - m)^T Sigma^-1 (d - m)"
    ∷ []
    )
  ∷ mkComparisonRow
    observedReceiptConsumptionRow
    "observed ATLAS MDL shape rows"
    "DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter"
    "outputs/sm_higgs_covariant_comparison/sm_higgs_covariant_comparison_summary.json"
    ( "consumes canonicalStandardModelHiggsHEPDataReceiptAdapter"
    ∷ "preserves four observed rows from the upstream adapter"
    ∷ "does not infer empirical adequacy without authority and holdout gates"
    ∷ []
    )
  ∷ []

canonicalHiggsComparisonArtifactRows :
  List HiggsComparisonArtifactRow
canonicalHiggsComparisonArtifactRows =
  mkArtifactRow
    comparisonLawScript
    "scripts/sm_higgs_covariant_comparison_law.py"
    "emits the fail-closed covariant comparison receipt"
  ∷ mkArtifactRow
    comparisonSummaryJSON
    "outputs/sm_higgs_covariant_comparison/sm_higgs_covariant_comparison_summary.json"
    "summary receipt for comparison gates and promotion bits"
  ∷ mkArtifactRow
    comparisonRowsJSON
    "outputs/sm_higgs_covariant_comparison/sm_higgs_covariant_comparison_rows.json"
    "per-observable baseline, covariance, and chi-square rows"
  ∷ mkArtifactRow
    comparisonMarkdownSummary
    "outputs/sm_higgs_covariant_comparison/sm_higgs_covariant_comparison_law.md"
    "human-readable non-promoting comparison summary"
  ∷ []

canonicalHiggsComparisonGateStatuses :
  List HiggsComparisonGateStatus
canonicalHiggsComparisonGateStatuses =
  mkGateStatus
    upstreamHEPDataAdapterGate
    true
    "consumes canonicalStandardModelHiggsHEPDataReceiptAdapter"
  ∷ mkGateStatus
    baselineReplayDigestGate
    false
    "need an accepted SM-relative theory baseline table or generator replay digest"
  ∷ mkGateStatus
    binningCompatibilityGate
    true
    "comparison rows record observable and binning compatibility obligations"
  ∷ mkGateStatus
    covariancePositiveDefiniteGate
    true
    "comparison rows require positive-definite covariance or a fail-closed verdict"
  ∷ mkGateStatus
    chiSquareLawWellTypedGate
    true
    "row surface fixes the covariance-aware chi-square comparison law"
  ∷ mkGateStatus
    authorityTokenGate
    false
    "HEPData, ATLAS, and baseline-provider authority tokens are not accepted"
  ∷ mkGateStatus
    holdoutProtocolGate
    false
    "need frozen-prediction or independent holdout protocol"
  ∷ mkGateStatus
    empiricalAndSMPromotionGate
    false
    "empirical validation and Standard Model promotion remain false"
  ∷ []

canonicalHiggsComparisonRowCount :
  Nat
canonicalHiggsComparisonRowCount =
  listCount canonicalHiggsComparisonRows

canonicalHiggsComparisonArtifactCount :
  Nat
canonicalHiggsComparisonArtifactCount =
  listCount canonicalHiggsComparisonArtifactRows

canonicalHiggsComparisonGateCount :
  Nat
canonicalHiggsComparisonGateCount =
  listCount canonicalHiggsComparisonGateStatuses

comparisonRowCountIsFour :
  canonicalHiggsComparisonRowCount ≡ 4
comparisonRowCountIsFour = refl

artifactRowCountIsFour :
  canonicalHiggsComparisonArtifactCount ≡ 4
artifactRowCountIsFour = refl

gateStatusCountIsEight :
  canonicalHiggsComparisonGateCount ≡ 8
gateStatusCountIsEight = refl

------------------------------------------------------------------------
-- Canonical receipt.

record StandardModelHiggsCovariantComparisonLaw : Setω where
  field
    receiptLabel :
      String

    emitterScript :
      String

    validationCommand :
      String

    consumedHEPDataAdapter :
      HEPData.StandardModelHiggsHEPDataReceiptAdapter

    consumedCanonicalHEPDataAdapter :
      Bool

    consumedCanonicalHEPDataAdapterIsTrue :
      consumedCanonicalHEPDataAdapter ≡ true

    comparisonRows :
      List HiggsComparisonRow

    comparisonRowCount :
      Nat

    comparisonRowCountMatches :
      comparisonRowCount ≡ listCount comparisonRows

    artifactRows :
      List HiggsComparisonArtifactRow

    artifactCount :
      Nat

    artifactCountMatches :
      artifactCount ≡ listCount artifactRows

    gateStatuses :
      List HiggsComparisonGateStatus

    gateCount :
      Nat

    gateCountMatches :
      gateCount ≡ listCount gateStatuses

    consumesUpstreamAdapter :
      Bool

    consumesUpstreamAdapterIsTrue :
      consumesUpstreamAdapter ≡ true

    comparisonRowsPresent :
      Bool

    comparisonRowsPresentIsTrue :
      comparisonRowsPresent ≡ true

    acceptedAuthorityTokenPresent :
      Bool

    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false

    holdoutProtocolAccepted :
      Bool

    holdoutProtocolAcceptedIsFalse :
      holdoutProtocolAccepted ≡ false

    empiricalValidationPromoted :
      Bool

    empiricalValidationPromotedIsFalse :
      empiricalValidationPromoted ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

open StandardModelHiggsCovariantComparisonLaw public

canonicalStandardModelHiggsCovariantComparisonLaw :
  StandardModelHiggsCovariantComparisonLaw
canonicalStandardModelHiggsCovariantComparisonLaw =
  record
    { receiptLabel =
        "canonical Standard Model Higgs covariant comparison law"
    ; emitterScript =
        "scripts/sm_higgs_covariant_comparison_law.py"
    ; validationCommand =
        "python scripts/sm_higgs_covariant_comparison_law.py"
    ; consumedHEPDataAdapter =
        HEPData.canonicalStandardModelHiggsHEPDataReceiptAdapter
    ; consumedCanonicalHEPDataAdapter =
        true
    ; consumedCanonicalHEPDataAdapterIsTrue =
        refl
    ; comparisonRows =
        canonicalHiggsComparisonRows
    ; comparisonRowCount =
        canonicalHiggsComparisonRowCount
    ; comparisonRowCountMatches =
        refl
    ; artifactRows =
        canonicalHiggsComparisonArtifactRows
    ; artifactCount =
        canonicalHiggsComparisonArtifactCount
    ; artifactCountMatches =
        refl
    ; gateStatuses =
        canonicalHiggsComparisonGateStatuses
    ; gateCount =
        canonicalHiggsComparisonGateCount
    ; gateCountMatches =
        refl
    ; consumesUpstreamAdapter =
        true
    ; consumesUpstreamAdapterIsTrue =
        refl
    ; comparisonRowsPresent =
        true
    ; comparisonRowsPresentIsTrue =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; holdoutProtocolAccepted =
        false
    ; holdoutProtocolAcceptedIsFalse =
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

canonicalHiggsCovariantComparisonRowCountIsFour :
  StandardModelHiggsCovariantComparisonLaw.comparisonRowCount
    canonicalStandardModelHiggsCovariantComparisonLaw
  ≡ 4
canonicalHiggsCovariantComparisonRowCountIsFour = refl

canonicalHiggsCovariantComparisonArtifactCountIsFour :
  StandardModelHiggsCovariantComparisonLaw.artifactCount
    canonicalStandardModelHiggsCovariantComparisonLaw
  ≡ 4
canonicalHiggsCovariantComparisonArtifactCountIsFour = refl

canonicalHiggsCovariantComparisonGateCountIsEight :
  StandardModelHiggsCovariantComparisonLaw.gateCount
    canonicalStandardModelHiggsCovariantComparisonLaw
  ≡ 8
canonicalHiggsCovariantComparisonGateCountIsEight = refl

canonicalHiggsCovariantComparisonAuthorityTokenStillFalse :
  StandardModelHiggsCovariantComparisonLaw.acceptedAuthorityTokenPresent
    canonicalStandardModelHiggsCovariantComparisonLaw
  ≡ false
canonicalHiggsCovariantComparisonAuthorityTokenStillFalse = refl

canonicalHiggsCovariantComparisonHoldoutStillFalse :
  StandardModelHiggsCovariantComparisonLaw.holdoutProtocolAccepted
    canonicalStandardModelHiggsCovariantComparisonLaw
  ≡ false
canonicalHiggsCovariantComparisonHoldoutStillFalse = refl

canonicalHiggsCovariantComparisonEmpiricalPromotionStillFalse :
  StandardModelHiggsCovariantComparisonLaw.empiricalValidationPromoted
    canonicalStandardModelHiggsCovariantComparisonLaw
  ≡ false
canonicalHiggsCovariantComparisonEmpiricalPromotionStillFalse = refl

canonicalHiggsCovariantComparisonSMPromotionStillFalse :
  StandardModelHiggsCovariantComparisonLaw.standardModelPromoted
    canonicalStandardModelHiggsCovariantComparisonLaw
  ≡ false
canonicalHiggsCovariantComparisonSMPromotionStillFalse = refl
