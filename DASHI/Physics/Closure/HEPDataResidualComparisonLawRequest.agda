module DASHI.Physics.Closure.HEPDataResidualComparisonLawRequest where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic as Authority
import DASHI.Physics.Closure.HEPDataDefectProjectionDiagnostic as Defect
import DASHI.Physics.Closure.HEPDataObservableSchema as HEP
import DASHI.Physics.Closure.HEPDataResidualObservableClassRequest as ResidualClass
import DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic as Calibration

------------------------------------------------------------------------
-- HEP-R6: residual comparison-law request.
--
-- HEP-E records a generic comparison-law receipt shape.  HEP-R6 narrows the
-- requested law target for residual/deviation profiles: compare a selected
-- HEPData residual profile against a DASHI defect/residual profile by a
-- residual-aware mode, not raw value equality.  This module is diagnostic-only:
-- it constructs no law, selected residual observable, covariance calibration,
-- projection receipt, authority token, or empirical validation.

data HEPDataResidualComparisonLawKind : Set where
  signPatternComparison :
    HEPDataResidualComparisonLawKind
  normalizedPullComparison :
    HEPDataResidualComparisonLawKind
  covarianceWhitenedDistanceComparison :
    HEPDataResidualComparisonLawKind
  defectClassMatchComparison :
    HEPDataResidualComparisonLawKind
  anomalyRankingComparison :
    HEPDataResidualComparisonLawKind

canonicalHEPDataResidualComparisonLawKinds :
  List HEPDataResidualComparisonLawKind
canonicalHEPDataResidualComparisonLawKinds =
  signPatternComparison
  ∷ normalizedPullComparison
  ∷ covarianceWhitenedDistanceComparison
  ∷ defectClassMatchComparison
  ∷ anomalyRankingComparison
  ∷ []

data HEPDataResidualComparisonLawDependency : Set where
  selectedResidualObservableDependency :
    HEPDataResidualComparisonLawDependency
  residualObservableClassRequestDependency :
    HEPDataResidualComparisonLawDependency
  covarianceCalibrationDependency :
    HEPDataResidualComparisonLawDependency
  defectProjectionReceiptDependency :
    HEPDataResidualComparisonLawDependency
  dashiDefectResidualProfileDependency :
    HEPDataResidualComparisonLawDependency
  acceptedAuthorityTokenDependency :
    HEPDataResidualComparisonLawDependency

canonicalHEPDataResidualComparisonLawDependencies :
  List HEPDataResidualComparisonLawDependency
canonicalHEPDataResidualComparisonLawDependencies =
  selectedResidualObservableDependency
  ∷ residualObservableClassRequestDependency
  ∷ covarianceCalibrationDependency
  ∷ defectProjectionReceiptDependency
  ∷ dashiDefectResidualProfileDependency
  ∷ acceptedAuthorityTokenDependency
  ∷ []

data HEPDataResidualComparisonLawMissingField : Set where
  missingSelectedResidualObservable :
    HEPDataResidualComparisonLawMissingField
  missingResidualObservableClassReceipt :
    HEPDataResidualComparisonLawMissingField
  missingCovarianceOrCalibrationReceipt :
    HEPDataResidualComparisonLawMissingField
  missingDefectProjectionReceipt :
    HEPDataResidualComparisonLawMissingField
  missingDASHIDefectResidualProfileTarget :
    HEPDataResidualComparisonLawMissingField
  missingResidualComparisonModeSelection :
    HEPDataResidualComparisonLawMissingField
  missingResidualComparisonPredicate :
    HEPDataResidualComparisonLawMissingField
  missingAcceptedAuthorityToken :
    HEPDataResidualComparisonLawMissingField

canonicalHEPDataResidualComparisonLawMissingFields :
  List HEPDataResidualComparisonLawMissingField
canonicalHEPDataResidualComparisonLawMissingFields =
  missingSelectedResidualObservable
  ∷ missingResidualObservableClassReceipt
  ∷ missingCovarianceOrCalibrationReceipt
  ∷ missingDefectProjectionReceipt
  ∷ missingDASHIDefectResidualProfileTarget
  ∷ missingResidualComparisonModeSelection
  ∷ missingResidualComparisonPredicate
  ∷ missingAcceptedAuthorityToken
  ∷ []

data HEPDataResidualComparisonLawStatus : Set where
  blockedAwaitingResidualComparisonLawReceipts :
    HEPDataResidualComparisonLawStatus

data HEPDataResidualComparisonLawBoundary : Set where
  noRawValueEqualityComparison :
    HEPDataResidualComparisonLawBoundary
  noComparisonLawConstructed :
    HEPDataResidualComparisonLawBoundary
  noEmpiricalValidationConstructed :
    HEPDataResidualComparisonLawBoundary
  noAcceptedAuthorityPromotion :
    HEPDataResidualComparisonLawBoundary
  noW3W4W5W8ClosureClaim :
    HEPDataResidualComparisonLawBoundary

canonicalHEPDataResidualComparisonLawBoundary :
  List HEPDataResidualComparisonLawBoundary
canonicalHEPDataResidualComparisonLawBoundary =
  noRawValueEqualityComparison
  ∷ noComparisonLawConstructed
  ∷ noEmpiricalValidationConstructed
  ∷ noAcceptedAuthorityPromotion
  ∷ noW3W4W5W8ClosureClaim
  ∷ []

record HEPDataResidualComparisonLawRequestSurface : Set where
  field
    comparisonLawKind :
      HEPDataResidualComparisonLawKind

    hepDataResidualProfileLabel :
      String

    dashiDefectResidualProfileLabel :
      String

    covarianceOrCalibrationPolicy :
      String

    projectionReceiptDependency :
      String

    authorityTokenDependency :
      String

    comparisonPredicateRequest :
      String

    nonRawEqualityJustification :
      String

record HEPDataResidualComparisonLawReceipt
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    residualObservableReceipt :
      Defect.HEPDataResidualObservableReceipt

    residualClassRequestSurface :
      ResidualClass.HEPDataResidualObservableClassRequestSurface

    covarianceCalibrationReceipt :
      Calibration.HEPDataUnitCalibrationRequirementReceipt observable

    defectProjectionContract :
      Defect.HEPDataResidualProfileProjectionContract observable

    acceptedAuthorityToken :
      Authority.HEPDataAcceptedDatasetAuthorityToken

    comparisonLawKind :
      HEPDataResidualComparisonLawKind

    HEPDataResidualProfile :
      Set

    DASHIDefectResidualProfile :
      Set

    comparisonPredicate :
      HEPDataResidualProfile →
      DASHIDefectResidualProfile →
      Set

    comparisonLawLabel :
      String

    comparisonLawMatchesSchemaTarget :
      comparisonLawLabel
      ≡
      HEP.HEPDataObservableSchemaSurface.comparisonLawTarget
        (HEP.HEPDataObservable.schema observable)

residualComparisonLawReceiptImpossibleHere :
  {observable : HEP.HEPDataObservable} →
  HEPDataResidualComparisonLawReceipt observable →
  ⊥
residualComparisonLawReceiptImpossibleHere receipt =
  Defect.residualObservableReceiptImpossibleHere
    (HEPDataResidualComparisonLawReceipt.residualObservableReceipt receipt)

data HEPDataResidualComparisonLawBoundaryToken : Set where
  diagnosticOnlyNoResidualComparisonLawPromotion :
    HEPDataResidualComparisonLawBoundaryToken

record HEPDataResidualComparisonLawRequestDiagnostic : Setω where
  field
    residualClassRequestDiagnostic :
      ResidualClass.HEPDataResidualObservableClassRequestDiagnostic

    defectProjectionDiagnostic :
      Defect.HEPDataDefectProjectionDiagnostic

    genericComparisonAuthorityDiagnostic :
      Authority.HEPDataComparisonAuthorityRouteDiagnostic

    unitCalibrationDiagnostic :
      Calibration.HEPDataUnitCalibrationRequirementDiagnostic

    currentStatus :
      HEPDataResidualComparisonLawStatus

    allowedComparisonLawKinds :
      List HEPDataResidualComparisonLawKind

    allowedComparisonLawKindsAreCanonical :
      allowedComparisonLawKinds
      ≡
      canonicalHEPDataResidualComparisonLawKinds

    requiredDependencies :
      List HEPDataResidualComparisonLawDependency

    requiredDependenciesAreCanonical :
      requiredDependencies
      ≡
      canonicalHEPDataResidualComparisonLawDependencies

    canonicalMissingFields :
      List HEPDataResidualComparisonLawMissingField

    canonicalMissingFieldsAreCanonical :
      canonicalMissingFields
      ≡
      canonicalHEPDataResidualComparisonLawMissingFields

    rawValueEqualityRejected :
      Bool

    residualAwareComparisonRequired :
      Bool

    futureReceiptBlocked :
      {observable : HEP.HEPDataObservable} →
      HEPDataResidualComparisonLawReceipt observable →
      ⊥

    diagnosticBoundary :
      HEPDataResidualComparisonLawBoundaryToken

    nonPromotionBoundary :
      List HEPDataResidualComparisonLawBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalHEPDataResidualComparisonLawBoundary

    requestInstructions :
      List String

    exactMissingExternalSurfaces :
      List String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

canonicalHEPDataResidualComparisonLawRequestDiagnostic :
  HEPDataResidualComparisonLawRequestDiagnostic
canonicalHEPDataResidualComparisonLawRequestDiagnostic =
  record
    { residualClassRequestDiagnostic =
        ResidualClass.canonicalHEPDataResidualObservableClassRequestDiagnostic
    ; defectProjectionDiagnostic =
        Defect.canonicalHEPDataDefectProjectionDiagnostic
    ; genericComparisonAuthorityDiagnostic =
        Authority.canonicalHEPDataComparisonAuthorityRouteDiagnostic
    ; unitCalibrationDiagnostic =
        Calibration.canonicalHEPDataUnitCalibrationRequirementDiagnostic
    ; currentStatus =
        blockedAwaitingResidualComparisonLawReceipts
    ; allowedComparisonLawKinds =
        canonicalHEPDataResidualComparisonLawKinds
    ; allowedComparisonLawKindsAreCanonical =
        refl
    ; requiredDependencies =
        canonicalHEPDataResidualComparisonLawDependencies
    ; requiredDependenciesAreCanonical =
        refl
    ; canonicalMissingFields =
        canonicalHEPDataResidualComparisonLawMissingFields
    ; canonicalMissingFieldsAreCanonical =
        refl
    ; rawValueEqualityRejected =
        true
    ; residualAwareComparisonRequired =
        true
    ; futureReceiptBlocked =
        residualComparisonLawReceiptImpossibleHere
    ; diagnosticBoundary =
        diagnosticOnlyNoResidualComparisonLawPromotion
    ; nonPromotionBoundary =
        canonicalHEPDataResidualComparisonLawBoundary
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; requestInstructions =
        "Select one residual-aware comparison mode: sign pattern, normalized pull, covariance-whitened distance, defect class match, or anomaly ranking"
        ∷ "Bind the mode to a selected HEPData residual/deviation profile and a DASHI defect/residual profile target"
        ∷ "Carry covariance, calibration, and projection receipts explicitly; do not compare raw values by equality"
        ∷ "If any dependency is absent, return the first missing typed field instead of fabricating a comparison law"
        ∷ []
    ; exactMissingExternalSurfaces =
        "selected HEPData residual/deviation observable receipt"
        ∷ "residual observable class request/receipt tying the profile to a non-collapsing observable"
        ∷ "covariance or unit-calibration receipt for normalized pull or whitening semantics"
        ∷ "DASHI defect/residual profile projection receipt"
        ∷ "specific residual comparison mode and predicate"
        ∷ "accepted dataset authority token"
        ∷ []
    ; coordinationMapNodeText =
        "rectangle \"HEP-R6\\nresidual comparison-law request\\nHEPData residual profile vs DASHI defect profile\\nsign/pull/whitened/defect/anomaly modes\\nnon-promoting\" as HEPDATA_HEPR6 #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_HEPE --> HEPDATA_HEPR6 : specialize generic comparison-law route to residual-aware law target\nHEPDATA_HEPR1 --> HEPDATA_HEPR6 : selected residual/deviation observable class dependency\nHEPDATA_HEPR2 --> HEPDATA_HEPR6 : DASHI defect/residual projection target dependency\nHEPDATA_HEPC --> HEPDATA_HEPR6 : covariance and calibration dependency\nHEPDATA_HEPR6 --> Plateau : selected residual observable + covariance/calibration + projection receipt + accepted authority token still missing\nHEPDATA_HEPR6 --> W3 : no accepted-authority or empirical adequacy promotion\nHEPDATA_HEPR6 --> W4 : no calibration promotion\nHEPDATA_HEPR6 --> W5 : no physical closure promotion\nHEPDATA_HEPR6 --> W8 : no origin receipt promotion"
    }

canonicalHEPDataResidualComparisonLawRequestStatus :
  HEPDataResidualComparisonLawStatus
canonicalHEPDataResidualComparisonLawRequestStatus =
  blockedAwaitingResidualComparisonLawReceipts
