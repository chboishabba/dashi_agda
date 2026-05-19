module DASHI.Physics.Closure.HEPDataAdapterTransformReceiptRequestDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataEmpiricalAuthorityReceiptCollation as Collation

------------------------------------------------------------------------
-- HEPData adapter-transform receipt request/diagnostic.
--
-- This module records the missing adapter-transform receipt between the raw
-- upstream HEPData t19/t20 CSV surface and the local normalized artifact.  It
-- is intentionally non-promoting: it names the conflicting value surfaces and
-- requests adapter semantics, but does not choose a selected surface, build
-- projection/comparison/authority receipts, or promote W3/W4/W5/W8.

data HEPDataAdapterTransformReceiptStatus : Set where
  blockedAwaitingAdapterTransformReceipt :
    HEPDataAdapterTransformReceiptStatus

data HEPDataAdapterTransformCandidateSurface : Set where
  rawUpstreamT19T20Surface :
    HEPDataAdapterTransformCandidateSurface
  localNormalizedArtifactSurface :
    HEPDataAdapterTransformCandidateSurface
  typedAdapterTransformationSurface :
    HEPDataAdapterTransformCandidateSurface

canonicalHEPDataAdapterTransformCandidateSurfaces :
  List HEPDataAdapterTransformCandidateSurface
canonicalHEPDataAdapterTransformCandidateSurfaces =
  rawUpstreamT19T20Surface
  ∷ localNormalizedArtifactSurface
  ∷ typedAdapterTransformationSurface
  ∷ []

data HEPDataSelectedValueSurfaceStatus : Set where
  selectedValueSurfaceBlockedUntilAdapterSemantics :
    HEPDataSelectedValueSurfaceStatus

data HEPDataAdapterTransformRequiredDecision : Set where
  chooseRawUpstreamT19Values :
    HEPDataAdapterTransformRequiredDecision
  chooseLocalNormalizedArtifactValues :
    HEPDataAdapterTransformRequiredDecision
  supplyTypedRawToNormalizedTransformation :
    HEPDataAdapterTransformRequiredDecision

canonicalHEPDataAdapterTransformRequiredDecisions :
  List HEPDataAdapterTransformRequiredDecision
canonicalHEPDataAdapterTransformRequiredDecisions =
  chooseRawUpstreamT19Values
  ∷ chooseLocalNormalizedArtifactValues
  ∷ supplyTypedRawToNormalizedTransformation
  ∷ []

data HEPDataAdapterTransformDiagnosticField : Set where
  adapterCollationSource :
    HEPDataAdapterTransformDiagnosticField
  adapterRawTableSurface :
    HEPDataAdapterTransformDiagnosticField
  adapterRawCovarianceSurface :
    HEPDataAdapterTransformDiagnosticField
  adapterRawFirstBins :
    HEPDataAdapterTransformDiagnosticField
  adapterNormalizedArtifactSurface :
    HEPDataAdapterTransformDiagnosticField
  adapterNormalizedFirstBins :
    HEPDataAdapterTransformDiagnosticField
  adapterSelectedValueSurfaceBlocker :
    HEPDataAdapterTransformDiagnosticField
  adapterRequiredSemanticDecision :
    HEPDataAdapterTransformDiagnosticField
  adapterNonPromotionBoundary :
    HEPDataAdapterTransformDiagnosticField

canonicalHEPDataAdapterTransformDiagnosticFields :
  List HEPDataAdapterTransformDiagnosticField
canonicalHEPDataAdapterTransformDiagnosticFields =
  adapterCollationSource
  ∷ adapterRawTableSurface
  ∷ adapterRawCovarianceSurface
  ∷ adapterRawFirstBins
  ∷ adapterNormalizedArtifactSurface
  ∷ adapterNormalizedFirstBins
  ∷ adapterSelectedValueSurfaceBlocker
  ∷ adapterRequiredSemanticDecision
  ∷ adapterNonPromotionBoundary
  ∷ []

data HEPDataAdapterTransformBoundary : Set where
  noSelectedValueSurface :
    HEPDataAdapterTransformBoundary
  noProjectionReceiptConstructed :
    HEPDataAdapterTransformBoundary
  noComparisonReceiptConstructed :
    HEPDataAdapterTransformBoundary
  noAuthorityReceiptConstructed :
    HEPDataAdapterTransformBoundary
  noW3Promotion :
    HEPDataAdapterTransformBoundary
  noW4Promotion :
    HEPDataAdapterTransformBoundary
  noW5Promotion :
    HEPDataAdapterTransformBoundary
  noW8Promotion :
    HEPDataAdapterTransformBoundary

canonicalHEPDataAdapterTransformBoundaries :
  List HEPDataAdapterTransformBoundary
canonicalHEPDataAdapterTransformBoundaries =
  noSelectedValueSurface
  ∷ noProjectionReceiptConstructed
  ∷ noComparisonReceiptConstructed
  ∷ noAuthorityReceiptConstructed
  ∷ noW3Promotion
  ∷ noW4Promotion
  ∷ noW5Promotion
  ∷ noW8Promotion
  ∷ []

record HEPDataAdapterTransformReceiptRequestDiagnostic : Setω where
  field
    status :
      HEPDataAdapterTransformReceiptStatus

    empiricalAuthorityCollation :
      Collation.HEPDataEmpiricalAuthorityReceiptCollation

    collationStatusIsAdapterTransformMissing :
      Collation.HEPDataEmpiricalAuthorityReceiptCollation.status
        empiricalAuthorityCollation
      ≡
      Collation.authoritySourcesCollatedButAdapterTransformMissing

    candidateSurfaces :
      List HEPDataAdapterTransformCandidateSurface

    candidateSurfacesAreCanonical :
      candidateSurfaces
      ≡
      canonicalHEPDataAdapterTransformCandidateSurfaces

    diagnosticFields :
      List HEPDataAdapterTransformDiagnosticField

    diagnosticFieldsAreCanonical :
      diagnosticFields
      ≡
      canonicalHEPDataAdapterTransformDiagnosticFields

    rawTableIdentity :
      List String

    rawCovarianceIdentity :
      List String

    rawFirstBinSurface :
      List String

    normalizedArtifactIdentity :
      List String

    normalizedFirstBinSurface :
      List String

    selectedValueSurfaceStatus :
      HEPDataSelectedValueSurfaceStatus

    selectedValueSurfaceIsBlocked :
      selectedValueSurfaceStatus
      ≡
      selectedValueSurfaceBlockedUntilAdapterSemantics

    requiredAdapterDecisions :
      List HEPDataAdapterTransformRequiredDecision

    requiredAdapterDecisionsAreCanonical :
      requiredAdapterDecisions
      ≡
      canonicalHEPDataAdapterTransformRequiredDecisions

    requestPayload :
      List String

    blockers :
      List String

    boundaries :
      List HEPDataAdapterTransformBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataAdapterTransformBoundaries

    nonPromotionBoundary :
      List String

canonicalHEPDataAdapterTransformReceiptRequestDiagnostic :
  HEPDataAdapterTransformReceiptRequestDiagnostic
canonicalHEPDataAdapterTransformReceiptRequestDiagnostic =
  record
    { status =
        blockedAwaitingAdapterTransformReceipt
    ; empiricalAuthorityCollation =
        Collation.canonicalHEPDataEmpiricalAuthorityReceiptCollation
    ; collationStatusIsAdapterTransformMissing =
        refl
    ; candidateSurfaces =
        canonicalHEPDataAdapterTransformCandidateSurfaces
    ; candidateSurfacesAreCanonical =
        refl
    ; diagnosticFields =
        canonicalHEPDataAdapterTransformDiagnosticFields
    ; diagnosticFieldsAreCanonical =
        refl
    ; rawTableIdentity =
        "raw upstream HEPData publication record = ins2079374"
        ∷ "raw upstream selected table = phistar mass 50-76"
        ∷ "raw upstream selected table DOI = 10.17182/hepdata.115656.v1/t19"
        ∷ "raw CSV path = scripts/data/hepdata/ins2079374_phistar_mass_50-76_t19.csv"
        ∷ "raw CSV sha256 = 1a1d280da645f4c55aba73aabf1b398a3fd9614532c363d972018f194b653677"
        ∷ []
    ; rawCovarianceIdentity =
        "raw upstream covariance table = Covariance matrices for phistar mass 50-76"
        ∷ "raw upstream covariance table DOI = 10.17182/hepdata.115656.v1/t20"
        ∷ "raw covariance CSV path = scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_t20.csv"
        ∷ "raw covariance CSV sha256 = fa4b694211862d4b07b761d0dab77c8fe1016d2ccd5015dc6f7bc3272c34201a"
        ∷ []
    ; rawFirstBinSurface =
        "raw t19 bin0 center/value = 0.002 / 228.59 pb per unit phi*"
        ∷ "raw t19 bin1 center/value = 0.006 / 225.69 pb per unit phi*"
        ∷ "raw t19 adjacent-bin delta = 2.90 pb per unit phi*"
        ∷ []
    ; normalizedArtifactIdentity =
        "normalized artifact path = scripts/data/hepdata_phistar_50_76_artifact.json"
        ∷ "normalized artifact sha256 = 20085dc6092e59a6afc381cb0bf2f03da2d19f375a22a0f9e701d7c890244139"
        ∷ "normalized source path = /home/c/Documents/code/dashifine/hepdata_npz/phistar_50_76.npz"
        ∷ []
    ; normalizedFirstBinSurface =
        "normalized bin0 center/value = 0.002 / 188.4"
        ∷ "normalized bin1 center/value = 0.006 / 185.09"
        ∷ "normalized adjacent-bin delta = 3.31"
        ∷ []
    ; selectedValueSurfaceStatus =
        selectedValueSurfaceBlockedUntilAdapterSemantics
    ; selectedValueSurfaceIsBlocked =
        refl
    ; requiredAdapterDecisions =
        canonicalHEPDataAdapterTransformRequiredDecisions
    ; requiredAdapterDecisionsAreCanonical =
        refl
    ; requestPayload =
        "Provide the missing adapter-transform receipt for phistar_50_76 between raw HEPData t19/t20 and the local normalized artifact"
        ∷ "The receipt must choose raw upstream t19 values, choose local normalized artifact values, or supply a typed raw-to-normalized transformation"
        ∷ "If a transformation is supplied, it must bind source table t19, covariance table t20, raw CSV checksum, covariance CSV checksum, normalized artifact checksum, and first-bin behavior"
        ∷ "The selected value surface remains blocked until those adapter semantics are accepted"
        ∷ []
    ; blockers =
        "raw t19 first bins are 228.59 and 225.69 with delta 2.90"
        ∷ "normalized first bins are 188.4 and 185.09 with delta 3.31"
        ∷ "the raw and normalized first-bin surfaces are both concrete but not semantically reconciled"
        ∷ "no local module may silently conflate raw upstream values with normalized artifact values"
        ∷ []
    ; boundaries =
        canonicalHEPDataAdapterTransformBoundaries
    ; boundariesAreCanonical =
        refl
    ; nonPromotionBoundary =
        "This module is a receipt request and diagnostic surface only"
        ∷ "It does not construct a selected HEPData observable or selected value surface"
        ∷ "It does not construct projection receipts, comparison receipts, authority receipts, accepted authority tokens, or accepted authority routes"
        ∷ "It does not construct residualObservableClassReceipt or checksum-bound selection receipt"
        ∷ "It does not promote W3, W4, W5, or W8"
        ∷ []
    }
