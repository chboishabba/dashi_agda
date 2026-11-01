module DASHI.Physics.Closure.HEPDataRatioAdapterTransformReceiptRequest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataAdapterTransformReceiptRequestDiagnostic as Adapter
import DASHI.Physics.Closure.HEPDataEmpiricalAuthorityReceiptCollation as Collation

------------------------------------------------------------------------
-- HEP-R21: ratio adapter-transform receipt request.
--
-- The adapter strategy is now narrowed to the HEPData ratio observable:
-- table t43 with covariance t44, dimensionless ratio 50-76 over 76-106.
-- Raw t19/t20 remains absolute-source context, and t68/t69 response matrices
-- remain fold-back inputs.  This is still only a request/diagnostic surface:
-- no predictionFixedAt receipt, projection receipt, comparison law, authority
-- token, or W3/W4/W5/W8 promotion is constructed here.

data HEPDataRatioAdapterTransformStatus : Set where
  ratioRouteSelectedButReceiptStillBlocked :
    HEPDataRatioAdapterTransformStatus

data HEPDataRatioAdapterSelectedRoute : Set where
  selectedRatioT43T44Dimensionless50To76Over76To106 :
    HEPDataRatioAdapterSelectedRoute

data HEPDataRatioAdapterInputSurface : Set where
  selectedRatioTableT43 :
    HEPDataRatioAdapterInputSurface
  selectedRatioCovarianceTableT44 :
    HEPDataRatioAdapterInputSurface
  absoluteSourceContextT19 :
    HEPDataRatioAdapterInputSurface
  absoluteSourceCovarianceContextT20 :
    HEPDataRatioAdapterInputSurface
  foldBackResponseMatrixT68 :
    HEPDataRatioAdapterInputSurface
  foldBackResponseMatrixT69 :
    HEPDataRatioAdapterInputSurface

canonicalHEPDataRatioAdapterInputSurfaces :
  List HEPDataRatioAdapterInputSurface
canonicalHEPDataRatioAdapterInputSurfaces =
  selectedRatioTableT43
  ∷ selectedRatioCovarianceTableT44
  ∷ absoluteSourceContextT19
  ∷ absoluteSourceCovarianceContextT20
  ∷ foldBackResponseMatrixT68
  ∷ foldBackResponseMatrixT69
  ∷ []

data HEPDataRatioAdapterReceiptField : Set where
  ratioRouteTableIdentity :
    HEPDataRatioAdapterReceiptField
  ratioRouteCovarianceIdentity :
    HEPDataRatioAdapterReceiptField
  ratioRouteObservableClass :
    HEPDataRatioAdapterReceiptField
  absoluteSourceContext :
    HEPDataRatioAdapterReceiptField
  foldBackResponseMatrixInputs :
    HEPDataRatioAdapterReceiptField
  scaleFactorDiagnosticNotes :
    HEPDataRatioAdapterReceiptField
  firstBinDiagnosticNotes :
    HEPDataRatioAdapterReceiptField
  predictionFixedAtBlocker :
    HEPDataRatioAdapterReceiptField
  projectionComparisonBlockers :
    HEPDataRatioAdapterReceiptField
  ratioNonPromotionBoundary :
    HEPDataRatioAdapterReceiptField

canonicalHEPDataRatioAdapterReceiptFields :
  List HEPDataRatioAdapterReceiptField
canonicalHEPDataRatioAdapterReceiptFields =
  ratioRouteTableIdentity
  ∷ ratioRouteCovarianceIdentity
  ∷ ratioRouteObservableClass
  ∷ absoluteSourceContext
  ∷ foldBackResponseMatrixInputs
  ∷ scaleFactorDiagnosticNotes
  ∷ firstBinDiagnosticNotes
  ∷ predictionFixedAtBlocker
  ∷ projectionComparisonBlockers
  ∷ ratioNonPromotionBoundary
  ∷ []

data HEPDataRatioAdapterRemainingBlockerField : Set where
  missingPredictionFixedAt :
    HEPDataRatioAdapterRemainingBlockerField
  missingTheoremSideProjectionReceipt :
    HEPDataRatioAdapterRemainingBlockerField
  missingResidualComparisonLawReceipt :
    HEPDataRatioAdapterRemainingBlockerField

canonicalHEPDataRatioAdapterRemainingBlockerFields :
  List HEPDataRatioAdapterRemainingBlockerField
canonicalHEPDataRatioAdapterRemainingBlockerFields =
  missingPredictionFixedAt
  ∷ missingTheoremSideProjectionReceipt
  ∷ missingResidualComparisonLawReceipt
  ∷ []

data HEPDataRatioAdapterBoundary : Set where
  noUncheckedNumericEquality :
    HEPDataRatioAdapterBoundary
  noAcceptedComparisonLaw :
    HEPDataRatioAdapterBoundary
  noAuthorityToken :
    HEPDataRatioAdapterBoundary
  noProjectionReceipt :
    HEPDataRatioAdapterBoundary
  noW3Promotion :
    HEPDataRatioAdapterBoundary
  noW4Promotion :
    HEPDataRatioAdapterBoundary
  noW5Promotion :
    HEPDataRatioAdapterBoundary
  noW8Promotion :
    HEPDataRatioAdapterBoundary

canonicalHEPDataRatioAdapterBoundaries :
  List HEPDataRatioAdapterBoundary
canonicalHEPDataRatioAdapterBoundaries =
  noUncheckedNumericEquality
  ∷ noAcceptedComparisonLaw
  ∷ noAuthorityToken
  ∷ noProjectionReceipt
  ∷ noW3Promotion
  ∷ noW4Promotion
  ∷ noW5Promotion
  ∷ noW8Promotion
  ∷ []

record HEPDataRatioAdapterTransformReceiptRequest : Setω where
  field
    status :
      HEPDataRatioAdapterTransformStatus

    previousAdapterDiagnostic :
      Adapter.HEPDataAdapterTransformReceiptRequestDiagnostic

    previousAdapterStillBlocked :
      Adapter.HEPDataAdapterTransformReceiptRequestDiagnostic.status
        previousAdapterDiagnostic
      ≡
      Adapter.blockedAwaitingAdapterTransformReceipt

    empiricalAuthorityCollation :
      Collation.HEPDataEmpiricalAuthorityReceiptCollation

    collationStatusIsAdapterTransformMissing :
      Collation.HEPDataEmpiricalAuthorityReceiptCollation.status
        empiricalAuthorityCollation
      ≡
      Collation.authoritySourcesCollatedButAdapterTransformMissing

    selectedRoute :
      HEPDataRatioAdapterSelectedRoute

    selectedRouteIsCanonical :
      selectedRoute
      ≡
      selectedRatioT43T44Dimensionless50To76Over76To106

    inputSurfaces :
      List HEPDataRatioAdapterInputSurface

    inputSurfacesAreCanonical :
      inputSurfaces
      ≡
      canonicalHEPDataRatioAdapterInputSurfaces

    receiptFields :
      List HEPDataRatioAdapterReceiptField

    receiptFieldsAreCanonical :
      receiptFields
      ≡
      canonicalHEPDataRatioAdapterReceiptFields

    selectedRatioTableIdentity :
      List String

    selectedRatioCovarianceIdentity :
      List String

    selectedObservableClass :
      List String

    absoluteSourceContextNotes :
      List String

    foldBackInputs :
      List String

    diagnosticScaleFactorNotes :
      List String

    diagnosticFirstBinNotes :
      List String

    remainingBlockerFields :
      List HEPDataRatioAdapterRemainingBlockerField

    remainingBlockerFieldsAreCanonical :
      remainingBlockerFields
      ≡
      canonicalHEPDataRatioAdapterRemainingBlockerFields

    remainingBlockerFieldNames :
      List String

    providerRequest :
      List String

    w0DeltaReport :
      List String

    boundaries :
      List HEPDataRatioAdapterBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataRatioAdapterBoundaries

    nonPromotionBoundary :
      List String

canonicalHEPDataRatioAdapterTransformReceiptRequest :
  HEPDataRatioAdapterTransformReceiptRequest
canonicalHEPDataRatioAdapterTransformReceiptRequest =
  record
    { status =
        ratioRouteSelectedButReceiptStillBlocked
    ; previousAdapterDiagnostic =
        Adapter.canonicalHEPDataAdapterTransformReceiptRequestDiagnostic
    ; previousAdapterStillBlocked =
        refl
    ; empiricalAuthorityCollation =
        Collation.canonicalHEPDataEmpiricalAuthorityReceiptCollation
    ; collationStatusIsAdapterTransformMissing =
        refl
    ; selectedRoute =
        selectedRatioT43T44Dimensionless50To76Over76To106
    ; selectedRouteIsCanonical =
        refl
    ; inputSurfaces =
        canonicalHEPDataRatioAdapterInputSurfaces
    ; inputSurfacesAreCanonical =
        refl
    ; receiptFields =
        canonicalHEPDataRatioAdapterReceiptFields
    ; receiptFieldsAreCanonical =
        refl
    ; selectedRatioTableIdentity =
        "selected adapter strategy = HEPData ratio table route"
        ∷ "selected observable table = ratio 50-76 over 76-106"
        ∷ "selected observable table DOI = 10.17182/hepdata.115656.v1/t43"
        ∷ "selected covariance table DOI = 10.17182/hepdata.115656.v1/t44"
        ∷ "selected value surface is dimensionless ratio, not absolute d sigma / d phi*"
        ∷ []
    ; selectedRatioCovarianceIdentity =
        "ratio covariance source = t44 covariance for selected ratio table t43"
        ∷ "t44 checksum is not asserted here; provider receipt must bind it if used for comparison"
        ∷ "t43 checksum is not asserted here; provider receipt must bind it if used for projection"
        ∷ []
    ; selectedObservableClass =
        "observable class = dimensionless binwise ratio of phi* mass window 50-76 over phi* mass window 76-106"
        ∷ "comparison target must consume ratio values from t43/t44, not raw absolute t19/t20 values"
        ∷ "the ratio route avoids silently treating absolute pb-per-phi* values as normalized local artifact values"
        ∷ []
    ; absoluteSourceContextNotes =
        "absolute-source context table = phistar mass 50-76, DOI 10.17182/hepdata.115656.v1/t19"
        ∷ "absolute-source context covariance = DOI 10.17182/hepdata.115656.v1/t20"
        ∷ "raw t19 first bins remain diagnostic context: 228.59 and 225.69 with delta 2.90"
        ∷ "raw t19/t20 are retained as source context only, not as the selected comparison value surface"
        ∷ "collation-bound raw CSV sha256 = 1a1d280da645f4c55aba73aabf1b398a3fd9614532c363d972018f194b653677"
        ∷ "collation-bound raw covariance CSV sha256 = fa4b694211862d4b07b761d0dab77c8fe1016d2ccd5015dc6f7bc3272c34201a"
        ∷ []
    ; foldBackInputs =
        "fold-back input response matrix table = t68"
        ∷ "fold-back input response matrix covariance/partner table = t69"
        ∷ "t68/t69 are retained as response-matrix fold-back inputs only"
        ∷ "this module does not assert a fold-back law from t68/t69 to t43/t44"
        ∷ []
    ; diagnosticScaleFactorNotes =
        "scale-factor notes are diagnostic strings only"
        ∷ "any scale factor between absolute t19/t20 context and ratio t43/t44 must be supplied by a typed adapter receipt"
        ∷ "no unchecked numeric equality between raw, normalized, ratio, or fold-back surfaces is asserted here"
        ∷ []
    ; diagnosticFirstBinNotes =
        "first-bin notes are diagnostic strings only"
        ∷ "previous normalized artifact first bins were recorded as 188.4 and 185.09 with delta 3.31"
        ∷ "previous raw t19 first bins were recorded as 228.59 and 225.69 with delta 2.90"
        ∷ "the selected t43 first-bin ratio value is not asserted by this request surface"
        ∷ []
    ; remainingBlockerFields =
        canonicalHEPDataRatioAdapterRemainingBlockerFields
    ; remainingBlockerFieldsAreCanonical =
        refl
    ; remainingBlockerFieldNames =
        "predictionFixedAt"
        ∷ "theoremSideProjectionReceipt"
        ∷ "residualComparisonLawReceipt"
        ∷ []
    ; providerRequest =
        "Supply HEP-R21 ratio adapter-transform receipt binding t43/t44 as the selected dimensionless observable surface"
        ∷ "Bind t19/t20 as absolute-source context and t68/t69 as fold-back response-matrix inputs"
        ∷ "Provide predictionFixedAt before any theorem-side projection or comparison law is accepted"
        ∷ "Provide projection/comparison receipts separately; this module does not construct them"
        ∷ []
    ; w0DeltaReport =
        "HEP-R21 selected route: t43/t44 ratio table for 50-76 over 76-106"
        ∷ "HEP-R21 retained context: raw t19/t20 absolute source values from the collation"
        ∷ "HEP-R21 retained fold-back inputs: response matrices t68/t69"
        ∷ "HEP-R21 remaining blockers: predictionFixedAt, theoremSideProjectionReceipt, residualComparisonLawReceipt"
        ∷ "HEP-R21 non-promotion boundary: no W3/W4/W5/W8, no accepted comparison law, no authority token"
        ∷ []
    ; boundaries =
        canonicalHEPDataRatioAdapterBoundaries
    ; boundariesAreCanonical =
        refl
    ; nonPromotionBoundary =
        "This module records a selected adapter strategy but is still request/diagnostic only"
        ∷ "It does not construct predictionFixedAt"
        ∷ "It does not construct theorem-side projection, residual comparison law, accepted comparison law, authority token, or accepted authority route"
        ∷ "It does not promote W3, W4, W5, or W8"
        ∷ []
    }
