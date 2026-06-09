module DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic as Authority
import DASHI.Physics.Closure.HEPDataNonCollapseObservableObligation as NonCollapse
import DASHI.Physics.Closure.HEPDataObservableSchema as HEP
import DASHI.Physics.Closure.HEPDataResidualComparisonLawRequest as Law
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Provider

------------------------------------------------------------------------
-- HEP-R9: residual bridge authority gate.
--
-- The residual bridge is a receipt filter, not a data bridge.  This module
-- classifies provider answers, links the residual provider payload intake to
-- the non-collapse obligation and residual comparison-law request, and blocks
-- every path that would fabricate accepted authority or promote W3/W4/W5/W8.

data HEPDataResidualBridgeAuthorityGateStatus : Set where
  blockedAwaitingResidualAuthorityReceiptChain :
    HEPDataResidualBridgeAuthorityGateStatus

data HEPDataResidualProviderAcceptedAnswerClass : Set where
  acceptedFullResidualReceiptChain :
    HEPDataResidualProviderAcceptedAnswerClass
  acceptedFirstMissingTypedResidualReceiptDiagnostic :
    HEPDataResidualProviderAcceptedAnswerClass

canonicalHEPDataResidualProviderAcceptedAnswerClasses :
  List HEPDataResidualProviderAcceptedAnswerClass
canonicalHEPDataResidualProviderAcceptedAnswerClasses =
  acceptedFullResidualReceiptChain
  ∷ acceptedFirstMissingTypedResidualReceiptDiagnostic
  ∷ []

data HEPDataResidualProviderRejectedAnswerClass : Set where
  rejectedRawSaturatedValues :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedLocalArtifactPathOnly :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedUnchecksumedSelection :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingResidualObservable :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingBaselineOrInvarianceModel :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingResidualDefinition :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingCovarianceOrCalibration :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingTheoremSideProjection :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingDefectProjection :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingResidualComparisonLaw :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingAcceptedAuthorityRoute :
    HEPDataResidualProviderRejectedAnswerClass
  rejectedMissingNonCollapseWitness :
    HEPDataResidualProviderRejectedAnswerClass

canonicalHEPDataResidualProviderRejectedAnswerClasses :
  List HEPDataResidualProviderRejectedAnswerClass
canonicalHEPDataResidualProviderRejectedAnswerClasses =
  rejectedRawSaturatedValues
  ∷ rejectedLocalArtifactPathOnly
  ∷ rejectedUnchecksumedSelection
  ∷ rejectedMissingResidualObservable
  ∷ rejectedMissingBaselineOrInvarianceModel
  ∷ rejectedMissingResidualDefinition
  ∷ rejectedMissingCovarianceOrCalibration
  ∷ rejectedMissingTheoremSideProjection
  ∷ rejectedMissingDefectProjection
  ∷ rejectedMissingResidualComparisonLaw
  ∷ rejectedMissingAcceptedAuthorityRoute
  ∷ rejectedMissingNonCollapseWitness
  ∷ []

data HEPDataResidualBridgeGateRequiredPayloadField : Set where
  gateRequiresSelectedResidualObservable :
    HEPDataResidualBridgeGateRequiredPayloadField
  gateRequiresBaselineOrInvarianceModel :
    HEPDataResidualBridgeGateRequiredPayloadField
  gateRequiresResidualDefinition :
    HEPDataResidualBridgeGateRequiredPayloadField
  gateRequiresCovarianceCalibration :
    HEPDataResidualBridgeGateRequiredPayloadField
  gateRequiresTheoremSideProjection :
    HEPDataResidualBridgeGateRequiredPayloadField
  gateRequiresDefectProjection :
    HEPDataResidualBridgeGateRequiredPayloadField
  gateRequiresResidualComparisonLaw :
    HEPDataResidualBridgeGateRequiredPayloadField
  gateRequiresAcceptedAuthorityRoute :
    HEPDataResidualBridgeGateRequiredPayloadField
  gateRequiresNonCollapseWitness :
    HEPDataResidualBridgeGateRequiredPayloadField

canonicalHEPDataResidualBridgeGateRequiredPayloadFields :
  List HEPDataResidualBridgeGateRequiredPayloadField
canonicalHEPDataResidualBridgeGateRequiredPayloadFields =
  gateRequiresSelectedResidualObservable
  ∷ gateRequiresBaselineOrInvarianceModel
  ∷ gateRequiresResidualDefinition
  ∷ gateRequiresCovarianceCalibration
  ∷ gateRequiresTheoremSideProjection
  ∷ gateRequiresDefectProjection
  ∷ gateRequiresResidualComparisonLaw
  ∷ gateRequiresAcceptedAuthorityRoute
  ∷ gateRequiresNonCollapseWitness
  ∷ []

data HEPDataResidualBridgeAuthorityGateBoundary : Set where
  diagnosticOnlyNoDataBridge :
    HEPDataResidualBridgeAuthorityGateBoundary
  noAcceptedAuthorityTokenConstructed :
    HEPDataResidualBridgeAuthorityGateBoundary
  noAcceptedAuthorityRouteConstructed :
    HEPDataResidualBridgeAuthorityGateBoundary
  noResidualComparisonLawConstructed :
    HEPDataResidualBridgeAuthorityGateBoundary
  noNonCollapseWitnessConstructed :
    HEPDataResidualBridgeAuthorityGateBoundary
  noW3Promotion :
    HEPDataResidualBridgeAuthorityGateBoundary
  noW4Promotion :
    HEPDataResidualBridgeAuthorityGateBoundary
  noW5Promotion :
    HEPDataResidualBridgeAuthorityGateBoundary
  noW8Promotion :
    HEPDataResidualBridgeAuthorityGateBoundary

canonicalHEPDataResidualBridgeAuthorityGateBoundaries :
  List HEPDataResidualBridgeAuthorityGateBoundary
canonicalHEPDataResidualBridgeAuthorityGateBoundaries =
  diagnosticOnlyNoDataBridge
  ∷ noAcceptedAuthorityTokenConstructed
  ∷ noAcceptedAuthorityRouteConstructed
  ∷ noResidualComparisonLawConstructed
  ∷ noNonCollapseWitnessConstructed
  ∷ noW3Promotion
  ∷ noW4Promotion
  ∷ noW5Promotion
  ∷ noW8Promotion
  ∷ []

record HEPDataResidualBridgeAuthorityGate : Setω where
  field
    providerPayloadIntake :
      Provider.HEPDataResidualProviderReceiptRequestPack

    nonCollapseObligation :
      NonCollapse.HEPDataNonCollapseObservableObligationDiagnostic

    residualComparisonLawRequest :
      Law.HEPDataResidualComparisonLawRequestDiagnostic

    currentStatus :
      HEPDataResidualBridgeAuthorityGateStatus

    acceptedAnswerClasses :
      List HEPDataResidualProviderAcceptedAnswerClass

    acceptedAnswerClassesAreCanonical :
      acceptedAnswerClasses
      ≡
      canonicalHEPDataResidualProviderAcceptedAnswerClasses

    rejectedAnswerClasses :
      List HEPDataResidualProviderRejectedAnswerClass

    rejectedAnswerClassesAreCanonical :
      rejectedAnswerClasses
      ≡
      canonicalHEPDataResidualProviderRejectedAnswerClasses

    requiredPayloadFields :
      List HEPDataResidualBridgeGateRequiredPayloadField

    requiredPayloadFieldsAreCanonical :
      requiredPayloadFields
      ≡
      canonicalHEPDataResidualBridgeGateRequiredPayloadFields

    empiricalCalibrationChecklist :
      List Provider.HEPDataResidualEmpiricalCalibrationChecklistItem

    empiricalCalibrationChecklistIsCanonical :
      empiricalCalibrationChecklist
      ≡
      Provider.canonicalHEPDataResidualEmpiricalCalibrationChecklist

    boundaries :
      List HEPDataResidualBridgeAuthorityGateBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataResidualBridgeAuthorityGateBoundaries

    residualBridgeIsReceiptFilter :
      Bool

    residualBridgeIsDataBridge :
      Bool

    rejectsBadDataAnswers :
      Bool

    acceptedAuthorityTokenConstructible :
      Bool

    acceptedAuthorityRouteConstructible :
      Bool

    residualComparisonLawConstructible :
      Bool

    nonCollapseWitnessConstructible :
      Bool

    impossibleAcceptedAuthorityTokenHere :
      Authority.HEPDataAcceptedDatasetAuthorityToken →
      ⊥

    impossibleAcceptedAuthorityRouteHere :
      {observable : HEP.HEPDataObservable} →
      Authority.HEPDataAcceptedDatasetAuthorityRoute observable →
      ⊥

    impossibleResidualComparisonLawReceiptHere :
      {observable : HEP.HEPDataObservable} →
      Law.HEPDataResidualComparisonLawReceipt observable →
      ⊥

    impossibleNonCollapseWitnessReceiptTargetHere :
      {observable : HEP.HEPDataObservable} →
      NonCollapse.HEPDataNonCollapseWitnessReceiptTarget observable →
      ⊥

    gateInstructions :
      List String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

    coordinationBoardSummary :
      String

canonicalHEPDataResidualBridgeAuthorityGate :
  HEPDataResidualBridgeAuthorityGate
canonicalHEPDataResidualBridgeAuthorityGate =
  record
    { providerPayloadIntake =
        Provider.canonicalHEPDataResidualProviderReceiptRequestPack
    ; nonCollapseObligation =
        NonCollapse.canonicalHEPDataNonCollapseObservableObligationDiagnostic
    ; residualComparisonLawRequest =
        Law.canonicalHEPDataResidualComparisonLawRequestDiagnostic
    ; currentStatus =
        blockedAwaitingResidualAuthorityReceiptChain
    ; acceptedAnswerClasses =
        canonicalHEPDataResidualProviderAcceptedAnswerClasses
    ; acceptedAnswerClassesAreCanonical =
        refl
    ; rejectedAnswerClasses =
        canonicalHEPDataResidualProviderRejectedAnswerClasses
    ; rejectedAnswerClassesAreCanonical =
        refl
    ; requiredPayloadFields =
        canonicalHEPDataResidualBridgeGateRequiredPayloadFields
    ; requiredPayloadFieldsAreCanonical =
        refl
    ; empiricalCalibrationChecklist =
        Provider.canonicalHEPDataResidualEmpiricalCalibrationChecklist
    ; empiricalCalibrationChecklistIsCanonical =
        refl
    ; boundaries =
        canonicalHEPDataResidualBridgeAuthorityGateBoundaries
    ; boundariesAreCanonical =
        refl
    ; residualBridgeIsReceiptFilter =
        true
    ; residualBridgeIsDataBridge =
        false
    ; rejectsBadDataAnswers =
        true
    ; acceptedAuthorityTokenConstructible =
        false
    ; acceptedAuthorityRouteConstructible =
        false
    ; residualComparisonLawConstructible =
        false
    ; nonCollapseWitnessConstructible =
        false
    ; impossibleAcceptedAuthorityTokenHere =
        Authority.acceptedDatasetAuthorityTokenImpossibleHere
    ; impossibleAcceptedAuthorityRouteHere =
        Authority.acceptedDatasetAuthorityRouteImpossibleHere
    ; impossibleResidualComparisonLawReceiptHere =
        Law.residualComparisonLawReceiptImpossibleHere
    ; impossibleNonCollapseWitnessReceiptTargetHere =
        NonCollapse.nonCollapseWitnessReceiptTargetImpossibleHere
    ; gateInstructions =
        "Accept only a full residual receipt chain or the first missing typed residual receipt diagnostic"
        ∷ "Require selected residual observable, baseline/invariance model, residual definition, covariance/calibration, theorem-side projection, defect projection, comparison law, accepted authority route, and non-collapse witness"
        ∷ "For W4/W5 Drell-Yan use, covariance/calibration includes unit calibration, PDF/luminosity convention, HEPData bin/covariance, chi2/dof reproducibility, scale-setting boundary, no-free-fit audit, and no-posterior-tuning freeze audit"
        ∷ "Reject raw saturated values, local artifact paths, unchecksumed selections, missing authority routes, and answers without a non-collapse witness"
        ∷ "Treat the residual bridge as a receipt filter only; do not transport local data into theorem authority"
        ∷ "Do not construct an accepted authority token or promote W3/W4/W5/W8"
        ∷ []
    ; coordinationMapNodeText =
        "rectangle \"HEP-R9\\nresidual bridge authority gate\\nreceipt filter, not data bridge\\naccept full chain or first-missing typed receipt\\nreject raw/path/unchecksumed/no-route/no-witness\" as HEPDATA_HEPR9 #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_HEPR4 --> HEPDATA_HEPR9 : residual provider payload intake\nHEPDATA_HEPR5 --> HEPDATA_HEPR9 : non-collapse witness obligation\nHEPDATA_HEPR6 --> HEPDATA_HEPR9 : residual comparison-law request\nHEPDATA_HEPE --> HEPDATA_HEPR9 : accepted authority route remains future receipt dependency\nHEPDATA_HEPR9 --> Plateau : blocked until full residual authority receipt chain or first-missing typed receipt\nHEPDATA_HEPR9 --> W3 : no accepted-authority promotion\nHEPDATA_HEPR9 --> W4 : no calibration promotion\nHEPDATA_HEPR9 --> W5 : no physical closure promotion\nHEPDATA_HEPR9 --> W8 : no origin receipt promotion"
    ; coordinationBoardSummary =
        "HEP-R9 added DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate: non-promoting residual authority gate links HEP-R4 provider payload intake, HEP-R5 non-collapse obligation, and HEP-R6 comparison-law request. It classifies accepted provider answers as full residual receipt chain or first-missing typed receipt only, rejects raw/path/unchecksumed/no-route/no-witness answers, and constructs no accepted authority token or W3/W4/W5/W8 promotion."
    }

canonicalHEPDataResidualBridgeAuthorityGateStatus :
  HEPDataResidualBridgeAuthorityGateStatus
canonicalHEPDataResidualBridgeAuthorityGateStatus =
  blockedAwaitingResidualAuthorityReceiptChain
