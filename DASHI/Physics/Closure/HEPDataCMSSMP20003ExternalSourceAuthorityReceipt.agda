module DASHI.Physics.Closure.HEPDataCMSSMP20003ExternalSourceAuthorityReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic as Route
import DASHI.Physics.Closure.HEPDataEmpiricalAuthorityReceiptCollation as Collation
import DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate as Gate

------------------------------------------------------------------------
-- CMS-SMP-20-003 external source-authority receipt surface.
--
-- This module records the confirmed source identity for the HEPData
-- ins2079374 package as a non-promoting typed receipt surface.  It is a
-- source-authority pointer only: it constructs no accepted dataset authority
-- token, no comparison law, no adapter receipt, and no W3/W8 promotion.

data CMSSMP20003SourceAuthorityReceiptStatus : Set where
  sourceIdentityRecordedButAuthorityRouteBlocked :
    CMSSMP20003SourceAuthorityReceiptStatus

data CMSSMP20003SourceAuthorityField : Set where
  sourceINSPIRERecord :
    CMSSMP20003SourceAuthorityField
  hepdataPublicationDOI :
    CMSSMP20003SourceAuthorityField
  cmsAnalysisIdentifier :
    CMSSMP20003SourceAuthorityField
  arxivIdentifier :
    CMSSMP20003SourceAuthorityField
  epjcPublicationPointer :
    CMSSMP20003SourceAuthorityField
  canonicalPaperDOIPointer :
    CMSSMP20003SourceAuthorityField
  rejectedWrongPaperDOIPointer :
    CMSSMP20003SourceAuthorityField
  primaryPhistarTablePointer :
    CMSSMP20003SourceAuthorityField
  primaryPhistarCovariancePointer :
    CMSSMP20003SourceAuthorityField
  electronResponseMatrixPointer :
    CMSSMP20003SourceAuthorityField
  muonResponseMatrixPointer :
    CMSSMP20003SourceAuthorityField
  nonPromotionBoundaryPointer :
    CMSSMP20003SourceAuthorityField
  remainingBlockerPointer :
    CMSSMP20003SourceAuthorityField

canonicalCMSSMP20003SourceAuthorityFields :
  List CMSSMP20003SourceAuthorityField
canonicalCMSSMP20003SourceAuthorityFields =
  sourceINSPIRERecord
  ∷ hepdataPublicationDOI
  ∷ cmsAnalysisIdentifier
  ∷ arxivIdentifier
  ∷ epjcPublicationPointer
  ∷ canonicalPaperDOIPointer
  ∷ rejectedWrongPaperDOIPointer
  ∷ primaryPhistarTablePointer
  ∷ primaryPhistarCovariancePointer
  ∷ electronResponseMatrixPointer
  ∷ muonResponseMatrixPointer
  ∷ nonPromotionBoundaryPointer
  ∷ remainingBlockerPointer
  ∷ []

record CMSSMP20003ExternalSourceAuthorityReceipt : Setω where
  field
    status :
      CMSSMP20003SourceAuthorityReceiptStatus

    empiricalAuthorityCollation :
      Collation.HEPDataEmpiricalAuthorityReceiptCollation

    empiricalAuthorityCollationStatus :
      Collation.HEPDataEmpiricalAuthorityReceiptCollationStatus

    empiricalAuthorityCollationStatusIsBlocked :
      empiricalAuthorityCollationStatus
      ≡
      Collation.authoritySourcesCollatedButAdapterTransformMissing

    residualAuthorityGateStatus :
      Gate.HEPDataResidualBridgeAuthorityGateStatus

    residualAuthorityGateStatusIsBlocked :
      residualAuthorityGateStatus
      ≡
      Gate.blockedAwaitingResidualAuthorityReceiptChain

    comparisonAuthorityRouteDiagnostic :
      Route.HEPDataComparisonAuthorityRouteDiagnostic

    comparisonAuthorityRouteStatus :
      Route.HEPDataComparisonAuthorityRouteStatus

    comparisonAuthorityRouteStatusIsBlocked :
      comparisonAuthorityRouteStatus
      ≡
      Route.blockedAwaitingSelectionCalibrationProjectionAuthorityAdapterReceipts

    acceptedDatasetAuthorityRouteConstructible :
      Bool

    acceptedDatasetAuthorityRouteConstructibleIsFalse :
      acceptedDatasetAuthorityRouteConstructible
      ≡
      false

    sourceAuthorityFields :
      List CMSSMP20003SourceAuthorityField

    sourceAuthorityFieldsAreCanonical :
      sourceAuthorityFields
      ≡
      canonicalCMSSMP20003SourceAuthorityFields

    sourceRecordIdentity :
      List String

    publicationIdentity :
      List String

    primaryDataAndCovariancePointers :
      List String

    responseMatrixPointers :
      List String

    paperDOICorrectionBoundary :
      List String

    nonPromotionBoundary :
      List String

    remainingBlockers :
      List String

    impossibleAcceptedDatasetAuthorityTokenHere :
      Route.HEPDataAcceptedDatasetAuthorityToken →
      ⊥

canonicalCMSSMP20003ExternalSourceAuthorityReceipt :
  CMSSMP20003ExternalSourceAuthorityReceipt
canonicalCMSSMP20003ExternalSourceAuthorityReceipt =
  record
    { status =
        sourceIdentityRecordedButAuthorityRouteBlocked
    ; empiricalAuthorityCollation =
        Collation.canonicalHEPDataEmpiricalAuthorityReceiptCollation
    ; empiricalAuthorityCollationStatus =
        Collation.authoritySourcesCollatedButAdapterTransformMissing
    ; empiricalAuthorityCollationStatusIsBlocked =
        refl
    ; residualAuthorityGateStatus =
        Gate.blockedAwaitingResidualAuthorityReceiptChain
    ; residualAuthorityGateStatusIsBlocked =
        refl
    ; comparisonAuthorityRouteDiagnostic =
        Route.canonicalHEPDataComparisonAuthorityRouteDiagnostic
    ; comparisonAuthorityRouteStatus =
        Route.blockedAwaitingSelectionCalibrationProjectionAuthorityAdapterReceipts
    ; comparisonAuthorityRouteStatusIsBlocked =
        refl
    ; acceptedDatasetAuthorityRouteConstructible =
        false
    ; acceptedDatasetAuthorityRouteConstructibleIsFalse =
        refl
    ; sourceAuthorityFields =
        canonicalCMSSMP20003SourceAuthorityFields
    ; sourceAuthorityFieldsAreCanonical =
        refl
    ; sourceRecordIdentity =
        "HEPData record = https://www.hepdata.net/record/ins2079374"
        ∷ "INSPIRE literature record = ins2079374"
        ∷ "HEPData submission DOI = 10.17182/hepdata.115656.v1"
        ∷ "analysis = CMS-SMP-20-003 / CERN-EP-2022-053"
        ∷ "arXiv = 2205.04897 [hep-ex]"
        ∷ []
    ; publicationIdentity =
        "experiment = CMS at LHC"
        ∷ "publication = Eur. Phys. J. C 83 (2023) 628"
        ∷ "canonical paper DOI = 10.1140/epjc/s10052-023-11631-7"
        ∷ "rejected wrong paper DOI pointer = 10.1140/epjc/s10052-023-11680-y"
        ∷ "HEPData collection DOI = 10.17182/hepdata.115656.v1"
        ∷ []
    ; primaryDataAndCovariancePointers =
        "primary observable table = phistar mass 50-76"
        ∷ "primary observable table DOI = 10.17182/hepdata.115656.v1/t19"
        ∷ "primary covariance table = Covariance matrices for phistar mass 50-76"
        ∷ "primary covariance table DOI = 10.17182/hepdata.115656.v1/t20"
        ∷ []
    ; responseMatrixPointers =
        "electron response matrix = electron response phistar mass 50-76"
        ∷ "electron response matrix DOI = 10.17182/hepdata.115656.v1/t68"
        ∷ "muon response matrix = muon response phistar mass 50-76"
        ∷ "muon response matrix DOI = 10.17182/hepdata.115656.v1/t69"
        ∷ []
    ; paperDOICorrectionBoundary =
        "The canonical CMS-SMP-20-003 paper DOI is 10.1140/epjc/s10052-023-11631-7"
        ∷ "The DOI 10.1140/epjc/s10052-023-11680-y is rejected as the wrong paper pointer for CMS-SMP-20-003"
        ∷ "This DOI correction is resolved at the source-pointer layer but remains non-promoting"
        ∷ []
    ; nonPromotionBoundary =
        "This module records source identity only"
        ∷ "It does not construct HEPDataAcceptedDatasetAuthorityToken"
        ∷ "It does not construct HEPDataITIRAcceptedAuthorityAdapterReceipt"
        ∷ "It does not construct HEPDataComparisonLawReceipt"
        ∷ "It does not construct HEPDataAcceptedDatasetAuthorityRoute"
        ∷ "It does not promote W3 accepted authority"
        ∷ "It does not promote W8 origin authority"
        ∷ []
    ; remainingBlockers =
        "adapter/projection/comparison route still missing"
        ∷ "raw t19/t20 and response t68/t69 source pointers are not a theorem-side DASHI projection"
        ∷ "selected value surface and checksum-bound adapter semantics remain external receipt obligations"
        ∷ "authority token remains constructorless in HEPDataComparisonAuthorityRouteDiagnostic"
        ∷ "paper DOI correction is no longer a blocker in this module"
        ∷ []
    ; impossibleAcceptedDatasetAuthorityTokenHere =
        Route.acceptedDatasetAuthorityTokenImpossibleHere
    }

canonicalCMSSMP20003ExternalSourceAuthorityReceiptStatus :
  CMSSMP20003SourceAuthorityReceiptStatus
canonicalCMSSMP20003ExternalSourceAuthorityReceiptStatus =
  CMSSMP20003ExternalSourceAuthorityReceipt.status
    canonicalCMSSMP20003ExternalSourceAuthorityReceipt
