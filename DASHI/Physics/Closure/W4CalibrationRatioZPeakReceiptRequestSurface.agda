module DASHI.Physics.Closure.W4CalibrationRatioZPeakReceiptRequestSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataEmpiricalAuthorityReceiptCollation as Collation
import DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic as Unit
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack as W4Request
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate

------------------------------------------------------------------------
-- W4 calibration/ratio Z-peak receipt request surface.
--
-- This module records the same-record CMS/HEPData Z-peak anchors needed for
-- a future ratio-calibration request: phistar 76-106 data/covariance,
-- channel response matrices, and the 50-76 / 76-106 phistar ratio anchor.
--
-- It is only a typed request/anchor surface.  It does not construct a W4 unit
-- calibration receipt, dimensional preservation proof, Candidate256 physical
-- calibration authority token, or any W4/W5/W8 promotion.

data W4CalibrationRatioZPeakRequestStatus : Set where
  blockedAtSameRecordRatioAnchorOnly :
    W4CalibrationRatioZPeakRequestStatus

data W4CalibrationRatioZPeakAnchorRole : Set where
  zPeakPhistarMeasurement :
    W4CalibrationRatioZPeakAnchorRole
  zPeakPhistarCovariance :
    W4CalibrationRatioZPeakAnchorRole
  zPeakElectronResponseMatrix :
    W4CalibrationRatioZPeakAnchorRole
  zPeakMuonResponseMatrix :
    W4CalibrationRatioZPeakAnchorRole
  lowMassToZPeakPhistarRatio :
    W4CalibrationRatioZPeakAnchorRole
  lowMassToZPeakPhistarRatioCovariance :
    W4CalibrationRatioZPeakAnchorRole

record W4CalibrationRatioZPeakTableAnchor : Set where
  field
    role :
      W4CalibrationRatioZPeakAnchorRole

    tableTitle :
      String

    tableDOI :
      String

    tableRecord :
      String

    anchorUse :
      String

canonicalW4CalibrationRatioZPeakAnchors :
  List W4CalibrationRatioZPeakTableAnchor
canonicalW4CalibrationRatioZPeakAnchors =
  record
    { role =
        zPeakPhistarMeasurement
    ; tableTitle =
        "phistar mass 76-106"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t21"
    ; tableRecord =
        "same HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
    ; anchorUse =
        "Z-peak phistar measured surface anchor only"
    }
  ∷ record
    { role =
        zPeakPhistarCovariance
    ; tableTitle =
        "Covariance matrices for phistar mass 76-106"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t22"
    ; tableRecord =
        "same HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
    ; anchorUse =
        "Z-peak phistar covariance anchor only"
    }
  ∷ record
    { role =
        zPeakElectronResponseMatrix
    ; tableTitle =
        "electron response phistar mass 76-106"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t70"
    ; tableRecord =
        "same HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
    ; anchorUse =
        "Z-peak electron-channel response-matrix anchor only"
    }
  ∷ record
    { role =
        zPeakMuonResponseMatrix
    ; tableTitle =
        "muon response phistar mass 76-106"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t71"
    ; tableRecord =
        "same HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
    ; anchorUse =
        "Z-peak muon-channel response-matrix anchor only"
    }
  ∷ record
    { role =
        lowMassToZPeakPhistarRatio
    ; tableTitle =
        "phistar mass 50-76 over mass 76-106"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t43"
    ; tableRecord =
        "same HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
    ; anchorUse =
        "50-76 / 76-106 phistar ratio table anchor only"
    }
  ∷ record
    { role =
        lowMassToZPeakPhistarRatioCovariance
    ; tableTitle =
        "Covariance matrices for phistar mass 50-76 over mass 76-106"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t44"
    ; tableRecord =
        "same HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
    ; anchorUse =
        "supporting ratio covariance anchor only"
    }
  ∷ []

data W4CalibrationRatioZPeakMissingRequirement : Set where
  missingTypedZPeakArtifactReceipt :
    W4CalibrationRatioZPeakMissingRequirement
  missingSameRecordT21T22ArtifactReceipt :
    W4CalibrationRatioZPeakMissingRequirement
  missingTypedRatioArtifactReceipt :
    W4CalibrationRatioZPeakMissingRequirement
  missingResponseMatrixConsumptionLaw :
    W4CalibrationRatioZPeakMissingRequirement
  missingRatioCovarianceCalibrationLaw :
    W4CalibrationRatioZPeakMissingRequirement
  missingCandidate256ScaleMapToZPeakRatio :
    W4CalibrationRatioZPeakMissingRequirement
  missingW4PhysicalUnitCalibrationReceipt :
    W4CalibrationRatioZPeakMissingRequirement
  missingDimensionalPreservationProof :
    W4CalibrationRatioZPeakMissingRequirement

canonicalW4CalibrationRatioZPeakMissingRequirements :
  List W4CalibrationRatioZPeakMissingRequirement
canonicalW4CalibrationRatioZPeakMissingRequirements =
  missingTypedZPeakArtifactReceipt
  ∷ missingSameRecordT21T22ArtifactReceipt
  ∷ missingTypedRatioArtifactReceipt
  ∷ missingResponseMatrixConsumptionLaw
  ∷ missingRatioCovarianceCalibrationLaw
  ∷ missingCandidate256ScaleMapToZPeakRatio
  ∷ missingW4PhysicalUnitCalibrationReceipt
  ∷ missingDimensionalPreservationProof
  ∷ []

data W4SameRecordZPeakRatioCalibrationLaw : Set where

sameRecordZPeakRatioCalibrationLawImpossibleHere :
  W4SameRecordZPeakRatioCalibrationLaw →
  ⊥
sameRecordZPeakRatioCalibrationLawImpossibleHere ()

record W4SameRecordZPeakT21T22ArtifactReceiptRequest : Set where
  field
    measurementAnchor :
      W4CalibrationRatioZPeakTableAnchor

    covarianceAnchor :
      W4CalibrationRatioZPeakTableAnchor

    measurementTableDOI :
      String

    measurementTableDOIIsT21 :
      measurementTableDOI
      ≡
      "10.17182/hepdata.115656.v1/t21"

    covarianceTableDOI :
      String

    covarianceTableDOIIsT22 :
      covarianceTableDOI
      ≡
      "10.17182/hepdata.115656.v1/t22"

    sameRecordRequirement :
      String

    requestedReceiptFields :
      List String

    requestBoundary :
      List String

canonicalW4SameRecordZPeakT21T22ArtifactReceiptRequest :
  W4SameRecordZPeakT21T22ArtifactReceiptRequest
canonicalW4SameRecordZPeakT21T22ArtifactReceiptRequest =
  record
    { measurementAnchor =
        record
          { role =
              zPeakPhistarMeasurement
          ; tableTitle =
              "phistar mass 76-106"
          ; tableDOI =
              "10.17182/hepdata.115656.v1/t21"
          ; tableRecord =
              "same HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
          ; anchorUse =
              "Z-peak phistar measured surface anchor only"
          }
    ; covarianceAnchor =
        record
          { role =
              zPeakPhistarCovariance
          ; tableTitle =
              "Covariance matrices for phistar mass 76-106"
          ; tableDOI =
              "10.17182/hepdata.115656.v1/t22"
          ; tableRecord =
              "same HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
          ; anchorUse =
              "Z-peak phistar covariance anchor only"
          }
    ; measurementTableDOI =
        "10.17182/hepdata.115656.v1/t21"
    ; measurementTableDOIIsT21 =
        refl
    ; covarianceTableDOI =
        "10.17182/hepdata.115656.v1/t22"
    ; covarianceTableDOIIsT22 =
        refl
    ; sameRecordRequirement =
        "t21 and t22 must be supplied from HEPData record ins2079374 / submission 10.17182/hepdata.115656.v1"
    ; requestedReceiptFields =
        "t21 acquisition URL, local path, SHA-256 digest, first header line, and bin binding"
        ∷ "t22 acquisition URL, local path, SHA-256 digest, first header line, and covariance-shape binding"
        ∷ "proof or typed diagnostic that t21/t22 share the same HEPData record and denominator Z-peak mass interval"
        ∷ "explicit statement that these artifacts are anchors only, not a physical unit carrier or dimensional law"
        ∷ []
    ; requestBoundary =
        "This request sharpens the Z-peak artifact intake to t21/t22 before any ratio-calibration law is inhabited"
        ∷ "It does not consume t43/t44, t70/t71, or response matrices"
        ∷ "It does not construct W4SameRecordZPeakRatioCalibrationLaw"
        ∷ "It does not construct Candidate256PhysicalCalibrationAuthorityToken or Candidate256PhysicalCalibrationExternalReceipt"
        ∷ []
    }

record W4CalibrationRatioZPeakReceiptRequestSurface : Setω where
  field
    status :
      W4CalibrationRatioZPeakRequestStatus

    w4RequestPack :
      W4Request.W4PhysicalCalibrationExternalReceiptRequestPack

    w4RequestStatus :
      W4Request.W4PhysicalCalibrationExternalReceiptRequestStatus

    w4RequestStatusIsBlocked :
      w4RequestStatus
      ≡
      W4Request.blockedAwaitingCandidate256PhysicalCalibrationExternalReceipt

    empiricalAuthorityCollation :
      Collation.HEPDataEmpiricalAuthorityReceiptCollation

    unitCalibrationDiagnostic :
      Unit.HEPDataUnitCalibrationRequirementDiagnostic

    zPeakAuthorityName :
      String

    sameRecordPublicationAuthority :
      List String

    sameRecordAnchors :
      List W4CalibrationRatioZPeakTableAnchor

    sameRecordAnchorsAreCanonical :
      sameRecordAnchors
      ≡
      canonicalW4CalibrationRatioZPeakAnchors

    zPeakT21T22ArtifactReceiptRequest :
      W4SameRecordZPeakT21T22ArtifactReceiptRequest

    zPeakT21T22ArtifactReceiptRequestIsCanonical :
      zPeakT21T22ArtifactReceiptRequest
      ≡
      canonicalW4SameRecordZPeakT21T22ArtifactReceiptRequest

    missingRequirements :
      List W4CalibrationRatioZPeakMissingRequirement

    missingRequirementsAreCanonical :
      missingRequirements
      ≡
      canonicalW4CalibrationRatioZPeakMissingRequirements

    providerRequestFields :
      List String

    calibrationRatioBoundary :
      List String

    notUnitCalibrationReceiptBoundary :
      List String

    nonPromotionBoundary :
      List String

    calibrationLawImpossibleHere :
      W4SameRecordZPeakRatioCalibrationLaw →
      ⊥

    candidate256AuthorityImpossibleHere :
      Gate.Candidate256PhysicalCalibrationAuthorityToken →
      ⊥

    candidate256ExternalReceiptImpossibleHere :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

canonicalW4CalibrationRatioZPeakReceiptRequestSurface :
  W4CalibrationRatioZPeakReceiptRequestSurface
canonicalW4CalibrationRatioZPeakReceiptRequestSurface =
  record
    { status =
        blockedAtSameRecordRatioAnchorOnly
    ; w4RequestPack =
        W4Request.canonicalW4PhysicalCalibrationExternalReceiptRequestPack
    ; w4RequestStatus =
        W4Request.blockedAwaitingCandidate256PhysicalCalibrationExternalReceipt
    ; w4RequestStatusIsBlocked =
        refl
    ; empiricalAuthorityCollation =
        Collation.canonicalHEPDataEmpiricalAuthorityReceiptCollation
    ; unitCalibrationDiagnostic =
        Unit.canonicalHEPDataUnitCalibrationRequirementDiagnostic
    ; zPeakAuthorityName =
        "same-record CMS/HEPData Z-peak phistar ratio-calibration anchor"
    ; sameRecordPublicationAuthority =
        "HEPData publication record = https://www.hepdata.net/record/ins2079374"
        ∷ "HEPData submission DOI = 10.17182/hepdata.115656.v1"
        ∷ "publication = CMS-SMP-20-003 / Eur. Phys. J. C 83 (2023) 628"
        ∷ "ratio denominator authority surface = Z mass peak interval 76 <= M_ll < 106 GeV"
        ∷ "anchor purpose = provider-facing calibration/ratio request only"
        ∷ []
    ; sameRecordAnchors =
        canonicalW4CalibrationRatioZPeakAnchors
    ; sameRecordAnchorsAreCanonical =
        refl
    ; zPeakT21T22ArtifactReceiptRequest =
        canonicalW4SameRecordZPeakT21T22ArtifactReceiptRequest
    ; zPeakT21T22ArtifactReceiptRequestIsCanonical =
        refl
    ; missingRequirements =
        canonicalW4CalibrationRatioZPeakMissingRequirements
    ; missingRequirementsAreCanonical =
        refl
    ; providerRequestFields =
        "First bind same-record t21/t22 local artifacts with checksums, first headers, bin binding, and covariance-shape binding"
        ∷ "Keep t21/t22 as Z-peak artifact anchors, not as a physical unit carrier or dimensional preservation law"
        ∷ "Bind raw or normalized local artifacts for t70/t71 and t43 only after the t21/t22 artifact request is discharged or diagnostically blocked"
        ∷ "State how the 50-76 / 76-106 ratio table is consumed as a calibration anchor"
        ∷ "State how electron and muon response matrices are consumed, if at all"
        ∷ "Provide a typed covariance/uncertainty handling law for the ratio-calibration surface"
        ∷ "Provide a typed map from Candidate256 surrogate scale to the Z-peak ratio-calibration carrier"
        ∷ "If promoting W4 later, separately provide the existing Candidate256 physical unit calibration receipt with dimensional preservation"
        ∷ []
    ; calibrationRatioBoundary =
        "The anchors name a same-record Z-peak calibration/ratio surface"
        ∷ "The immediate W4 artifact intake is narrowed to t21/t22 measurement/covariance receipt fields"
        ∷ "The anchors can guide a future provider receipt for ratio calibration"
        ∷ "The constructorless W4SameRecordZPeakRatioCalibrationLaw records that no calibration law is inhabited here"
        ∷ "No response-matrix, covariance, or ratio-consumption theorem is constructed here"
        ∷ []
    ; notUnitCalibrationReceiptBoundary =
        "This surface is not a HEPDataUnitCalibrationRequirementReceipt"
        ∷ "This surface does not choose PhysicalUnitCarrier, DimensionCarrier, dimensionOfUnit, or conversionCalibrationMap"
        ∷ "This surface does not prove preservation or monotonicity for physical units"
        ∷ "The imported HEPDataUnitCalibrationRequirementDiagnostic remains blocked"
        ∷ []
    ; nonPromotionBoundary =
        "This module does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "This module does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This module does not discharge W4 physical calibration, W5 GR/QFT promotion, or W8 origin promotion"
        ∷ "This module does not promote the HEPData empirical authority collation into accepted physical closure"
        ∷ []
    ; calibrationLawImpossibleHere =
        sameRecordZPeakRatioCalibrationLawImpossibleHere
    ; candidate256AuthorityImpossibleHere =
        External.candidate256PhysicalCalibrationAuthorityTokenImpossibleHere
    ; candidate256ExternalReceiptImpossibleHere =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    }

canonicalW4CalibrationRatioZPeakAnchorsAreRequestOnly :
  W4CalibrationRatioZPeakReceiptRequestSurface.sameRecordAnchors
    canonicalW4CalibrationRatioZPeakReceiptRequestSurface
  ≡
  canonicalW4CalibrationRatioZPeakAnchors
canonicalW4CalibrationRatioZPeakAnchorsAreRequestOnly =
  refl

canonicalW4CalibrationRatioZPeakLawIsUninhabited :
  W4SameRecordZPeakRatioCalibrationLaw →
  ⊥
canonicalW4CalibrationRatioZPeakLawIsUninhabited =
  W4CalibrationRatioZPeakReceiptRequestSurface.calibrationLawImpossibleHere
    canonicalW4CalibrationRatioZPeakReceiptRequestSurface
