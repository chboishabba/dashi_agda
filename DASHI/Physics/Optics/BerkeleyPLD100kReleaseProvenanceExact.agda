module DASHI.Physics.Optics.BerkeleyPLD100kReleaseProvenanceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact as Conv
import DASHI.Physics.Optics.BerkeleyPLDExposureProvenanceCoordinateExact as Coordinate

------------------------------------------------------------------------
-- 100K PARALLEL LENSLESS DATASET ACQUISITION / RELEASE-LINEAGE RECEIPT
--
-- Kabuli et al., ConvRML, Optics Express 34(18), 33992--34005 (2026),
-- DOI 10.1364/OE.608614, directly identifies the PLD as the first 100,000
-- MIRFLICKR-1M images. The published automated acquisition method states that
-- display/data capture are synchronized across all three cameras, with 200 ms
-- between cameras and 500 ms between displayed images, and that exposure times
-- calibrated from a reference measurement are 80 ms RML, 50 ms diffuser and
-- 4 ms lens.
--
-- That pays publication-level provenance for the 100k acquisition as a dataset.
-- Separately, release-lineage capture_display.py at commits 86cecbb... (June),
-- 5fba26f... (September) and final 55cca430... carries RGB8, gain=0 and
-- [25000,80000,18000] us in diffuser/RML/ground-truth order. The discrepancy is
-- preserved rather than silently resolved. No per-archive run log has been
-- recovered that welds either configuration to each released archive byte set.
------------------------------------------------------------------------

convRMLDOI : String
convRMLDOI = "10.1364/OE.608614"

pldRepository : String
pldRepository = "Waller-Lab/parallel-lensless-dataset"
pldFinalReleaseCommit : String
pldFinalReleaseCommit = "55cca430641ad785bd7bc355fb0f00671c0d7441"
captureLineageJuneCommit : String
captureLineageJuneCommit = "86cecbb103338e2e6cb4dcd4ee85b10f4827a8f9"
captureLineageSeptemberCommit : String
captureLineageSeptemberCommit = "5fba26f34714d907ded084aefbe24e37b1dd4189"
newDatasetTutorialLinksCommit : String
newDatasetTutorialLinksCommit = "06d1e3e825d367031cc27b225375d20610cf3b83"

mainPLDDriveRoot : String
mainPLDDriveRoot = "1CqPliG5rZIYH5zA6cXdrA6cvDF7obbvc"
fullResolutionMeasurementsFolder : String
fullResolutionMeasurementsFolder = "1YLSHYeM7jJeAMJpNxtArQRKj13QIjtqj"
rmlMeasurementsFolder : String
rmlMeasurementsFolder = "1G_60zOp4hplFz-JzVHVLHieTEuO3Ykjx"
diffuserMeasurementsFolder : String
diffuserMeasurementsFolder = "1IoCGBQjfTSus04yUnBvpPbQZrOAnGJ7J"
rml0k25kArchive : String
rml0k25kArchive = "13tVwvJv_WaoXPwVejLqQsDcNk9AyEj3s"
rml25k50kArchive : String
rml25k50kArchive = "1TUPSCRVfvlZsEUnEq6PnVkGjjE7vlXLH"
rml50k75kArchive : String
rml50k75kArchive = "16UmN-NB6HFNsRRwCEWhwSd-y9-oVD_Hd"
rml75k100kArchive : String
rml75k100kArchive = "18Pf3n41IFBhbKKSddmK58iv5l0FX8ZyY"

awb100kSeparateDatasetLabel : String
awb100kSeparateDatasetLabel = "AWB 100k Dataset - SEPARATE DATASET"
awb25kSeparateDatasetLabel : String
awb25kSeparateDatasetLabel = "AWB 25k Dataset - SEPARATE DATASET"

------------------------------------------------------------------------
-- Direct published 100k acquisition coordinates.
------------------------------------------------------------------------

firstHundredThousandMIRFLICKRImagesPaid : Bool
firstHundredThousandMIRFLICKRImagesPaid = true

publishedSynchronizedThreeCameraAcquisitionPaid : Bool
publishedSynchronizedThreeCameraAcquisitionPaid = true

publishedInterCameraDelayMs : Nat
publishedInterCameraDelayMs = 200

publishedInterImageDelayMs : Nat
publishedInterImageDelayMs = 500

publishedRMLExposureMs : Nat
publishedRMLExposureMs = 80

publishedDiffuserExposureMs : Nat
publishedDiffuserExposureMs = 50

publishedLensExposureMs : Nat
publishedLensExposureMs = 4

published100kAcquisitionProvenancePaid : Bool
published100kAcquisitionProvenancePaid = true

published100kExposureIdentityPaid : Bool
published100kExposureIdentityPaid = true

------------------------------------------------------------------------
-- Release-code lineage: stronger than generic repository defaults, weaker than
-- a same-byte archive run log. Keep the mismatch explicit.
------------------------------------------------------------------------

releaseCaptureDiffuserExposureUs : Nat
releaseCaptureDiffuserExposureUs = 25000
releaseCaptureRMLExposureUs : Nat
releaseCaptureRMLExposureUs = 80000
releaseCaptureGroundTruthExposureUs : Nat
releaseCaptureGroundTruthExposureUs = 18000

releaseCaptureGainZeroPaid : Bool
releaseCaptureGainZeroPaid = true
releaseCaptureRGB8Paid : Bool
releaseCaptureRGB8Paid = true
main100kArchiveIdentityPinned : Bool
main100kArchiveIdentityPinned = true
awbDatasetsExplicitlySeparated : Bool
awbDatasetsExplicitlySeparated = true
releaseLineageCaptureParametersPinned : Bool
releaseLineageCaptureParametersPinned = true

exactArchiveRunLogRecovered : Bool
exactArchiveRunLogRecovered = false

exactArchiveExposureSameRunPaid : Bool
exactArchiveExposureSameRunPaid = false

record BerkeleyPLD100kReleaseProvenanceReceipt : Set where
  field
    doi : String
    repository : String
    finalCommit : String
    juneCaptureCommit : String
    septemberCaptureCommit : String
    driveRoot : String
    first100kMIRFLICKR : Bool
    synchronizedThreeCameraAcquisition : Bool
    interCameraDelayMs : Nat
    interImageDelayMs : Nat
    publishedRMLExposure : Nat
    publishedDiffuserExposure : Nat
    publishedLensExposure : Nat
    publishedAcquisitionProvenance : Bool
    publishedExposureIdentity : Bool
    releaseDiffuserExposureUs : Nat
    releaseRMLExposureUs : Nat
    releaseGroundTruthExposureUs : Nat
    gainZero : Bool
    rgb8 : Bool
    main100kArchiveIdentity : Bool
    awbSeparation : Bool
    releaseLineageParameters : Bool
    archiveRunLog : Bool
    archiveExposureSameRun : Bool

open BerkeleyPLD100kReleaseProvenanceReceipt public

berkeleyPLD100kReleaseProvenanceReceipt : BerkeleyPLD100kReleaseProvenanceReceipt
berkeleyPLD100kReleaseProvenanceReceipt = record
  { doi = convRMLDOI
  ; repository = pldRepository
  ; finalCommit = pldFinalReleaseCommit
  ; juneCaptureCommit = captureLineageJuneCommit
  ; septemberCaptureCommit = captureLineageSeptemberCommit
  ; driveRoot = mainPLDDriveRoot
  ; first100kMIRFLICKR = firstHundredThousandMIRFLICKRImagesPaid
  ; synchronizedThreeCameraAcquisition = publishedSynchronizedThreeCameraAcquisitionPaid
  ; interCameraDelayMs = publishedInterCameraDelayMs
  ; interImageDelayMs = publishedInterImageDelayMs
  ; publishedRMLExposure = publishedRMLExposureMs
  ; publishedDiffuserExposure = publishedDiffuserExposureMs
  ; publishedLensExposure = publishedLensExposureMs
  ; publishedAcquisitionProvenance = published100kAcquisitionProvenancePaid
  ; publishedExposureIdentity = published100kExposureIdentityPaid
  ; releaseDiffuserExposureUs = releaseCaptureDiffuserExposureUs
  ; releaseRMLExposureUs = releaseCaptureRMLExposureUs
  ; releaseGroundTruthExposureUs = releaseCaptureGroundTruthExposureUs
  ; gainZero = releaseCaptureGainZeroPaid
  ; rgb8 = releaseCaptureRGB8Paid
  ; main100kArchiveIdentity = main100kArchiveIdentityPinned
  ; awbSeparation = awbDatasetsExplicitlySeparated
  ; releaseLineageParameters = releaseLineageCaptureParametersPinned
  ; archiveRunLog = exactArchiveRunLogRecovered
  ; archiveExposureSameRun = exactArchiveExposureSameRunPaid
  }

-- Publication-level acquisition provenance is now paid for the named 100k PLD.
-- Byte-archive lineage remains a stronger object: without a per-run manifest we
-- do not identify every released archive's bytes with one capture-script state.
