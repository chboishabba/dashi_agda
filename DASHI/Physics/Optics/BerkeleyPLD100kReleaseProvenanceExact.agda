module DASHI.Physics.Optics.BerkeleyPLD100kReleaseProvenanceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact as Conv
import DASHI.Physics.Optics.BerkeleyPLDExposureProvenanceCoordinateExact as Coordinate

------------------------------------------------------------------------
-- 100K PARALLEL LENSLESS DATASET RELEASE-LINEAGE RECEIPT
--
-- The final PLD repository identifies tutorials/preprocess_4x_PLD.ipynb as the
-- up-to-date preprocessing path corresponding to the 100,000-image PLD used by
-- ConvRML. The public Drive root separately labels the main PLD, an AWB 100k
-- dataset, and an AWB 25k dataset. The main full-resolution RML branch is split
-- into 0--25k, 25--50k, 50--75k and 75--100k archives.
--
-- The release-lineage capture_display.py at commits 86cecbb... (2026-06-21),
-- 5fba26f... (2026-09-06) and final 55cca430... uses RGB8, gain=0, and
-- exposure_times [25000, 80000, 18000] us in diffuser/RML/ground-truth order.
-- This strongly pins the RELEASE CONFIGURATION LINEAGE. No per-run log or
-- metadata file was observed beside the published archives that welds those
-- defaults to the exact bytes in every 25k archive. Therefore same-run exposure
-- identity remains fail-closed.
------------------------------------------------------------------------

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
    repository : String
    finalCommit : String
    juneCaptureCommit : String
    septemberCaptureCommit : String
    tutorialLinksCommit : String
    driveRoot : String
    fullResolutionFolder : String
    rmlFolder : String
    diffuserFolder : String
    firstRMLArchive : String
    lastRMLArchive : String
    awb100kLabel : String
    awb25kLabel : String
    diffuserExposureUs : Nat
    rmlExposureUs : Nat
    groundTruthExposureUs : Nat
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
  { repository = pldRepository
  ; finalCommit = pldFinalReleaseCommit
  ; juneCaptureCommit = captureLineageJuneCommit
  ; septemberCaptureCommit = captureLineageSeptemberCommit
  ; tutorialLinksCommit = newDatasetTutorialLinksCommit
  ; driveRoot = mainPLDDriveRoot
  ; fullResolutionFolder = fullResolutionMeasurementsFolder
  ; rmlFolder = rmlMeasurementsFolder
  ; diffuserFolder = diffuserMeasurementsFolder
  ; firstRMLArchive = rml0k25kArchive
  ; lastRMLArchive = rml75k100kArchive
  ; awb100kLabel = awb100kSeparateDatasetLabel
  ; awb25kLabel = awb25kSeparateDatasetLabel
  ; diffuserExposureUs = releaseCaptureDiffuserExposureUs
  ; rmlExposureUs = releaseCaptureRMLExposureUs
  ; groundTruthExposureUs = releaseCaptureGroundTruthExposureUs
  ; gainZero = releaseCaptureGainZeroPaid
  ; rgb8 = releaseCaptureRGB8Paid
  ; main100kArchiveIdentity = main100kArchiveIdentityPinned
  ; awbSeparation = awbDatasetsExplicitlySeparated
  ; releaseLineageParameters = releaseLineageCaptureParametersPinned
  ; archiveRunLog = exactArchiveRunLogRecovered
  ; archiveExposureSameRun = exactArchiveExposureSameRunPaid
  }

-- Cross-pollination boundary: the prior ExperimentalCoordinateDesign receipt
-- explains why exposure-profile equality cannot identify a dataset. This owner
-- supplies the stronger archive/release lineage needed for the selected 100k
-- PLD while preserving the final missing same-run-log witness.
