module DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.MatchedPhotonImagerComparatorExact as Comparator
import DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact as InfoSource

------------------------------------------------------------------------
-- CURRENT BERKELEY PARALLEL-COMPARATOR SOURCE RECEIPT
--
-- Kabuli, Hung, Ponomarenko, Markley & Waller,
-- "ConvRML: high-quality lensless imaging with random multi-focal lenslets",
-- Optics Express 34(18), 33992--34005 (2026), DOI 10.1364/OE.608614.
--
-- The publication reports a standardized parallel acquisition setup with
-- identical Basler daA1920-160uc / Sony IMX392 sensors, common illumination,
-- approximately equal magnification and reference-calibrated exposures of
-- 80 ms (RML), 50 ms (diffuser), and 4 ms (lens).
--
-- The public PLD capture submodule pinned by the ConvRML repository exposes a
-- distinct released-code surface: commit 55cca430... sets RGB8, gain=0 and
-- default exposure_times = [25000, 80000, 18000] microseconds in order
-- Diffuser/RML/ground-truth.  Those defaults are not silently identified with
-- the paper-reported 50/80/4 ms values. Exact dataset-run provenance must say
-- which capture configuration generated the selected measurements.
------------------------------------------------------------------------

convRMLDOI : String
convRMLDOI = "10.1364/OE.608614"

convRMLArXiv : String
convRMLArXiv = "2602.04834"

convRMLRepository : String
convRMLRepository = "lakabuli/ConvRML"

convRMLCommit : String
convRMLCommit = "0a895cb372a3c7090904027ed7c82fc0a74133c5"

parallelDatasetRepository : String
parallelDatasetRepository = "Waller-Lab/parallel-lensless-dataset"

parallelDatasetCommit : String
parallelDatasetCommit = "55cca430641ad785bd7bc355fb0f00671c0d7441"

sensorModel : String
sensorModel = "Basler daA1920-160uc / Sony IMX392"

releasedCaptureFormat : String
releasedCaptureFormat = "RGB8"

measurementsPerSystem : Nat
measurementsPerSystem = 100000

-- Publication-reported exposure calibration.
rmlExposureMilliseconds : Nat
rmlExposureMilliseconds = 80

diffuserExposureMilliseconds : Nat
diffuserExposureMilliseconds = 50

lensExposureMilliseconds : Nat
lensExposureMilliseconds = 4

-- Released capture_display.py defaults at the pinned PLD commit.
releasedDiffuserExposureMicroseconds : Nat
releasedDiffuserExposureMicroseconds = 25000

releasedRMLExposureMicroseconds : Nat
releasedRMLExposureMicroseconds = 80000

releasedGroundTruthExposureMicroseconds : Nat
releasedGroundTruthExposureMicroseconds = 18000

parallelLensDiffuserRMLAcquisitionPaid : Bool
parallelLensDiffuserRMLAcquisitionPaid = true

sameSceneParallelAcquisitionPaid : Bool
sameSceneParallelAcquisitionPaid = true

hundredThousandMeasurementsPerSystem : Bool
hundredThousandMeasurementsPerSystem = true

publicRMLAndDiffuserDatasetPathsPaid : Bool
publicRMLAndDiffuserDatasetPathsPaid = true

lensedGroundTruthCoordinatePaid : Bool
lensedGroundTruthCoordinatePaid = true

identicalSensorModelPaid : Bool
identicalSensorModelPaid = true

sameIlluminationPaid : Bool
sameIlluminationPaid = true

sameMagnificationPaid : Bool
sameMagnificationPaid = true

exposureCalibrationPaid : Bool
exposureCalibrationPaid = true

releasedCaptureGainZeroPaid : Bool
releasedCaptureGainZeroPaid = true

releasedCaptureRGB8Paid : Bool
releasedCaptureRGB8Paid = true

paperVsReleasedDefaultExposureMismatchExplicit : Bool
paperVsReleasedDefaultExposureMismatchExplicit = true

exactDatasetExposureIdentityReconciled : Bool
exactDatasetExposureIdentityReconciled = false

equalExposureAcrossSystemsPaid : Bool
equalExposureAcrossSystemsPaid = false

matchedPhotonAcrossSystemsPaid : Bool
matchedPhotonAcrossSystemsPaid = false

fresnelZonePlateArmPaid : Bool
fresnelZonePlateArmPaid = false

record BerkeleyConvRMLParallelComparatorReceipt : Set where
  field
    doi : String
    arxiv : String
    repository : String
    commit : String
    pldRepository : String
    pldCommit : String
    sensor : String
    releasedPixelFormat : String
    measurementsEach : Nat
    paperRMLExposureMs : Nat
    paperDiffuserExposureMs : Nat
    paperLensExposureMs : Nat
    releasedDiffuserExposureUs : Nat
    releasedRMLExposureUs : Nat
    releasedGroundTruthExposureUs : Nat
    parallelThreeSystemAcquisition : Bool
    sameSceneAcquisition : Bool
    sourceReportsHundredThousandEach : Bool
    publicRMLDiffuserPaths : Bool
    lensedGroundTruthCoordinate : Bool
    identicalSensorModel : Bool
    sameIllumination : Bool
    sameMagnification : Bool
    exposureCalibration : Bool
    releasedGainZero : Bool
    releasedRGB8 : Bool
    exposureSourceMismatchExplicit : Bool
    exactDatasetExposureReconciled : Bool
    equalExposureAcrossSystems : Bool
    matchedPhotonAcrossSystems : Bool
    fresnelZonePlateArm : Bool

open BerkeleyConvRMLParallelComparatorReceipt public

berkeleyConvRMLParallelComparatorReceipt : BerkeleyConvRMLParallelComparatorReceipt
berkeleyConvRMLParallelComparatorReceipt = record
  { doi = convRMLDOI
  ; arxiv = convRMLArXiv
  ; repository = convRMLRepository
  ; commit = convRMLCommit
  ; pldRepository = parallelDatasetRepository
  ; pldCommit = parallelDatasetCommit
  ; sensor = sensorModel
  ; releasedPixelFormat = releasedCaptureFormat
  ; measurementsEach = measurementsPerSystem
  ; paperRMLExposureMs = rmlExposureMilliseconds
  ; paperDiffuserExposureMs = diffuserExposureMilliseconds
  ; paperLensExposureMs = lensExposureMilliseconds
  ; releasedDiffuserExposureUs = releasedDiffuserExposureMicroseconds
  ; releasedRMLExposureUs = releasedRMLExposureMicroseconds
  ; releasedGroundTruthExposureUs = releasedGroundTruthExposureMicroseconds
  ; parallelThreeSystemAcquisition = parallelLensDiffuserRMLAcquisitionPaid
  ; sameSceneAcquisition = sameSceneParallelAcquisitionPaid
  ; sourceReportsHundredThousandEach = hundredThousandMeasurementsPerSystem
  ; publicRMLDiffuserPaths = publicRMLAndDiffuserDatasetPathsPaid
  ; lensedGroundTruthCoordinate = lensedGroundTruthCoordinatePaid
  ; identicalSensorModel = identicalSensorModelPaid
  ; sameIllumination = sameIlluminationPaid
  ; sameMagnification = sameMagnificationPaid
  ; exposureCalibration = exposureCalibrationPaid
  ; releasedGainZero = releasedCaptureGainZeroPaid
  ; releasedRGB8 = releasedCaptureRGB8Paid
  ; exposureSourceMismatchExplicit = paperVsReleasedDefaultExposureMismatchExplicit
  ; exactDatasetExposureReconciled = exactDatasetExposureIdentityReconciled
  ; equalExposureAcrossSystems = equalExposureAcrossSystemsPaid
  ; matchedPhotonAcrossSystems = matchedPhotonAcrossSystemsPaid
  ; fresnelZonePlateArm = fresnelZonePlateArmPaid
  }

-- Same sensor/illumination/geometry plus explicit gain/format/exposure controls
-- materially narrow the comparator uncertainty. They still do not create equal
-- photons because exposure times differ, optical apertures/encoders differ and
-- the paper/released-code exposure surfaces must be reconciled for the exact
-- selected dataset before any terminal matched-photon claim.
