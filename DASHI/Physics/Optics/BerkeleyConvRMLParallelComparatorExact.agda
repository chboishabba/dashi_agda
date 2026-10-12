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
-- The source reports a standardized parallel acquisition setup that images the
-- same scene with RML, diffuser and conventional-lens systems. It further pays
-- useful detector-control coordinates: identical Basler daA1920-160uc / Sony
-- IMX392 sensor models, same illumination, approximately equal magnification,
-- and reference-calibrated exposures of 80 ms (RML), 50 ms (diffuser), and
-- 4 ms (lens). These unequal exposures explicitly block any silent inference
-- of equal exposure or matched incident/detected photon budget.
------------------------------------------------------------------------

convRMLDOI : String
convRMLDOI = "10.1364/OE.608614"

convRMLArXiv : String
convRMLArXiv = "2602.04834"

convRMLRepository : String
convRMLRepository = "lakabuli/ConvRML"

convRMLCommit : String
convRMLCommit = "0a895cb372a3c7090904027ed7c82fc0a74133c5"

sensorModel : String
sensorModel = "Basler daA1920-160uc / Sony IMX392"

measurementsPerSystem : Nat
measurementsPerSystem = 100000

rmlExposureMilliseconds : Nat
rmlExposureMilliseconds = 80

diffuserExposureMilliseconds : Nat
diffuserExposureMilliseconds = 50

lensExposureMilliseconds : Nat
lensExposureMilliseconds = 4

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
    sensor : String
    measurementsEach : Nat
    rmlExposureMs : Nat
    diffuserExposureMs : Nat
    lensExposureMs : Nat
    parallelThreeSystemAcquisition : Bool
    sameSceneAcquisition : Bool
    sourceReportsHundredThousandEach : Bool
    publicRMLDiffuserPaths : Bool
    lensedGroundTruthCoordinate : Bool
    identicalSensorModel : Bool
    sameIllumination : Bool
    sameMagnification : Bool
    exposureCalibration : Bool
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
  ; sensor = sensorModel
  ; measurementsEach = measurementsPerSystem
  ; rmlExposureMs = rmlExposureMilliseconds
  ; diffuserExposureMs = diffuserExposureMilliseconds
  ; lensExposureMs = lensExposureMilliseconds
  ; parallelThreeSystemAcquisition = parallelLensDiffuserRMLAcquisitionPaid
  ; sameSceneAcquisition = sameSceneParallelAcquisitionPaid
  ; sourceReportsHundredThousandEach = hundredThousandMeasurementsPerSystem
  ; publicRMLDiffuserPaths = publicRMLAndDiffuserDatasetPathsPaid
  ; lensedGroundTruthCoordinate = lensedGroundTruthCoordinatePaid
  ; identicalSensorModel = identicalSensorModelPaid
  ; sameIllumination = sameIlluminationPaid
  ; sameMagnification = sameMagnificationPaid
  ; exposureCalibration = exposureCalibrationPaid
  ; equalExposureAcrossSystems = equalExposureAcrossSystemsPaid
  ; matchedPhotonAcrossSystems = matchedPhotonAcrossSystemsPaid
  ; fresnelZonePlateArm = fresnelZonePlateArmPaid
  }

-- Comparator is imported only to identify the stronger target contract.
-- Same sensor/illumination/geometry plus calibrated exposure is valuable
-- standardisation evidence, but unequal exposures and distinct apertures/encoders
-- mean a matched-photon claim still requires explicit photon/throughput receipts.
