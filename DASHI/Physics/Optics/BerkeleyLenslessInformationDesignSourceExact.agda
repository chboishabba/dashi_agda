module DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.DiffuserInformationDesignExact as Design
import DASHI.Physics.Optics.MatchedPhotonImagerComparatorExact as Comparator

------------------------------------------------------------------------
-- PUBLISHED SOURCE / DATA-AVAILABILITY RECEIPT
--
-- Kabuli, Pinkard, Markley, Hung, Waller, Optica 13(2), 227--235 (2026).
-- This source supplies an information-design experiment and public experimental
-- data surfaces comparing optimized RML and DiffuserCam systems.
--
-- IMPORTANT PHOTON BOUNDARY
-- Section-5 public code does not infer physical acquisition photon counts from
-- the cameras. For each real experimental dataset it performs the analysis
-- normalization
--
--   full_dataset / np.mean(full_dataset)
--   -> multiply by mean_photon_count = 500
--   -> add bias = 10
--   -> inject synthetic noise under PoissonNoiseModel.
--
-- Therefore a matched *analysis-photon normalization* is source-paid, while a
-- physical incident/detected-photon calibration of the acquisition systems is
-- not. The latter remains required for a physical matched-photon comparator.
------------------------------------------------------------------------

lenslessInfoDesignDOI : String
lenslessInfoDesignDOI = "10.1364/OPTICA.570334"

lenslessInfoDesignArXiv : String
lenslessInfoDesignArXiv = "2506.08513"

lenslessInfoDesignRepository : String
lenslessInfoDesignRepository = "lakabuli/LenslessInfoDesign"

lenslessInfoDesignCommit : String
lenslessInfoDesignCommit = "f26873c2b58b82d84353bab2bf6edd478c5892a8"

experimentalPhotonAnalysisScript : String
experimentalPhotonAnalysisScript = "experimental_eval/2025_03_29_sec5_experimental_MI_estimation.py"

experimentalPhotonAnalysisScriptBlobSHA : String
experimentalPhotonAnalysisScriptBlobSHA = "dc8af843841870d714ccd70f0d689eaeee34d788"

experimentalMeanPhotonCount : Nat
experimentalMeanPhotonCount = 500

experimentalAnalysisBias : Nat
experimentalAnalysisBias = 10

publishedOpticaArticlePinned : Bool
publishedOpticaArticlePinned = true

informationOptimalEncoderExperimentPinned : Bool
informationOptimalEncoderExperimentPinned = true

parallelLenslessMeasurementsAvailable : Bool
parallelLenslessMeasurementsAvailable = true

analysisPhotonNormalizationPaid : Bool
analysisPhotonNormalizationPaid = true

analysisPoissonNoiseModelPaid : Bool
analysisPoissonNoiseModelPaid = true

physicalAcquisitionPhotonCalibrationPaid : Bool
physicalAcquisitionPhotonCalibrationPaid = false

matchedPhysicalPhotonBudgetPaid : Bool
matchedPhysicalPhotonBudgetPaid = false

rmlAndDiffuserCamModelsAvailable : Bool
rmlAndDiffuserCamModelsAvailable = true

publishedRealRMLVsDiffuserCamComparison : Bool
publishedRealRMLVsDiffuserCamComparison = true

-- The source comparison is between lensless systems / analysis channels. Do not
-- promote it to the stronger focused-lens / diffuser / Fresnel-zone-plate
-- physical matched-photon comparator.
focusedLensFZPComparisonPaid : Bool
focusedLensFZPComparisonPaid = false

record PublishedLenslessInformationComparison : Set where
  field
    doi : String
    arxiv : String
    codeRepository : String
    codeCommit : String
    photonAnalysisScript : String
    photonAnalysisBlobSHA : String
    analysisMeanPhotonCount : Nat
    analysisBias : Nat
    publicationPinned : Bool
    informationDesignExperimentPinned : Bool
    parallelMeasurements : Bool
    matchedAnalysisPhotonNormalization : Bool
    analysisPoissonNoise : Bool
    physicalPhotonCalibration : Bool
    matchedPhysicalPhotonBudget : Bool
    rmlVsDiffuserCamModels : Bool
    realRMLVsDiffuserCamComparison : Bool
    focusedLensDiffuserFZPComparison : Bool

open PublishedLenslessInformationComparison public

publishedLenslessInformationComparison : PublishedLenslessInformationComparison
publishedLenslessInformationComparison = record
  { doi = lenslessInfoDesignDOI
  ; arxiv = lenslessInfoDesignArXiv
  ; codeRepository = lenslessInfoDesignRepository
  ; codeCommit = lenslessInfoDesignCommit
  ; photonAnalysisScript = experimentalPhotonAnalysisScript
  ; photonAnalysisBlobSHA = experimentalPhotonAnalysisScriptBlobSHA
  ; analysisMeanPhotonCount = experimentalMeanPhotonCount
  ; analysisBias = experimentalAnalysisBias
  ; publicationPinned = publishedOpticaArticlePinned
  ; informationDesignExperimentPinned = informationOptimalEncoderExperimentPinned
  ; parallelMeasurements = parallelLenslessMeasurementsAvailable
  ; matchedAnalysisPhotonNormalization = analysisPhotonNormalizationPaid
  ; analysisPoissonNoise = analysisPoissonNoiseModelPaid
  ; physicalPhotonCalibration = physicalAcquisitionPhotonCalibrationPaid
  ; matchedPhysicalPhotonBudget = matchedPhysicalPhotonBudgetPaid
  ; rmlVsDiffuserCamModels = rmlAndDiffuserCamModelsAvailable
  ; realRMLVsDiffuserCamComparison = publishedRealRMLVsDiffuserCamComparison
  ; focusedLensDiffuserFZPComparison = focusedLensFZPComparisonPaid
  }

-- Design and Comparator are intentionally imported only as target semantics.
-- A common synthetic analysis photon scale cannot manufacture matched optical
-- throughput, quantum efficiency, exposure, incident photons or detected
-- photoelectrons in the physical acquisition.
