module DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.DiffuserInformationDesignExact as Design
import DASHI.Physics.Optics.MatchedPhotonImagerComparatorExact as Comparator

------------------------------------------------------------------------
-- PUBLISHED SOURCE / DATA-AVAILABILITY RECEIPT
--
-- Kabuli, Pinkard, Markley, Hung, Waller, Optica 13(2), 227--235 (2026).
-- This source directly supplies an information-design experiment and public
-- experimental data surfaces comparing an optimized random-microlens (RML)
-- system with DiffuserCam.  It is not a focused-lens/diffuser/FZP three-way
-- matched-photon experiment, so that stronger comparator remains open.
------------------------------------------------------------------------

lenslessInfoDesignDOI : String
lenslessInfoDesignDOI = "10.1364/OPTICA.570334"

lenslessInfoDesignArXiv : String
lenslessInfoDesignArXiv = "2506.08513"

lenslessInfoDesignRepository : String
lenslessInfoDesignRepository = "lakabuli/LenslessInfoDesign"

lenslessInfoDesignCommit : String
lenslessInfoDesignCommit = "f26873c2b58b82d84353bab2bf6edd478c5892a8"

publishedOpticaArticlePinned : Bool
publishedOpticaArticlePinned = true

informationOptimalEncoderExperimentPinned : Bool
informationOptimalEncoderExperimentPinned = true

parallelLenslessMeasurementsAvailable : Bool
parallelLenslessMeasurementsAvailable = true

photonCountCalibrationAvailable : Bool
photonCountCalibrationAvailable = true

rmlAndDiffuserCamModelsAvailable : Bool
rmlAndDiffuserCamModelsAvailable = true

publishedRealRMLVsDiffuserCamComparison : Bool
publishedRealRMLVsDiffuserCamComparison = true

-- The source comparison is between two lensless systems.  Do not promote it
-- to the stronger focused-lens / diffuser / Fresnel-zone-plate comparator.
focusedLensFZPComparisonPaid : Bool
focusedLensFZPComparisonPaid = false

record PublishedLenslessInformationComparison : Set where
  field
    doi : String
    arxiv : String
    codeRepository : String
    codeCommit : String
    publicationPinned : Bool
    informationDesignExperimentPinned : Bool
    parallelMeasurements : Bool
    photonCalibration : Bool
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
  ; publicationPinned = publishedOpticaArticlePinned
  ; informationDesignExperimentPinned = informationOptimalEncoderExperimentPinned
  ; parallelMeasurements = parallelLenslessMeasurementsAvailable
  ; photonCalibration = photonCountCalibrationAvailable
  ; rmlVsDiffuserCamModels = rmlAndDiffuserCamModelsAvailable
  ; realRMLVsDiffuserCamComparison = publishedRealRMLVsDiffuserCamComparison
  ; focusedLensDiffuserFZPComparison = focusedLensFZPComparisonPaid
  }

-- Design and Comparator are intentionally imported only as target semantics.
-- Source/data availability cannot by itself inhabit a universal design optimum
-- or the repository's stronger matched-three-imager comparator.
