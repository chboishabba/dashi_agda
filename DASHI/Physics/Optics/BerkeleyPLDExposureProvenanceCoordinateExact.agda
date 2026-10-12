module DASHI.Physics.Optics.BerkeleyPLDExposureProvenanceCoordinateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact as Conv

------------------------------------------------------------------------
-- PRODUCTIVE CROSS-POLLINATION: ACQUISITION-PROVENANCE COORDINATES
--
-- The Berkeley/PLD source surface contains three distinct acquisition tranches:
--   * the 100k publication-facing experiment;
--   * the current released 100k capture-code defaults;
--   * the repository-labelled earlier 25k AWB capture path.
--
-- The paper-facing 50/80/4 ms exposure profile is also present in the older AWB
-- capture code. Therefore an exposure triple alone cannot identify which data
-- tranche generated a selected measurement. Reuse the repository's canonical
-- ExperimentalCoordinateDesign machinery: dataset tranche is a provenance
-- discriminator, while exposure profile is a measured acquisition coordinate.
------------------------------------------------------------------------

data AcquisitionWorld : Set where
  paper100k : AcquisitionWorld
  releasedCurrent100k : AcquisitionWorld
  earlierAWB25k : AcquisitionWorld

data DatasetTranche : Set where
  paperTranche : DatasetTranche
  currentReleasedTranche : DatasetTranche
  earlierAWBTranche : DatasetTranche

data ExposureProfile : Set where
  exposure50_80_4 : ExposureProfile
  exposure25_80_18 : ExposureProfile

data AcquisitionCoordinate : Set where
  datasetTrancheCoordinate : AcquisitionCoordinate
  exposureProfileCoordinate : AcquisitionCoordinate

data AcquisitionValue : Set where
  trancheValue : DatasetTranche → AcquisitionValue
  exposureValue : ExposureProfile → AcquisitionValue

data AcquisitionDimension : Set where
  provenanceDimension : AcquisitionDimension
  exposureDimension : AcquisitionDimension

data NoAcquisitionControl : Set where
  noAcquisitionControl : NoAcquisitionControl

coordinateRole : AcquisitionCoordinate → Design.CoordinateRole
coordinateRole datasetTrancheCoordinate = Design.derivedDiscriminator
coordinateRole exposureProfileCoordinate = Design.measuredObservable

coordinateDimension : AcquisitionCoordinate → AcquisitionDimension
coordinateDimension datasetTrancheCoordinate = provenanceDimension
coordinateDimension exposureProfileCoordinate = exposureDimension

coordinateRead : AcquisitionCoordinate → AcquisitionWorld → AcquisitionValue
coordinateRead datasetTrancheCoordinate paper100k = trancheValue paperTranche
coordinateRead datasetTrancheCoordinate releasedCurrent100k = trancheValue currentReleasedTranche
coordinateRead datasetTrancheCoordinate earlierAWB25k = trancheValue earlierAWBTranche
coordinateRead exposureProfileCoordinate paper100k = exposureValue exposure50_80_4
coordinateRead exposureProfileCoordinate releasedCurrent100k = exposureValue exposure25_80_18
coordinateRead exposureProfileCoordinate earlierAWB25k = exposureValue exposure50_80_4

applyAcquisitionControl : NoAcquisitionControl → AcquisitionWorld → AcquisitionWorld
applyAcquisitionControl noAcquisitionControl world = world

coordinateReference : AcquisitionCoordinate → String
coordinateReference datasetTrancheCoordinate = "paper/current-release/earlier-AWB dataset tranche"
coordinateReference exposureProfileCoordinate = "exposure profile from publication or pinned capture code"

dimensionReference : AcquisitionCoordinate → String
dimensionReference datasetTrancheCoordinate = "source/provenance coordinate"
dimensionReference exposureProfileCoordinate = "camera exposure coordinate"

calibrationReference : AcquisitionCoordinate → String
calibrationReference datasetTrancheCoordinate = Conv.parallelDatasetRepository
calibrationReference exposureProfileCoordinate = Conv.convRMLDOI

controlReference : NoAcquisitionControl → String
controlReference noAcquisitionControl = "observation-only provenance comparison"

pldAcquisitionCoordinateDesign :
  Design.ExperimentalCoordinateDesign
    AcquisitionWorld NoAcquisitionControl AcquisitionValue AcquisitionDimension
pldAcquisitionCoordinateDesign =
  Design.experimentalCoordinateDesign
    AcquisitionCoordinate
    coordinateRole
    coordinateDimension
    coordinateRead
    applyAcquisitionControl
    coordinateReference
    dimensionReference
    calibrationReference
    controlReference

-- Existing high-level label deliberately collapses the three source worlds.
highLevelPLDCode : AcquisitionWorld → Bool
highLevelPLDCode _ = true

paperReleasedTrancheDifferent :
  trancheValue paperTranche ≡ trancheValue currentReleasedTranche → ⊥
paperReleasedTrancheDifferent ()

paperVsReleasedCollision :
  Design.CoordinateSeparatesCollision pldAcquisitionCoordinateDesign highLevelPLDCode
paperVsReleasedCollision =
  Design.coordinateSeparatesCollision
    datasetTrancheCoordinate
    paper100k
    releasedCurrent100k
    refl
    paperReleasedTrancheDifferent

-- The publication-facing and earlier-AWB worlds share the same exposure-profile
-- code. Hence matching 50/80/4 alone cannot prove dataset identity.
paperAndAWBShareExposureProfile :
  coordinateRead exposureProfileCoordinate paper100k
    ≡ coordinateRead exposureProfileCoordinate earlierAWB25k
paperAndAWBShareExposureProfile = refl

exposureProfileDoesNotIdentifyDataset : Bool
exposureProfileDoesNotIdentifyDataset = true

exposureProvenanceCollisionFormalised : Bool
exposureProvenanceCollisionFormalised = true

-- Preserve the source-owner stopping rule: the exact selected 100k dataset run
-- still lacks a same-object capture-configuration receipt.
exactDatasetExposureProvenancePaid : Bool
exactDatasetExposureProvenancePaid = Conv.exactDatasetExposureIdentityReconciled
