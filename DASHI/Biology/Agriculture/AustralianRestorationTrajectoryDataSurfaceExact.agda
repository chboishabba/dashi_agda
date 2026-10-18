module DASHI.Biology.Agriculture.AustralianRestorationTrajectoryDataSurfaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- AUSTRALIAN RESTORATION QUANTITATIVE TRAJECTORY DATA SURFACE
--
-- ARTICLE
--
-- Liddicoat et al. (2022) develop soil-eDNA bacterial-community
-- rehabilitation-trajectory assessments for three >25-year post-mining
-- chronosequences in south-west Western Australia.
--
-- DATA / CODE PROVENANCE
--
-- The supporting Flinders repository exposes the underlying data and R code
-- and labels the deposited dataset reusable under CC-BY.  The public
-- liddic/resto_traj code repository declares an MIT licence.
--
-- These licence/provenance statements belong to their respective artifacts:
-- the journal article, deposited dataset and code repository are not one
-- authority object.
--
-- DASHI uses this as a quantitative age-indexed data surface that can support
-- future proof-search for increment/majorant models.  It remains a
-- chronosequence: rehabilitation age is not repeated measurement of the same
-- plot, and microbiome-reference similarity is not the whole ecosystem state.
------------------------------------------------------------------------

liddicoatEtAl2022DOI : String
liddicoatEtAl2022DOI = "10.1016/j.jenvman.2022.114748"

liddicoatEtAl2022 : Attribution.AttributedSource
liddicoatEtAl2022 = Attribution.mkDOISource
  "Craig Liddicoat; Siegfried L. Krauss; Andrew Bissett; Ryan J. Borrett; Luisa C. Ducki; Shawn D. Peddle; Paul Bullock; Mark P. Dobrowolski; Andrew Grigg; Mark Tibbett; Martin F. Breed"
  "Next generation restoration metrics: Using soil eDNA bacterial community data to measure trajectories towards rehabilitation targets"
  "Journal of Environmental Management 310:114748"
  "2022" liddicoatEtAl2022DOI "https://doi.org/10.1016/j.jenvman.2022.114748"
  Attribution.academicArticleSource
  "Proof-of-concept soil-eDNA bacterial-community rehabilitation trajectory assessments across three long-term post-mining chronosequences in south-west Western Australia. The study examines similarity-to-reference trajectories, alternative distance/data-processing choices and recovery-time modelling. Retained as quantitative chronosequence/model evidence, not repeated same-plot longitudinal recovery or whole-ecosystem convergence."
  Attribution.publicAttribution

supportingDatasetURL : String
supportingDatasetURL =
  "https://open.flinders.edu.au/articles/dataset/Code_and_data_supporting_Next_generation_restoration_metrics_Using_soil_eDNA_bacterial_community_data_to_measure_trajectories_towards_rehabilitation_targets_/16920985"

supportingDatasetLicence : String
supportingDatasetLicence = "CC-BY; repository describes the deposited dataset as reusable for any purpose"

restoTrajCodeURL : String
restoTrajCodeURL = "https://github.com/liddic/resto_traj"

restoTrajCodeLicence : String
restoTrajCodeLicence = "MIT"

data RestorationMineSite : Set where
  huntly : RestorationMineSite
  eneabba : RestorationMineSite
  worsley : RestorationMineSite

record RestorationTrajectoryDataReceipt : Set where
  field
    source : Attribution.AttributedSource
    site : RestorationMineSite
    samplingYear : Nat
    minimumRehabilitationAge : Nat
    maximumRehabilitationAge : Nat
    observerReading : String
    designReading : String
    boundedReading : String

open RestorationTrajectoryDataReceipt public

huntlyTrajectoryData : RestorationTrajectoryDataReceipt
huntlyTrajectoryData = record
  { source = liddicoatEtAl2022
  ; site = huntly
  ; samplingYear = 2016
  ; minimumRehabilitationAge = 2
  ; maximumRehabilitationAge = 29
  ; observerReading =
      "soil bacterial eDNA community similarity to multiple ecological reference samples, with soil abiotic context available in the supporting data"
  ; designReading =
      "Alcoa Huntly rehabilitation chronosequence sampled in 2016, spanning 2-29-year-old rehabilitation"
  ; boundedReading =
      "age-indexed cross-sectional rehabilitation data; not repeated measurement of one restoration plot"
  }

eneabbaTrajectoryData : RestorationTrajectoryDataReceipt
eneabbaTrajectoryData = record
  { source = liddicoatEtAl2022
  ; site = eneabba
  ; samplingYear = 2019
  ; minimumRehabilitationAge = 7
  ; maximumRehabilitationAge = 38
  ; observerReading =
      "soil bacterial eDNA community similarity to reference under multiple processing/distance choices"
  ; designReading =
      "Iluka Eneabba mineral-sands rehabilitation chronosequence sampled in 2019, spanning 7-38-year-old rehabilitation"
  ; boundedReading =
      "age-indexed cross-sectional rehabilitation data; not repeated measurement of one restoration plot"
  }

worsleyTrajectoryData : RestorationTrajectoryDataReceipt
worsleyTrajectoryData = record
  { source = liddicoatEtAl2022
  ; site = worsley
  ; samplingYear = 2019
  ; minimumRehabilitationAge = 2
  ; maximumRehabilitationAge = 28
  ; observerReading =
      "soil bacterial eDNA community similarity to reference with soil physicochemical measurements in the study data surface"
  ; designReading =
      "South32 Worsley bauxite rehabilitation chronosequence sampled in 2019, spanning 2-28-year-old rehabilitation"
  ; boundedReading =
      "age-indexed cross-sectional rehabilitation data; not repeated measurement of one restoration plot"
  }

record TrajectoryDataBoundary : Set where
  field
    depositedDatasetExplicitlyReusable : Bool
    publicAnalysisCodeHasExplicitLicence : Bool
    articleLicenceEqualsDatasetLicence : Bool
    ageIndexedChronosequenceEqualsRepeatedSamePlotTrajectory : Bool
    microbiomeSimilarityTrajectoryEqualsWholeEcosystemTrajectory : Bool
    modelPredictedRecoveryTimeEqualsObservedSuccessiveStateIncrement : Bool
    alternativeDistanceMeasuresMayBeErased : Bool
    referenceSiteVariabilityMayBeErased : Bool
    datasetAutomaticallySuppliesCauchyIncrementMajorant : Bool
    crossMineTrajectoryCreatesSameEmpiricalObject : Bool
    trajectoryModelCreatesDeploymentAuthority : Bool

open TrajectoryDataBoundary public

canonicalTrajectoryDataBoundary : TrajectoryDataBoundary
canonicalTrajectoryDataBoundary = record
  { depositedDatasetExplicitlyReusable = true
  ; publicAnalysisCodeHasExplicitLicence = true
  ; articleLicenceEqualsDatasetLicence = false
  ; ageIndexedChronosequenceEqualsRepeatedSamePlotTrajectory = false
  ; microbiomeSimilarityTrajectoryEqualsWholeEcosystemTrajectory = false
  ; modelPredictedRecoveryTimeEqualsObservedSuccessiveStateIncrement = false
  ; alternativeDistanceMeasuresMayBeErased = false
  ; referenceSiteVariabilityMayBeErased = false
  ; datasetAutomaticallySuppliesCauchyIncrementMajorant = false
  ; crossMineTrajectoryCreatesSameEmpiricalObject = false
  ; trajectoryModelCreatesDeploymentAuthority = false
  }

attributionRule : String
attributionRule =
  "Liddicoat et al. 2022 (DOI 10.1016/j.jenvman.2022.114748) owns the published microbiota rehabilitation-trajectory study and its reported model/observer findings. The Flinders supporting-data deposit owns its deposited files and CC-BY reuse statement. The liddic/resto_traj repository owns its R code and MIT licence. DASHI owns only the typed separation of article/data/code provenance, mine-site age-window receipts and no-promotion boundaries. Chronosequence age does not become repeated same-plot time, microbiome similarity does not become whole-ecosystem state, model recovery time does not become an observed successive-state increment, and the data surface does not by itself create a Cauchy majorant or deployment authority."
