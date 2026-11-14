module DASHI.Physics.Plasma.KSW668EmpiricalBoundariesExact where

open import DASHI.Core.Prelude

import DASHI.Biology.KSW668HumanCarbon14ObservedExact as Human
import DASHI.Biology.KSW668EmpiricalIsotopeMagnetoreceptionSourceExact as Pigeon
import DASHI.Physics.Plasma.KSW668IsotopeCausalResidualExact as Residual

------------------------------------------------------------------------
-- KSW 668 cross-lane SOURCE-CARRIER EMPIRICAL MAX CUT.
--
-- Real observations are numerical/source-indexed, not arbitrary postulates
-- that a current/emotion/KK mechanism has been realized. A verified source
-- with E1 observations is NOT sufficient to establish E2 causality.
------------------------------------------------------------------------

data AcquisitionState : Set where
  sourceReferenceLocated : AcquisitionState
  sourceRowsTranscribed : AcquisitionState
  rawFileHashVerified : AcquisitionState
  sampleAlignedAndCalibrated : AcquisitionState
  notObserved : AcquisitionState

record SourceScopedMeasurement : Set where
  constructor source-scoped-measurement
  field
    label : String
    originalAuthorsAndDOI : String
    measurementValue : Nat
    originalReportedUncertainty : Nat
    fixedPointScale : Nat
    unitsAndConventions : String
    acquisitionState : AcquisitionState
    originalArtifactReference : String
    sourceVsDerivedBoundary : String

originalDonor24TendonAMS : SourceScopedMeasurement
originalDonor24TendonAMS = source-scoped-measurement
  "Donor24 tendon; original human AMS ID 16243"
  "Heinemeier et al. FASEB J (2013) 10.1096/fj.12-225599"
  13571 35 100 "pMC, analytical sigma (not F14C, not tissue activity)"
  sourceRowsTranscribed
  "Heinemeier Table 1; Artifacts/ksw668/heinemeier2013_original_human_ams_table1.csv"
  "Direct published observation. Tissue nuclear production not measured."

originalDonor24MuscleAMS : SourceScopedMeasurement
originalDonor24MuscleAMS = source-scoped-measurement
  "Donor24 psoas skeletal muscle; original AMS ID 17279"
  "Heinemeier et al. FASEB J (2013) 10.1096/fj.12-225599"
  10996 34 100 "pMC, analytical sigma"
  sourceRowsTranscribed
  "Heinemeier Table 1; Artifacts/ksw668/heinemeier2013_original_human_ams_table1.csv"
  "Direct published observation. Different tissue pool, same donor."

originalDonor26TendonAMS : SourceScopedMeasurement
originalDonor26TendonAMS = source-scoped-measurement
  "Donor26 tendon; original AMS ID 16246"
  "Heinemeier et al. FASEB J (2013) 10.1096/fj.12-225599"
  14848 41 100 "pMC, analytical sigma"
  sourceRowsTranscribed
  "Heinemeier Table 1; Artifacts/ksw668/heinemeier2013_original_human_ams_table1.csv"
  "Direct published observation, not longitudinal or causal intervention."

originalDonor26MuscleAMS : SourceScopedMeasurement
originalDonor26MuscleAMS = source-scoped-measurement
  "Donor26 muscle; original AMS ID 17281"
  "Heinemeier et al. FASEB J (2013) 10.1096/fj.12-225599"
  10979 34 100 "pMC, analytical sigma"
  sourceRowsTranscribed
  "Heinemeier Table 1; Artifacts/ksw668/heinemeier2013_original_human_ams_table1.csv"
  "Direct published observation, not same-tissue pre/post."

originalDonor24SameObjectDifference :
  SourceScopedMeasurement.measurementValue originalDonor24TendonAMS
  ≡ SourceScopedMeasurement.measurementValue originalDonor24MuscleAMS
    + 2575
originalDonor24SameObjectDifference = refl

originalDonor26SameObjectDifference :
  SourceScopedMeasurement.measurementValue originalDonor26TendonAMS
  ≡ SourceScopedMeasurement.measurementValue originalDonor26MuscleAMS
    + 3869
originalDonor26SameObjectDifference = refl

originalPublishedDonor24Comparison :
  Human.pMCHundredths Human.donor24Tendon
  ≡ Human.pMCHundredths Human.donor24Muscle + 2575
originalPublishedDonor24Comparison =
  Human.donor24MeasuredDifferentTissue14C

originalPublishedPigeonOvercastSampleCount :
  Pigeon.numberPigeons Pigeon.pigeonControl
    + Pigeon.numberPigeons Pigeon.pigeonDepleted ≡ 34
originalPublishedPigeonOvercastSampleCount =
  Pigeon.publishedOvercastTotal

record EmpiricalClosureGates : Set where
  constructor empirical-closure-gates
  field
    sourceDOI : String
    mmsBurstRawSeries : AcquisitionState
    mmsFGMEDPFPIFrameMatch : AcquisitionState
    movebankGpsRawTracking : AcquisitionState
    movebankTreatmentAndWeatherJoin : AcquisitionState
    enaRawFastqSeries : AcquisitionState
    originalHumanAMS2013Table : AcquisitionState
    humanWithinPersonEmotionIntervention : AcquisitionState
    siteSpecificGroundNeutronSpectrum : AcquisitionState
    originalPARMAOrGordonNumericSpectrum : AcquisitionState
    sameSampleUptakeClearanceAndNuclearResidual : AcquisitionState
    physicalKKEinsteinObserverSolution : AcquisitionState

empiricalStatusAsOf20261114 : EmpiricalClosureGates
empiricalStatusAsOf20261114 = empirical-closure-gates
  "Original author DOI inventory in Docs/physics/KSW668CrossProgrammeMaxCut.md"
  sourceReferenceLocated
  notObserved
  sourceReferenceLocated
  notObserved
  sourceReferenceLocated
  sourceRowsTranscribed
  notObserved
  notObserved
  sourceReferenceLocated
  notObserved
  notObserved

------------------------------------------------------------------------
-- Source-verified original table > bibliographic citation; however,
-- sourceRowsTranscribed is deliberately NOT rawFileHashVerified and does
-- not inhabit the nuclear / emotion-causation physical residual contract.
------------------------------------------------------------------------
